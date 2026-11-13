"""audit92_families.py -- second pass over audit92_population.jsonl.

For every pair-control (the 92 residuals and the 146 three-cell controls) this
pass reduces the certifying pair's four endpoints to comb/seam data:

  inner seam : b, c are the two edges of ONE blocked zone of one reading rho_i,
               b = (8M-1)/(8 rho_i), c = (8M+1)/(8 rho_i)  =>  gap = c-b = 1/(4 rho_i)
               and the j=0 upper condition d(c-b) <= 3/4 becomes d <= 3 rho_i.
  scissors   : a, e are the two edges of ONE clear zone of one reading rho_o,
               a = (8L+1)/(8 rho_o), e = (8L+7)/(8 rho_o)  =>  span = e-a = 3/(4 rho_o)
               and the j=0 lower condition 1/4 <= d(e-a) becomes rho_o/3 <= d.

So for seam+scissors pairs the whole two-cell certificate is the ratio band
rho_o/3 <= d <= 3 rho_i plus the two cell-containment inequalities -- the
shared-lemma candidate.  Mixed outer edges (a and/or e on other readings or
window edges) are recorded separately.

Also: the exact j of the higher-j controls, the handoff partners and the rate
ranges covered, and the chain-box fires at d=t6 listed box by box.

Exact Fractions throughout; output audit92_families.out (new file).
"""
import json
import os
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations
from math import floor

HERE = os.path.dirname(os.path.abspath(__file__))
R = Q(1, 8)


def load():
    recs = []
    with open(os.path.join(HERE, "audit92_population.jsonl")) as f:
        for l in f:
            l = l.strip()
            if l:
                recs.append(json.loads(l))
    return recs


def binders(v, core):
    out = []
    for rho in core:
        t = v * rho - Q(1, 8)
        if t.denominator == 1 and t >= 0:
            out.append((rho, int(t), "entry"))
        t = v * rho - Q(7, 8)
        if t.denominator == 1 and t >= 0:
            out.append((rho, int(t), "exit"))
    return out


def inner_seam(b_bind, c_bind):
    """(rho_i, M) with b = (8M-1)/(8 rho_i) exit of clear lap M-1 and
    c = (8M+1)/(8 rho_i) entry of clear lap M."""
    out = []
    for rb, lb, kb in b_bind:
        if kb != "exit":
            continue
        for rc, lc, kc in c_bind:
            if kc == "entry" and rb == rc and lc == lb + 1:
                out.append((rb, lc))
    return out


def scissors(a_bind, e_bind):
    """(rho_o, L) with a = (8L+1)/(8 rho_o) and e = (8L+7)/(8 rho_o)."""
    out = []
    for ra, la, ka in a_bind:
        if ka != "entry":
            continue
        for re_, le, ke in e_bind:
            if ke == "exit" and ra == re_ and le == la:
                out.append((ra, la))
    return out


def analyze(rec):
    core = [Q(s) for s in rec["core"]]
    d = Q(rec["d"])
    cells = [(Q(a), Q(b)) for a, b in rec["cells"]]
    cd = rec["canon"]
    A = (Q(cd["A"][0]), Q(cd["A"][1]))
    B = (Q(cd["B"][0]), Q(cd["B"][1]))
    a, b, c, e = A[0], A[1], B[0], B[1]
    bb = binders(b, core)
    cb = binders(c, core)
    ab = binders(a, core)
    eb = binders(e, core)
    seam = inner_seam(bb, cb)
    scis = scissors(ab, eb)
    shape = {"seam": seam, "scissors": scis,
             "gap_eq_1_over_4rho": None, "span_eq_3_over_4rho": None,
             "d_le_3rho_i": None, "d_ge_rho_o_3": None,
             "wA": e if False else b - a, "wB": e - c,
             "dspan": d * (e - a), "dgap": d * (c - b),
             "winA": 1 if a < 1 else 2, "winB": 1 if c < 1 else 2}
    if seam:
        rho_i, M = seam[0]
        shape["gap_eq_1_over_4rho"] = (c - b == Q(1, 4 * rho_i))
        shape["d_le_3rho_i"] = (d <= 3 * rho_i)
        shape["rho_i"], shape["M"] = rho_i, M
    if scis:
        rho_o, L = scis[0]
        shape["span_eq_3_over_4rho"] = (e - a == Q(3, 4 * rho_o))
        shape["d_ge_rho_o_3"] = (d >= rho_o / 3)
        shape["rho_o"], shape["L"] = rho_o, L
    # handoff partner for the canonical pair (ordered, j0 form)
    hp = None
    if cd["jg"] == 0 and b <= c:
        for u, v in cells:
            if c - b <= 3 * (v - u):
                hp = (u, v)
                break
    shape["handoff_partner"] = hp
    shape["handoff_self"] = (hp == B) if hp else None
    if hp:
        W = hp[1] - hp[0]
        shape["handoff_covers_all_d"] = (Q(1, 4) <= d * (e - a)) and (c - b <= 3 * W)
        shape["pair_rate_interval"] = (Q(1, 4 * (e - a)), Q(3, 4 * (c - b)))
        shape["wide_threshold"] = Q(1, 4 * W)
    return shape


def slotclass(core, rho):
    if rho == 1:
        return "pin"
    if rho == max(core):
        return "max"
    return f"i{core.index(rho)}"


def main():
    recs = load()
    out = []

    def emit(s=""):
        out.append(s)
        print(s, flush=True)

    n92 = [r for r in recs if r["label"] == "pair-residual"]
    n146 = [r for r in recs if r["label"] == "three-cell"]

    emit("== shape analysis of canonical certifying pairs ==")
    shapetally92, shapetally146 = Counter(), Counter()
    fam = defaultdict(list)
    detail = []
    for rec in recs:
        core = [Q(s) for s in rec["core"]]
        sh = analyze(rec)
        rec["shape"] = sh
        seam = sh["seam"]
        scis = sh["scissors"]
        if seam and scis:
            kind = "seam+scissors"
        elif seam:
            kind = "seam-mixed"
        elif scis:
            kind = "scissors-only"
        else:
            kind = "other"
        cls = (kind,
               slotclass(core, seam[0][0]) if seam else None,
               seam[0][1] if seam else None,
               slotclass(core, scis[0][0]) if scis else None,
               scis[0][1] if scis else None,
               rec["canon"]["jg"])
        key = (rec["label"], kind)
        (shapetally92 if rec["label"] == "pair-residual" else shapetally146)[key] += 1
        if rec["label"] == "pair-residual":
            fam[cls].append(rec)
        if rec["label"] == "pair-residual":
            detail.append((rec, sh, cls))

    emit("canonical-pair shape census [count by (label, kind)]:")
    for k in ("seam+scissors", "seam-mixed", "scissors-only", "other"):
        emit(f"  {k:14s}: 92-pop {shapetally92[('pair-residual', k)]:3d}   "
             f"146-pop {shapetally146[('three-cell', k)]:3d}")

    emit("")
    emit("== reduced j0 conditions where applicable (92-pop, canonical pairs) ==")
    n_gap = sum(1 for r, s, c in detail if s["seam"])
    n_gap_ok = sum(1 for r, s, c in detail if s["seam"] and s["d_le_3rho_i"])
    n_scis = sum(1 for r, s, c in detail if s["scissors"])
    n_scis_ok = sum(1 for r, s, c in detail if s["scissors"] and s["d_ge_rho_o_3"])
    n_both = sum(1 for r, s, c in detail if s["seam"] and s["scissors"]
                 and s["d_le_3rho_i"] and s["d_ge_rho_o_3"])
    n_gapexact = sum(1 for r, s, c in detail if s["seam"] and s["gap_eq_1_over_4rho"])
    n_scisex = sum(1 for r, s, c in detail if s["scissors"] and s["span_eq_3_over_4rho"])
    emit(f"  inner seam present: {n_gap}/92; gap == 1/(4 rho_i) exactly: {n_gapexact}; "
         f"d <= 3 rho_i: {n_gap_ok}")
    emit(f"  scissors outer present: {n_scis}/92; span == 3/(4 rho_o) exactly: {n_scisex}; "
         f"d >= rho_o/3: {n_scis_ok}")
    emit(f"  full ratio-band certificate (seam+scissors, both reduced conditions): "
         f"{n_both}/92")

    emit("")
    emit("== family table (92-pop, by shape class; seam slot/lap and scissors slot/lap) ==")
    for cls, rs in sorted(fam.items(), key=lambda kv: -len(kv[1])):
        rec = rs[0]
        sh = rec["shape"]
        coreF = [Q(s) for s in rec["core"]]
        ex = f"core=({','.join(rec['core'])}) d={rec['d']}"
        extras = []
        if sh["seam"]:
            extras.append(f"rho_i={sh['seam'][0][0]} (slot {slotclass(coreF, sh['seam'][0][0])}, M={sh['seam'][0][1]})")
        if sh["scissors"]:
            extras.append(f"rho_o={sh['scissors'][0][0]} (L={sh['scissors'][0][1]})")
        if sh.get("handoff_partner"):
            extras.append(f"handoff cell [{sh['handoff_partner'][0]},{sh['handoff_partner'][1]}]"
                          f"{' (self)' if sh['handoff_self'] else ''}")
        emit(f"  n={len(rs):3d} {cls[0]:14s} seam={cls[1]}/{cls[2]} scis={cls[3]}/{cls[4]} "
             f"j={cls[5]}  {ex}  " + "; ".join(extras))

    emit("")
    emit("== all-pairs shape scan (92-pop): does SOME incompatible pair of the "
         "control carry the seam+scissors ratio-band shape? ==")
    cnt = 0
    cnt_seam = 0
    lacking = []
    for rec in n92:
        core = [Q(s) for s in rec["core"]]
        d = Q(rec["d"])
        cells = [(Q(a), Q(b)) for a, b in rec["cells"]]
        ok = False
        ok_seam = False
        for p in rec["pairs"]:
            A, B = cells[p["i"]], cells[p["j"]]
            a, b, c, e = A[0], A[1], B[0], B[1]
            if floor(d * (e - a) - Q(1, 4)) != 0:
                continue
            se = inner_seam(binders(b, core), binders(c, core))
            sc = scissors(binders(a, core), binders(e, core))
            if se:
                ok_seam = True
                if sc and d <= 3 * se[0][0] and d >= sc[0][0] / 3:
                    ok = True
                    break
        cnt += ok
        cnt_seam += ok_seam
        if not ok:
            lacking.append(rec)
    emit(f"  controls with at least one seam+scissors ratio-band j0 pair: {cnt}/92")
    emit(f"  controls with at least one seam-flank (one blocked zone) j0 pair: "
         f"{cnt_seam}/92")
    emit(f"  controls without any seam+scissors pair: {len(lacking)}")
    emit("")
    emit("== raw canonical pairs of the controls outside the seam+scissors "
         "ratio-band coverage (for family inspection) ==")
    for rec in lacking:
        emit(f"  core=({','.join(rec['core'])}) d={rec['d']} mech={rec['mech']} "
             f"canon={rec['canon']['kind']} jg={rec['canon']['jg']} "
             f"A=[{rec['canon']['A'][0]},{rec['canon']['A'][1]}] "
             f"B=[{rec['canon']['B'][0]},{rec['canon']['B'][1]}] "
             f"binders a={rec['binders']['a']} b={rec['binders']['b']} "
             f"c={rec['binders']['c']} e={rec['binders']['e']}")

    emit("")
    emit("== the two higher-j controls, in full ==")
    for rec, sh, cls in detail:
        if cls[5] >= 1:
            emit(f"  core=({','.join(rec['core'])}) d={rec['d']} canon j={cls[5]} "
                 f"A=[{rec['canon']['A'][0]},{rec['canon']['A'][1]}] "
                 f"B=[{rec['canon']['B'][0]},{rec['canon']['B'][1]}] "
                 f"winA={sh['winA']} winB={sh['winB']} seam={sh['seam']} "
                 f"scissors={sh['scissors']} mech={rec['mech']}")
            emit(f"    all pair j values: {sorted(set(p['jg'] for p in rec['pairs']))}; "
                 f"n pairs={len(rec['pairs'])}")

    emit("")
    emit("== per-control one-liners (92-pop): d vs ratio band, handoff range ==")
    for rec, sh, cls in detail:
        core = [Q(s) for s in rec["core"]]
        bits = [f"d={rec['d']}"]
        if sh["seam"]:
            bits.append(f"d<=3*{sh['seam'][0][0]}:{sh['d_le_3rho_i']}")
        if sh["scissors"]:
            bits.append(f"d>={sh['scissors'][0][0]}/3:{sh['d_ge_rho_o_3']}")
        if sh.get("pair_rate_interval"):
            lo, hi = sh["pair_rate_interval"]
            bits.append(f"pair covers d in [{lo},{hi}]")
        if sh.get("wide_threshold"):
            bits.append(f"wide at d>={sh['wide_threshold']}"
                        f"{' [covers all d>=pair-lo]' if sh.get('handoff_covers_all_d') else ''}")
        emit(f"  ({','.join(rec['core'])}) " + " ".join(bits))

    emit("")
    emit("== chain boxes firing a pair mechanism at d=t6 (exact embedding) ==")
    # recompute quickly from the first pass logic
    import importlib.util
    import sys
    spec = importlib.util.spec_from_file_location(
        "cascade_anchor_audit", os.path.join(HERE, "audit92_anchor_lib.py"))
    anchor = importlib.util.module_from_spec(spec)
    sys.modules["cascade_anchor_audit"] = anchor
    spec.loader.exec_module(anchor)
    sys.path.insert(0, HERE)
    import cascade_rejection_audit as cra
    from itertools import combinations_with_replacement
    d0 = {}
    with open(os.path.join(os.path.dirname(HERE), "j2_g1sweep_checkpoint.jsonl")) as f:
        for l in f:
            l = l.strip()
            if not l:
                continue
            try:
                rr = json.loads(l)
            except Exception:
                continue
            d0[tuple(rr["t"])] = rr
    allt = set(combinations_with_replacement(range(1, 18), 6))
    chain = sorted(t for t in allt if t in d0 and d0[t].get("s1") == "chain")
    for t in chain:
        core = (Q(1),) + tuple(Q(x) for x in t[:5])
        cells = cra.clear_cells(core)
        dd = Q(t[5])
        wide = any(dd * (b - a) >= 2 * R for a, b in cells)
        prs = [(i, j) for i, j in
               combinations(range(len(cells)), 2)
               if cra.incompatible(dd, cells[i], cells[j])]
        if wide or not prs:
            continue
        sh = pinch = None
        wp = None
        w = max(core)
        if Q(145, 21) <= w <= 7 and dd >= w and all(Q(1) <= q <= 5 for q in core if q != w):
            P1 = (Q(1, 8), Q(7) / (8 * w))
            P2 = (Q(9) / (8 * w), Q(7, 40))
            if all(any(A <= p and q <= B for A, B in cells) for p, q in (P1, P2)) \
                    and cra.incompatible(dd, P1, P2):
                pinch = True
        # handoff on best pair
        hf = False
        for i, j in prs:
            (a, b), (c, e) = cells[i], cells[j]
            if floor(dd * (e - a) - Q(1, 4)) == 0 and b <= c:
                if any(c - b <= 3 * (v - u) for u, v in cells):
                    hf = True
        kind = "pinch" if pinch else ("handoff" if hf else "pair")
        jgs = sorted({floor(dd * (cells[j][1] - cells[i][0]) - 2 * R)
                      for i, j in prs})
        emit(f"  box={t} d=t6={dd} kind={kind} n_pairs={len(prs)} jg={jgs}")

    with open(os.path.join(HERE, "audit92_families.out"), "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
