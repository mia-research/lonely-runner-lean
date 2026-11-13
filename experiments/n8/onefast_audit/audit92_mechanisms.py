"""audit92_mechanisms.py -- regenerate the 5,772-control broad sweep of
cascade_rejection_audit.broader_controls, isolate the 92 pair-controls that the
three-cell criterion does not explain, classify each by its certifying mechanism

  (a) pinch theorem   (one_fast_of_first_window_pinch: cells [1/8, 7/(8w)],
                       [9/(8w), 7/40], readings in [1,5], w in [145/21,7], d >= w)
  (b) j=0 ordered pair (clear_of_integer_gap at j=0: 1/4 <= d(e-a), d(c-b) <= 3/4)
  (c) width handoff    (clear_for_fast_rates_of_gap_and_width: j=0 pair plus a
                       cell of width W with c-b <= 3W, so the pair + wide cell
                       cover every rate d >= 1/(4(e-a)))
  (d) higher-j pair    (clear_of_integer_gap at j >= 1)
  (e) none of these    (genuinely uncertified residual)

extract the endpoint-setting readings of the certifying pairs (comb edges
(8j+1)/(8 rho) entry / (8j+7)/(8 rho) exit), build family signatures, and run
the controls: the 146 three-cell population, the 73 chain boxes of
j2_g1sweep_checkpoint.jsonl (embedded as six-slow cores (1, t1..t5) with the
box maximum t6 as fast reading), and a full-population soundness re-check.

Everything is exact (Fractions); floats play no role.  New files only; nothing
existing is modified.  Provenance: the sweep logic is imported verbatim from
cascade_rejection_audit.py in this directory; its dependency cascade_anchor_audit
is aliased from the local byte-copy audit92_anchor_lib.py (taken from
/tmp/lrc-n8-filter-assembly-codex/LonelyRunnerFresh/cascade_anchor_audit.py).
Output: audit92_population.jsonl and audit92_mechanisms.out (both new).
"""
import importlib.util
import json
import os
import sys
import time
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations_with_replacement, combinations
from math import floor
from random import Random

HERE = os.path.dirname(os.path.abspath(__file__))
N8 = os.path.dirname(HERE)

# ---- provenance imports (no existing file modified) -------------------------
_spec = importlib.util.spec_from_file_location(
    "cascade_anchor_audit", os.path.join(HERE, "audit92_anchor_lib.py"))
_anchor = importlib.util.module_from_spec(_spec)
sys.modules["cascade_anchor_audit"] = _anchor
_spec.loader.exec_module(_anchor)
sys.path.insert(0, HERE)
import cascade_rejection_audit as cra  # noqa: E402

R = cra.R
clear_cells = cra.clear_cells
rejects = cra.rejects
incompatible = cra.incompatible
phase_sweep = cra.phase_sweep


# ---- population regeneration (verbatim loop of cra.broader_controls) --------
def broad_population():
    rng = Random(8)
    cores = [(1, *c) for c in combinations(range(2, 13), 5)]
    grid = [Q(i, 16) for i in range(17, 257)]
    cores += [(1, *sorted(rng.sample(grid, 5))) for _ in range(500)]
    assert len(cores) == 962 and len(set(map(tuple, cores))) == 962
    recs, counts = [], Counter()
    for core in cores:
        cells = clear_cells(core)
        for offset in (Q(1, 16), Q(1, 4), 1, 3, 8, 16):
            d = max(core) + offset
            wide = any(d * (b - a) >= 2 * R for a, b in cells)
            prs = []
            for i, j in combinations(range(len(cells)), 2):
                if incompatible(d, cells[i], cells[j]):
                    (a, b), (c, e) = cells[i], cells[j]
                    x = d * (e - a) - 2 * R
                    y = d * (c - b) + 2 * R
                    assert floor(x) + 1 >= y          # no integer in (x, y)
                    prs.append(dict(i=i, j=j, jg=floor(x), x=x, y=y,
                                    span=e - a, gap=c - b,
                                    dspan=d * (e - a), dgap=d * (c - b)))
            pair = (not wide) and bool(prs)
            bad = any(all(rejects(d, c, ph) for c in cells)
                      for ph in phase_sweep(d, cells))
            assert bad == (not wide and not pair)     # framework re-check
            fired3 = False
            if pair:
                for (a, b), (c, e), (f, g) in combinations(cells, 3):
                    if (3 * (f - e) <= e - a and d * (g - c) >= Q(5, 4)
                            and 9 * (c - b) <= 23 * (g - c)):
                        fired3 = True
                        break
            label = ("one cell" if wide else
                     "three-cell" if fired3 else
                     "pair-residual" if pair else "common rejection")
            counts[label] += 1
            if label in ("three-cell", "pair-residual"):
                recs.append(dict(core=[str(q) for q in core], d=str(d),
                                 offset=str(offset), label=label,
                                 cells=[(str(a), str(b)) for a, b in cells],
                                 pairs=[dict(i=p["i"], j=p["j"], jg=p["jg"],
                                             x=str(p["x"]), y=str(p["y"]),
                                             span=str(p["span"]),
                                             gap=str(p["gap"]),
                                             dspan=str(p["dspan"]),
                                             dgap=str(p["dgap"]))
                                         for p in prs]))
    return dict(counts), recs


# ---- mechanism classification -----------------------------------------------
def pinch_shape(core, d):
    """Hypotheses of one_fast_of_first_window_pinch for this core and rate."""
    w = max(core)
    others = [q for q in core if q != w]
    if not (Q(145, 21) <= w <= 7 and d >= w):
        return None
    if not all(Q(1) <= q <= 5 for q in others):
        return None
    return w


def pinch_cells_ok(cells, w, d):
    """The canonical pinch cells are retained and the pair is incompatible."""
    P1 = (Q(1, 8), Q(7) / (8 * w))
    P2 = (Q(9) / (8 * w), Q(7, 40))
    if not all(any(A <= p and q <= B for A, B in cells) for p, q in (P1, P2)):
        return False
    return incompatible(d, P1, P2)


def classify_control(core, d, cells, prs):
    w = max(core)
    flags = dict(pinch=False, j0=False, handoff=False, jpos=False, jneg=False)
    jg_all = [p["jg"] for p in prs]
    flags["j0"] = any(g == 0 for g in jg_all)
    flags["jpos"] = any(g >= 1 for g in jg_all)
    flags["jneg"] = any(g < 0 for g in jg_all)
    wp = pinch_shape(core, d)
    if wp is not None and pinch_cells_ok(cells, wp, d):
        flags["pinch"] = True
    # width handoff on some j=0 pair (ordered cells, third cell of width W
    # with gap <= 3W; the pair's own second cell may serve, as in the pinch)
    handoff_partners = []
    for p in prs:
        if p["jg"] != 0:
            continue
        (a, b), (c, e) = cells[p["i"]], cells[p["j"]]
        if b > c:
            continue
        for u, v in cells:
            if c - b <= 3 * (v - u):
                handoff_partners.append((p["i"], p["j"], cells.index((u, v))))
                break
    flags["handoff"] = bool(handoff_partners)
    if flags["pinch"]:
        mech = "pinch"
    elif flags["handoff"]:
        mech = "handoff"
    elif flags["j0"]:
        mech = "j0-pair"
    elif flags["jpos"]:
        mech = "higher-j"
    else:
        mech = "uncertified"
    return flags, mech, wp, handoff_partners


def canonical_pair(cells, prs, core, d):
    """Pinch pair if it fires, else the (min jg, tightest) incompatible pair."""
    w = pinch_shape(core, d)
    if w is not None and pinch_cells_ok(cells, w, d):
        return (Q(1, 8), Q(7) / (8 * w)), (Q(9) / (8 * w), Q(7, 40)), "pinch"
    best = min(prs, key=lambda p: (p["jg"], p["y"] - p["x"], p["i"], p["j"]))
    return cells[best["i"]], cells[best["j"]], "pair"


def binders(v, core):
    """All (reading, lap, kind, numerator) with (lap+1/8)/rho == v (entry) or
    (lap+7/8)/rho == v (exit).  Entry edges bound clear cells from the left,
    exit edges from the right."""
    out = []
    for rho in core:
        t = v * rho - Q(1, 8)
        if t.denominator == 1 and t >= 0:
            out.append((str(rho), int(t), "entry", 8 * int(t) + 1))
        t = v * rho - Q(7, 8)
        if t.denominator == 1 and t >= 0:
            out.append((str(rho), int(t), "exit", 8 * int(t) + 7))
    return out


def window_of(cell):
    a, _ = cell
    return 1 if a < 1 else 2


def signature(core, cellA, cellB, jg):
    """Family signature: window indices, per-endpoint binder (kind, numerator,
    slot of the reading in the sorted core, lap), and the j class."""
    def slot(rho):
        return core.index(Q(rho))
    sig = []
    for cell in (cellA, cellB):
        sig.append(window_of(cell))
    for cell, side in ((cellA, "L"), (cellA, "R"), (cellB, "L"), (cellB, "R")):
        v = cell[0] if side == "L" else cell[1]
        bs = binders(v, core)
        want = "entry" if side == "L" else "exit"
        prim = [b for b in bs if b[2] == want]
        assert prim, (cell, side, bs)
        b = min(prim, key=lambda t: (slot(t[0]), t[1]))
        sig.append((b[2], b[3], slot(b[0]), b[1]))
    sig.append("j0" if jg == 0 else "jpos" if jg >= 1 else "jneg")
    return tuple(sig)


def sig_str(sig):
    winA, winB = sig[0], sig[1]
    names = []
    for k, (kind, num, slot, lap) in enumerate(sig[2:6]):
        names.append(f"{kind}(num{num},slot{slot},lap{lap})")
    return (f"W{winA}->W{winB} a=" + names[0] + " b=" + names[1]
            + " c=" + names[2] + " e=" + names[3] + " " + sig[6])


# ---- main -------------------------------------------------------------------
def main():
    t0 = time.time()
    out = []

    def emit(s=""):
        out.append(s)
        print(s, flush=True)

    emit("== audit92: 5,772-control regeneration, 92-residual mechanism census ==")
    counts, recs = broad_population()
    emit(f"population counts: {dict(sorted(counts.items()))}")
    assert counts == Counter({"one cell": 5534, "pair-residual": 92,
                              "three-cell": 146}), counts
    emit("verified: 5534 one-cell / 238 pairs = 146 three-cell + 92 residual; "
         "common rejection 0; phase assertion re-checked on all 5,772")

    n92 = [r for r in recs if r["label"] == "pair-residual"]
    n146 = [r for r in recs if r["label"] == "three-cell"]
    assert len(n92) == 92 and len(n146) == 146

    # classify both populations, dump per-control records
    fam92, fam146 = Counter(), Counter()
    mech = Counter()
    jtally = Counter()
    cross = Counter()
    lines = []
    for r in recs:
        core = [Q(s) for s in r["core"]]
        d = Q(r["d"])
        cells = [(Q(a), Q(b)) for a, b in r["cells"]]
        prs = [dict(p, x=Q(p["x"]), y=Q(p["y"]), span=Q(p["span"]),
                    gap=Q(p["gap"]), dspan=Q(p["dspan"]), dgap=Q(p["dgap"]))
               for p in r["pairs"]]
        flags, m, wp, hp = classify_control(core, d, cells, prs)
        r["flags"] = flags
        r["mech"] = m
        cellA, cellB, kind = canonical_pair(cells, prs, core, d)
        jg = 0 if kind == "pinch" else min(
            p["jg"] for p in prs
            if cells[p["i"]] == cellA and cells[p["j"]] == cellB)
        sig = signature(core, cellA, cellB, jg)
        r["canon"] = dict(kind=kind, A=[str(cellA[0]), str(cellA[1])],
                          B=[str(cellB[0]), str(cellB[1])], jg=jg,
                          sig=sig_str(sig))
        r["binders"] = {k: binders(v, core) for k, v in
                        (("a", cellA[0]), ("b", cellA[1]),
                         ("c", cellB[0]), ("e", cellB[1]))}
        for g in (p["jg"] for p in prs):
            jtally[g] += 1
        if r["label"] == "pair-residual":
            mech[m] += 1
            fam92[sig] += 1
        else:
            fam146[sig] += 1
        if r["label"] == "pair-residual":
            lines.append(
                f"core=({','.join(r['core'])}) d={r['d']} mech={m} "
                f"pinch={flags['pinch']} handoff={flags['handoff']} "
                f"j0={flags['j0']} jpos={flags['jpos']} jneg={flags['jneg']} "
                f"canon={r['canon']['kind']} jg={jg} "
                f"A=[{r['canon']['A'][0]},{r['canon']['A'][1]}] "
                f"B=[{r['canon']['B'][0]},{r['canon']['B'][1]}] sig={r['canon']['sig']}")

    with open(os.path.join(HERE, "audit92_population.jsonl"), "w") as f:
        for r in recs:
            f.write(json.dumps(r, default=str) + "\n")

    emit("")
    emit("== mechanism census over the 92 ==")
    for k, v in sorted(mech.items()):
        emit(f"  {k}: {v}")
    fl146 = Counter()
    for r in n146:
        for f, v in r["flags"].items():
            if v:
                fl146[f] += 1
    fl92 = Counter()
    for r in n92:
        for f, v in r["flags"].items():
            if v:
                fl92[f] += 1
    emit("  flag fires  [92 | 146]: " + "; ".join(
        f"{f} {fl92[f]} | {fl146[f]}" for f in ("pinch", "handoff", "j0", "jpos", "jneg")))
    emit(f"  j-g census over all 238x pairs: {dict(sorted(jtally.items()))}")

    emit("")
    emit("== the 92, one line each ==")
    out.extend(lines)

    emit("")
    emit("== family table (canonical-pair signatures, the 92) ==")
    for sig, n in fam92.most_common():
        cover146 = fam146.get(sig, 0)
        emit(f"  n92={n:3d} n146={cover146:3d}  {sig_str(sig)}")

    emit("")
    emit("== chain-box control (73 boxes of j2_g1sweep_checkpoint.jsonl) ==")
    d0 = {}
    with open(os.path.join(N8, "j2_g1sweep_checkpoint.jsonl")) as f:
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
    assert len(chain) == 73, len(chain)
    cb = Counter()
    cb_ex = []
    for t in chain:
        core = (Q(1),) + tuple(Q(x) for x in t[:5])
        dmax = Q(t[5])
        cells = clear_cells(core)
        for dd, tag in ((dmax, "d=t6"),) + tuple(
                (dmax + off, f"d=t6+{off}") for off in
                (Q(1, 16), Q(1, 4), 1, 3, 8, 16)):
            wide = any(dd * (b - a) >= 2 * R for a, b in cells)
            prs = []
            for i, j in combinations(range(len(cells)), 2):
                if incompatible(dd, cells[i], cells[j]):
                    (a, b), (c, e) = cells[i], cells[j]
                    prs.append(dict(i=i, j=j, jg=floor(dd * (e - a) - 2 * R)))
            pair = (not wide) and bool(prs)
            flags, m, _, _ = classify_control(core, dd, cells, prs)
            key = (tag, "wide" if wide else m if pair else "common-rejection")
            cb[key] += 1
            if pair and tag == "d=t6":
                cb_ex.append(f"  box={t} d={dd} mech={m} "
                             f"jg={sorted(set(p['jg'] for p in prs))}")
    emit(f"  73 boxes x 7 rates; verdict census:")
    for k, v in sorted(cb.items(), key=str):
        emit(f"    {k[0]:>10s} {k[1]:>16s}: {v}")
    if cb_ex:
        emit("  fires at d=t6 (exact embedding):")
        out.extend(cb_ex[:24])

    emit("")
    emit(f"runtime {time.time() - t0:.1f}s")
    with open(os.path.join(HERE, "audit92_mechanisms.out"), "w") as f:
        f.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
