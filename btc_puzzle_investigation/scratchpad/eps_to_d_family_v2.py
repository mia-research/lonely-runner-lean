#!/usr/bin/env python3
"""
eps_to_d_family_v2.py  —  RUN of PREREG_eps_to_d_constraint_v2.md (frozen family).

Omnibus G (multiplicity-free) + declared 31-map Holm list, matched within-j control, plants.
Scan curves {547,907} first; §9: if BOTH omnibus non-sig AND all 31 maps Holm-null on scan
(U-power z>=11), the family-wide SCOPED NULL is reached and no confirm run is needed.

Features (x-only, exact): eps{0,1,2}, sg{-1,0,1}, sband3{0,1,2}, sextant{0..5}, chi2(y){+-1}.
Targets (scalars only): carry=[d1 lam^j + d2 lam^j >= m] (two-key); c mod3/mod2/[!=0]/sign (single-key).
j = chi3 index = stratifier only. G/permutation are the allowed statistic floats; signal path integer.

FLOAT CARVE-OUT (per no-float rule + PREREG v2 §7): the ONLY float is inside gstat() (the G
log-likelihood statistic) and the display float(). All FEATURES (eps,sg,sband3,sextant,chi2y) and
TARGETS (carry,c) are exact integers; the verdict is the integer permutation count. G is a monotone
statistic ranked against a matched permutation null — the exact case the rule permits (same carve-out
as cheap_partial_shadow_v1 / glv_closure). check_no_float.sh flags only these gstat/display lines.
"""
import math
import random
from fractions import Fraction as Fr
from collections import Counter
from eps_to_d_run_v1 import (legendre, padd, prime_order_curve, full_orbit,
                             find_glv, chi3_index)
from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, enorm, sextant as sextant_uv


def make_features(p):
    eis, eps = build(p)
    R1, R2 = reduced_basis(p)
    DET = R1[0] * R2[1] - R1[1] * R2[0]

    def coeffs(z):
        return (Fr(z[0] * R2[1] - z[1] * R2[0], DET), Fr(z[1] * R1[0] - z[0] * R1[1], DET))

    # orientation: pick +/- so the (|u±v|>1/2) flap matches eps!=0 most often (integer compare)
    agree_plus = 0
    for x in range(1, p):
        u, v = coeffs(eis(x))
        flap = 0 if -Fr(1, 2) <= u + v <= Fr(1, 2) else 1
        if flap == (1 if eps(x) != 0 else 0):
            agree_plus += 1
    use_plus = (2 * agree_plus >= p - 1)

    def sg(x):
        u, v = coeffs(eis(x))
        s = u + v if use_plus else u - v
        return 0 if -Fr(1, 2) <= s <= Fr(1, 2) else (1 if s > 0 else -1)

    def sband3(x):
        E = enorm(eis(x))
        if 16 * E < 3 * p:
            return 0
        if 16 * E < 6 * p:
            return 1
        return 2

    def sxt(x):
        return sextant_uv(*eis(x))

    return eis, eps, sg, sband3, sxt


def gstat(pairs_by_stratum):
    """pairs_by_stratum: dict stratum -> list of (feat, tgt). G = sum_strata 2 sum O ln(O/E)."""
    total = 0.0
    for rows in pairs_by_stratum.values():
        N = len(rows)
        if N == 0:
            continue
        rc = Counter(f for f, t in rows)
        cc = Counter(t for f, t in rows)
        jc = Counter(rows)
        g = 0.0
        for (f, t), O in jc.items():
            E = rc[f] * cc[t] / N
            if O > 0 and E > 0:
                g += O * math.log(O / E)
        total += 2 * g
    return total


def holm(pvals):
    """Holm-Bonferroni: return list of (label, p, reject) at family alpha=0.05."""
    order = sorted(range(len(pvals)), key=lambda i: pvals[i][1])
    N = len(pvals)
    out = [None] * N
    still = True
    for rank, i in enumerate(order):
        label, p = pvals[i]
        thresh = Fr(5, 100) / (N - rank)
        rej = still and (p <= thresh)
        if not rej:
            still = False
        out[i] = (label, p, rej)
    return out


def run_omnibus_and_maps(p, m, G, d1, B_omni=5000, B_map=2000, rng=None):
    rng = rng or random.Random(0)
    xs = full_orbit(G, p, m)
    lam, beta, wp = find_glv(xs, p, m)
    eis, eps, sg, sband3, sxt = make_features(p)

    # ----- two-key reps (carry target), one per <phi>-orbit of sum scalar t=(d1+d2) -----
    seen = set(); reps = []
    for d2 in range(1, m):
        t = (d1 + d2) % m
        if t == 0:
            continue
        om = min(t, (lam * t) % m, (lam * lam * t) % m)
        if om in seen:
            continue
        seen.add(om)
        x = xs[t]
        if x is None:
            continue
        j = chi3_index(x, p, wp)
        reps.append(dict(t=t, d2=d2, j=j,
                         eps=eps(x), sg=sg(x), sb=sband3(x), sxt=sxt(x),
                         chi2y=1 if legendre(_yof(xs, t, p), p) == 1 else 0))
    U = len(reps)

    def carry(d2, j):
        lj = pow(lam, j, m)
        return 1 if (d1 * lj % m) + (d2 * lj % m) >= m else 0

    strat = {}
    for r in reps:
        strat.setdefault(r['j'], []).append(r['d2'])

    # real targets
    for r in reps:
        r['carry'] = carry(r['d2'], r['j'])

    # ---- OMNIBUS (carry): J=(eps,sign(sg),sband3) vs carry, per j-strata ----
    def Jtuple(r):
        return (r['eps'], (1 if r['sg'] > 0 else (-1 if r['sg'] < 0 else 0)), r['sb'])

    def omni_G(tgt_of):
        pbs = {}
        for r in reps:
            pbs.setdefault(r['j'], []).append((Jtuple(r), tgt_of(r)))
        return gstat(pbs)

    G_real = omni_G(lambda r: r['carry'])

    # ---- declared binary maps (feature -> {0,1}) vs carry ----
    def m_eps2(r): return 1 if r['eps'] == 2 else 0
    def m_eps1(r): return 1 if r['eps'] == 1 else 0
    def m_slt(r): return 1 if r['sb'] == 0 else 0
    def m_shi(r): return 1 if r['sb'] == 2 else 0
    def m_sgpos(r): return 1 if r['sg'] > 0 else 0
    def m_chi2(r): return 1 if r['chi2y'] == 1 else 0
    def m_sxt024(r): return 1 if r['sxt'] in (0, 2, 4) else 0
    binmaps = [("eps==2", m_eps2), ("eps==1", m_eps1), ("s<3/16", m_slt),
               ("s>=3/8", m_shi), ("sg>0", m_sgpos), ("chi2y==1", m_chi2),
               ("sxt in024", m_sxt024)]

    def map_G(feat_of, tgt_of):
        pbs = {}
        for r in reps:
            pbs.setdefault(r['j'], []).append((feat_of(r), tgt_of(r)))
        return gstat(pbs)

    G_maps = {name: map_G(f, lambda r: r['carry']) for name, f in binmaps}

    # ---- shared permutation null (permute carry target within j-bin) ----
    cnt_omni = 0
    cnt_maps = {name: 0 for name, _ in binmaps}
    B = max(B_omni, B_map)
    for b in range(B):
        # permuted carry: draw d2' within same j-bin per rep
        perm = [carry(rng.choice(strat[r['j']]), r['j']) for r in reps]
        pbs_o = {}
        for r, pc in zip(reps, perm):
            pbs_o.setdefault(r['j'], []).append((Jtuple(r), pc))
        if gstat(pbs_o) >= G_real:
            cnt_omni += 1
        for name, f in binmaps:
            pbs = {}
            for r, pc in zip(reps, perm):
                pbs.setdefault(r['j'], []).append((f(r), pc))
            if gstat(pbs) >= G_maps[name]:
                cnt_maps[name] += 1
    p_omni = Fr(cnt_omni + 1, B + 1)
    pmap = {name: Fr(cnt_maps[name] + 1, B + 1) for name, _ in binmaps}

    # ---- PLANTS ----
    # positive: feature := carry (identity) -> G_pos maximal; control (target permuted) must fall below
    pos_pbs = {}
    for r in reps:
        pos_pbs.setdefault(r['j'], []).append((r['carry'], r['carry']))
    G_pos = gstat(pos_pbs)
    cnt_pos = 0
    for _ in range(300):
        perm = [carry(rng.choice(strat[r['j']]), r['j']) for r in reps]
        pbs = {}
        for r, pc in zip(reps, perm):
            pbs.setdefault(r['j'], []).append((r['carry'], pc))
        if gstat(pbs) >= G_pos:
            cnt_pos += 1
    # negative: mu3-respecting random feature (constant per j) vs carry -> G_neg ~ control
    negbin = {j: rng.randint(0, 1) for j in strat}
    neg_pbs = {}
    for r in reps:
        neg_pbs.setdefault(r['j'], []).append((negbin[r['j']], r['carry']))
    G_neg = gstat(neg_pbs)

    return dict(p=p, m=m, d1=d1, U=U, p_omni=p_omni, G_real=G_real, pmap=pmap,
                pos_ok=(cnt_pos <= 2), G_neg=G_neg, G_pos=G_pos)


def _yof(xs, t, p):
    # recover y of [t]G from x by solving y^2=x^3+7 with a fixed sign convention (parity)
    x = xs[t]
    rhs = (x ** 3 + 7) % p
    from eps_to_d_run_v1 import tonelli
    y = tonelli(rhs, p)
    return y  # sign convention fixed (tonelli principal root); chi2(y) uses it consistently


def run_singlekey(p, m, G, B=3000, rng=None):
    """Single-key c-arm: c-mod3 omnibus + 24 declared maps (binary c-targets x7 + ternary x3)."""
    rng = rng or random.Random(0)
    xs = full_orbit(G, p, m)
    lam, beta, wp = find_glv(xs, p, m)
    eis, eps, sg, sband3, sxt = make_features(p)
    seen = set(); reps = []
    for d in range(1, m):
        orb = []
        for k in range(3):
            lk = pow(lam, k, m)
            orb += [(lk * d) % m, (-lk * d) % m]
        d0 = min(x for x in orb if x != 0)
        if d0 in seen:
            continue
        seen.add(d0)
        js = None
        for k in range(3):
            lk = pow(lam, k, m)
            if (lk * d0) % m == d % m:
                js = (k, 0); break
            if (-lk * d0) % m == d % m:
                js = (k, 1); break
        jj, s = js
        c = (((-1) ** s) * d0 * pow(lam, jj, m) - d) // m
        x = xs[d]
        reps.append(dict(d=d, j=chi3_index(x, p, wp), c=c,
                         eps=eps(x), sg=sg(x), sb=sband3(x), sxt=sxt(x),
                         chi2y=1 if legendre(_yof(xs, d, p), p) == 1 else 0))
    U = len(reps)
    strat = {}
    for r in reps:
        strat.setdefault(r['j'], []).append(r['c'])

    def J(r):
        return (r['eps'], 1 if r['sg'] > 0 else (-1 if r['sg'] < 0 else 0), r['sb'])
    binf = [("eps==2", lambda r: 1 if r['eps'] == 2 else 0),
            ("eps==1", lambda r: 1 if r['eps'] == 1 else 0),
            ("s<3/16", lambda r: 1 if r['sb'] == 0 else 0),
            ("s>=3/8", lambda r: 1 if r['sb'] == 2 else 0),
            ("sg>0", lambda r: 1 if r['sg'] > 0 else 0),
            ("chi2y==1", lambda r: 1 if r['chi2y'] == 1 else 0),
            ("sxt024", lambda r: 1 if r['sxt'] in (0, 2, 4) else 0)]
    ternf = [("sxt%3", lambda r: r['sxt'] % 3),
             ("sg+1", lambda r: r['sg'] + 1),
             ("sband3", lambda r: r['sb'])]
    bintg = [("c%2", lambda c: c % 2), ("[c!=0]", lambda c: 1 if c != 0 else 0),
             ("sign(c)", lambda c: 1 if c > 0 else 0)]

    def Gof(feat_vals, tgt_vals):
        pbs = {}
        for r, fv, tv in zip(reps, feat_vals, tgt_vals):
            pbs.setdefault(r['j'], []).append((fv, tv))
        return gstat(pbs)

    # real
    real = {}
    Jvals = [J(r) for r in reps]
    cm3 = [r['c'] % 3 for r in reps]
    real[("OMNI", "c%3")] = Gof(Jvals, cm3)
    for tn, tf in bintg:
        tv = [tf(r['c']) for r in reps]
        for fn, ff in binf:
            real[(fn, tn)] = Gof([ff(r) for r in reps], tv)
    for fn, ff in ternf:
        real[(fn, "c%3")] = Gof([ff(r) for r in reps], cm3)

    cnt = {k: 0 for k in real}
    for _ in range(B):
        cp = [rng.choice(strat[r['j']]) for r in reps]      # permuted c within j-bin
        cm3p = [c % 3 for c in cp]
        if Gof(Jvals, cm3p) >= real[("OMNI", "c%3")]:
            cnt[("OMNI", "c%3")] += 1
        for tn, tf in bintg:
            tvp = [tf(c) for c in cp]
            for fn, ff in binf:
                if Gof([ff(r) for r in reps], tvp) >= real[(fn, tn)]:
                    cnt[(fn, tn)] += 1
        for fn, ff in ternf:
            if Gof([ff(r) for r in reps], cm3p) >= real[(fn, "c%3")]:
                cnt[(fn, "c%3")] += 1
    pv = {k: Fr(cnt[k] + 1, B + 1) for k in real}
    return U, pv


def confirm_carry_omni(p, m, G, d1, B=3000, rng=None):
    """Lean confirm: carry-omnibus permutation p-value only (the frozen scan survivor)."""
    rng = rng or random.Random(0)
    xs = full_orbit(G, p, m)
    lam, beta, wp = find_glv(xs, p, m)
    eis, eps, sg, sband3, sxt = make_features(p)
    seen = set(); reps = []
    for d2 in range(1, m):
        t = (d1 + d2) % m
        if t == 0:
            continue
        om = min(t, (lam * t) % m, (lam * lam * t) % m)
        if om in seen:
            continue
        seen.add(om)
        x = xs[t]
        if x is None:
            continue
        reps.append(dict(j=chi3_index(x, p, wp), d2=d2,
                         J=(eps(x), 1 if sg(x) > 0 else (-1 if sg(x) < 0 else 0), sband3(x))))
    U = len(reps)
    strat = {}
    for r in reps:
        strat.setdefault(r['j'], []).append(r['d2'])

    def carry(d2, j):
        lj = pow(lam, j, m)
        return 1 if (d1 * lj % m) + (d2 * lj % m) >= m else 0

    def omni(tgt):
        pbs = {}
        for r, tv in zip(reps, tgt):
            pbs.setdefault(r['j'], []).append((r['J'], tv))
        return gstat(pbs)

    G_real = omni([carry(r['d2'], r['j']) for r in reps])
    cnt = 0
    for _ in range(B):
        perm = [carry(rng.choice(strat[r['j']]), r['j']) for r in reps]
        if omni(perm) >= G_real:
            cnt += 1
    return U, Fr(cnt + 1, B + 1), G_real


def main():
    print("PREREG_eps_to_d_constraint_v2 — RUN (scan curves only; confirm gated on a scan hit)\n")
    for (lo, hi) in [(547, 548), (907, 908)]:
        r = prime_order_curve(lo, hi)
        if not r:
            continue
        p, m, G = r
        print(f"=== scan curve p={p} m={m} (U~{m//3}) ===")
        results = []
        for d1 in (1, 7, 13):
            res = run_omnibus_and_maps(p, m, G, d1, B_omni=3000, B_map=3000,
                                       rng=random.Random(1000 + d1))
            results.append(res)
            hm = holm([(n, pv) for n, pv in res['pmap'].items()])
            surv = [n for (n, pv, rej) in hm if rej]
            print(f"  d1={d1}: U={res['U']}  omnibus p={res['p_omni'].numerator}/{res['p_omni'].denominator}"
                  f"  G_real={res['G_real']:.1f}  plant pos_ok={res['pos_ok']} G_pos={res['G_pos']:.1f} "
                  f"G_neg={res['G_neg']:.2f}")
            print(f"        map p-values: " + ", ".join(f"{n}={float(pv):.3f}" for n, pv in res['pmap'].items()))
            print(f"        Holm survivors (carry x binmaps): {surv if surv else 'NONE'}")

        # single-key c-arm (c%3 omnibus + 24 maps); Holm over full 31 (7 carry@d1=1 + 24 single)
        Usk, pv_sk = run_singlekey(p, m, G, B=3000, rng=random.Random(4000 + p))
        carry_d1_1 = results[0]['pmap']            # 7 carry x binmaps at d1=1
        fam31 = [((f"carry:{n}"), pv) for n, pv in carry_d1_1.items()]
        fam31 += [((f"{fn}:{tn}"), pv) for (fn, tn), pv in pv_sk.items() if fn != "OMNI"]
        hm31 = holm(fam31)
        surv31 = [(lab, float(pv)) for (lab, pv, rej) in hm31 if rej]
        print(f"  single-key U={Usk}: c%3-omnibus p={pv_sk[('OMNI','c%3')].numerator}/"
              f"{pv_sk[('OMNI','c%3')].denominator}")
        print(f"  FAMILY Holm/31 survivors: {surv31 if surv31 else 'NONE'}   "
              f"(carry-omnibus d1=1 p={results[0]['p_omni'].numerator}/{results[0]['p_omni'].denominator})")
        print()

    # ---- CONFIRM: the frozen scan survivor = (carry omnibus, d1=13) on OOS curves {1303,1669,2089} ----
    print("=== CONFIRM (frozen survivor: carry omnibus, d1=13) on OOS {1303,1669,2089}, Holm/3 ===")
    confp = []
    for (lo, hi) in [(1303, 1304), (1669, 1670), (2089, 2090)]:
        r = prime_order_curve(lo, hi)
        if not r:
            print(f"  (no prime-order curve at p={lo})")
            continue
        p, m, G = r
        U, pv, Greal = confirm_carry_omni(p, m, G, 13, B=3000, rng=random.Random(9000 + p))
        confp.append((p, pv))
        print(f"  p={p} m={m} U={U}: carry-omnibus(d1=13) p={pv.numerator}/{pv.denominator}  G_real={Greal:.1f}")
    # Holm over the 3 confirm p-values at alpha=0.05
    hm = holm([(f"p={p}", pv) for p, pv in confp])
    allrej = confp and all(rej for (_, _, rej) in hm)
    print(f"  Holm/3 survive-all: {allrej}  -> {'CONFIRMED (real, scoped)' if allrej else 'DISCARDED as scan chance hit'}")


if __name__ == "__main__":
    main()
