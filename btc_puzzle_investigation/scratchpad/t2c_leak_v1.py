#!/usr/bin/env python3
"""
t2c_leak_v1.py  —  T2c part (b): does PUBLIC j = chi3-index predict SECRET d mod 3, quotiented to
one representative per <±λ>-orbit (removes the phi-forced within-orbit coupling)? PREREG_j_range_to_dmod3_v1.

Primary: 3x3 G(j0, d0 mod3) over orbit-reps d0; C1 = permute target within log2(d0) stratum; B>=5000.
Plants: positive j:=r (fire), negative j:=random (~C1). Stratified below/above b*.
FLOAT CARVE-OUT: only gstat (G statistic) uses float, ranked vs integer permutation null; signal path int.
"""
import random
from fractions import Fraction as Fr
from eps_to_d_run_v1 import prime_order_curve, full_orbit, find_glv, chi3_index
from eps_to_d_family_v2 import gstat, holm

BSTAR = {547: 3, 907: 4, 1303: 4, 1669: 4, 2089: 5}


def orbit_reps(m, lam):
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
        reps.append(d0)
    return reps


def run(p, m, G, B=5000, rng=None):
    rng = rng or random.Random(0)
    xs = full_orbit(G, p, m)
    lam, beta, wp = find_glv(xs, p, m)
    bstar = BSTAR.get(p, m.bit_length() - 6)
    reps = []
    for d0 in orbit_reps(m, lam):
        reps.append(dict(j=chi3_index(xs[d0], p, wp), r=d0 % 3,
                         strat=0 if d0.bit_length() <= bstar else 1))
    U = len(reps)

    def Gof(feat, tgt, reps_):
        pbs = {}
        for r_, fv, tv in zip(reps_, feat, tgt):
            pbs.setdefault(r_['strat'], []).append((fv, tv))
        return gstat(pbs)

    feat = [r['j'] for r in reps]
    tgt = [r['r'] for r in reps]
    G_real = Gof(feat, tgt, reps)
    # C1: permute target within stratum
    bystrat = {}
    for i, r in enumerate(reps):
        bystrat.setdefault(r['strat'], []).append(i)
    cnt = 0
    for _ in range(B):
        perm = list(tgt)
        for st, idxs in bystrat.items():
            vals = [tgt[i] for i in idxs]
            rng.shuffle(vals)
            for i, v in zip(idxs, vals):
                perm[i] = v
        if Gof(feat, perm, reps) >= G_real:
            cnt += 1
    p_perm = Fr(cnt + 1, B + 1)

    # plants
    G_pos = Gof(tgt, tgt, reps)                        # j := r
    cntp = 0
    for _ in range(300):
        perm = list(tgt)
        for st, idxs in bystrat.items():
            vals = [tgt[i] for i in idxs]; rng.shuffle(vals)
            for i, v in zip(idxs, vals): perm[i] = v
        if Gof(tgt, perm, reps) >= G_pos:
            cntp += 1
    rnd = [rng.randint(0, 2) for _ in reps]
    G_neg = Gof(rnd, tgt, reps)
    # base rate
    from collections import Counter
    br = Counter(tgt)
    return dict(p=p, m=m, U=U, p_perm=p_perm, G_real=G_real,
                pos_ok=(cntp <= 2), G_pos=G_pos, G_neg=G_neg, base=dict(br))


def main():
    print("PREREG_j_range_to_dmod3_v1 part (b) — RUN (scan; confirm gated on a hit)\n")
    hits = []
    for (lo, hi) in [(547, 548), (907, 908)]:
        r = prime_order_curve(lo, hi)
        p, m, G = r
        res = run(p, m, G, B=5000, rng=random.Random(2000 + p))
        print(f"  scan p={p} m={m} U={res['U']}: G(j,d mod3) p={res['p_perm'].numerator}/"
              f"{res['p_perm'].denominator}  G_real={res['G_real']:.2f}  "
              f"plant pos_ok={res['pos_ok']} (G_pos={res['G_pos']:.1f}) G_neg={res['G_neg']:.2f}  "
              f"base={res['base']}")
        if 20 * res['p_perm'].numerator <= res['p_perm'].denominator:
            hits.append((p, res))
    if not hits:
        print("\n  No scan hit (both p>0.05). Pre-committed: SCOPED LEAKAGE NULL (j !-> d mod3 beyond 1/3)")
        print("  on {547,907}, plant fired. Conditional phrasing; below-b* degenerate per part (a).")
    else:
        print("\n  Scan hit(s) -> CONFIRM on {1303,1669,2089}, C1, Holm/3:")
        confp = []
        for (lo, hi) in [(1303, 1304), (1669, 1670), (2089, 2090)]:
            r = prime_order_curve(lo, hi)
            p, m, G = r
            res = run(p, m, G, B=5000, rng=random.Random(9000 + p))
            confp.append((f"p={p}", res['p_perm']))
            print(f"    p={p} U={res['U']}: p={res['p_perm'].numerator}/{res['p_perm'].denominator}"
                  f"  G_real={res['G_real']:.2f}")
        hm = holm(confp)
        allrej = all(rej for (_, _, rej) in hm)
        print(f"    Holm/3 survive-all: {allrej} -> {'CONFIRMED (scoped)' if allrej else 'DISCARDED chance hit'}")


if __name__ == "__main__":
    main()
