#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
c2_grouplaw_diffset_stageA_v1.py -- executes frozen PREREG_c2_grouplaw_diffset_v2.md (Stage A).

Group-law difference-set D={x(P_i-P_j)} of M=80 band-random points [d]G, d uniform in
[2^{k-1},2^k); readouts chi2/chi3/chi6 (all legal, x(-Q)=x(Q)); E2/E3/E6=|sum chi|^2 exact int.
Null = M-subsets of a P=640 uniform-random-point pool (Step-1's calibrated null; inflation ~1.5%).

Gate-required controls (all before the arms):
  fresh-vs-pool : 60 FRESH M-uniform sets must rank ~uniform vs the pool null (mean pctile in
                  [0.42,0.58] per channel) -- tests the fresh-arm-vs-pooled-null axis C-NEG is blind to.
  C-GLV         : phi-closed set -> E3=E6=0 exact (E2 not forced).
  3 plants      : E2 (QR bias) fires E2 only; E3 (cubic bias) fires E3 only & E6=0; E6 (joint mu6
                  cell) fires E6 -- per-channel power (the chi2/chi6 channels are the new content).
Two-sided 99th screen; candidate = same tail 5/5 fresh-seed OOS; per-channel epsilon*.

Exact integer signal path; arm regenerated FRESH per OOS seed, pool fixed (v2 sec.0.2).
Usage: python3 c2_grouplaw_diffset_stageA_v1.py [M] [P] [Rnull] [seed]
"""
import sys
import time
import bisect
import random

from shortscalar_sum_stageA_v1 import (
    scalar_mult, point_add, code_of, random_point, stats_from_hist,
    G, N_ORDER, P_FIELD, BETA, chi3_class,
)

KS = [40, 64, 96, 128, 160, 200]
OOS_SEEDS = [20260802, 31337, 27182818, 16180339, 14142135]
NAMES = ("E2", "E3", "E6")


def gl_diff_code(Pi, Pj):
    """code(3b+c) of x(P_i - P_j); None if P_i==P_j."""
    xj, yj = Pj
    D = point_add(Pi, (xj, (P_FIELD - yj) % P_FIELD))
    return None if D is None else code_of(D[0])


def diffset_hist(points):
    H = [0, 0, 0, 0, 0, 0]
    Mn = len(points)
    for i in range(Mn):
        Pi = points[i]
        for j in range(i + 1, Mn):
            c = gl_diff_code(Pi, points[j])
            if c is not None:
                H[c] += 1
    return H


def stats3(H):
    e2, e3, e6, _ = stats_from_hist(H, sum(H))
    return e2, e3, e6


# ---- code-space per-channel plants (mechanical power check) ---------------
def hist_e2(T, m):
    nb0, nb1 = T // 2 + m, T - (T // 2 + m)
    H = [nb0 // 3] * 3 + [nb1 // 3] * 3
    for r in range(nb0 - 3 * (nb0 // 3)): H[r] += 1
    for r in range(nb1 - 3 * (nb1 // 3)): H[3 + r] += 1
    return H


def hist_e3(T, m):
    nc0 = T // 3 + m; nc1 = (T - nc0) // 2; nc2 = T - nc0 - nc1
    H = [0] * 6
    for nc, cells in ((nc0, (0, 3)), (nc1, (1, 4)), (nc2, (2, 5))):
        H[cells[0]] = nc // 2; H[cells[1]] = nc - nc // 2
    return H


def hist_e6(T, m):
    h0 = T // 6 + m; rest = T - h0; e = rest // 5
    H = [h0] + [e] * 5
    for r in range(rest - 5 * e): H[1 + r] += 1
    return H


def band_points(k, Mn, rng):
    return [scalar_mult(rng.randrange(1 << (k - 1), 1 << k), G) for _ in range(Mn)]


def p_upper(nullsorted, v):
    return (len(nullsorted) - bisect.bisect_left(nullsorted, v)) / len(nullsorted)


def tail(p):
    return "HI" if p <= 0.005 else ("LO" if p >= 0.995 else ".")


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 80
    P = int(sys.argv[2]) if len(sys.argv) > 2 else 640
    Rnull = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 20260802
    T = M * (M - 1) // 2
    rng = random.Random(seed)

    print("=" * 82)
    print(f"C2 GROUP-LAW DIFFERENCE-SET  M={M} P={P} Rnull={Rnull} seed={seed}  chi2/chi3/chi6")
    print(f"  BIG-O: pool C(P,2)={P*(P-1)//2:,} gl-diffs (once) + {len(KS)*len(OOS_SEEDS)} arms x T={T:,}")
    print(f"  inflation T^2/C(P,2) = {T*T/(P*(P-1)//2):.0f} vs T={T} = {T*T/(P*(P-1)//2)/T*100:.2f}%")
    print("=" * 82)
    t0 = time.perf_counter()

    # ---- pool + null distribution ----
    tp = time.perf_counter()
    pool = [random_point(rng) for _ in range(P)]
    code = [[0] * P for _ in range(P)]
    for i in range(P):
        for j in range(i + 1, P):
            c = gl_diff_code(pool[i], pool[j])
            code[i][j] = c if c is not None else -1
    print(f"[pool] {P} pts, C(P,2) gl-diff codes in {time.perf_counter()-tp:.0f}s")

    def null_draw():
        idx = rng.sample(range(P), M); idx.sort()
        H = [0, 0, 0, 0, 0, 0]
        for a in range(M):
            row = code[idx[a]]
            for b in range(a + 1, M):
                cd = row[idx[b]]
                if cd >= 0: H[cd] += 1
        return stats3(H)

    null = {nm: [] for nm in NAMES}
    for _ in range(Rnull):
        for nm, v in zip(NAMES, null_draw()): null[nm].append(v)
    for nm in NAMES: null[nm].sort()
    v99 = {nm: null[nm][(99 * Rnull) // 100] for nm in NAMES}
    print(f"[null] {Rnull} subset draws; medians "
          + " ".join(f"{nm}={null[nm][Rnull//2]}" for nm in NAMES)
          + " | 99th " + " ".join(f"{nm}={v99[nm]}" for nm in NAMES))

    # ---- fresh-vs-pool check (the Defect-1 axis) ----
    print("-" * 82)
    fresh = {nm: [] for nm in NAMES}
    for _ in range(60):
        pts = [random_point(rng) for _ in range(M)]
        for nm, v in zip(NAMES, stats3(diffset_hist(pts))): fresh[nm].append(v)
    ok = True
    for nm in NAMES:
        mp = sum(1 - p_upper(null[nm], v) for v in fresh[nm]) / len(fresh[nm])  # mean lower-pctile
        passed = 0.42 <= mp <= 0.58
        ok = ok and passed
        print(f"[fresh-vs-pool] {nm}: mean pctile={mp:.3f}  [{'PASS' if passed else 'FAIL'}]")
    print(f"  -> fresh arm and pooled null {'indistinguishable (null usable)' if ok else 'DIFFER -- pool inflated, ABORT'}")
    assert ok, "fresh-vs-pool FAILED: pool null inflated at these params"

    # ---- C-GLV ----
    S = []
    for _ in range(max(1, M // 3)):
        x, y = random_point(rng)
        S += [(x, y), ((BETA * x) % P_FIELD, y), ((BETA * BETA * x) % P_FIELD, y)]
    eg = stats3(diffset_hist(S))
    print(f"[C-GLV] phi-closed |S|={len(S)}: E2={eg[0]} E3={eg[1]} E6={eg[2]}"
          f" -> {'PASS' if eg[1]==0 and eg[2]==0 else 'FAIL'} (E3=E6=0 forced)")
    assert eg[1] == 0 and eg[2] == 0

    # ---- 3 per-channel plants ----
    print("-" * 82)
    print("[plants] per-channel power (fires own channel above null 99th; marginals give E6=0):")
    for ch, builder in (("E2", hist_e2), ("E3", hist_e3), ("E6", hist_e6)):
        row = []
        for f in (0.0, 0.02, 0.05):
            e2, e3, e6 = stats3(builder(T, int(f * T)))
            fired = {"E2": e2, "E3": e3, "E6": e6}[ch] > v99[ch]
            row.append(f"f={f}:{ch}={ {'E2':e2,'E3':e3,'E6':e6}[ch]}{'*' if fired else ''}(E6={e6})")
        print(f"    {ch}-plant: " + "  ".join(row))

    # ---- ARMS: band-random, two-sided, 5-seed OOS ----
    print("=" * 82)
    print(f"BAND ARMS (two-sided 99th; same-tail {len(OOS_SEEDS)}/{len(OOS_SEEDS)} OOS):")
    ta = time.perf_counter()
    candidates = []
    allp = {nm: [] for nm in NAMES}
    for k in KS:
        rows = {nm: [] for nm in NAMES}
        for sd in OOS_SEEDS:
            arng = random.Random(sd ^ (k * 0x9E3779B1))
            pts = band_points(k, M, arng)
            for nm, v in zip(NAMES, stats3(diffset_hist(pts))):
                rows[nm].append(p_upper(null[nm], v))
        line = []
        for nm in NAMES:
            ps = rows[nm]
            allp[nm].extend(ps)
            tags = "".join(tail(p) for p in ps)
            hi = all(p <= 0.005 for p in ps); lo = all(p >= 0.995 for p in ps)
            if hi or lo: candidates.append((k, nm, "HI" if hi else "LO"))
            line.append(f"{nm}[{tags}]{'<=CAND' if (hi or lo) else ''}")
        print(f"  k={k:>3}: " + "  ".join(line))
    print(f"[arms] {len(KS)*len(OOS_SEEDS)} band arms in {time.perf_counter()-ta:.0f}s")
    # AUDIT: systematic sub-threshold lean per channel (0.5 = no lean; the R-CONTIG failure mode)
    print("[audit] mean arm pctile per channel (n=30 cells; systematic lean = disregarded sub-threshold effect):")
    for nm in NAMES:
        mp = sum(1 - p for p in allp[nm]) / len(allp[nm])
        lo_n = sum(1 for p in allp[nm] if p >= 0.90)   # arm in low 10%
        hi_n = sum(1 for p in allp[nm] if p <= 0.10)   # arm in high 10%
        flag = "LEAN" if not (0.42 <= mp <= 0.58) else "flat"
        print(f"    {nm}: mean pctile={mp:.3f} [{flag}]  arm-in-low10%={lo_n}/30 arm-in-high10%={hi_n}/30"
              f"  full p: [{', '.join(f'{p:.2f}' for p in sorted(allp[nm]))}]")

    # ---- per-channel bound ----
    import math
    print("-" * 82)
    print("PER-CHANNEL bound (Rule 5; eps* from each form's own null 99th):")
    for nm in NAMES:
        if nm == "E2":
            eps = math.sqrt(v99[nm]) / T          # E2=(n+-n-)^2 -> |n+-n-|/T
        else:
            eps = 2 * math.sqrt(v99[nm]) / T       # E3/E6 2-D forms
        print(f"    {nm}: null99={v99[nm]:>10}  eps*~{eps*100:.2f}%  (excess vs expected class size)")

    print("=" * 82)
    if candidates:
        print(f"CANDIDATE cells (same tail 5/5): {candidates}")
        print("  -> chi2/chi6 hit = item-C2 payoff; characterize (anomaly-drill), do NOT name mechanism.")
    else:
        print("No cell screened same-tail 5/5. BOUNDED on chi2/chi3/chi6 at the eps* floors above.")
        print("  -> band-confinement leaves no detectable difference-set character structure (a bound;")
        print("     open below eps*, larger M, other characters, k-dependence untested here).")
    print(f"TOTAL WALL TIME: {time.perf_counter()-t0:.0f}s")


if __name__ == "__main__":
    main()
