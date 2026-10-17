#!/usr/bin/env python3
"""Mine the joint slow closure (o7_joint_v1 machinery; float search, EXACT verification of every closure) on six-runner
slow-region sets, split j = 1 only (slow v1, fast five-block F), under restrictions:
  R0: as o7_joint_v1 (4 best patterns with q1 <= 12, any runner-1 stretch);
  R1: first runner-1 stretch only (alpha in [1/(7 v1), 6/(7 v1)]);
  R2: pattern q1 = 1 only (Q_k = round(F_k / F_1));
  R3: q1 = 1 and first stretch;
  R4: Q = (1,1,1,1,1) (pure cluster form, c = v2) and any stretch.
Reports success counts and, for R0 closures, the distribution of q1, the stretch index, sigma = e_max/c, e_max/v1."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from o7_joint_v1 import lonely_iv, y_admissible, exact_ok, patterns
def try_close(P, pats, first_only):
    S, F = P[:1], P[1:]; v1 = P[0]
    ivs = [(1 / (7 * v1), 6 / (7 * v1))] if first_only else lonely_iv(S)
    for sig, Q, c, e in pats:
        ic = 1 / float(c)
        for lo, hi in ivs:
            if hi - lo <= ic: continue
            n = max(2, min(200, int((hi - lo) / ic * 2)))
            for k in range(n):
                a = lo + (hi - lo - ic) * k / (n - 1)
                for ylo, yhi in y_admissible(F, Q, e, a):
                    ym = (ylo + yhi) / 2
                    if exact_ok(S, F, Q, c, e, Fr(a).limit_denominator(10**9), Fr(ym).limit_denominator(10**9)):
                        return dict(q1=Q[0], Q=tuple(Q), m=int(a * v1), sigma=float(sig), ev1=float(max(e)) / v1)
    return None
def pats_q1(F):
    Q = [max(1, round(f / F[0])) for f in F]; c = min(Fr(f, q) for f, q in zip(F, Q))
    e = [f - c * q for f, q in zip(F, Q)]; return [(max(e) / c, Q, c, e)]
def pats_ones(F):
    c = Fr(F[0]); e = [f - c for f in F]; return [(max(e) / c, [1] * 5, c, e)]
if __name__ == "__main__":
    rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 5); N = int(sys.argv[1])
    res = Counter(); q1s = Counter(); ms = Counter(); sig = Counter(); ev = Counter(); fails = {k: [] for k in "R0 R1 R2 R3 R4".split()}
    done = 0
    while done < N:
        v1 = rnd.randint(1, 30); v5 = rnd.randint(100 * v1 + 1, 100 * v1 + 20000); v6 = rnd.randint(v5 + 1, 6 * v5 - 1)
        P = (v1, *sorted(rnd.sample(range(v1 + 1, v5), 3)), v5, v6)
        if math.gcd(*P) != 1: continue
        done += 1; F = P[1:]
        r0 = try_close(P, patterns(F)[:4], False)
        tests = {"R0": r0, "R1": try_close(P, patterns(F)[:4], True), "R2": try_close(P, pats_q1(F), False),
                 "R3": try_close(P, pats_q1(F), True), "R4": try_close(P, pats_ones(F), False)}
        for k, r in tests.items():
            res[(k, r is not None)] += 1
            if r is None and len(fails[k]) < 5: fails[k].append(P)
        if r0:
            q1s[r0["q1"]] += 1; ms[min(r0["m"], 10)] += 1
            sig[round(min(r0["sigma"], 1), 1)] += 1; ev[min(int(r0["ev1"]), 1000) // 100 * 100] += 1
    print(f"{N} random slow-region sets (j = 1 only):")
    for k in "R0 R1 R2 R3 R4".split(): print(f"   {k}: closed {res[(k, True)]}, not {res[(k, False)]}; e.g. {fails[k][:3]}")
    print("   R0 closures: q1", sorted(q1s.items()), "; stretch index (cap 10)", sorted(ms.items()))
    print("   R0 sigma = e_max/c (0.1 bins)", sorted(sig.items()), "; e_max/v1 (bins of 100, cap 1000)", sorted(ev.items()))
