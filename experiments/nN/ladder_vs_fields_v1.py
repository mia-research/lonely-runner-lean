"""The L_0 ladder (PROOF_REQUIREMENTS_v2 section 7) against the Lean rational-opening fields.

Both return an instant t = a/(8D) with the band test D <= (d*a mod 8D) <= 7D for every d.
  ladder (v2 form): the least resolution D with SOME a = 8j+1, j < D, clearing every d.  D need not
      be a disparity; dead lattices (8D | some d) never clear, so starting at L_0 changes nothing.
  ladder (SKETCH_v7 form): D over 1..7*d_min, candidates t = p/(8D), p in {1,3,5,7}.
  fields: D = e a disparity, N | e, M = e/N, a = 8*i*M + 1 for some i < N  (RationalOpening8).
      N* = the least N over all flanks e in S and divisors N of e with such an i; N = e is Theorem 10.
Objects: the 7 EightResidual sets of [1,40] (eight_residual_count_v5.out); the 1,436 rule-miss
("hard") sets with largest 41..60 (hard_sets_41_60.json); 3,000 random primitive 7-sets of [1,60].
"""
import json, random, time
from math import gcd
from functools import reduce
from collections import Counter

def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)
def ladder_v2(S):
    D = 1
    while True:
        for j in range(D):
            if clears(S, D, 8 * j + 1): return D, 8 * j + 1
        D += 1
def ladder_v7(S):
    dmin = min(S)
    for D in range(1, 7 * dmin + 1):
        for p in (1, 3, 5, 7):
            if clears(S, D, p): return D, p
    return None
def fields_N(S):
    best = None
    for e in S:
        for N in range(1, e + 1):
            if e % N: continue
            if best is not None and N >= best[0]: break
            M = e // N
            if any(clears(S, e, 8 * i * M + 1) for i in range(N)): best = (N, e); break
    return best

RES7 = [(2, 12, 15, 21, 32, 34, 38), (4, 5, 6, 8, 14, 32, 37), (4, 5, 6, 14, 16, 34, 38),
        (4, 5, 6, 14, 17, 32, 38), (4, 5, 6, 14, 32, 34, 38), (4, 6, 14, 15, 16, 34, 38),
        (4, 7, 8, 15, 29, 36, 37)]
H = [tuple(S) for S in json.load(open('hard_sets_41_60.json'))]
rnd = random.Random(25); R = set()
while len(R) < 3000:
    S = tuple(sorted(rnd.sample(range(1, 61), 7)))
    if reduce(gcd, S) == 1: R.add(S)
R = sorted(R)
t0 = time.time()
print("the 7 EightResidual sets of [1,40]:")
for S in RES7:
    D, a = ladder_v2(S); v7 = ladder_v7(S); N = fields_N(S)
    print(f"  {S}: ladder D*={D}, a={a} (t={a}/{8*D}), D* a disparity: {D in S};  SKETCH_v7 form: {v7};  fields N*={N[0]} at e={N[1]}")
for label, sets in (("1,436 rule-miss sets, largest 41..60", H), ("3,000 random primitive 7-sets of [1,60]", R)):
    Ds = Counter(); inS = 0; v7fail = 0; Ns = Counter(); le = Counter()
    for S in sets:
        D, a = ladder_v2(S); Ds[D] += 1; inS += D in S
        v7fail += ladder_v7(S) is None
        N, e = fields_N(S); Ns[N] += 1
        le['D* < e(N*)' if D < e else ('D* = e(N*)' if D == e else 'D* > e(N*)')] += 1
    print(f"{label}:")
    print(f"  ladder D*: max {max(Ds)}, distribution {sorted(Ds.items())}")
    print(f"  D* is a disparity: {inS}/{len(sets)};  SKETCH_v7 form finds nothing: {v7fail}/{len(sets)}")
    print(f"  fields N*: max {max(Ns)}, distribution {sorted(Ns.items())}")
    print(f"  ladder resolution against the fields' flank: {dict(le)}")
print(f"({time.time() - t0:.0f}s)")
