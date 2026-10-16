#!/usr/bin/env python3
"""Order seven (six speeds, band [1/7, 6/7]) phase-1 map. Per primitive set v1 < ... < v6 (whole numbers):
 - lonely intervals over one period t in [0, 1) (band-interval intersection, floats);
 - closers by the number of runners whose laps are tracked:
     T4: a 4-runner block window [L, U] (all four in band) with the other two (speeds a <= b) handled by the two-runner
         window: U - L >= 2/(7a) + 2/(7b)  (runner a has band stretches of length (5/7)/a every 1/a; any window of that
         length contains a stretch portion of length >= (2/7)/b, across which runner b sweeps 2/7 of a lap);
     T5: a 5-runner block window with the sixth runner (speed c) folded: c (U - L) >= 2/7;
     T6: a lap box: an instant with all six in band (positive-length interval);
     TIGHT: lonely only at isolated instants (no positive-length interval, but a point);
 - for T4/T5 the tracked/handled runners (pattern).
Reports counts by minimal tracked size, the T5-only and T6-only sets, and the tight sets."""
import math, sys, random
from itertools import combinations
from collections import Counter
EPS = 1e-12
def bands(v):
    return [((m + 1 / 7) / v, (m + 6 / 7) / v) for m in range(v)]
def inter(A, B, strict=True):
    i = j = 0; out = []
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if (hi > lo + EPS) if strict else (hi >= lo - EPS): out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def block(S, idx, strict=True):
    cur = bands(S[idx[0]])
    for k in idx[1:]: cur = inter(cur, bands(S[k]), strict)
    return cur
def classify(S):
    full = block(S, range(6))
    if not full:
        pt = block(S, range(6), strict=False)
        return ("TIGHT" if pt else "NOT LONELY"), None
    # T4
    for idx in combinations(range(6), 4):
        rest = [k for k in range(6) if k not in idx]; a, b = S[rest[0]], S[rest[1]]
        need = 2 / (7 * a) + 2 / (7 * b)
        if any(U - L >= need - EPS for L, U in block(S, idx)): return "T4", tuple(k + 1 for k in rest)
    for idx in combinations(range(6), 5):
        r = [k for k in range(6) if k not in idx][0]
        if any(S[r] * (U - L) >= 2 / 7 - EPS for L, U in block(S, idx)): return "T5", (r + 1,)
    return "T6", None
def run(sets, label):
    c = Counter(); pat = Counter(); ex = {"T5": [], "T6": [], "TIGHT": [], "NOT LONELY": []}
    for S in sets:
        k, p = classify(S); c[k] += 1
        if p: pat[(k, p)] += 1
        if k in ex and len(ex[k]) < 30: ex[k].append(S)
    print(f"== {label}: {len(sets)} sets: {dict(c)}")
    print("   patterns (handled runners):", pat.most_common(12))
    for k, l in ex.items():
        if l: print(f"   {k} ({c[k]}):", l[:30])
H = int(sys.argv[1]) if len(sys.argv) > 1 else 20
run([S for S in combinations(range(1, H + 1), 6) if math.gcd(*S) == 1], f"primitive order-seven sets <= {H}")
if len(sys.argv) > 2:
    random.seed(7); big = []
    while len(big) < 3000:
        S = tuple(sorted(random.sample(range(1, int(sys.argv[2]) + 1), 6)))
        if math.gcd(*S) == 1: big.append(S)
    run(big, f"random order-seven sets <= {sys.argv[2]}")
