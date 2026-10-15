#!/usr/bin/env python3
"""Grid-displacement observation at order six. Start: the grid configuration v1*(1,2,3,4,5), isolated at the grid
instant 1/(6 v1). Move one speed at a time to the target set S (v5, then v4, v3, v2), each along N rational steps;
at every sample compute the earliest lonely instant T (exact cascade on the five positive speeds). Record the
flank of T (the element whose opening T is) and every JUMP: consecutive samples whose T are not on the same
flank-opening branch (flank or opening index changes). At a jump, report which element is in the way at the old
branch's instant just after the change (it closed the old isolation), and the new flank/opening.
Usage: six_deform_v1.py N s1 s2 s3 s4 s5"""
import sys
from fractions import Fraction as F
N = int(sys.argv[1]); S = [int(x) for x in sys.argv[2:7]]
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
thr = F(1, 6)
def earliest(V):
    m = min(V); t = F(1, 6 * m)
    for _ in range(100000):
        blk = [d for d in V if cd(d * t) < thr]
        if not blk: return t
        t = max((-((-(d * t - thr).numerator) // (d * t - thr).denominator) + thr) / d for d in blk)
    raise RuntimeError
def branch(V, t):
    # which element's opening is t: index and lap (ties: lowest index)
    for i, d in enumerate(V):
        x = d * t - thr
        if x.denominator == 1: return (i + 1, int(x))
    return (0, None)
V = [F(S[0] * k) for k in range(1, 6)]
order = [4, 3, 2, 1]                       # move v5, v4, v3, v2
prevT = earliest(V); prevB = branch(V, prevT)
print(f"start grid {[str(x) for x in V]}: T = {prevT} branch {prevB}")
jumps = 0
for idx in order:
    a, b = V[idx], F(S[idx])
    for j in range(1, N + 1):
        W = list(V); W[idx] = a + (b - a) * F(j, N)
        if len(set(W)) < 5: continue
        T = earliest(W); B = branch(W, T)
        if B != prevB:
            jumps += 1
            closer = [k + 1 for k, d in enumerate(W) if cd(d * prevT) < thr]
            print(f"  moving v{idx+1}: step {j}/{N}, speed {float(W[idx]):.3f}: JUMP {prevB} -> {B}; "
                  f"T {float(prevT):.5f} -> {float(T):.5f}; old instant now blocked by {closer}")
        prevT, prevB = T, B
    V[idx] = b
print(f"end {S}: T = {prevT} = {float(prevT):.5f}, v1*T = {float(S[0]*prevT):.4f}, branch {prevB}; jumps {jumps}")
