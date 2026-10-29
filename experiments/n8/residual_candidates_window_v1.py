# E639: the cluster class with the slow cluster's exact clear window instead of a gate.  Slow cluster S = first m readings (whole numbers, d_min = S[0] kept as the time unit 1/S[0]).
# Window: a maximal interval on which every s in S is 1/8-clear, found by exact interval arithmetic over one period 1/g (g = gcd of S).  Fast part: singleton rungs (ChainOK2 under gap2) and a terminal single or pair
# with total gap L = gap2; the class holds when some window of S has width at least L.  Counts whole-number sets passing the simple fields of EightResidual with residue-settled sets removed, in no fixed instant
# and not covered by the gate-based chain.  Exact.  usage: N
import sys, math, itertools
from fractions import Fraction as F
exec(open('residual_candidates_qgate_v1.py').read().split("cnt = 0; fixed = 0")[0])
def clear_iv(x, T):
    out = []; n = 0
    while True:
        lo = F(8 * n + 1, 8) / x; hi = F(8 * n + 7, 8) / x
        if lo > T: break
        out.append((lo, min(hi, T))); n += 1
    return out
def meet(A, B):
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi: out.append((lo, hi))
        if A[i][1] < B[j][1]: i += 1
        else: j += 1
    return out
def max_window(S):
    g = 0
    for d in S: g = math.gcd(g, d)
    T = F(2, g)
    J = clear_iv(F(S[0]), T)
    for s in S[1:]: J = meet(J, clear_iv(F(s), T))
    return max((hi - lo for lo, hi in J), default=F(0))
def chain_window(S):
    r = [F(d) for d in S]; n = len(r)
    for m in range(1, 7):
        for k in (1, 2):
            if m + k > n: continue
            rungs = r[m:n - k]; T = r[n - k:]
            LT = F(1, 4) / T[0] if k == 1 else F(1, 2) / T[0]
            gaps = [LT]
            for x in reversed(rungs): gaps.append(F(1, 4) / x + 2 * gaps[-1])
            gaps.reverse()
            if not all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs))): continue
            if max_window(S[:m]) >= gaps[0]: return True
    return False
cnt = 0; fixed = 0; gate = 0; win = 0; left = []
for S in itertools.combinations(range(1, N + 1), 7):
    if not simple_fields(S) or residue_settled(S): continue
    cnt += 1
    if fixedR(S): fixed += 1; continue
    if chain2([F(d, S[0]) for d in S]) or chain2q([F(d) for d in S]): gate += 1; continue
    if chain_window(S): win += 1; continue
    left.append(S)
print('N', N, 'after simple fields and residue cases', cnt, 'fixed instant', fixed, 'gate chain', gate, 'window chain only', win, 'neither', len(left))
print('examples', left[:8])
