# E639: the chain class with a better gate for the slow cluster.  Slow cluster S = first m readings; its gate is the best of
#   native 1/(m+1)  and  1/q  for q in 2..7 when every s in S is n u (u = unit, n whole) with q not dividing n, instant 1/(q u)  (S commensurable with unit u = g/j, g = gcd of S, j in 1..8).
# Then singleton rungs (ChainOK2 under gap2) and a terminal single or pair.  Count the whole-number sets passing the simple fields of EightResidual, residue-settled sets removed,
# that are in neither the fixed-instant list nor this chain class.  Exact.  usage: N
import sys, math, itertools
from fractions import Fraction as F
exec(open('residual_candidates_growth_v3.py').read().split("cand = 0; resid = 0")[0])
def slow_gate(S):
    """best gate for the slow set S (list of Fractions): returns max of 1/(len+1) and the q-gates."""
    best = F(1, len(S) + 1)
    den = 1
    for d in S: den = den * d.denominator // math.gcd(den, d.denominator)
    a = [int(d * den) for d in S]; g = 0
    for x in a: g = math.gcd(g, x)
    for j in range(1, 9):
        if any((x * j) % g for x in a): continue
        ns = [x * j // g for x in a]
        for q in range(2, 8):
            if all(n % q for n in ns): best = max(best, F(1, q))
    return best
def chain2q(r):
    n = len(r)
    for m in range(0, 7):
        for k in (1, 2):
            if m + k > n: continue
            rungs = r[m:n - k]; T = r[n - k:]
            LT = F(1, 4) / T[0] if k == 1 else F(1, 2) / T[0]
            gaps = [LT]
            for x in reversed(rungs): gaps.append(F(1, 4) / x + 2 * gaps[-1])
            gaps.reverse()
            if not all(gaps[i + 1] <= F(3, 4) / rungs[i] for i in range(len(rungs))): continue
            if m == 0: return True
            M = r[m - 1]; gam = slow_gate(r[:m])
            if gam > E and gaps[0] * M <= 2 * (gam - E): return True
    return False
cnt = 0; fixed = 0; chain_old = 0; chain_q = 0; left = []
for S in itertools.combinations(range(1, N + 1), 7):
    if not simple_fields(S) or residue_settled(S): continue
    cnt += 1
    if fixedR(S): fixed += 1; continue
    r = [F(d, S[0]) for d in S]
    if chain2(r): chain_old += 1; continue
    if chain2q([F(d) for d in S]): chain_q += 1; continue
    left.append(S)
print('N', N, 'after simple fields and residue cases', cnt, 'fixed instant', fixed, 'chain (native gate)', chain_old, 'chain with q-gate only', chain_q, 'neither', len(left))
print('examples', left[:8])
