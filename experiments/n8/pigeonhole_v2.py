"""Two extensions of the counting argument, in the DISCRETE candidate setting.

(a) per-s_k pigeonhole: we may CHOOSE s_k, so ask if ANY single s_k has
    (blocking pairs among its candidates) < (its candidate count).
(b) Hunter-Kounias on the candidate set:
    |union A_i| <= sum|A_i| - max_spanning_tree sum |A_i ^ A_j|
    A witness exists if |union| < N.  Deficit to cover: sum|A_i| - N.
"""
from itertools import combinations

def cands(sk):
    A = sk + ((1-sk) % 8); out = []
    while A <= 7*sk: out.append(A); A += 8
    return out

def analyse(S, sk):
    """Return (N, blocked-sets per reading) for the candidates of sk."""
    C = cands(sk); N = len(C)
    A = {}
    for si in S:
        if si == sk or si == 1: continue
        M = 8*sk
        A[si] = {j for j, a in enumerate(C) if min((si*a) % M, M - (si*a) % M) < sk}
    return N, A

def hk(N, A):
    """Hunter-Kounias upper bound on |union|."""
    ks = list(A)
    if not ks: return 0
    pw = {}
    for a, b in combinations(ks, 2): pw[(a, b)] = len(A[a] & A[b])
    par = {k: k for k in ks}
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    tree = 0
    for (a, b), v in sorted(pw.items(), key=lambda kv: -kv[1]):
        ra, rb = find(a), find(b)
        if ra != rb: par[ra] = rb; tree += v
    return sum(len(A[k]) for k in ks) - tree

pool = pers = hkw = tot = 0
neither = []
for combo in combinations(range(2, 31), 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo; tot += 1
    tN = tB = 0; okS = okH = False
    for sk in S:
        N, A = analyse(S, sk)
        b = sum(len(v) for v in A.values())
        tN += N; tB += b
        if b < N: okS = True
        if hk(N, A) < N: okH = True
    if tB < tN: pool += 1
    if okS: pers += 1
    if okH: hkw += 1
    if not okH: neither.append(S)
print(f"EXHAUSTIVE Branch B, readings [2,30]: {tot:,} profiles\n")
print(f"  (0) pooled pigeonhole, as run before     : {pool:>7,}  ({100*pool/tot:6.2f}%)")
print(f"  (a) per-s_k pigeonhole                   : {pers:>7,}  ({100*pers/tot:6.2f}%)")
print(f"  (b) per-s_k Hunter-Kounias               : {hkw:>7,}  ({100*hkw/tot:6.2f}%)")
print(f"\n  profiles settled by NEITHER (b) nor below: {len(neither):,}")
for S in neither[:6]: print("     ", S)
