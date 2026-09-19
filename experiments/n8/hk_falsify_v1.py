"""Falsification battery for the discrete Hunter-Kounias result.  Be hostile to it."""
from itertools import combinations
import random

def cands(sk, n):
    A = sk + ((1-sk) % n); out = []
    while A <= (n-1)*sk: out.append(A); A += n
    return out

def sets(S, sk, n):
    C = cands(sk, n); N = len(C); M = n*sk
    A = {}
    for si in S:
        if si == sk or si == 1: continue
        A[si] = {j for j, a in enumerate(C) if min((si*a) % M, M - (si*a) % M) < sk}
    return N, A

def hk(A):
    ks = list(A)
    if not ks: return 0
    pw = {(a,b): len(A[a] & A[b]) for a, b in combinations(ks, 2)}
    par = {k: k for k in ks}
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    tree = 0
    for (a, b), v in sorted(pw.items(), key=lambda kv: -kv[1]):
        ra, rb = find(a), find(b)
        if ra != rb: par[ra] = rb; tree += v
    return sum(len(A[k]) for k in ks) - tree

def truth(N, A):
    u = set()
    for v in A.values(): u |= v
    return N - len(u)        # number of unblocked candidates = witnesses

# --- CHECK 1: is the HK bound actually an upper bound on |union|? ---
rng = random.Random(1); viol = 0; trivial = 0; tested = 0
for _ in range(20000):
    n = rng.choice([7,8,9,11,13]); k = n-1
    S = [1] + sorted(rng.sample(range(2, 200), k-1))
    sk = rng.choice(S)
    N, A = sets(S, sk, n)
    if N == 0: continue
    tested += 1
    u = set()
    for v in A.values(): u |= v
    if hk(A) < len(u): viol += 1
    if sum(len(v) for v in A.values()) < N: trivial += 1
print(f"CHECK 1  HK >= |union| on {tested:,} instances: violations = {viol}  "
      f"(0 required)   [{trivial:,} were already trivial by first moment]")

# --- CHECK 2: does it prove too much?  Other orders, where LRC is OPEN. ---
print(f"\nCHECK 2  does the argument settle orders where LRC is open?")
print(f"{'n':>4} {'profiles':>9} {'HK settles':>11} {'true witness':>13}  verdict")
for n in [7, 8, 9, 11, 13, 17]:
    k = n-1; okH = 0; okT = 0; N_ = 3000
    rng2 = random.Random(20260919)
    for _ in range(N_):
        S = [1] + sorted(rng2.sample(range(2, 200), k-1))
        h = t = False
        for sk in S:
            N, A = sets(S, sk, n)
            if N == 0: continue
            if hk(A) < N: h = True
            if truth(N, A) > 0: t = True
        okH += h; okT += t
    v = "PROVES TOO MUCH" if (n >= 11 and okH == N_) else ("consistent" if okH <= okT else "BOUND BROKEN")
    print(f"{n:>4} {N_:>9,} {okH:>11,} {okT:>13,}  {v}")
