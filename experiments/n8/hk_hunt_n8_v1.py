"""Hostile search for an n=8 integer profile that discrete Hunter-Kounias fails to settle."""
from itertools import combinations
import random

def sets(S, sk, n=8):
    C = []; A = sk + ((1-sk) % n)
    while A <= (n-1)*sk: C.append(A); A += n
    M = n*sk; out = {}
    for si in S:
        if si == sk or si == 1: continue
        out[si] = {j for j, a in enumerate(C) if min((si*a) % M, M - (si*a) % M) < sk}
    return len(C), out

def hk(A):
    ks = list(A)
    if not ks: return 0
    pw = {(a,b): len(A[a] & A[b]) for a, b in combinations(ks, 2)}
    par = {k: k for k in ks}
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    tree = 0
    for (a,b), v in sorted(pw.items(), key=lambda kv: -kv[1]):
        ra, rb = find(a), find(b)
        if ra != rb: par[ra] = rb; tree += v
    return sum(len(A[k]) for k in ks) - tree

def settled(S):
    for sk in S:
        N, A = sets(S, sk)
        if N and hk(A) < N: return True
    return False

fails = []
def scan(name, gen, cap=None):
    n = bad = 0
    for S in gen:
        n += 1
        if not settled(tuple(S)):
            bad += 1
            if len(fails) < 8: fails.append((name, tuple(S)))
        if cap and n >= cap: break
    print(f"  {name:<34} {n:>9,} profiles   NOT settled: {bad:,}")

print("HOSTILE SEARCH, n = 8, all integer profiles (not just Branch B)\n")
scan("exhaustive [1,20], 7 readings", ([1]+list(c) for c in combinations(range(2,21),6)))
scan("exhaustive [1,26], 7 readings", ([1]+list(c) for c in combinations(range(2,27),6)))
rng = random.Random(20260919)
scan("random [2,10^3]", ([1]+sorted(rng.sample(range(2,1000),6)) for _ in range(120000)))
scan("random [2,10^5]", ([1]+sorted(rng.sample(range(2,100000),6)) for _ in range(60000)))
scan("APs  a, a+d, ...", ([1]+[a+i*d for i in range(6)]
      for a in range(2,60) for d in range(1,40)))
scan("powers of 2 heavy", ([1]+sorted(set([2**rng.randrange(1,12) for _ in range(6)]))
      for _ in range(40000) ), cap=40000)
scan("multiples of a base", ([1]+sorted({g*i for i in rng.sample(range(1,40),6)})
      for g in [2,3,4,6,8,12,16,24] for _ in range(6000)))
scan("all divisible by 8", ([1]+sorted(rng.sample(range(8,800,8),6)) for _ in range(40000)))
scan("dense small (the rule-breakers)", ([1]+list(c) for c in combinations(range(2,16),6)))
print()
if fails:
    print("COUNTEREXAMPLES:")
    for nm, S in fails: print(f"   [{nm}]  {S}")
else:
    print("no counterexample found in any arm")
