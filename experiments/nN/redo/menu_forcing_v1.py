"""What forces room: for every set of 7 distinct whole-number readings in 1..24 (the slowest runner of eight moving
runners), test exactly every instant of the menu:
  B        the bound 1/(8 d_min)
  L(a/q)   the ladder rungs a/q, q = 2..8, gcd(a, q) = 1
  N(a,s)   the nudges a/8 + s/(8 d0), d0 the largest multiple of 8 (if any), a odd, s = +-1
  R(a/q,s) rung R1 instants a/q + s/(8 min D_q), D_q the multiples of q (if any), s = +-1
  V        reverse R1, 9/(8 e), e the largest reading
and record which families isolate each set.  Then: how many sets each family is needed for (no other family works),
and, for the sets the bound does not isolate, the joint pattern of families that work.  Exact."""
import itertools
from fractions import Fraction as F
from math import gcd
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

def lonely(T, t): return t > 0 and all(nd(d * t) >= F(1, 8) for d in T)

def families(T):
    ok = set()
    if lonely(T, F(1, 8 * T[0])): ok.add('B')
    for q in range(2, 9):
        for a in range(1, q):
            if gcd(a, q) != 1: continue
            if lonely(T, F(a, q)): ok.add('L')
            D = [d for d in T if d % q == 0]
            if D:
                for s in (1, -1):
                    if lonely(T, F(a, q) + F(s, 8 * min(D))): ok.add(f'R{q}')
    m8 = [d for d in T if d % 8 == 0]
    if m8:
        d0 = max(m8)
        for a in (1, 3, 5, 7):
            for s in (1, -1):
                if lonely(T, F(a, 8) + F(s, 8 * d0)): ok.add('N')
    if lonely(T, F(9, 8 * T[-1])): ok.add('V')
    return frozenset(ok)

def chunk(first):
    pat = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        pat[families((first,) + rest)] += 1
    return pat

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    pat = Counter()
    for p in parts: pat.update(p)
    tot = sum(pat.values())
    print(f"reading sets (7 distinct in 1..24): {tot}")
    none = pat[frozenset()]
    print(f"  isolated by no menu instant: {none}")
    fams = sorted({f for k in pat for f in k})
    for f in fams:
        print(f"  {f:4s} works: {sum(v for k, v in pat.items() if f in k):7d}; the only family that works: {sum(v for k, v in pat.items() if k == frozenset([f])):6d}")
    notB = Counter({k: v for k, v in pat.items() if 'B' not in k})
    print(f"  sets the bound does not isolate: {sum(notB.values())}; their most common patterns:")
    for k, v in notB.most_common(15): print(f"    {sorted(k)}: {v}")
