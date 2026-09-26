"""Map how the cascade's isolations divide among the PROVED lemmas.  Every set T of 7 distinct whole-number readings in
1..32 (the slowest runner of eight moving runners).  Each set is tagged with every proved lemma that settles it:
  R1        max <= 7 min                                     (lonely at 1/(8 min))
  ladder    some q in 2..8 divides no reading                (lonely at 1/q; grid at modulus q)
  nudge     GridNudgeN at t0 = a/8, a in {1,3,5,7}: the largest reading is the only multiple of 8 and the a-residues
            of the others avoid 7 (forward) or 1 (backward)
  revR1     all others in [e/9, 7e/9], e the largest          (lonely at 9/(8e))
  offlat    OffLatticeN: some reading x not divisible by the gcd of the others
  flanksum  FlankSumN at some reading's flank: whole ratios not divisible by 8, sum over movers (1/4 + 1/c) < 1
The sets settled by none: the cascade's isolation (scale reading e, lap k, R, moves).  Exact."""
import itertools
from fractions import Fraction as F
from math import gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
from residual_cascade_v1 import cascade_flank

def r1(T): return T[-1] <= 7 * T[0]
def ladder(T): return any(all(d % q for d in T) for q in range(2, 9))
def nudge(T):
    d0 = T[-1]
    if d0 % 8 or any(d % 8 == 0 for d in T[:-1]): return False
    for a in (1, 3, 5, 7):
        res = [(a * d) % 8 for d in T[:-1]]
        if 7 not in res or 1 not in res: return True
    return False
def revr1(T):
    e = T[-1]; return all(9 * d >= e and 9 * d <= 7 * e for d in T[:-1])
def offlat(T):
    for i, x in enumerate(T):
        g = reduce(gcd, T[:i] + T[i + 1:])
        if x % g: return True
    return False
def flanksum(T):
    for e in T:
        s = F(0); ok = True
        for d in T:
            r = F(d, e)
            if r.denominator == 1:
                if r.numerator % 8 == 0: ok = False; break
            else: s += F(1, 4) + F(1, r.denominator)
        if ok and s < 1: return True
    return False

TESTS = [('R1', r1), ('ladder', ladder), ('nudge', nudge), ('revR1', revr1), ('offlat', offlat), ('flanksum', flanksum)]

def chunk(first):
    tags = Counter(); only = Counter(); none = []; ncount = 0
    for rest in itertools.combinations(range(first + 1, 33), 6):
        T = (first,) + rest
        hit = [name for name, f in TESTS if f(T)]
        for h in hit: tags[h] += 1
        if len(hit) == 1: only[hit[0]] += 1
        if not hit:
            ncount += 1
            if len(none) < 400:
                t, e, k, mv = cascade_flank(list(T)); none.append((T, e, k, mv, float(8 * T[0] * t)))
    return tags, only, ncount, none

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 27))
    tags = Counter(); only = Counter(); n = 0; none = []
    for a, b, c, d in parts: tags.update(a); only.update(b); n += c; none += d
    total = sum(1 for _ in itertools.combinations(range(1, 33), 7))
    print(f"reading sets (7 distinct in 1..32): {total}")
    for name, _ in TESTS: print(f"  settled by {name:9s}: {tags[name]:8d}   (by it alone: {only[name]})")
    print(f"  settled by none of them: {n}")
    ek = Counter((e == T[0] and k == 0, min(k, 4)) for T, e, k, mv, R in none)
    print(f"  (in the first 400 per start) cascade isolation for the unsettled: at the bound / lap k: {sorted(ek.items())}")
    for T, e, k, mv, R in none[:12]:
        print(f"    T {T}: isolation at scale reading {e}, lap {k}, R {R:.3f}, {mv} moves")
