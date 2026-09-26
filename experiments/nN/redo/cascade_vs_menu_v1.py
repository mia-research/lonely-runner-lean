"""Owner: the cascade does not search, so a mechanism dictates where the isolation is displaced.  Test whether it is the
menu of views: for every set of 7 distinct whole-number readings in 1..24, the cascade's isolation t* (the first lonely
instant at or after the bound) against the explicit views -- the bound 1/(8 d_min); ladder rungs a/q; nudges
a/8 +- 1/(8 d0); rung R1 a/q +- 1/(8 min D_q); reverse R1 9/(8 e) -- and, since the cascade's instant is always a
candidate scale, the second openings (8k+1)/(8e) for k = 1 (the next opening of each reading).  Is t* itself one of
the views?  If not, how far is the earliest successful view beyond t*?  Exact."""
import itertools
from fractions import Fraction as F
from math import gcd, floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)
def lonely(T, t): return t > 0 and all(nd(d * t) >= E8 for d in T)

def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)

def views(T):
    V = {('B',): F(1, 8 * T[0])}
    for q in range(2, 9):
        D = [d for d in T if d % q == 0]
        for a in range(1, q):
            if gcd(a, q) != 1: continue
            V[('L', a, q)] = F(a, q)
            if D:
                for s in (1, -1): V[('R', a, q, s)] = F(a, q) + F(s, 8 * min(D))
    m8 = [d for d in T if d % 8 == 0]
    if m8:
        for a in (1, 3, 5, 7):
            for s in (1, -1): V[('N', a, s)] = F(a, 8) + F(s, 8 * max(m8))
    V[('V',)] = F(9, 8 * T[-1])
    for e in T: V[('O', e)] = F(9, 8 * e)       # the next opening (k = 1) of each reading
    return V

def chunk(first):
    c = Counter(); fam = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; ts = cascade(T); V = views(T)
        hit = [k for k, t in V.items() if t == ts]
        if hit:
            c['cascade instant is a view'] += 1; fam[hit[0][0]] += 1
        else:
            c['not a view'] += 1
            ok = [t for t in V.values() if t >= ts and lonely(T, t)]
            c['a later view isolates'] += bool(ok)
    return c, fam

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); fam = Counter()
    for a, b in parts: c.update(a); fam.update(b)
    print(f"reading sets: {sum(v for k, v in c.items() if k in ('cascade instant is a view', 'not a view'))}")
    for k, v in c.items(): print(f"  {k}: {v}")
    print(f"  the view the cascade lands on, by family: {sorted(fam.items(), key=lambda x: -x[1])}")
