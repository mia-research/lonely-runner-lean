"""E160: the transport claim, through the cascade.  For every move of every Case B chain (readings <= 24): the state
before the move normalised by scale and grid (each reading's eighth-slot floor(8 d t) mod 8 at the move's start, the
captured/setting runner's rank, and for each other reading whether it is faster than the setter) and the obstruction
after the move (the ranks of the readings in the subject's window at the new instant, or 'lands').  Question 1: does the
normalised state determine the next obstruction (one outcome per state)?  Question 2: how often is the next obstruction a
single reading (one pair) vs two or more?  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import defaultdict, Counter
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def moves(T):
    t = F(1, 8 * T[0]); out = []
    while True:
        W = [i for i, d in enumerate(T) if nd(d * t) < E8]
        if not W:
            out.append((None, t)); return out
        ex = {i: (F(floor(T[i] * t - E8) + 1) + E8) / T[i] for i in W}
        t2 = max(ex.values()); a = max(W, key=lambda i: ex[i])
        state = (tuple(floor(8 * d * t) % 8 for d in T), a, tuple(d > T[a] for d in T))
        W2 = tuple(i for i, d in enumerate(T) if nd(d * t2) < E8)
        out.append((state, W2 if W2 else 'lands'))
        t = t2
def chunk(first):
    det = defaultdict(set); mult = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1] <= 24 * T[0]): continue
        for st, nxt in moves(T):
            if st is None: continue
            det[st].add(nxt)
            mult['lands' if nxt == 'lands' else 'next obstruction: %d reading(s)' % len(nxt)] += 1
    return det, mult
if __name__ == '__main__':
    D = defaultdict(set); M = Counter()
    with Pool(8) as p:
        for det, mult in p.imap_unordered(chunk, range(1, 19)):
            for k, v in det.items(): D[k] |= v
            M.update(mult)
    amb = [k for k, v in D.items() if len(v) > 1]
    print("normalised states: %d; states with more than one next obstruction: %d (%.1f%%)" % (len(D), len(amb), 100 * len(amb) / len(D)))
    print("outcomes of moves:", dict(M))
    for k in amb[:8]: print("   ambiguous state", k, "->", sorted(map(str, D[k]))[:6])
