"""Owner: where two runners share a slot and no scale separates them, isolation may take multiple cycles.  A chain of
nudges with every setter distinct has at most 7 moves and ends inside the first lap (Thm 6.25: each move < 9/7, and
(9/7)^7 < 7); longer relays need a setter to repeat.  Test: in chains where a setter repeats, is the repeating reading
crowded -- another reading within g of it, with g small against the repeater's own scale (g * t at the repeat < 1/8:
the two sit in the same eighth there, i.e. share the slot)?  Compare with the chains without a repeat (the setters'
nearest neighbour reading at their setting instant).  Exhaustive readings <= 24.  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def chain(T):
    t = F(1, 8 * T[0]); setters = []; times = []
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return setters, times
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in way}
        s = max(ex, key=lambda x: ex[x]); setters.append(s); times.append(t); t = ex[s]

def shares(T, s, t):
    """another reading sits in the same eighth as s at instant t (|d - s| * t < 1/8)"""
    return any(d != s and abs(d - s) * t < E8 for d in T)

def chunk(first):
    c = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        setters, times = chain(T)
        if not setters: continue
        seen = {}; rep = None
        for i, s in enumerate(setters):
            if s in seen and rep is None: rep = (s, times[i])
            seen[s] = i
        if rep:
            c['repeat chains'] += 1
            c['repeater shares its eighth with a neighbour at the repeat'] += shares(T, rep[0], rep[1])
        else:
            c['no-repeat chains'] += 1
            c['some setter shares its eighth when it sets (no repeat)'] += any(shares(T, s, t) for s, t in zip(setters, times))
    return c

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter()
    for p in parts: c.update(p)
    for k, v in c.items(): print(f"  {k}: {v}")
