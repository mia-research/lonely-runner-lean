"""E150 v3: all 772 exceptions (no cap), classified by the mechanism the landing is:
  S-own: t* = S's own landing from t0 (G clear there);
  nudge: at the bound every reading is on an eighth (d_min | every reading) and the largest is the only one = 0 mod 8 d_min,
         and t* = t0 + 1/(8 d_max) (GridNudgeN, forward);
  S-next: t* is a later S-point (S's cascade continued past points G blocks);
  G-next: t* is a later G-point (G's cascade continued past points S blocks);
  (a landing is always some reading's exit, so S-next / G-next = the flank's group).  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade_from(T, t):
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def points(A, t, tmax):
    """the lonely points of A (cascade landings, restarting past each) up to tmax"""
    out = []
    while t <= tmax:
        p = cascade_from(A, t); out.append(p)
        if p > tmax: break
        t = p + F(1, 10 ** 9)   # strictly after p; exact rational step past the point
    return out
def classify(T):
    t0 = F(1, 8 * T[0]); ts = cascade_from(T, t0)
    if ts == t0: return None
    gi = max(range(1, 7), key=lambda i: F(T[i], T[i - 1]))
    S = T[:gi]; G = T[gi:]; tg = cascade_from(G, t0)
    if tg == ts and F(S[-1], S[0]) <= 7 and tg <= F(7, 8 * S[-1]): return None
    kind = 'later block' if tg == ts else 'delayed'
    if cascade_from(S, t0) == ts: return (kind, 'S-own')
    if all(d % T[0] == 0 for d in T):
        res = [(d // T[0]) % 8 for d in T]
        if res.count(0) == 1 and res[-1] == 0 and ts == t0 + F(1, 8 * T[-1]): return (kind, 'nudge (GridNudgeN)')
    f = next(i for i, d in enumerate(T) if (8 * d * ts) % 8 == 1)   # the landing is the flank's exit
    if f < gi: return (kind, 'S-next: the flank is a slow reading (S leads, G blocked its earlier points)')
    return (kind, 'G-next: the flank is a fast reading (G leads, S blocked its earlier points)')
def chunk(first):
    C = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if 7 * T[0] < T[-1]:
            c = classify(T)
            if c: C[c] += 1
            if c and c[1] == 'other' and len(ex) < 10: ex.append(T)
    return C, ex
if __name__ == '__main__':
    C = Counter(); EX = []
    with Pool(8) as p:
        for c, e in p.imap_unordered(chunk, range(1, 19)): C.update(c); EX += e
    print("total:", sum(C.values()))
    for k, v in sorted(C.items()): print("  %5d  %s" % (v, k))
    print("other, examples:", EX[:20])
