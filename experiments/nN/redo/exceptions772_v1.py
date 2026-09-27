"""E150: the 772 Case B (readings <= 24) exceptions to the two regimes (E148): 703 where the slow group S blocks the fast
group G's own landing t_G, 69 where t_G lies in a later block of S.  For each: S's spread (R1 or not), the blocker(s) at
t_G (rank in S, lap), and whether the full landing t* is G's next lonely point at which S is clear (G's cascade
continued past the blocked points).  Exact."""
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
def G_points_until(G, S, t, tmax):
    """walk G's lonely points from t; return the first at which S is clear, and how many G-points were skipped"""
    skipped = 0
    while t <= tmax:
        tg = cascade_from(G, t)
        if all(nd(s * tg) >= E8 for s in S): return tg, skipped
        skipped += 1
        # step just past tg: next G-lonely point strictly later -> restart from the blockers' exits
        bl = [s for s in S if nd(s * tg) < E8]
        t = max((F(floor(s * tg - E8) + 1) + E8) / s for s in bl)
    return None, skipped
def study(first):
    C = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if not (7 * T[0] < T[-1]): continue
        t0 = F(1, 8 * T[0]); ts = cascade_from(T, t0)
        if ts == t0: continue
        gi = max(range(1, 7), key=lambda i: F(T[i], T[i - 1]))
        S = T[:gi]; G = T[gi:]; tg = cascade_from(G, t0)
        sR1 = F(S[-1], S[0]) <= 7
        if tg == ts and sR1 and tg <= F(7, 8 * S[-1]): continue      # the two regimes
        kind = 'later block' if tg == ts else 'delayed'
        bl = [(i, floor(S[i] * tg)) for i in range(len(S)) if nd(S[i] * tg) < E8]
        tn, skipped = G_points_until(G, S, t0, ts)
        C[(kind, 'S is R1' if sR1 else 'S spread > 7', '|S| = %d' % len(S))] += 1
        C[(kind, 'landing = first G-point with S clear' if tn == ts else 'landing elsewhere', 'G-points skipped %s' % min(skipped, 3))] += 1
        for (i, lap) in bl: C[(kind, 'blocker rank in S %s (from top %d), lap %d' % (i, len(S) - 1 - i, lap))] += 1
        if len(ex) < 400: ex.append((kind, T, S, G, float(8 * T[0] * tg), float(8 * T[0] * ts), bl))
    return C, ex
if __name__ == '__main__':
    C = Counter(); EX = []
    with Pool(8) as p:
        for c, e in p.imap_unordered(study, range(1, 19)): C.update(c); EX += e
    for k, v in sorted(C.items()): print("  %5d  %s" % (v, k))
    print("\nexamples (kind, T, S, G, R_G, R*, blockers (rank, lap)):")
    for e in sorted(EX, key=lambda e: e[1])[:30]: print("  ", e)
    import pickle; pickle.dump(EX, open('exceptions772_v1.pkl', 'wb'))
