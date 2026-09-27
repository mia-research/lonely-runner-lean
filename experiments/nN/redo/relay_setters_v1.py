"""E140: who drives a long relay.  For each chain (band to 24, Case B to 24 with >= 4 moves, late fine band shapes):
the setters (runner whose exit sets each move), the number of distinct setters, the share of moves set by the two most
frequent setters, and whether consecutive setters alternate within that pair.  Also, at each single-runner move, where
the next move's runner sits (eighths) at the exit instant.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
E8 = F(1, 8)
def pos8(d, t): return (8 * d * t) % 8
def trace(T):
    t = F(1, 8 * T[0]); mv = []
    while True:
        W = [d for d in T if (lambda p: p < 1 or p > 7)(pos8(d, t))]
        if not W: return 8 * T[0] * t, mv
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(ex.values()); a = max(W, key=lambda d: ex[d])
        mv.append((len(W), T.index(a), t2)); t = t2
def study(pop, sets, minlen):
    dist = Counter(); share = Counter(); alt = Counter(); nextpos = Counter()
    for T in sets:
        R, mv = trace(T)
        if len(mv) < minlen: continue
        setters = [m[1] for m in mv]
        c = Counter(setters); dist[(pop, 'distinct setters %d' % len(c))] += 1
        top2 = sum(v for _, v in c.most_common(2)); share[(pop, 'top-two share %s' % ('all' if top2 == len(mv) else '>=75%' if 4 * top2 >= 3 * len(mv) else '<75%'))] += 1
        pair = {k for k, _ in c.most_common(2)}
        a = sum(1 for x, y in zip(setters, setters[1:]) if x in pair and y in pair and x != y)
        alt[(pop, 'consecutive setters alternating within the top pair: %s' % ('all' if a == len(mv) - 1 else '>=half' if 2 * a >= len(mv) - 1 else '<half'))] += 1
        for (w, s, t2), nxt in zip(mv, mv[1:]):
            if w == 1:
                b = T[nxt[1]]
                p = pos8(b, t2); nextpos[(pop, 'next runner at exit: %s' % ('in (7,8)' if p > 7 else 'in [0,1)' if p < 1 else 'clear'))] += 1
    return [dist, share, alt, nextpos]
if __name__ == '__main__':
    band = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 9 * T[0]]
    caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1]]
    D1 = 27720; rng = random.Random(41); late = set()
    for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
        T = [int(round(x * D1)) for x in sd]
        for step in range(3000):
            U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
            if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
            if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
            T = U; late.add(tuple(U))
    for pop, S, ml in (('band24 (>=4 moves)', band, 4), ('caseB24 (>=4 moves)', caseB, 4), ('late', sorted(late), 1)):
        for C in study(pop, S, ml):
            for k, v in sorted(C.items()): print("  %6d  %s" % (v, k))
        print()
