"""E142: every move of every chain as a sweep step or a bridge.  Consecutive setters a -> b with exit laps k_a, k_b:
  sweep step: b slower than a and k_b = k_a (then necessarily s_a (8k-1)/(8k+1) < s_b);
  bridge: anything else, classed as (faster runner / slower runner) x (lap up / same / down).
Checks the sweep-step ratio condition on every sweep step.  Populations: band to 24, Case B to 24, late fine shapes."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
E8 = F(1, 8)
def pos8(d, t): return (8 * d * t) % 8
def moves(T):
    t = F(1, 8 * T[0]); out = []
    while True:
        W = [d for d in T if (lambda p: p < 1 or p > 7)(pos8(d, t))]
        if not W: return out
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(ex.values()); a = max(W, key=lambda d: ex[d]); k = floor(a * t2 - E8)
        out.append((a, k)); t = t2
def classify(T):
    c = Counter(); bad = 0
    mv = moves(T)
    for (a, ka), (b, kb) in zip(mv, mv[1:]):
        if b < a and kb == ka:
            c['sweep step'] += 1
            if not (a * (8 * ka - 1) < b * (8 * ka + 1)): bad += 1
        else:
            c['bridge: %s runner, lap %s' % ('faster' if b > a else 'slower' if b < a else 'same', 'up' if kb > ka else 'down' if kb < ka else 'same')] += 1
    return c, bad
def chunk(first):
    C = Counter(); B = 0
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if 7 * T[0] < T[-1]:
            c, b = classify(T); B += b
            for k, v in c.items(): C[('caseB24' if T[-1] > 9 * T[0] else 'band24', k)] += v
    return C, B
if __name__ == '__main__':
    C = Counter(); B = 0
    with Pool(8) as p:
        for c, b in p.imap_unordered(chunk, range(1, 19)): C.update(c); B += b
    D1 = 27720; rng = random.Random(41); late = set()
    for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
        T = [int(round(x * D1)) for x in sd]
        for step in range(3000):
            U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
            if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
            if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
            T = U; late.add(tuple(U))
    for T in late:
        c, b = classify(T); B += b
        for k, v in c.items(): C[('late', k)] += v
    for pop in ('band24', 'caseB24', 'late'):
        print("==", pop)
        for k, v in sorted(((k[1], v) for k, v in C.items() if k[0] == pop), key=lambda kv: -kv[1]): print("  %7d  %s" % (v, k))
    print("sweep steps violating the ratio condition:", B)
