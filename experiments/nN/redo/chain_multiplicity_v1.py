"""E139: the cascade's chain, move by move, by how many runners are in the subject's window at once (w).  Owner: two in
one slot is the only hard case; with three or more the cluster is an AP at its own scale.  For every move: w, and the
number of moves left to the landing.  Populations: band to 24, Case B to 24 (spread (7,24]), late fine band shapes.
Also: along each chain, the sequence of w (the chain's signature).  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
E8 = F(1, 8)
def pos8(d, t): return (8 * d * t) % 8
def trace(T):
    t = F(1, 8 * T[0]); ws = []
    while True:
        W = [d for d in T if (lambda p: p < 1 or p > 7)(pos8(d, t))]
        if not W: return 8 * T[0] * t, ws
        ws.append(len(W))
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in W)
def tally(pop, sets):
    left = Counter(); sig = Counter()
    for T in sets:
        R, ws = trace(T)
        for i, w in enumerate(ws): left[(pop, 'w=%d' % min(w, 4), 'moves left %s' % (min(len(ws) - i - 1, 4) if len(ws) - i - 1 < 4 else '>=4'))] += 1
        sig[(pop, tuple(ws) if len(ws) <= 6 else tuple(ws[:6]) + ('...',))] += 1
    return left, sig
def chunk(first):
    band = []; caseB = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest
        if 7 * T[0] < T[-1] <= 9 * T[0]: band.append(T)
        if 7 * T[0] < T[-1]: caseB.append(T)
    l1, s1 = tally('band24', band); l2, s2 = tally('caseB24', caseB)
    l1.update(l2); s1.update(s2); return l1, s1
if __name__ == '__main__':
    L = Counter(); S = Counter()
    with Pool(8) as p:
        for l, s in p.imap_unordered(chunk, range(1, 19)): L.update(l); S.update(s)
    D1 = 27720; rng = random.Random(41); late = set()
    for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
        T = [int(round(x * D1)) for x in sd]
        for step in range(3000):
            U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
            if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
            if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
            T = U; late.add(tuple(U))
    l, s = tally('late', sorted(late)); L.update(l); S.update(s)
    for pop in ('band24', 'caseB24', 'late'):
        print("==", pop)
        for w in ('w=1', 'w=2', 'w=3', 'w=4'):
            row = {k[2]: v for k, v in L.items() if k[0] == pop and k[1] == w}
            tot = sum(row.values())
            if tot: print("  %s (%d moves): %s" % (w, tot, ', '.join('%s: %d' % (k, row[k]) for k in sorted(row))))
        print("  commonest chain signatures (w per move):", [(k[1], v) for k, v in S.most_common() if k[0] == pop][:8])
