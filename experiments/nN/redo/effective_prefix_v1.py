# Locality: at a predicted effective crossing with state index i the move sequence before and after share exactly the first i moves.
import sys, random
sys.argv = [sys.argv[0]]
exec(open('effective_crossings_v1.py').read().split('\nif __name__ ==')[0])
rnd = random.Random(316)
bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]), ("wide", [F(1), F(2), F(5), F(11), F(23), F(47), F(95)]),
         ("clump", [F(1), F(30), F(31), F(33), F(36), F(40), F(45)])]
for i in range(6): bases.append(("rand%d" % i, [F(x, 1) for x in sorted(rnd.sample(range(10, 400), 7))]))
bases = [(n, [F(x) / b[0] for x in b]) for n, b in bases]
from collections import Counter
tot = same = 0; kinds = Counter(); bad = []
for name, base in bases:
    for r in range(25):
        k = rnd.choice((1, 2, 3, 4, 5)); movers = tuple(sorted(rnd.sample(range(7), k)))
        p = list(base); q = [F(0)] * 7
        for m in movers:
            span = max(F(1), base[m] / 3); q[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-150, 300), 100) * span) - base[m]
        s0 = F(rnd.randint(1, 9999), 10007)
        pred, steps = predicted_next(p, q, s0)
        if pred is None or pred[0] >= 1: continue
        s = pred[0]; i = pred[1]; eps = F(1, 10**9)
        l0 = label(rho_at(p, q, s - eps))[:-1]; l1 = label(rho_at(p, q, s + eps))[:-1]
        cp = 0
        while cp < min(len(l0), len(l1)) and l0[cp] == l1[cp]: cp += 1
        tot += 1; kind = ("start" if pred[2][1] == -1 else "end")
        kinds[(kind, 'prefix=i' if cp == i else ('prefix=i-1' if cp == i - 1 else 'other'))] += 1
        if cp in (i, i - 1): same += 1
        else: bad.append((name, movers, float(s), i, cp, len(l0), len(l1)))
print("effective crossings checked:", tot, "; common prefix of the move sequence before/after is i or i-1 (the first differing move leaves state i, or state i-1 for a setter swap):", same)
print("by kind of the crossing edge (start/end, prefix == i):", sorted(kinds.items()))
for b in bad[:12]: print("  prefix != i:", b)
