# Large test of the effective-crossing rule: predicted next change of the move sequence vs the cascade's actual next change.
import sys, random, os
sys.argv = [sys.argv[0]]
exec(open('effective_crossings_v1.py').read().split('\nif __name__ ==')[0])
rnd = random.Random(315)
def randbase():
    xs = sorted(rnd.sample(range(10, 400), 7)); return [F(x, 10) * F(10, xs[0]) if False else F(x, xs[0]) for x in xs]
bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]), ("g14", [F(x) for x in (1, 2, 3, 4, 5, 7, 14)]),
         ("3AP", [F(3 * x) for x in range(1, 8)]), ("wide", [F(1), F(2), F(5), F(11), F(23), F(47), F(95)]),
         ("clump", [F(1), F(30), F(31), F(33), F(36), F(40), F(45)])]
for i in range(6): bases.append(("rand%d" % i, randbase()))
tot = ok = 0; bad = []; byk = {}; badfull = []
for name, base in bases:
    for r in range(25):
        k = rnd.choice((1, 2, 3, 4, 5, 6)); movers = tuple(sorted(rnd.sample(range(7), k)))
        p = list(base); q = [F(0)] * 7
        for m in movers:
            span = max(F(1), base[m] / 3)
            q[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-150, 300), 100) * span) - base[m]
        for t in range(2):
            s0 = F(rnd.randint(1, 9999), 10007)
            pred, steps = predicted_next(p, q, s0); obs, a, b = observed_next(p, q, s0, N=600)
            tot += 1; byk.setdefault(k, [0, 0]); byk[k][0] += 1
            if (obs is None and pred is None) or (obs is not None and pred is not None and a - 1e-12 <= float(pred[0]) <= b + 1e-12 and abs(float(pred[0]) - obs) < 1e-6):
                ok += 1; byk[k][1] += 1
            else:
                bad.append((name, movers, float(s0), None if pred is None else float(pred[0]), obs, None if pred is None else pred[2]))
                badfull.append((name, list(p), list(q), s0, pred, obs))
print("predictions:", tot, "; equal to the observed next change (or both: no further change):", ok, "; not:", len(bad))
print("by number of movers (total, matching):", sorted(byk.items()))
for b in bad[:20]: print("  MISMATCH", b)

import pickle
pickle.dump(badfull, open('effective_crossings_bad.pkl', 'wb'))
