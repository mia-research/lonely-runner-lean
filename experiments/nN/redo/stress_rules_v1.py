# Stress test of (a) the effective-crossing rule (E312) and (b) hop = birth/death of a lonely-set component (E313) on bases full of exact
# coincidences: small integers (many ties and tangencies), small-denominator rationals, multiples of an AP, and bases with a repeated lap structure.
import sys, random
sys.argv = [sys.argv[0]]
exec(open('effective_crossings_v1.py').read().split('\nif __name__ ==')[0])
exec(open('hop_is_gap_event_v1.py').read().split('from collections import Counter')[0].split("sys.argv = [sys.argv[0]]\n")[1].split("exec(open('effective_crossings_v1.py').read().split('\\nif __name__ ==')[0])\n")[-1])
from collections import Counter
rnd = random.Random(324)
def norm(xs):
    xs = sorted(xs); return [F(x) / xs[0] for x in xs]
fams = {
 "small ints": lambda: norm(rnd.sample(range(1, 25), 7)),
 "rationals": lambda: norm(sorted({F(rnd.randint(2, 30), rnd.choice((2, 3, 4, 5, 6))) for _ in range(9)})[:7] if True else None),
 "k*AP": lambda: norm([F(rnd.randint(1, 5) * j) for j in range(1, 8)]),
 "AP+1 moved": lambda: norm([F(j) for j in range(1, 8)][:6] + [F(rnd.randint(8, 40))]),
 "two clumps": lambda: norm([F(rnd.randint(1, 3) * 8 + j) for j in range(0, 3)] + [F(rnd.randint(4, 6) * 8 + j) for j in range(0, 4)]),
}
ok = tot = 0; bad = []; hop = Counter(); hbad = []
EPS = F(1, 10**9); TINY = F(1, 10**6)
for name, f in fams.items():
    for r in range(30):
        base = f()
        if len(set(base)) < 7: continue
        k = rnd.choice((1, 2, 3)); movers = tuple(sorted(rnd.sample(range(7), k)))
        p = list(base); q_ = [F(0)] * 7
        for m in movers: q_[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-100, 300), 100) * max(F(1), base[m] / 4)) - base[m]
        for t in range(2):
            s0 = F(rnd.randint(1, 9999), 10007)
            pred, steps = predicted_next(p, q_, s0); obs, a, b = observed_next(p, q_, s0, N=400)
            tot += 1
            if (obs is None and pred is None) or (obs is not None and pred is not None and a - 1e-12 <= float(pred[0]) <= b + 1e-12 and abs(float(pred[0]) - obs) < 1e-6): ok += 1
            else: bad.append((name, movers, float(s0), None if pred is None else (float(pred[0]), pred[2]), obs))
            if pred is not None and pred[0] < 1:
                s = pred[0]
                La = lonely_set(rho_at(p, q_, s - EPS)); Lb = lonely_set(rho_at(p, q_, s + EPS))
                if La and Lb:
                    Ra, Rb = La[0][0], Lb[0][0]
                    if abs(Rb - Ra) < TINY: hop["continuous"] += 1
                    elif Rb > Ra and La[0][1] - La[0][0] < TINY and Lb[0][0] >= La[0][1] - TINY: hop["forward = first component dies"] += 1
                    elif Rb < Ra and Lb[0][1] - Lb[0][0] < TINY and Lb[0][1] <= La[0][0] + TINY: hop["backward = earlier component born"] += 1
                    else: hop["OTHER"] += 1; hbad.append((name, movers, float(s), float(Ra), float(Rb)))
print("effective-crossing rule on coincidence-rich bases: predictions", tot, "; exact:", ok, "; not:", len(bad))
for b in bad[:12]: print("   MISMATCH", b)
print("hop = gap event on the same crossings:", dict(hop))
for b in hbad[:8]: print("   hop exception", b)
