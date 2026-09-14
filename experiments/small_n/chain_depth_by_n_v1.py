"""Moment-iteration chain length at threshold 1/n, n-1 differences, exact rationals.
move: from t, every runner in the way (circ dist < 1/n) sends t to its next opening (k+1/n)/d; take the max.
Start at the bound 1/(n*dmin). Count moves until fixed. Random + near-AP (adversarial) speed sets."""
from fractions import Fraction as F
import random, math
random.seed(1)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); t = F(1, n) / min(ds); moves = 0; setters = []
    while True:
        best = t; who = None
        for d in ds:
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, d
        if best == t: return moves, t, setters
        t = best; moves += 1; setters.append(who)
        if moves > 10000: return None, t, setters
def run(n, trials):
    worst = (0, None); hist = {}
    for _ in range(trials):
        kind = random.random()
        if kind < 0.5:
            v = sorted(set(F(random.randint(1, 4000), random.randint(1, 60)) for _ in range(n)))
        else:  # near-AP: base + i*gap + small deviation
            g = F(random.randint(1, 50), random.randint(1, 7))
            v = sorted(set(i * g + F(random.randint(-200, 200), 1000 * random.randint(1, 9)) for i in range(n)))
        if len(v) < n: continue
        for i, vi in enumerate(v):
            ds = sorted(set(abs(w - vi) for w in v if w != vi))
            m, t, s = chain(ds, n)
            hist[m] = hist.get(m, 0) + 1
            if m is None or m > worst[0]: worst = (m, (v, vi, [str(x) for x in s]))
    return hist, worst
for n in (3, 4, 5, 6, 7, 8):
    hist, worst = run(n, 20000 if n < 6 else 6000)
    tot = sum(hist.values())
    print(f"n={n} subjects={tot} max_moves={worst[0]} hist={dict(sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0])))}")
