"""Check (1) the return lemma at n=4..8: if the setter of move i (lap P) is in the way at iterate i+1, where move i+1
was set by a runner at lap Q, then Q < (2P+1)/(n-2);  (2) at n=4, tau = a*t after moves 1,2,3 is below 5/12, 25/36, 3/4;
(3) at n=4, the nearest runner is never in the way at any iterate after the bound."""
from fractions import Fraction as F
import math, random
random.seed(7)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); t = th / ds[0]; its = [(t, 0, 0, frozenset())]
    while True:
        best = t; who = None; inway = set()
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                inway.add(i); k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        its[-1] = its[-1][:3] + (frozenset(inway),)
        if who is None: return its
        t = best; its.append((t, who[0], who[1], frozenset()))
tested = {n: 0 for n in range(4, 9)}; fails = {n: 0 for n in range(4, 9)}
bounds = [F(5, 12), F(25, 36), F(3, 4)]; bfail = 0; afail = 0; n4 = 0
for n in range(4, 9):
    trials = 60000 if n == 4 else 8000
    for _ in range(trials):
        if random.random() < 0.5:
            v = sorted(set(F(random.randint(1, 10**5), random.randint(1, 997)) for _ in range(n)))
        else:
            g = F(random.randint(1, 50), random.randint(1, 7))
            v = sorted(set(i * g + F(random.randint(-300, 300), 1000 * random.randint(1, 9)) for i in range(n)))
        if len(v) < n: continue
        for vi in v:
            ds = sorted(set(abs(w - vi) for w in v if w != vi))
            its = chain(ds, n)
            # its[0] = bound, setter index 0 (nearest) at lap 0
            for j in range(len(its) - 1):
                _, x, P, _ = its[j]; _, y, Q, inw = its[j + 1]
                if x in inw:
                    tested[n] += 1
                    if not (Q * (n - 2) < 2 * P + 1): fails[n] += 1
            if n == 4:
                n4 += 1
                for j in range(1, len(its)):
                    tau = ds[0] * its[j][0]
                    if j <= 3 and not tau < bounds[j - 1]: bfail += 1
                    if 0 in its[j][3]: afail += 1
                if len(its) - 1 > 3: bfail += 1
for n in range(4, 9):
    print(f'n={n}: returning setters tested {tested[n]}, violations of Q < (2P+1)/(n-2): {fails[n]}')
print(f'n=4: subjects {n4}, tau-bound or length violations {bfail}, nearest runner in the way at an iterate {afail}')
