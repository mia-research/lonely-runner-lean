"""Does the named instant always exist?

CLAIM UNDER TEST: for every arrangement and every runner i there is a t at which
i is lonely AND its two track-flanks are its two speed-neighbours (mod 8).

Falsifier: one runner with no such t in a full period.
Complete boundary set; exact rationals; closed comparisons; nobody pinned.
"""
from fractions import Fraction as F
import random
from collections import Counter

def frac(x):
    r = x - int(x); return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

def named_all(V):
    D = sorted({abs(V[a]-V[b]) for a in range(8) for b in range(a+1,8)})
    B = set()
    for d in D:
        for num in (0,1,4,7):
            k = 0
            while F(8*k+num, 8*d) <= 1:
                B.add(F(8*k+num, 8*d)); k += 1
    out = {}
    for t in sorted(x for x in B if 0 < x <= 1):
        if len(out) == 8: break
        P = [frac(F(v)*t) for v in V]
        o = sorted(range(8), key=lambda j: P[j])
        for z, i in enumerate(o):
            if i in out: continue
            if o[z-1] != (i-1) % 8 or o[(z+1) % 8] != (i+1) % 8: continue
            if all(nrm(F(V[i]-V[j])*t) >= F(1,8) for j in range(8) if j != i):
                out[i] = t
    return out

random.seed(13579)
miss = []; N = 0; ratios = []; cnt = Counter()
for span, reps in ((20, 120), (40, 120), (90, 90), (200, 60)):
    for _ in range(reps):
        V = sorted(random.sample(range(1, span+1), 8))
        out = named_all(V); N += 1
        cnt[len(out)] += 1
        if len(out) < 8:
            miss.append((V, sorted(set(range(8)) - set(out))))
        else:
            ts = list(out.values()); ratios.append(float(max(ts)/min(ts)))
print('arrangements tested: %d' % N)
print('runners named per arrangement:', dict(sorted(cnt.items())))
print('arrangements with a runner UNNAMED: %d' % len(miss))
for V, r in miss[:8]:
    print('   V=%-40s unnamed: %s' % (V, ['r%d' % (x+1) for x in r]))
if ratios:
    ratios.sort(); n = len(ratios)
    print()
    print('when all eight are named, latest/earliest time ratio:')
    print('   median %.1fx   90th %.1fx   max %.1fx' % (ratios[n//2], ratios[9*n//10], ratios[-1]))
