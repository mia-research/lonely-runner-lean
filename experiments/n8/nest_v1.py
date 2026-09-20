"""Section 7d's lemma, applied once per reading instead of once.

Step 4 gives the window I_1 = [1/8, 7/8], where s_1 = 1 is clear.
Reading s is clear exactly on the closed intervals [(8j+1)/(8s), (8j+7)/(8s)],
which repeat with period 1/s and have length 3/(4s).  Section 7d's lemma: an
interval of length at least 1/s contains a whole period, so it meets that set.

So order the readings 1 = s_1 <= s_2 <= ... <= s_7 and nest:
    I_1 = [1/8, 7/8]                        length 3/4
    I_k = a clear interval of s_k inside I_{k-1}    length 3/(4 s_k)
Each step needs |I_{k-1}| >= 1/s_k, i.e.  s_k >= (4/3) s_{k-1}.
Any point of I_7 is a moment.  No density, no counting, exact rationals.
"""
from fractions import Fraction as F
import random
from collections import Counter

def frac(x):
    r = x - int(x); return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

def nest(s):
    """s sorted, s[0] == 1. Returns (interval, step that failed or None)."""
    lo, hi = F(1,8), F(7,8)
    for k in range(1, len(s)):
        x = s[k]; best = None
        j = 0
        while F(8*j+1, 8*x) <= hi:
            a, b = F(8*j+1, 8*x), F(8*j+7, 8*x)
            a2, b2 = max(a, lo), min(b, hi)
            if a >= lo and b <= hi:            # a WHOLE clear interval inside
                best = (a, b); break
            j += 1
        if best is None: return None, k
        lo, hi = best
    return (lo, hi), None

random.seed(20260913)
res = Counter(); failat = Counter(); N = 0; growth = Counter()
for span in (40, 200, 1000, 5000):
    for _ in range(400):
        V = sorted(random.sample(range(1, span+1), 8))
        for i in range(8):
            d = [F(abs(V[i]-V[j])) for j in range(8) if j != i]
            m = min(d); s = sorted(x/m for x in d); N += 1
            I, k = nest(s)
            if I is None:
                res['fails'] += 1; failat[k] += 1
            else:
                res['returns'] += 1
                u = I[0]
                assert all(nrm(x*u) >= F(1,8) for x in s)
            growth['all s_k >= (4/3) s_{k-1}' if all(s[k] >= F(4,3)*s[k-1]
                    for k in range(1, 7)) else 'growth condition fails'] += 1
print('the nest, over %d runner-instances:' % N)
for k, v in res.items(): print('   %-10s %6d  (%5.2f%%)' % (k, v, 100*v/N))
print()
print('   fails first at reading #: %s' % dict(sorted(failat.items())))
print()
for k, v in growth.items(): print('   %-32s %6d  (%5.2f%%)' % (k, v, 100*v/N))
