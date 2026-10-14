"""CANDIDATE: for every 8-speed arrangement and every runner there is a rational
   u = p/q  with  q <= Q  and  u in [1/8, 7/8],  clearing the subject.

The spine is the case q = 8.  This is that object with the denominator freed.
Falsifier: one runner-instance needing q > Q, or needing no q at all.
Reported: the distribution of the least working q, and the worst case seen.
"""
from fractions import Fraction as F
import random
from math import gcd
from collections import Counter

def frac(x):
    r = x - int(x); return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

CAND = [(q, p) for q in range(2, 60) for p in range(1, q)
        if gcd(p, q) == 1 and F(1,8) <= F(p,q) <= F(7,8)]
CAND.sort()

def least_q(s):
    for q, p in CAND:
        u = F(p, q)
        if all(nrm(x*u) >= F(1,8) for x in s): return q, p
    return None, None

def readings(V, i):
    ds = [F(abs(V[i]-V[j])) for j in range(len(V)) if j != i]
    m = min(ds); return sorted(d/m for d in ds)

def sweep(gen, tag):
    c = Counter(); worst = (0, None); miss = []
    n = 0
    for V in gen:
        for i in range(8):
            s = readings(V, i); n += 1
            q, p = least_q(s)
            if q is None: miss.append((V, i)); c['NONE'] += 1; continue
            c[q] += 1
            if q > worst[0]: worst = (q, (V, i, p))
    print('%-34s %6d instances   max q = %-3d   none: %d'
          % (tag, n, worst[0], len(miss)))
    if worst[1]:
        V, i, p = worst[1]
        print('      hardest: V=%s  r%d  cleared at %d/%d' % (V, i+1, p, worst[0]))
    return c

random.seed(97531)
tot = Counter()
tot += sweep([sorted(random.sample(range(1,41),8)) for _ in range(400)], 'random, span 40')
tot += sweep([sorted(random.sample(range(1,301),8)) for _ in range(400)], 'random, span 300')
tot += sweep([sorted(random.sample(range(1,5001),8)) for _ in range(400)], 'random, span 5000')
tot += sweep([[a+k*d for k in range(8)] for a in range(1,13) for d in range(1,13)], 'arithmetic progressions')
tot += sweep([sorted(random.sample(range(b,b+16),8)) for b in random.sample(range(1,400),300)], 'clustered')
L = [2520,1260,840,720,630,504,420,360,280,252,240,210,180,168,144,120,105,90,84,72,60,56,48,40,36,30,24,20,16,12,10,8,6,4,2,1]
tot += sweep([sorted(random.sample(L,8)) for _ in range(400)], 'highly composite speeds')
tot += sweep([sorted(random.sample([2**k for k in range(1,14)]+[3*2**k for k in range(1,10)],8)) for _ in range(300)], 'powers of two')
print()
print('ALL SWEEPS -- least working denominator q:')
run = 0; N = sum(v for k,v in tot.items() if k != 'NONE')
for k in sorted(tot, key=lambda z: (isinstance(z,str), z)):
    run += tot[k]
    print('   q = %-6s %6d   cumulative %6.2f%%' % (k, tot[k], 100*run/N))
