"""WHY_IT_PREDICTS_v1 section 4: how far past the FIRST LIVE LATTICE can the witness
be forced?  Observed <= 3 over 12,000 instances, 88% at zero.  Nobody has pushed it.

Objects are the file's own.  s_1 = 1, readings s_2..s_7 >= 1.
Lattice L: candidates u = p/(8L), p = L..7L, so u in [1/8, 7/8].
L is DEAD  <=>  some s_j = 0 mod 8L                       (section 2, proved)
L_0 = first live lattice;  L_w = first lattice carrying a witness;  gap = L_w - L_0.

Pointwise throughout: a witness is a named u, never a measure.  Exact rationals.
"""
from fractions import Fraction as F
import random
from collections import Counter

def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1-f)

def dead(s, L):
    return any(x.denominator == 1 and x.numerator % (8*L) == 0 for x in s)

def witness_on(s, L):
    for p in range(L, 7*L+1):
        u = F(p, 8*L)
        if all(nrm(x*u) >= F(1,8) for x in s): return u
    return None

def analyse(s, Lmax=400):
    L0 = None; Lw = None
    for L in range(1, Lmax+1):
        if L0 is None and not dead(s, L): L0 = L
        if witness_on(s, L) is not None: Lw = L; break
    if L0 is None or Lw is None: return None
    return L0, Lw, Lw - L0

# ---- adversarial: readings engineered to kill the low lattices
random.seed(20260913)
best = (-1, None); dist = Counter(); N = 0
def trial(s):
    global best, N
    s = sorted(set(s))
    if len(s) != 7 or s[0] != 1: return
    r = analyse(s)
    if r is None: return
    L0, Lw, g = r; dist[g] += 1; N += 1
    if g > best[0]: best = (g, (s, L0, Lw))

# family A: one reading a high multiple of 8 (kills a divisor-closed block)
for _ in range(4000):
    k = random.choice([8,16,24,32,40,48,56,64,72,80,96,120,144,168,192,240])
    s = [F(1)] + [F(k)] + [F(random.randint(2, 300)) for _ in range(5)]
    trial(s)
# family B: several multiples of 8, to widen the dead set
for _ in range(4000):
    ks = random.sample([8,16,24,32,40,48,56,64,72,80,88,96,104,112,120,144,168,192,216,240], 3)
    s = [F(1)] + [F(k) for k in ks] + [F(random.randint(2,300)) for _ in range(3)]
    trial(s)
# family C: highly composite multiples of 8 -- Dead is divisor-closed
for _ in range(4000):
    ks = random.sample([8*x for x in (1,2,3,4,6,8,12,16,24,30,36,48,60,72,90,120,180,210,360)], 3)
    s = [F(1)] + [F(k) for k in ks] + [F(random.randint(2,400)) for _ in range(3)]
    trial(s)
# family D: real arrangements, for a control
for _ in range(4000):
    V = sorted(random.sample(range(1, 600), 8)); i = random.randrange(8)
    d = [F(abs(V[i]-V[j])) for j in range(8) if j != i]
    m = min(d); trial([x/m for x in d])

print('instances analysed: %d' % N)
print('gap = (witness lattice) - (first live lattice):')
for g in sorted(dist): print('   gap %-3d %7d  (%6.3f%%)' % (g, dist[g], 100*dist[g]/N))
print()
g, (s, L0, Lw) = best
print('LARGEST GAP FOUND: %d' % g)
print('   readings   %s' % [str(x) for x in s])
print('   first live lattice L_0 = %d ; witness first appears at L = %d' % (L0, Lw))
