"""The cascade's failures, indexed by d_min.  Objects are SKETCH_v7 section 7c's:
candidate instants t = p/(8D) with p in {1,3,5,7}; the ceiling D <= 7 d_min(i);
Dead(i) the divisors of M(i) = { d/8 : 8 | d }; L_0 the first live lattice.

Question: section 7c says the failures need a small d_min, because the ceiling
7 d_min caps the range before you can step past the dead bottom.  How small?
"""
from fractions import Fraction as F
import random
from collections import Counter

def clears(ds, D):
    """t = p/(8D) clears runner i for some p in {1,3,5,7}:  D <= (d p mod 8D) <= 7D."""
    for p in (1,3,5,7):
        if all(D <= (d*p) % (8*D) <= 7*D for d in ds): return p
    return None

def cascade(ds):
    m = min(ds)
    for D in range(1, 7*m + 1):
        if clears(ds, D) is not None: return D
    return None

random.seed(1357)
bydmin = {}
tot = Counter(); fails = []
for span in (40, 120, 400, 1500, 6000):
    for _ in range(700):
        V = sorted(random.sample(range(1, span+1), 8))
        for i in range(8):
            ds = [abs(V[i]-V[j]) for j in range(8) if j != i]
            m = min(ds)
            D = cascade(ds)
            k = bydmin.setdefault(m, [0,0])
            k[0] += 1
            tot['all'] += 1
            if D is None:
                k[1] += 1; tot['fail'] += 1
                if len(fails) < 6: fails.append((V, i, sorted(ds)))

print('cascade over %d runner-instances; nothing clears in %d (%.3f%%)'
      % (tot['all'], tot['fail'], 100*tot['fail']/tot['all']))
print()
print('  d_min   instances   nothing clears')
for m in sorted(bydmin)[:14]:
    n, f = bydmin[m]
    print('   %-6d %8d    %5d  (%6.2f%%)' % (m, n, f, 100*f/n))
big = [(m,v) for m,v in bydmin.items() if m > 13]
bn = sum(v[0] for m,v in big); bf = sum(v[1] for m,v in big)
print('   >13   %8d    %5d  (%6.2f%%)' % (bn, bf, 100*bf/bn if bn else 0))
print()
print('  every failure seen, with its d_min:')
for V,i,ds in fails:
    print('     V=%-42s r%d  d_min=%d  differences %s' % (V, i+1, min(ds), ds))
