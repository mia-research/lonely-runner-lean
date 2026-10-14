"""spine_patterns_v1 -- the spine's shut-structure, exactly.

L1.  Reading s shuts the spine point u = p/8  iff  ||s p/8|| < 1/8  iff  dist(sp, 8Z) < 1.
     Writing s = 8k + f with f the SIGNED distance from s to the nearest multiple of 8
     (|f| <= 4), dist(sp, 8Z) = dist(fp, 8Z).  So the shut-set depends on f alone.

L2.  Hence a reading's shut-set is a function of one number in [-4,4], and both the list
     of achievable shut-sets and the list of minimal ways to shut all four spine points
     are finite and computable.

Self-tests, because an earlier hand run of this got both wrong:
  T1  each shut-region must be symmetric under f -> -f (dist is even in f).
      The first attempt enumerated m from -1 up and silently dropped the negative
      branches for p = 5 and p = 7; the asymmetry is what exposed it.
  T2  each shut-region must have total length exactly 2 out of 8 (density 1/4):
      over one period 8/p of fp, the shut window has width 2/p, and there are p
      periods in [-4,4].
  T3  minimal collections must be enumerated at every size up to 4, not stopped at
      the first size that yields any.  Four singletons [1]+[3]+[5]+[7] is minimal and
      an early break misses it.
"""
from fractions import Fraction as F
import itertools, random
from collections import defaultdict, Counter

P4 = (1, 3, 5, 7)

def regions(p):
    """{ f in [-4,4] : dist(fp, 8Z) < 1 }, as disjoint open intervals."""
    iv = []
    for m in range(-(p + 2), p + 3):                      # T1: both directions
        a, b = max(F(8*m - 1, p), F(-4)), min(F(8*m + 1, p), F(4))
        if b > a: iv.append((a, b))
    return sorted(iv)

R = {p: regions(p) for p in P4}

# ---- T1, T2 -----------------------------------------------------------------
for p in P4:
    assert sorted((-b, -a) for a, b in R[p]) == R[p], ('T1 asymmetric', p)
    assert sum(b - a for a, b in R[p]) == 2, ('T2 wrong total', p)

# ---- the achievable shut-sets ------------------------------------------------
pts = sorted({x for p in P4 for a, b in R[p] for x in (a, b)} | {F(-4), F(4)})
span = defaultdict(F); where = defaultdict(list)
for a, b in zip(pts, pts[1:]):
    mid = (a + b) / 2
    pat = frozenset(p for p in P4 if any(lo < mid < hi for lo, hi in R[p]))
    span[pat] += b - a; where[pat].append((a, b))

print('=== L1  shut-region of each spine point, in f = signed dist(s, 8Z) ===')
for p in P4:
    print('  p=%d  %s' % (p, '  U  '.join('(%s,%s)' % (a, b) for a, b in R[p])))
    print('        total %s of 8   density %s' % (sum(b-a for a,b in R[p]), F(1,4)))

print()
print('=== L2a  achievable shut-sets, by total f-length out of 8 ===')
for pat, L in sorted(span.items(), key=lambda z: (-z[1], sorted(z[0]))):
    print('  %-16s length %-9s density %-8s' % (sorted(pat) if pat else '(none)', L, L/8))
assert sum(span.values()) == 8
print('  --- %d achievable shut-sets (%d non-empty); total length %s, as it must be'
      % (len(span), len([p for p in span if p]), sum(span.values())))
never = [frozenset(c) for k in range(1,5) for c in itertools.combinations(P4,k)
         if frozenset(c) not in span]
print('  subsets of {1,3,5,7} that NEVER occur: %s' % sorted(sorted(x) for x in never))

# ---- the minimal collections -------------------------------------------------
pats = [p for p in span if p]; full = frozenset(P4); mins = []
for k in (1, 2, 3, 4):                                     # T3: every size
    for c in itertools.combinations_with_replacement(pats, k):
        if frozenset().union(*c) != full: continue
        if any(frozenset().union(*d) == full
               for j in range(1, k) for d in itertools.combinations(c, j)): continue
        mins.append(c)
print()
print('=== L2b  minimal ways to shut all four spine points ===')
for k in (1, 2, 3, 4):
    g = [c for c in mins if len(c) == k]
    print('  size %d : %d' % (k, len(g)))
    for c in g: print('        %s' % ' + '.join(str(sorted(x)) for x in c))
print('  --- %d minimal collections; maximum size %d' % (len(mins), max(len(c) for c in mins)))

# ---- census on real readings -------------------------------------------------
def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)
def pat_of(s): return frozenset(p for p in P4 if nrm(s * F(p, 8)) < F(1, 8))

random.seed(8888)
occ = Counter(); need = Counter(); N = R_ = 0; unseen_ok = True
for sp in (40, 200, 1200, 6000):
    for _ in range(400):
        V = sorted(random.sample(range(1, sp + 1), 8))
        for i in range(8):
            ds = [F(abs(V[i] - V[j])) for j in range(8) if j != i]
            m = min(ds); s = sorted(d / m for d in ds); N += 1
            Ps = [pat_of(x) for x in s if pat_of(x)]
            if not Ps or frozenset().union(*Ps) != full: continue
            R_ += 1
            for k in (1, 2, 3, 4):
                hit = [c for c in itertools.combinations(Ps, k) if frozenset().union(*c) == full]
                if hit:
                    need[k] += 1
                    occ[tuple(sorted(tuple(sorted(x)) for x in hit[0]))] += 1
                    break
print()
print('=== census on %d runner-instances, four spans ===' % N)
print('  residual (all four shut): %d = %.1f%%' % (R_, 100*R_/N))
print('  MINIMUM readings needed: ' + '  '.join('%d:%d(%.1f%%)' % (k, need[k], 100*need[k]/R_)
                                                for k in sorted(need)))
print('  cases observed:')
for c, v in occ.most_common(20):
    print('     %-32s %5d  (%5.1f%%)' % (' + '.join(str(list(x)) for x in c), v, 100*v/R_))
print('  all %d minimal cases observed: %s' % (len(mins), len(occ) == len(mins)))
