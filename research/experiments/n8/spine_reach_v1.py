"""spine_reach_v1 -- what the spine u = p/8 settles, and what is left.

Pre-registered quantities (fixed before the run; nothing else is reported):

  Q1  share of runner-instances for which SOME p in {1,3,5,7} gives
      ||s_j p/8|| >= 1/8 for all seven, split by reading integrality and by span.
  Q2  of the instances where all four are shut, the share with d_max > 7 d_min.
      Falsifier: a single instance with d_max <= 7 d_min and all four shut.
  Q3  of those, how many distinct runners are needed to shut all four, and
      whether the one-runner case is exactly  dist(s, 8Z) < 1/7.
      Falsifier: any one-runner instance with dist(s,8Z) >= 1/7, or any s with
      dist(s,8Z) < 1/7 that fails to shut all four.
  Q4  the lap k of the nearest runner in which the subject first comes clear.
      C1 as stated demands k = 0; LRC demands only some k.  Falsifier: k > 0.

Exact rationals throughout.  Candidate instants are the ends of the cells, never
a cell interior: inside a cell every ||s t|| - 1/8 is affine with no zero, so the
minimum over j is concave and its sign at the two ends settles the cell.
"""
from fractions import Fraction as F
import random
from collections import Counter

def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)

def dist8(s):
    """distance from s to the nearest multiple of 8, exactly."""
    k = round(F(s, 8))
    return abs(s - 8 * k)

def live_spine(s):
    return [p for p in (1, 3, 5, 7) if all(nrm(x * F(p, 8)) >= F(1, 8) for x in s)]

def clear_in(ds, lo, hi):
    B = {lo, hi}
    for d in ds:
        for num in (0, 1, 4, 7):
            k = int(lo * d) - 1
            while F(8 * k + num, 8) / d <= hi:
                t = F(8 * k + num, 8) / d
                if lo <= t <= hi: B.add(t)
                k += 1
    return any(all(nrm(d * t) >= F(1, 8) for d in ds) for t in sorted(B))

random.seed(20260915)
SPANS = (20, 40, 120, 600, 3000)
q1 = Counter(); nblk = Counter(); ratio = Counter(); one = Counter(); lap = Counter()
q3fail = []; q2fail = []
for span in SPANS:
    for _ in range(300):
        V = sorted(random.sample(range(1, span + 1), 8))
        for i in range(8):
            ds = [F(abs(V[i] - V[j])) for j in range(8) if j != i]
            m = min(ds); s = sorted(d / m for d in ds)
            integral = all(x.denominator == 1 for x in s)
            tag = 'integral' if integral else 'mixed'
            L = live_spine(s)
            q1[(span, tag, bool(L))] += 1
            q1[('ALL', tag, bool(L))] += 1
            if not L:
                if s[-1] <= 7: q2fail.append((V, i))
                ratio['d_max > 7 d_min' if s[-1] > 7 else 'd_max <= 7 d_min'] += 1
                shut = {x for x in s if any(nrm(x * F(p, 8)) < F(1, 8) for p in (1, 3, 5, 7))
                        and len(live_spine([x])) == 0}
                need = set()
                for p in (1, 3, 5, 7):
                    for x in s:
                        if nrm(x * F(p, 8)) < F(1, 8): need.add(x); break
                nblk[len(need)] += 1
                if len(need) == 1:
                    x = next(iter(need))
                    one['dist < 1/7' if dist8(x) < F(1, 7) else 'dist >= 1/7'] += 1
                    if dist8(x) >= F(1, 7): q3fail.append((V, i, str(x)))
            for k in range(0, 40):
                if clear_in(s, k + F(1, 8), k + F(7, 8)): lap[k] += 1; break
            else: lap['>40'] += 1

def pct(a, b): return 100.0 * a / b if b else 0.0
print('Q1  spine u = p/8 clears the subject')
for span in SPANS + ('ALL',):
    for tag in ('integral', 'mixed'):
        y = q1[(span, tag, True)]; n = q1[(span, tag, False)]
        if y + n: print('    span %-5s %-9s %5d/%-5d = %5.1f%%' % (span, tag, y, y + n, pct(y, y + n)))
    y = q1[(span,'integral',True)] + q1[(span,'mixed',True)]
    t = y + q1[(span,'integral',False)] + q1[(span,'mixed',False)]
    print('    span %-5s %-9s %5d/%-5d = %5.1f%%' % (span, 'BOTH', y, t, pct(y, t)))
R = sum(ratio.values())
print('\nQ2  of the %d instances with all four shut:' % R)
for k, v in ratio.items(): print('    %-18s %5d  (%5.1f%%)' % (k, v, pct(v, R)))
print('    falsifier instances: %d' % len(q2fail))
print('\nQ3  distinct runners needed to shut all four:')
for k in sorted(nblk): print('    %d  %5d  (%5.1f%%)' % (k, nblk[k], pct(nblk[k], R)))
print('    one-runner case vs dist(s,8Z) < 1/7: %s   falsifiers: %d' % (dict(one), len(q3fail)))
N = sum(lap.values())
print('\nQ4  lap of the nearest runner at first clearance (%d instances):' % N)
for k in sorted(lap, key=str): print('    lap %-4s %5d  (%6.2f%%)' % (k, lap[k], pct(lap[k], N)))
