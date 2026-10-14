"""one_shutter_v1 -- is the one-shutter row of the residual provable by a move off the spine?

Setting.  All four spine points shut; exactly ONE runner does the shutting, so by
C1_STATUS_v2 section 2 its reading has dist(s, 8Z) < 1/7.  The other six are clear at
every spine point, each with a margin.

The move.  Take u = p/8 + delta.  Writing s = 8k + f with |f| = dist(s,8Z) < 1/7,
we have ||s p/8|| = |f|p/8, so the shutter needs

    NEED(p)  =  the smallest |delta| with ||s(p/8 + delta)|| >= 1/8

and each clear runner j permits |delta| up to

    ROOM(j,p) =  (||s_j p/8|| - 1/8) / s_j          (linear until it turns at a kink)

The move fits at (p, direction) iff NEED <= min_j ROOM.  Pre-registered questions:

  Q1  does some (p, direction) fit, in every one-shutter instance?
      Falsifier: one instance where all eight attempts fail.
  Q2  is NEED <= 1/(8s) always -- i.e. is the shutter's requirement bounded by its own speed?
  Q3  how small does min_j ROOM get, and does it correlate with failure?
"""
from fractions import Fraction as F
import random
from collections import Counter

def nrm(x):
    f = x - int(x)
    if f < 0: f += 1
    return min(f, 1 - f)

def dist8(s): return abs(s - 8 * round(F(s, 8)))

def shutters(s):
    """the runners that shut all four spine points on their own"""
    return [x for x in s if all(nrm(x * F(p, 8)) < F(1, 8) for p in (1, 3, 5, 7))]

def exact_move(s, p):
    """smallest |delta| each way that brings EVERY reading to >= 1/8, by walking the
    exact breakpoints -- no linearisation, no midpoint."""
    base = F(p, 8); out = {}
    for sign in (1, -1):
        cand = {F(0)}
        for x in s:
            ph = (x * base) % 1
            for num in (1, 7):
                # solve  x*(base + sign*d) = m + num/8   for the least d >= 0
                for m in range(-1, int(x) + 2):
                    d = (F(m) + F(num, 8) - ph) / (x * sign)
                    if d >= 0: cand.add(d)
        ok = None
        for d in sorted(cand):
            if d > F(1, 2): break
            u = base + sign * d
            if F(1,8) <= u <= F(7,8) and all(nrm(x * u) >= F(1,8) for x in s):
                ok = d; break
        out[sign] = ok
    return out

random.seed(4242)
fit = Counter(); q2 = Counter(); N = 0; fails = []; needs = []
for span in (40, 200, 1200):
    for _ in range(500):
        V = sorted(random.sample(range(1, span + 1), 8))
        for i in range(8):
            ds = [F(abs(V[i] - V[j])) for j in range(8) if j != i]
            m = min(ds); s = sorted(d / m for d in ds)
            if any(all(nrm(x*F(p,8)) >= F(1,8) for x in s) for p in (1,3,5,7)): continue
            sh = shutters(s)
            if len(sh) != 1: continue
            N += 1
            best = None
            for p in (1, 3, 5, 7):
                for sg, d in exact_move(s, p).items():
                    if d is not None and (best is None or d < best[0]): best = (d, p, sg)
            if best is None: fails.append((V, i, [str(x) for x in s]))
            else:
                fit[(best[1], best[2])] += 1
                needs.append((best[0], sh[0]))
                q2['delta <= 1/(8s)' if best[0] <= F(1,8)/sh[0] else 'delta > 1/(8s)'] += 1

print('one-shutter instances: %d' % N)
print('Q1  instances where no (p, direction) fits: %d' % len(fails))
for f in fails[:3]: print('      %s r%d  %s' % (f[0], f[1]+1, f[2]))
print()
print('Q1  which (spine point, direction) the smallest successful move used:')
for k, v in sorted(fit.items()): print('      p=%d  %s   %5d  (%5.1f%%)' % (k[0], '+' if k[1]>0 else '-', v, 100*v/N))
print()
print('Q2  %s' % dict(q2))
if needs:
    r = sorted(d * sh for d, sh in needs)
    print('      s * delta  -- min %s   median %s   max %s' % (r[0], r[len(r)//2], r[-1]))
