"""The owner's procedure, run end to end on one arrangement.
Steps are NEIGHBOUR_INTERVAL_v1 section 1:
  1. from its two speed-neighbours, d_min
  2. that fixes the window [1/(8 d_min), 7/(8 d_min)] in time, [1/8,7/8] in location
  3. verify the other six inside it; the first point where all clear is the moment
Then, at that moment: the three runners whose location is pinned, and the five elsewhere.
"""
from fractions import Fraction as F

def frac(x):
    r = x - int(x)
    return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

V = [10, 65, 101, 126, 159, 222, 256, 271]        # SKETCH_v6 section 7b's own example
N = len(V)

def run(i):
    print('-'*78)
    print('SUBJECT r%d, speed %d' % (i+1, V[i]))
    # step 1
    lo = V[i]-V[i-1] if i > 0 else None
    hi = V[i+1]-V[i] if i < N-1 else None
    cand = [x for x in (lo, hi) if x is not None]
    dmin = min(cand)
    print('  1. speed-neighbours: %s   gaps in speed %s   ->  d_min = %d'
          % ([V[i-1] if i>0 else None, V[i+1] if i<N-1 else None], cand, dmin))
    # step 2
    print('  2. window:  location u in [1/8, 7/8]   time t in [%s, %s]'
          % (F(1,8*dmin), F(7,8*dmin)))
    # step 3
    ds = [F(abs(V[i]-V[j])) for j in range(N) if j != i]
    s  = sorted(d/F(dmin) for d in ds)
    print('  3. the other six, as readings s = d/d_min: %s' % [str(x) for x in s])
    B = {F(1,8), F(7,8)}
    for x in s:
        for num in (0,1,4,7):
            k = 0
            while F(8*k+num,8)/x <= F(7,8):
                t = F(8*k+num,8)/x
                if F(1,8) <= t <= F(7,8): B.add(t)
                k += 1
    u = next((t for t in sorted(B) if all(nrm(x*t) >= F(1,8) for x in s)), None)
    if u is None:
        print('     no moment in the first window'); return
    t = u/F(dmin)
    p = '  (a spine instant, p=%s)' % (u*8) if (u*8).denominator == 1 else ''
    print('     first moment:  u* = %s%s      t* = %s' % (u, p, t))
    # the isolation event
    print()
    pos = {j: frac(F(V[j]-V[i])*t) for j in range(N)}
    order = sorted(range(N), key=lambda j: pos[j])
    z = order.index(i)
    left, right = order[z-1], order[(z+1) % N]
    gl = pos[i]-pos[left] if pos[i] > pos[left] else pos[i]-pos[left]+1
    gr = pos[right]-pos[i] if pos[right] > pos[i] else pos[right]-pos[i]+1
    print('  AT THAT MOMENT -- positions on the track, subject placed at 0:')
    print('     THE THREE THAT ARE PINNED')
    print('       subject   r%d  at 0' % (i+1))
    print('       behind    r%d  at %-12s  gap to subject %-10s %s'
          % (left+1, pos[left], gl, 'ON the 1/8 threshold' if gl == F(1,8) else ''))
    print('       ahead     r%d  at %-12s  gap to subject %-10s %s'
          % (right+1, pos[right], gr, 'ON the 1/8 threshold' if gr == F(1,8) else ''))
    print('     THE OTHER FIVE -- all outside the isolation space (1-1/8, 1/8):')
    for j in order:
        if j in (i, left, right): continue
        print('       r%d  at %-14s  distance from subject %-10s  clear: %s'
              % (j+1, pos[j], nrm(F(V[j]-V[i])*t), nrm(F(V[j]-V[i])*t) >= F(1,8)))
    print('     isolation space is (-1/8, 1/8) about the subject; every one of the')
    print('     seven is at distance >= 1/8:', all(nrm(F(V[j]-V[i])*t) >= F(1,8)
                                                   for j in range(N) if j != i))

print('ARRANGEMENT  V =', V)
for i in range(N): run(i)
