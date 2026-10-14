"""The owner's procedure, run end to end -- TRUE TRACK POSITIONS.

v1 displayed frac((v_j - v_i) t), which pins the subject at 0.  That is the
subject's rotating frame.  Gaps and cyclic order survive a rigid rotation, so the
isolation test was unaffected, but every position printed was wrong and the lap
counts were meaningless.  Here every runner's position is frac(v_j * t) and its
lap count is floor(v_j * t) -- nobody is pinned anywhere.

The isolation test itself still uses the differences, which is correct: loneliness
is a statement about pairwise distances on the track.
"""
from fractions import Fraction as F

def frac(x):
    r = x - int(x)
    return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

V = [10, 65, 101, 126, 159, 222, 256, 271]
N = 8

def moment(i):
    lo = V[i]-V[i-1] if i > 0 else None
    hi = V[i+1]-V[i] if i < N-1 else None
    m  = min(x for x in (lo, hi) if x is not None)
    ds = [F(abs(V[i]-V[j])) for j in range(N) if j != i]
    s  = sorted(d/F(m) for d in ds)
    B  = {F(1,8), F(7,8)}
    for x in s:
        for num in (0,1,4,7):
            k = 0
            while F(8*k+num,8)/x <= F(7,8):
                t = F(8*k+num,8)/x
                if F(1,8) <= t <= F(7,8): B.add(t)
                k += 1
    u = next(t for t in sorted(B) if all(nrm(x*t) >= F(1,8) for x in s))
    return m, u, u/F(m)

print('V = %s        (nobody is pinned; positions are frac(v_j * t) on the track)' % V)
for i in range(N):
    m, u, t = moment(i)
    P   = {j: frac(F(V[j])*t) for j in range(N)}
    lap = {j: int(F(V[j])*t)  for j in range(N)}
    order = sorted(range(N), key=lambda j: P[j])
    z = order.index(i)
    L, R = order[z-1], order[(z+1) % N]
    gl = P[i]-P[L] + (1 if P[L] > P[i] else 0)
    gr = P[R]-P[i] + (0 if P[R] > P[i] else 1)
    print()
    print('-'*86)
    print('r%d (speed %d):  d_min = %d,  u* = %s,  t* = %s' % (i+1, V[i], m, u, t))
    print('   track position of the subject: %s      laps completed: %d' % (P[i], lap[i]))
    print('   cycles of the slowest runner r1 at this instant: %s' % (t*V[0]))
    print('   the three that are pinned by the event:')
    print('      behind   r%d  at %-12s (lap %d)   gap %-10s %s'
          % (L+1, P[L], lap[L], gl, 'EXACTLY 1/8' if gl == F(1,8) else ''))
    print('      subject  r%d  at %-12s (lap %d)' % (i+1, P[i], lap[i]))
    print('      ahead    r%d  at %-12s (lap %d)   gap %-10s %s'
          % (R+1, P[R], lap[R], gr, 'EXACTLY 1/8' if gr == F(1,8) else ''))
    print('   the other five, on the track:')
    for j in order:
        if j in (i, L, R): continue
        print('      r%d  at %-14s (lap %d)   distance from subject %s'
              % (j+1, P[j], lap[j], nrm(F(V[j]-V[i])*t)))
    gaps = [P[order[(k+1) % N]] - P[order[k]] + (1 if k == N-1 else 0) for k in range(N)]
    print('   the eight gaps: %s   sum %s' % ([str(g) for g in gaps], sum(gaps)))
