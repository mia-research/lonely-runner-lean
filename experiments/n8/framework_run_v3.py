"""The owner's procedure -- the AP-LIKE isolation, not the first one.

v1 pinned the subject at 0 (wrong frame).  v2 fixed the frame but still solved for
the FIRST moment, which is not what the framework delivers.  The framework delivers
an isolation with the AP's structure: the subject and its two flanking runners in a
known relative configuration, and the other five guaranteed outside that space --
with their individual positions NOT determined.  That is the spine instant u = p/8.

Nobody is pinned: positions are frac(v_j * t), laps are floor(v_j * t).
"""
from fractions import Fraction as F

def frac(x):
    r = x - int(x)
    return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

def dmin(V, i):
    N = len(V)
    lo = V[i]-V[i-1] if i > 0 else None
    hi = V[i+1]-V[i] if i < N-1 else None
    return min(x for x in (lo, hi) if x is not None)

def ap_like(V, i):
    """the first spine instant that clears the subject"""
    N = len(V); m = dmin(V, i)
    s = [F(abs(V[i]-V[j]))/F(m) for j in range(N) if j != i]
    for p in (1,3,5,7):
        u = F(p,8)
        if all(nrm(x*u) >= F(1,8) for x in s): return m, p, u, u/F(m)
    return m, None, None, None

def show(V, tag):
    N = len(V)
    print('='*92); print(tag); print('V = %s' % V); print('='*92)
    print(' subj  d_min  p   u*    t*         behind          subject        ahead           five')
    print(' '+'-'*89)
    for i in range(N):
        m, p, u, t = ap_like(V, i)
        if p is None:
            print(' r%-4d %-6d  --  no spine instant clears this runner' % (i+1, m)); continue
        P = {j: frac(F(V[j])*t) for j in range(N)}
        lap = {j: int(F(V[j])*t) for j in range(N)}
        o = sorted(range(N), key=lambda j: P[j]); z = o.index(i)
        L, R = o[z-1], o[(z+1) % N]
        gl = P[i]-P[L] + (1 if P[L] > P[i] else 0)
        gr = P[R]-P[i] + (0 if P[R] > P[i] else 1)
        five = [j for j in range(N) if j not in (i, L, R)]
        out = all(nrm(F(V[j]-V[i])*t) >= F(1,8) for j in five)
        print(' r%-4d %-6d %-3d %-5s %-10s r%d gap %-8s r%d lap %-2d   r%d gap %-8s %s'
              % (i+1, m, p, u, t, L+1, gl, i+1, lap[i], R+1, gr,
                 'all outside' if out else 'FAIL'))
    print()

show([10, 65, 101, 126, 159, 222, 256, 271], "SKETCH_v6 section 7b's own example")
show([1,2,3,4,5,6,7,8], "the AP itself, for comparison")
