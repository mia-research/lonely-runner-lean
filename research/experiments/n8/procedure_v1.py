"""Steps 3-5 of PROOF_CANDIDATE_v3, run for each of the eight runners.

Step 3  m = min(v_i - v_{i-1}, v_{i+1} - v_i), from the two speed-neighbours.
Step 4  u = m t ; the window is u in [1/8, 7/8] ; s_j = d_j/m >= 1.
Step 5  at u, runner j has floor(s_j u) laps and phase s_j u mod 1 ; clear iff that
        phase is in [1/8, 7/8].

Boundary Set Method: the candidate set is the window ends plus every u at which some
s_j u sits on 1/8 or 7/8 (mod 1).  BOUNDARY POINTS AND OPEN CELLS ARE EVALUATED
SEPARATELY, and touching closed zones are never merged -- the AP's own reading is
four isolated points and any merge loses them.  Exact rationals, closed >=.
Nobody is pinned anywhere.
"""
from fractions import Fraction as F

def frac(x):
    r = x - int(x); return r + 1 if r < 0 else r
def nrm(x):
    f = frac(x); return min(f, 1-f)

def procedure(V, i):
    N = len(V)
    below = V[i]-V[i-1] if i > 0 else None
    above = V[i+1]-V[i] if i < N-1 else None
    m = min(x for x in (below, above) if x is not None)          # Step 3
    d = [F(abs(V[i]-V[j])) for j in range(N) if j != i]
    s = sorted(x/F(m) for x in d)                                # Step 4
    B = {F(1,8), F(7,8)}
    for x in s:
        for num in (1, 7):
            k = 0
            while F(8*k+num, 8)/x <= F(7,8):
                u = F(8*k+num, 8)/x
                if F(1,8) <= u <= F(7,8): B.add(u)
                k += 1
    B = sorted(B)
    ok = [all(nrm(x*u) >= F(1,8) for x in s) for u in B]         # Step 5, closed >=
    # boundary points first, in order; then open cells, evaluated separately
    for k, u in enumerate(B):
        if ok[k]: return m, s, u, 'boundary point'
    for k in range(len(B)-1):
        a, b = B[k], B[k+1]
        if ok[k] and ok[k+1]:                                    # affine, no interior zero
            return m, s, (a+b)/2, 'open cell (%s, %s)' % (a, b)
    return m, s, None, None

V = [3, 17, 23, 41, 58, 79, 96, 131]
print('V = %s' % V)
print('(not an AP: successive gaps %s)' % [V[k+1]-V[k] for k in range(7)])
print()
print(' runner  speed  m = d_min   window t in            u*            t*            check')
print(' ' + '-'*90)
res = []
for i in range(8):
    m, s, u, how = procedure(V, i)
    if u is None:
        print(' r%-6d %-6d %-11d %-22s NO RETURN' % (i+1, V[i], m, '')); continue
    t = u/F(m)
    good = all(nrm(F(abs(V[i]-V[j]))*t) >= F(1,8) for j in range(8) if j != i)
    print(' r%-6d %-6d %-11d %-22s %-13s %-13s %s'
          % (i+1, V[i], m, '[%s, %s]' % (F(1,8*m), F(7,8*m)), u, t, 'lonely' if good else 'FAIL'))
    res.append((i, m, s, u, t))
print()
for i, m, s, u, t in res:
    print(' r%d: readings s_j = %s' % (i+1, [str(x) for x in s]))
    print('     at u* = %s the six phases are %s' % (u, [str(frac(x*u)) for x in s]))
    print('     laps completed relative to r%d: %s' % (i+1, [int(x*u) for x in s]))
