from fractions import Fraction as F
import random
def frac(x): return x - int(x) + (1 if x - int(x) < 0 else 0)
def nrm(x):
    f = frac(x); return min(f, 1-f)
def pat(s): return tuple(p for p in (1,3,5,7) if nrm(s*F(p,8)) < F(1,8))
def dist8(s): return abs(s - 8*round(F(s,8)))

def attempt(s, p, sign):
    """The move.  At u0 = p/8, each CLEAR reading permits a displacement (ROOM)
    before it drops below 1/8; each SHUT reading demands one (NEED).  The move
    fits iff max NEED <= min ROOM, with u staying inside [1/8,7/8]."""
    u0 = F(p,8); need = F(0); room = None; who_n = who_r = None
    for x in s:
        ph = frac(x*u0)
        if F(1,8) <= ph <= F(7,8):                       # clear: contributes ROOM
            r = ((F(7,8)-ph) if sign==1 else (ph-F(1,8)))/x
            if room is None or r < room: room, who_r = r, x
        else:                                            # shut: contributes NEED
            d = ((F(1,8)-ph) if ph < F(1,8) else (1-ph+F(1,8))) if sign==1 \
                else ((ph+F(1,8)) if ph < F(1,8) else (ph-F(7,8)))
            d = d/x
            if d > need: need, who_n = d, x
    # u must stay in the window
    lim = (F(7,8)-u0) if sign==1 else (u0-F(1,8))
    if room is None or lim < room: room, who_r = lim, 'window edge'
    return need, room, who_n, who_r

def readings(V, i):
    ds = [F(abs(V[i]-V[j])) for j in range(8) if j != i]
    m = min(ds); return sorted(d/m for d in ds)

def full_clear(s):
    """every u in [1/8,7/8] where all readings clear -- exact, ends of cells only"""
    B = {F(1,8), F(7,8)}
    for x in s:
        for num in (0,1,4,7):
            k = 0
            while F(8*k+num,8)/x <= F(7,8):
                t = F(8*k+num,8)/x
                if F(1,8) <= t <= F(7,8): B.add(t)
                k += 1
    return [t for t in sorted(B) if all(nrm(x*t) >= F(1,8) for x in s)]

def show(V, i, title):
    s = readings(V, i)
    print('='*78); print(title); print('='*78)
    print('speeds %s   subject r%d' % (V, i+1))
    print()
    print('  reading s_j        f = dist to 8Z      shuts')
    for x in s:
        print('   %-16s %-18s %s' % (x, dist8(x), list(pat(x)) if pat(x) else '-'))
    print('  every spine point is shut:',
          all(any(p in pat(x) for x in s) for p in (1,3,5,7)))
    print()
    print('  the move, all eight attempts:')
    print('   p  dir      NEED (max demanded)   ROOM (min permitted)   fits')
    ok = False
    for p in (1,3,5,7):
        for sg in (1,-1):
            n, r, wn, wr = attempt(s, p, sg)
            f = n <= r; ok = ok or f
            print('   %d  %s   %-21s %-22s %s' % (p, '+' if sg>0 else '-', n, r, 'YES' if f else 'no'))
    print()
    g = full_clear(s)
    print('  does the move fit anywhere: %s' % ('YES' if ok else 'NO'))
    print('  is the subject actually lonely somewhere in the window: %s' % ('YES' if g else 'NO'))
    if g: print('  first such instant: u = %s' % g[0])
    print()

# ---- case A: residual, one shutter, move fits
random.seed(3)
A = B = None
for _ in range(40000):
    V = sorted(random.sample(range(1,200),8)); i = random.randrange(8)
    s = readings(V,i)
    if any(all(nrm(x*F(p,8)) >= F(1,8) for x in s) for p in (1,3,5,7)): continue
    fits = any(attempt(s,p,sg)[0] <= attempt(s,p,sg)[1] for p in (1,3,5,7) for sg in (1,-1))
    sh = [x for x in s if len(pat(x))==4]
    if A is None and fits and len(sh)==1: A=(V,i)
    if B is None and not fits: B=(V,i)
    if A and B: break
if A: show(A[0],A[1],'CASE A -- the move fits.  One reading shuts the whole spine.')
if B: show(B[0],B[1],'CASE B -- the move fits NOWHERE, yet the runner IS lonely.')
else: print('no CASE B found in 40,000 draws')
