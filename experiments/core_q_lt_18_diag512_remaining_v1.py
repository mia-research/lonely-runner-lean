"""For the remaining BHK 5.2.12 diagonal cases, find (a) the longest 0123-gap
(runners 0,1,2,3 away) -> s upper bound, and (b) whether every surviving s in
(r, s_upper] has an explicit lonely witness.  If yes, the case closes with just
the interval upper bound + free lower bound s>r (no Claim-20 lower bound)."""
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def cdist(x):
    f=frac(x); return min(f,1-f)

def longest_0123_gap(p,q):
    """Return (t_a, t_b, length) longest interval in BHK-time t where runners
    0,1,2,3 (speeds p,q-p,q,q+p, positions frac(n*t/q)) are all away (cd>=1/6).
    Exact via event points: runner n is away on t where frac(n t/q) in [1/6,5/6];
    boundaries at n t/q = k+1/6 or k+5/6 => t = q(k+1/6)/n etc."""
    ns=[p,q-p,q,p+q]
    # collect all boundary t in [0,q)
    pts=set([F(0),F(q)])
    for n in ns:
        # t = q*(k + c)/n for c in {1/6,5/6}, k integer, t in [0,q)
        kmax = n + 2
        for k in range(-1, kmax+1):
            for c in (F(1,6),F(5,6)):
                t = F(q)*(k+c)/n
                if F(0) <= t <= F(q):
                    pts.add(t)
    pts=sorted(pts)
    best=(None,None,F(0))
    for i in range(len(pts)-1):
        ta,tb=pts[i],pts[i+1]
        mid=(ta+tb)/2
        if all(cdist(n*mid/q)>=F(1,6) for n in ns):
            if tb-ta>best[2]:
                best=(ta,tb,tb-ta)
    return best

def find_witness(ns, max_den=80):
    for d in range(2,max_den+1):
        for a in range(1,d):
            th=F(a,d)
            if all(cdist(n*th)>=F(1,6) for n in ns):
                return th
    return None

for p,q in [(1,6),(2,7),(2,9),(1,10)]:
    r=p+q
    ta,tb,L=longest_0123_gap(p,q)
    sbound = F(q)/(3*L) if L>0 else None
    smax = int(sbound) if sbound else None
    print(f"\n=== ({p},{q},{r}) ===  longest 0123-gap t in [{ta},{tb}] L={L}={float(L):.4f}")
    print(f"   s <= q/(3L) = {sbound}={float(sbound):.3f} -> s_max={smax}; surviving s in ({r},{smax}]")
    allwit=True
    for s in range(r+1, smax+1):
        nsf=[p,q-p,q,r,s]
        w=find_witness(nsf)
        if w:
            fr=[frac(n*w) for n in nsf]
            print(f"   s={s}: witness tau={w} fracs={[f'{float(x):.3f}' for x in fr]}")
        else:
            allwit=False
            print(f"   s={s}: NO witness  <-- needs lower bound / different arg")
    print(f"   ALL surviving s have witnesses: {allwit}")
