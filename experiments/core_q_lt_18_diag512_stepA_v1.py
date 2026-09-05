"""Step A (s upper bound) de-risk for BHK 5.2.12 diagonal cases (1,7,8) & (1,12,13).

We work in BHK-time t (runner 3 = our index 2 has v=1). Our-time tau = t/(g*q),
but fract positions only depend on n_i and t/q since {w_i tau}={n_i t/q}.
Runner i position at BHK-time t: frac(n_i * t / q), n=(p,q-p,q,q+p,s).
A 0123-gap over [t_a,t_b]: runners 0,1,2,3 all have circDist>=1/6 throughout.
Then runner 4 must cover => Icc subset unsafeOf w4 => (t_b-t_a)/q <= 1/(3 s)
=> s <= q/(3*(t_b-t_a)).   (lengths in BHK-time; /q converts to tau, the 1/(3 w4)
 with w4=g*s and tau-length=(tb-ta)/(g q) gives s <= q/(3 (tb-ta)).)
"""
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def cdist(x):
    f=frac(x); return min(f,1-f)

def runner_band(ni, q, ta, tb, samples=2000):
    """min/max of frac(ni*t/q) over [ta,tb]; also whether it wraps an integer."""
    vals=[]
    for k in range(samples+1):
        t = ta + (tb-ta)*F(k,samples)
        vals.append(frac(ni*t/q))
    # detect wrap: if both near 0 and near 1 appear -> crosses integer
    return min(vals), max(vals)

def analyze(p,q,s_label, ta, tb, slist):
    r=p+q; ns=[p,q-p,q,r]
    print(f"\n=== ({p},{q},{r}) interval [{ta},{tb}] (BHK-time) len={tb-ta}={float(tb-ta):.4f} ===")
    L=tb-ta
    sbound = q/(3*L)
    print(f"  s <= q/(3L) = {sbound} = {float(sbound):.4f}")
    allaway=True
    for i,ni in enumerate(ns):
        lo,hi = runner_band(ni,q,ta,tb)
        away = lo>=F(1,6) and hi<=F(5,6)
        # exact endpoint fracs
        fa=frac(ni*ta/q); fb=frac(ni*tb/q)
        print(f"  runner{i}(n={ni}): frac in [{float(lo):.4f},{float(hi):.4f}] "
              f"ends({fa}={float(fa):.3f} -> {fb}={float(fb):.3f}) away={away}")
        allaway = allaway and away
    print(f"  -> valid 0123-gap: {allaway}")
    # witnesses for each surviving s (tau-time witness theta in g=1 units)
    for sv in slist:
        nsf=[p,q-p,q,r,sv]
        found=None
        for d in range(2,60):
            for a in range(1,d):
                th=F(a,d)
                if all(cdist(n*th)>=F(1,6) for n in nsf):
                    found=th; break
            if found: break
        if found:
            fr=[frac(n*found) for n in nsf]
            print(f"  s={sv}: witness tau={found}; fracs={[f'{float(x):.3f}' for x in fr]}")
        else:
            print(f"  s={sv}: NO witness")

# (1,7,8): BHK [7/6 + x2/6, 7/6 + x4/2], x2=q/(q-p)=7/6, x4=q/(q+p)=7/8
x2=F(7,6); x4=F(7,8)
analyze(1,7,"s=9", F(7,6)+x2/6, F(7,6)+x4/2, [9])

# (1,12,13): BHK [2 + x2/3, 2 + 2 x4/3], x2=q/(q-p)=12/11, x4=q/(q+p)=12/13
x2b=F(12,11); x4b=F(12,13)
analyze(1,12,"s in 14,15", F(2)+x2b/3, F(2)+2*x4b/3, [14,15])

# also (1,5,6) and (1,6,7) intervals for reference (need Claim20 lower too)
# (1,5,6): [5/2 + x2/6, 5/2 + 1/3], x2=5/4
analyze(1,5,"s=13?", F(5,2)+F(5,4)/6, F(5,2)+F(1,3), list(range(7,14)))
# (1,6,7): BHK pins s=13 via 2v3<v5<2v4; the 01234-gap is (5x1/12,7x1/12)->[3-1/6,...]
