"""Predictions stated before running.  P1 negatives, P2 complex t, P3 arbitrary threshold."""
from fractions import Fraction as F
import math, random
def cdq(x):
    f=x-math.floor(x); return min(f,1-f)

print("=== P1: negative speeds / translation change nothing ===")
random.seed(1); bad=0; tot=0
for _ in range(3000):
    V=sorted(random.sample(range(-40,41),8))
    if len(set(V))!=8: continue
    for c in (0,17,-23):
        for sgn in (1,-1):
            W=sorted(sgn*(v+c) for v in V)
            for k in range(8):
                A=sorted(abs(V[k]-w) for w in V if w!=V[k])
                j=[i for i,w in enumerate(W) if w==sgn*(V[k]+c)][0]
                B=sorted(abs(W[j]-w) for w in W if w!=W[j])
                tot+=1
                if A!=B: bad+=1
print(f"    disparity multisets identical under v -> sgn*(v+c): {tot} checks, {bad} differences")

print()
print("=== P2: complex t with real speeds == uniform tilt ===")
N=8
def cyl(z): return math.hypot(cdq(z.real), z.imag)
bad=0
for _ in range(20000):
    v=random.uniform(0.5,50); tau=random.uniform(0.001,0.3); sig=random.uniform(0,0.1)
    lhs=cyl(complex(v*tau, v*sig))                 # real speed, complex time
    eps=sig/tau
    rhs=math.hypot(cdq(v*tau), eps*v*tau)          # tilted speed, real time
    if abs(lhs-rhs)>1e-12: bad+=1
print(f"    |dist(v*(tau+i sig), Z) - dist_tilt(v(1+i eps), tau)| > 1e-12 : {bad} of 20,000")

print()
print("=== P3: arbitrary threshold gamma in place of 1/n ===")
def lonely_g(ds,t,g): return all(cdq(d*t)>=g for d in ds)
def cert_g(ds,e,j,g,Q):
    """opening (j+g)/e ; criterion with g = p/Q rational"""
    t=F(j)+g
    return all(cdq(float(d)*float(t)/e)>=float(g) for d in ds)
bad=0; tot=0
for _ in range(4000):
    ds=sorted(random.sample(range(1,30),7))
    for g in (F(1,8),F(1,5),F(1,12),F(3,25)):
        for e in ds:
            for j in range(0,4):
                t=(F(j)+g)/e
                direct=lonely_g([F(d) for d in ds],t,g)
                # modular form: d*(Qj+p) mod (Q e) in [p e, (Q-p) e] with g=p/Q
                p,Q=g.numerator,g.denominator
                modu=all(p*e<=(d*(Q*j+p))%(Q*e)<=(Q-p)*e for d in ds)
                tot+=1
                if direct!=modu: bad+=1
print(f"    generalised certificate criterion vs direct, thresholds 1/8,1/5,1/12,3/25:")
print(f"       {tot} checks, {bad} mismatches")
print()
ratio_bad=0; rtot=0
for _ in range(4000):
    ds=sorted(random.sample(range(1,40),7))
    for g in (F(1,8),F(1,5),F(1,12),F(3,25)):
        lim=(1/g)-1
        if max(ds)<=lim*min(ds):
            rtot+=1
            if not lonely_g([F(d) for d in ds],g/min(ds),g): ratio_bad+=1
print(f"    ratio condition d_max <= (1/g - 1) d_min  =>  lonely at g/d_min:")
print(f"       {rtot} instances, {ratio_bad} failures")
