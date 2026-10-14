"""Speeds in C, time in R.  Position lives on the cylinder C/Z; loneliness is
   dist(d*t, Z) >= 1/n,  with dist(z,Z)^2 = circDist(Re z)^2 + (Im z)^2."""
from fractions import Fraction as F
import cmath, math
N=8
def cd_real(x):
    f=x-math.floor(x); return min(f,1-f)
def cyl(z):
    return math.hypot(cd_real(z.real), z.imag)
def lonely(ds,t,n=N):
    return all(cyl(d*t)>=1.0/n for d in ds)

print("=== 1. the prediction: |Im(d t)| >= 1/n forces clearance, whatever the real part ===")
bad=0
for _ in range(20000):
    import random
    a=random.uniform(-5,5); b=random.uniform(1/N,3)
    z=complex(a,b)
    if cyl(z) < 1.0/N: bad+=1
print(f"    counterexamples in 20,000 samples: {bad}")
print("    so a disparity with imaginary part at least 1/n never obstructs.")

print()
print("=== 2. a hard real arrangement, then the same one perturbed into C ===")
BASE=[30,74,96,127,159,175,224]            # the depth-23 deep case
def first_lonely_real(ds,n=N,steps=4_000_00):
    dm=min(ds); t=1.0/(n*dm)
    for _ in range(steps):
        if lonely(ds,t,n): return t
        nxt=[]
        for d in ds:
            k=math.floor(d*t-1.0/n)
            while k+1.0/n < d*t: k+=1
            nxt.append((k+1.0/n)/d)
        t2=max(x for x in nxt if x>t)
        t=t2
    return None
t0=first_lonely_real([float(x) for x in BASE])
print(f"    real disparities {BASE}")
print(f"       first lonely t = {t0:.8f}   R = t0*8*30 = {t0*8*30:.5f}")
for eps in (0.001,0.01,0.05,0.125,0.2):
    ds=[complex(x, eps*x) for x in BASE]        # tilt every speed into C
    t=1.0/(N*min(abs(d) for d in ds))
    found=None
    for _ in range(200000):
        if lonely(ds,t): found=t; break
        t*= 1.0000005
        if t>t0*2: break
    print(f"       tilt {eps:<6}: first lonely t = {found if found is None else round(found,8)}"
          f"   (real answer {t0:.6f})")
