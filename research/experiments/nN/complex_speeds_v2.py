"""Corrected scan.  Tilting d -> d(1+ei) leaves Re(d t) = d t exactly (t real),
so the real obstruction is UNCHANGED and the imaginary part only adds distance:
     clear  iff  circDist(d t)^2 + (e d t)^2 >= 1/n^2 .
Prediction: isolation is monotonically EARLIER as e grows, never later."""
import math
N=8
def cd(x):
    f=x-math.floor(x); return min(f,1-f)
def clear(d,t,e): return math.hypot(cd(d*t),e*d*t) >= 1.0/N
def first_lonely(ds,e,tmax,step):
    t=step
    while t<tmax:
        if all(clear(d,t,e) for d in ds): return t
        t+=step
    return None
BASE=[30,74,96,127,159,175,224]
print("  tilt e    first lonely t     ratio to the real answer")
t0=first_lonely(BASE,0.0,0.2,1e-7)
print(f"  {0.0:<9} {t0:.7f}          1.000   (the real conjecture)")
for e in (0.001,0.005,0.01,0.02,0.05,0.1,0.125,0.2,0.5):
    t=first_lonely(BASE,e,0.2,1e-7)
    print(f"  {e:<9} {t:.7f}          {t/t0:.3f}")
print()
print("  monotone?  ", end="")
ts=[first_lonely(BASE,e,0.2,1e-7) for e in (0.0,0.001,0.005,0.01,0.02,0.05,0.1,0.2,0.5)]
print("yes" if all(a>=b-1e-12 for a,b in zip(ts,ts[1:])) else "NO")
print()
print("  and the trivial regime: when does the imaginary part alone clear every disparity?")
for e in (0.05,0.125,0.5,1.0):
    # need e*d*t >= 1/8 for the SMALLEST d
    t=1.0/(N*e*min(BASE))
    print(f"    e={e:<6} every disparity clear from t >= 1/(n e d_min) = {t:.6f}")
