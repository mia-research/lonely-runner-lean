"""P: with position v t + a t^2/2 the boundary discipline survives and the scale recursion breaks.
Reading of a disparity: r(t) = d t + alpha t^2/2,  d = dv, alpha = da."""
import math, random
N=8
def cd(x):
    f=x-math.floor(x); return min(f,1-f)
def r(d,al,t): return d*t+al*t*t/2

print("=== A. boundary discipline: are obstruction sets still OPEN intervals with clear endpoints? ===")
random.seed(5); bad=0; tot=0
for _ in range(4000):
    d=random.uniform(0.5,20); al=random.uniform(-5,5)
    t=random.uniform(0.01,2)
    v=cd(r(d,al,t))
    if abs(v-1.0/N)<1e-9:            # a boundary point: must count as CLEAR
        tot+=1
        if not (v>=1.0/N-1e-12): bad+=1
# endpoints are clear by definition of >=; test openness instead: obstruction is a strict inequality
open_ok=True
for _ in range(2000):
    d=random.uniform(0.5,20); al=random.uniform(-5,5); t=random.uniform(0.01,2)
    if cd(r(d,al,t))<1.0/N:                       # in the way
        h=1e-9
        if not (cd(r(d,al,t+h))<1.0/N or cd(r(d,al,t-h))<1.0/N): open_ok=False
print(f"    reading is continuous in t, condition closed  =>  obstruction sets open: {open_ok}")
print("    (boundary discipline needs only continuity of the reading; it survives)")

print()
print("=== B. are the openings still (j + 1/n)/e ? ===")
print("    solve  d t + alpha t^2/2 = j + 1/n   for t:")
for d,al,j in ((7,0,0),(7,3,0),(7,3,1),(7,-2,2)):
    c=j+1.0/N
    if al==0:
        roots=[c/d]
    else:
        disc=d*d+2*al*c
        roots=[] if disc<0 else [(-d+math.sqrt(disc))/al, (-d-math.sqrt(disc))/al]
    linear=c/d
    print(f"    d={d}, alpha={al:>3}, j={j}:  roots {['%.6f'%x for x in roots if x>0]}"
          f"   vs linear (j+1/n)/e = {linear:.6f}")

print()
print("=== C. the scale recursion: does t -> lambda t scale all readings alike? ===")
lam=1.7; bad=0
for _ in range(3000):
    d=random.uniform(0.5,20); al=random.uniform(-5,5); t=random.uniform(0.01,1)
    if abs(r(d,al,lam*t) - lam*r(d,al,t))>1e-9: bad+=1
print(f"    r(d,alpha,lam t) == lam * r(d,alpha,t) ?   failures: {bad} of 3000")
print("    with alpha = 0 it holds identically; with alpha != 0 it fails for every sample.")
print("    so D_{j+1} = D_j * lambda has nothing to act on: the recursion on scale breaks.")

print()
print("=== D. does isolation still occur? ===")
random.seed(9); miss=0; tot=0
for _ in range(400):
    ds=[(random.uniform(1,20),random.uniform(-3,3)) for _ in range(7)]
    tot+=1
    found=False
    t=0.001
    while t<6:
        if all(cd(r(d,al,t))>=1.0/N for d,al in ds): found=True; break
        t+=0.0002
    if not found: miss+=1
print(f"    accelerating profiles with no lonely t found in (0,6]: {miss} of {tot}")
