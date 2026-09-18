"""Firewall ruling (owner, 2026-09-18): covering arguments built from the framework's OWN objects
are admitted; the ban protects against accidental import, which this is not.

The AP is the extremal covering configuration and its clear set is a SINGLE POINT: readings 1..7 at
R = 1 give distances 1/8,2/8,3/8,4/8,3/8,2/8,1/8 -- touching the threshold at both ends.  S > 7
destroys that point (reading 7 goes past 7).  So trace the first clear point R along the
one-parameter AP family

    readings  1, 1+u, 1+2u, ..., 1+6u     S = 1+6u,  u from 1.00 upward

and watch where R goes when S crosses 7.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
def Rdir(S, RMAX=60.0):
    c=[1.0]
    for s in S:
        k=1
        while (8*k+1)/s<=RMAX:
            r=(8*k+1)/s
            if r>=1.0: c.append(r)
            k+=1
    c.sort()
    for R in c:
        ok=True
        for s in S:
            m=(s*(R+1e-13))%8.0
            if m<1.0 or m>7.0: ok=False; break
        if ok: return R
    return None
print("  the AP family: readings 1, 1+u, ..., 1+6u\n")
print(f"  {'u':>8} {'S':>8} {'first clear R':>15} {'band':>5}")
prev=None
for i in range(0,61):
    u=1.0+i*0.005
    S=[1.0+k*u for k in range(7)]
    R=Rdir(S)
    band=int(R//8) if R else None
    mark=""
    if prev is not None and R is not None and abs(R-prev)>1.0: mark="   <-- JUMP"
    print(f"  {u:>8.3f} {1+6*u:>8.3f} {R:>15.6f} {band:>5}{mark}")
    prev=R
print()
print("  exact AP (u = 1, S = 7): clear set in [1,15]")
S=[float(k) for k in range(1,8)]
pts=[]
import numpy as np
for R in np.arange(1.0, 15.0001, 0.0001):
    if all(1.0 <= (s*R)%8.0 <= 7.0 for s in S): pts.append(round(R,4))
print(f"    clear points found at 1e-4 resolution: {pts[:12]}{' ...' if len(pts)>12 else ''}")
print(f"    total: {len(pts)} sample points  (measure ~ {len(pts)*1e-4:.4f})")
