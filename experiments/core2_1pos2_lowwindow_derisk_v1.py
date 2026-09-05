#!/usr/bin/env python3
"""
(1,2) core2 P'-window — the CORRECT (lower) window.
===================================================
For (1,2), line Y={2X}. The (43) cut Y<=5/12-p/(3q) is an UPPER bound X<=Xcut2.
Part-1's window sat near h41 (Y~1/3, top) -> incompatible with (43).
The real P'-window on Y=2X: bottom = lower slant (h42a), top = min(h42b-upper, Xcut2, Xv, h41).
  h42a:  1/(3s) <= (5/6-X)/r + (2X-1/6)/p      [increasing in X -> X >= Xa]
  h42b:  1/(3s) <= (5/6-X)/r + (1/3-2X)/(q-p)  [decreasing in X -> X <= Xb]
  h40:   2X >= 1/6 - pM   -> X >= 1/12 - pM/2
  h39:   X >= 1/6 - rM
  h41:   X <= 1/6 + (q-p)M/2 = Xv
  (43):  X <= 5/24 - p/(6q) = Xcut2
window = [max(Xa, X40, X39), min(Xb, Xv, Xcut2)].  Need width >= 1/q and a grid pt.
"""
import math
def frac(x): return x - math.floor(x)

def run(qmax=120):
    tot=0; wok=0; gok=0; gfail=[]
    for q in range(7,qmax+1):
        for p in range(1,q):
            if p%2!=0 or math.gcd(p,q)!=1 or 6*p>=q: continue
            if (2*q+p)%2!=0: continue
            r=(2*q+p)//2
            if not (q<r and 2*r<3*q) or math.gcd(r,q)!=1: continue
            for s in range(r+1,3*q+1):
                if s<q: continue
                tot+=1
                M=(s-q)/(3*q*s)
                # Xa from h42a:  1/(3s) - 5/(6r) + 1/(6p) <= X*(2/p - 1/r)
                ca = 2/p - 1/r
                Xa = (1/(3*s) - 5/(6*r) + 1/(6*p))/ca
                # Xb from h42b:  1/(3s) - 5/(6r) - 1/(3(q-p)) <= -X*(1/r + 2/(q-p))
                cb = 1/r + 2/(q-p)
                Xb = (5/(6*r) + 1/(3*(q-p)) - 1/(3*s))/cb
                X39 = 1/6 - r*M
                X40 = 1/12 - p*M/2
                Xv = 1/6 + (q-p)*M/2
                Xcut2 = 5/24 - p/(6*q)
                lo = max(Xa, X39, X40)
                top = min(Xb, Xv, Xcut2)
                if top - lo >= 1/q - 1e-12: wok+=1
                # actual grid point Y=2X branch (X<1/2)
                found=False
                for m in range(1,2*q,2):
                    X=frac(r*m/(2*q))
                    if X>=0.5: continue
                    if lo-1e-9<=X<=top+1e-9: found=True; break
                if found: gok+=1
                else: gfail.append((q,p,r,s,round(lo,3),round(top,3)))
    print(f"(1,2): completions={tot}")
    print(f"  window [max-lower, min-upper] width>=1/q: {wok}")
    print(f"  actual grid pt in window:                 {gok}  (fail {len(gfail)})")
    ge18=[t for t in gfail if t[0]>=18]
    print(f"  grid failures with q>=18: {len(ge18)}")
    if ge18: print("   ", ge18[:12])

run()
