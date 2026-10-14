"""Item 3, redirected: EXHIBIT (e,k) in the middle region, do not count how many exist.

Structure already proved:  at a = e*s with e*s = 1 (mod n), every non-multiple d reads exactly
e*(d*s mod n) -- ON the grid points e*1 .. e*(n-1), which are precisely the band's endpoints and
interior marks.  So rho = 0 is the spine configuration: multiples read 0 (blocked), and any
non-multiple with d*s mod n in {1, n-1} sits on a band EDGE with zero slack.

Hence the rule: pick the flank so that no non-multiple sits on an edge --

      exists e in ds, gcd(e,n)=1, with  d * e^{-1} mod n  in [2, n-2]  for every non-multiple d

-- which leaves slack e on both sides, room to move rho and bring the multiples in.
This is a condition on the difference set that NAMES the flank.  Measure its reach.
"""
from itertools import combinations
import math
def interior_flank(ds, n):
    for e in ds:
        if math.gcd(e, n) != 1: continue
        u = pow(e, -1, n)
        nonmult = [d for d in ds if d % n != 0 and d != e]
        if all(2 <= (d*u) % n <= n-2 for d in nonmult): return e
    return None
def works(ds,e,n):
    M=n*e
    for j in range(e):
        if all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in ds): return True
    return False
for n,HI in ((5,26),(6,20),(7,15),(8,13)):
    k=n-1; mid=0; fires=0; sound=0
    for c in combinations(range(1,HI+1),k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        M=sum(1 for d in c if d%n==0)
        if not (1 <= M <= len(c)-2): continue
        mid+=1
        e=interior_flank(c,n)
        if e is not None:
            fires+=1
            if works(c,e,n): sound+=1
    print(f"n={n}  middle-region sets in [1,{HI}]: {mid}")
    print(f"   interior-band flank exists : {fires}")
    print(f"   ... and that flank WORKS   : {sound}"
          f"   {'(sound on all of them)' if sound==fires else '(NOT sound: '+str(fires-sound)+' fail)'}")
    print()
