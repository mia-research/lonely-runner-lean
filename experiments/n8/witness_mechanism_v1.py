from math import gcd
from itertools import combinations
def allowed(d,e):
    g=gcd(d,e); dp=d//g; c=e//g
    return c, sorted(k for k in range(c) if c <= (dp*(8*k+1)) % (8*c) <= 7*c)
def wit(ds,e): return [k for k in range(e) if all(e<=(d*(8*k+1))%(8*e)<=7*e for d in ds)]

def report(ds,label):
    print(f"\n{label}  ds={ds}")
    print(f"  {'flank e':>7} | {'moduli c_d = e/gcd(d,e)':38} | {'empty A_d?':10} | pairwise coprime | witness k")
    for e in ds:
        cons=[allowed(d,e) for d in ds]
        cs=[c for c,_ in cons]
        empt=[c for c,A in cons if not A]
        nz=[c for c in cs if c>1]
        pc=all(gcd(x,y)==1 for x,y in combinations(nz,2)) if len(nz)>1 else True
        w=wit(ds,e)
        print(f"  {e:>7} | {str(cs):38} | {str(empt) if empt else 'none':10} | {str(pc):16} | {w if w else '-- none --'}")

report([2,3,4,5,6,7,16], "THE UNIQUE |S|=1 SET")
report([1,2,3,4,5,6,7],  "THE AP (extremal)")
report([2,6,8,9,11,14,15], "the tau-extremal set")

print("\n\nc_d = 1 means e | d, and then the constraint is all-or-nothing:")
print("  clear at EVERY opening iff 8 does not divide d/e  (the framework's integer-ratio theorem).")
print("  So a flank e that divides another disparity d with 8 | d/e is DEAD at every opening.")
print("\nCheck that this is what kills the small flanks of the |S|=1 set:")
ds=[2,3,4,5,6,7,16]
for e in ds:
    dead=[d for d in ds if d%e==0 and (d//e)%8==0]
    if dead: print(f"  flank {e:>2}: killed outright by d={dead} (ratio {[d//e for d in dead]}, divisible by 8)")
