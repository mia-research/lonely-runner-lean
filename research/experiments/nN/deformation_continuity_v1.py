"""Does the isolation point MOVE under deformation, or JUMP?
Deform one reading continuously and watch R.  Exact rational arithmetic."""
from fractions import Fraction as F
N=F(8)
def R_of(S,cap=200000):
    R=F(1)
    for _ in range(cap):
        out=[]
        for s in S:
            r=(s*R)%N
            if r<1: out.append((F(1)-r)/s)
            elif r>N-1: out.append((F(9)-r)/s)
        if not out: return R
        R=R+max(out)
    return None
print("=== A. the AP itself: is its isolation an INTERVAL or an isolated point? ===")
S=[F(i) for i in range(1,8)]
def lonely(S,t):
    return all(min((s*t)%1, 1-((s*t)%1))>=F(1,8) for s in S)
t0=F(1,8)
print(f"    t = 1/8 lonely?            {lonely(S,t0)}")
for eps in (F(1,1000),F(1,100000)):
    print(f"    t = 1/8 + {eps}: {lonely(S,t0+eps)}      t = 1/8 - {eps}: {lonely(S,t0-eps)}")
print("    => the AP's own isolation instant is ISOLATED, not an interval.")
print()
print("=== B. deform one reading and watch R ===")
print("    S = (1,2,3,4,5,6, 7+e), e sweeping upward in steps of 1/200")
prev=None; jumps=0; vals=[]
for k in range(0,121):
    e=F(k,200)
    S=[F(1),F(2),F(3),F(4),F(5),F(6),F(7)+e]
    R=R_of(S)
    vals.append((e,R))
    if prev is not None and R is not None and prev is not None and R!=prev: jumps+=1
    prev=R
print(f"    distinct R values over the sweep: {len(set(v for _,v in vals))}")
print(f"    changes between consecutive steps: {jumps} of {len(vals)-1}")
seen=[]
last=None
for e,R in vals:
    if R!=last: seen.append((str(e),float(R) if R else None)); last=R
print(f"    R as e increases: {seen[:14]}")
