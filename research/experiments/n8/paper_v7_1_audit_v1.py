"""Audit of PAPER_v7_1.md: every mathematically checkable claim, verified independently.
Each check prints PASS/FAIL and the evidence. No claim is taken from the paper's own prose."""
from fractions import Fraction as F
from math import gcd
from itertools import combinations
R=[]
def chk(name, ok, ev=""):
    R.append((name,ok,ev)); print(("  PASS  " if ok else "  FAIL  ")+name+(("   "+ev) if ev else ""))

def cdist(x):           # circle distance to nearest integer
    f=x-int(x)
    if f<0: f+=1
    return min(f,1-f)
def lonely(ds,t,n): return all(cdist(d*t)>=F(1,n) for d in ds)

print("=== A. worked example, section 7.1 (n=8, arrangement 1,2,3,4,5,6,8,9, subject 1) ===")
arr=[1,2,3,4,5,6,8,9]; subj=1; ds=sorted(abs(v-subj) for v in arr if v!=subj)
chk("disparity set is {1,2,3,4,5,7,8}", ds==[1,2,3,4,5,7,8], str(ds))
t0=F(1,8*min(ds)); chk("bound t0 = 1/8", t0==F(1,8), str(t0))
s0=[cdist(d*t0) for d in ds]
chk("step 0 distances 1/8,1/4,3/8,1/2,3/8,1/8,0",
    s0==[F(1,8),F(1,4),F(3,8),F(1,2),F(3,8),F(1,8),F(0)], str(s0))
chk("step 0: runner 8 is the ONLY one in the way",
    [d for d,x in zip(ds,s0) if x<F(1,8)]==[8])
t1=F(1+F(1,8),8); chk("move 0 -> 9/64", t1==F(9,64), str(t1))
s1=[cdist(d*t1) for d in ds]
chk("step 1 distances 9/64,9/32,27/64,7/16,19/64,1/64,1/8",
    s1==[F(9,64),F(9,32),F(27,64),F(7,16),F(19,64),F(1,64),F(1,8)], str(s1))
chk("step 1: runner 7 is the ONLY one in the way",
    [d for d,x in zip(ds,s1) if x<F(1,8)]==[7])
t2=F(1+F(1,8),7); chk("move 1 -> 9/56", t2==F(9,56), str(t2))
s2=[cdist(d*t2) for d in ds]
chk("step 2 distances 9/56,9/28,27/56,5/14,11/56,1/8,2/7",
    s2==[F(9,56),F(9,28),F(27,56),F(5,14),F(11,56),F(1,8),F(2,7)], str(s2))
chk("step 2 is lonely (cascade halts)", lonely(ds,t2,8))
chk("no earlier lonely instant among the steps", not lonely(ds,t0,8) and not lonely(ds,t1,8))
chk("certificate (e,j)=(7,1): 9/56 = (1+1/8)/7", F(1+F(1,8),7)==F(9,56))
chk("R1 fails: d_max > 7*d_min", max(ds)>7*min(ds), f"{max(ds)}>{7*min(ds)}")
chk("R3 fails: some disparity divisible by 8", any(d%8==0 for d in ds))
chk("R6 applies at q=6: no disparity divisible by 6", all(d%6 for d in ds))
r6=[cdist(d*F(1,6)) for d in ds]
chk("R6 readings at t=1/6 are 1/6,1/3,1/2,1/3,1/6,1/6,1/3",
    r6==[F(1,6),F(1,3),F(1,2),F(1,3),F(1,6),F(1,6),F(1,3)], str(r6))
chk("t=1/6 is lonely", lonely(ds,F(1,6),8))
M=sum(1 for d in ds if d%8==0); chk("example sits in the middle: M=1, c=7", (M,len(ds))==(1,7))

print()
print("=== B. Theorem 10, the modular criterion, against direct computation ===")
def opening_lonely_direct(ds,e,j,n): return lonely(ds,F(n*j+1,n*e),n)
def opening_lonely_modular(ds,e,j,n):
    a=n*j+1
    return all(e<=(d*a)%(n*e)<=(n-1)*e for d in ds)
bad=[]
for n in (5,6,7,8):
    for ds_ in combinations(range(1,16),n-1):
        for e in ds_:
            for j in range(0,e+3):
                if opening_lonely_direct(list(ds_),e,j,n)!=opening_lonely_modular(list(ds_),e,j,n):
                    bad.append((n,ds_,e,j))
chk("Theorem 10 matches direct computation", not bad, f"{len(bad)} mismatches over n=5..8")
per=[]
for n in (5,8):
    for ds_ in combinations(range(1,14),n-1):
        for e in ds_:
            for j in range(0,e):
                if opening_lonely_modular(list(ds_),e,j,n)!=opening_lonely_modular(list(ds_),e,j+e,n):
                    per.append((n,ds_,e,j))
chk("period e in j (Theorem 10's periodicity)", not per, f"{len(per)} violations")

print()
print("=== C. the rules ===")
# R1 / Theorem 8
v=[]
for n in (4,5,6,7,8):
    for ds_ in combinations(range(1,20),n-1):
        if max(ds_)<=(n-1)*min(ds_) and not lonely(list(ds_),F(1,n*min(ds_)),n): v.append((n,ds_))
chk("R1 (Theorem 8): d_max<=(n-1)d_min => lonely at 1/(n d_min)", not v, f"{len(v)} counterexamples")
# R6 equivalence
v=[]
for n in (5,8):
    for ds_ in combinations(range(1,18),n-1):
        for q in range(2,n+1):
            if lonely(list(ds_),F(1,q),n) != all(d%q for d in ds_): v.append((n,ds_,q))
chk("R6 is an equivalence for 2<=q<=n", not v, f"{len(v)} counterexamples")
# R3
v=[]
for n in (5,7,8,9):
    for ds_ in combinations(range(1,16),n-1):
        if all(d%n for d in ds_):
            for e in ds_:
                if gcd(e,n)==1:
                    sinv=pow(e,-1,n); a=(e*sinv)%(n*e) or e*sinv
                    if not opening_lonely_modular(list(ds_),e,(e*sinv-1)//n,n) or (e*sinv-1)%n:
                        v.append((n,ds_,e))
chk("R3 witness a=e*(e^-1 mod n) is a valid opening index and clears", not v, f"{len(v)} failures")

print()
print("=== D. section 12's example {1,2,3,5} at n=5 ===")
ds5=[1,2,3,5]; n=5
chk("e=3 at j=2 clears", opening_lonely_modular(ds5,3,2,n))
chk("e=5 at j=1 clears", opening_lonely_modular(ds5,5,1,n))
M=sum(1 for d in ds5 if d%n==0); c=len(ds5)
chk("it is in the middle: 1<=M<=c-2", 1<=M<=c-2, f"M={M}, c={c}")
r4 = (n in (2,3,5,7,11,13)) and any(d%n==0 for d in ds5) and \
     sum(1 for d in ds5 if d%n==0)==1 and max(ds5)%n==0
chk("R4's stated hypotheses HOLD for this set (n prime, n|e, e largest, no other multiple)", r4)
chk("and R4's witness r=1 (a=6, i.e. e=5 at j=1) clears", opening_lonely_modular(ds5,5,1,n))

print()
print("=== E. the identities quoted in section 14 ===")
v=[(s,m,) for s in range(1,60) for m in range(0,30) if (s*(8*m+1))%(8*s)!=s%(8*s)]
chk("14.3  (s*(8m+1)) mod 8s = s  (a reading never blocks its own candidate)", not v, f"{len(v)} failures")
v=[(s,x,k) for s in range(1,40) for x in range(0,9) for k in range(-5,6)
   if s*(8-x)-8*k != -(s*x-8*(s-k))]
chk("14.4  s(8-x)-8k = -(sx-8(s-k))  (the reflection identity)", not v, f"{len(v)} failures")
def clear_res(r,b): return b<=8*r+1<=7*b
chk("14.6  q=1 clears every modulus 2..9", all(clear_res(1,b) for b in range(2,10)))
chk("14.6  q=1 fails from b=10", not clear_res(1,10))
v=[(q,b) for q in range(1,40) for b in range(q+1,300) if clear_res(q,b)!=(8*q+1>=b and 7*b>=8*q+1)]
chk("14.6  reach window (8q+1)/7 <= b <= 8q+1 for 0<q<b", not v, f"{len(v)} failures")

print()
print("=== F. blocker bound n-3 (section 14.3 / 15 / 18) ===")
n=8   # EXPLICIT: section D rebinds n=5; this check is order 8
print("    (order fixed at n =",n,")")
def blk(profile,sk,m):
    A=8*m+1
    return [s for s in profile if not (sk<=(s*A)%(n*sk)<=(n-1)*sk)]
res={}
for label,cond in [("unqualified (all m>=0)", lambda sk,m: True),
                   ("R>=1",                   lambda sk,m: 8*m+1>=sk),
                   ("R mod 8 in [1,7]",       lambda sk,m: sk<=(8*m+1)%(8*sk)<=7*sk)]:
    worst=0;wit=None
    for prof in combinations(range(1,26),7):
        if prof[0]!=1: continue
        for sk in prof:
            for m in range(0,15):
                if not cond(sk,m): continue
                b=blk(list(prof),sk,m)
                if len(b)>worst: worst,wit=len(b),(prof,sk,m,b)
    res[label]=(worst,wit); print(f"    {label:24s} max={worst}")
chk("the bound as STATED in the paper (unqualified) FAILS",
    res["unqualified (all m>=0)"][0]>5, f"max={res['unqualified (all m>=0)'][0]}, witness={res['unqualified (all m>=0)'][1]}")
chk("the bound HOLDS, and is tight, once restricted to R mod 8 in [1,7]",
    res["R mod 8 in [1,7]"][0]==5, f"max={res['R mod 8 in [1,7]'][0]} = n-3")
mm=sum(1 for sk in range(1,40) for m in range(0,60)
       if (not (sk<=(8*m+1)%(8*sk)<=7*sk)) == (1<=((8*m+1)/sk)%8<=7))
chk("'the unit never blocks' is EQUIVALENT to R mod 8 in [1,7]", mm==0, f"{mm} mismatches")

print()
print("=== SUMMARY ===")
f=[n for n,ok,_ in R if not ok]
print(f"  {len(R)-len(f)}/{len(R)} pass")
for n in f: print("   FAILED:",n)
