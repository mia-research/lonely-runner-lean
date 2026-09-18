"""A: does the PERIOD explode under rational refinement while the ISOLATION INSTANT stays put?
   B: is the R envelope for INCOMMENSURABLE disparities inside the commensurable one?
Exact throughout: Fraction for A, Q(sqrt2) for B.  2026-09-18."""
import sys, math, random
sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import gcd, floor, ceil
from itertools import combinations
from lattice_witness_irrational_v1 import sign, floor_q2

TH=F(1,8)
# ---------- rational cascade ----------
def circd(x):
    x=x-floor(x); return min(x,1-x)
def inWay(d,t): return circd(d*t)<TH
def nextOp(d,t):
    k=ceil(d*t-TH)
    if k<0:k=0
    while F(k,1)+TH<d*t:k+=1
    return (F(k,1)+TH)/d
def move(ds,t):
    b=[d for d in ds if inWay(d,t)]
    return t if not b else max(nextOp(d,t) for d in b)
def cascade(ds):
    t=TH/min(ds); n=0
    while n<20000:
        nt=move(ds,t)
        if nt==t: return t,n
        t=nt; n+=1
    return None,n
def period_of(v):
    """v rationals -> P = 1/G with G = gcd of pairwise differences (as a rational)."""
    diffs=[abs(b-a) for a,b in combinations(v,2)]
    num=0; den=None
    for d in diffs:
        num=gcd(num,d.numerator)
        den=d.denominator if den is None else den*d.denominator//gcd(den,d.denominator)
    return F(den,num)   # 1/G where G = num/den

print("="*74)
print("A. RATIONAL REFINEMENT LADDER   base (1,2,3,x,5,6,7,8),  x -> 13/3")
print("   subject = the runner at x")
print(f"   {'x':>12} {'period P':>16} {'isolation t':>18} {'u=d_min*t':>12} {'moves':>6}")
lad=[F(43,10),F(433,100),F(4333,1000),F(43333,10000),F(433333,100000),F(4333333,1000000),F(13,3)]
for x in lad:
    v=[F(1),F(2),F(3),x,F(5),F(6),F(7),F(8)]
    P=period_of(v)
    ds=sorted(abs(w-x) for w in v if w!=x)
    t,n=cascade(ds)
    u=min(ds)*t
    print(f"   {str(x):>12} {str(P):>16} {str(t):>18} {str(u):>12} {n:>6}")

print()
print("   same ladder, subject = runner 1 (sees x as a disparity)")
print(f"   {'x':>12} {'period P':>16} {'isolation t':>18} {'u=d_min*t':>12} {'moves':>6}")
for x in lad:
    v=[F(1),F(2),F(3),x,F(5),F(6),F(7),F(8)]
    P=period_of(v)
    ds=sorted(abs(w-F(1)) for w in v if w!=F(1))
    t,n=cascade(ds)
    u=min(ds)*t
    print(f"   {str(x):>12} {str(P):>16} {str(t):>18} {str(u):>12} {n:>6}")

# ---------- Q(sqrt2) cascade ----------
def mul(x,y): return (x[0]*y[0]+2*x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def inv(x):
    a,b=x; den=a*a-2*b*b; return (a/den,-b/den)
def sub(x,y): return (x[0]-y[0],x[1]-y[1])
def lt(x,y): return sign(*sub(x,y))<0
def fv(x): return float(x[0])+float(x[1])*math.sqrt(2)
def cd_lt(x):
    k=floor_q2(*x); fr=sub(x,(F(k),F(0)))
    return lt(fr,(TH,F(0))) or lt((1-TH,F(0)),fr)
def nextOp_q(d,t):
    dt=mul(d,t); k=ceil(fv(dt)-1/8)
    if k<0: k=0
    while lt(( F(k)+TH,F(0)), dt): k+=1
    while not lt((F(k-1)+TH,F(0)), dt) and k>0: k-=1
    return mul((F(k)+TH,F(0)), inv(d))
def cascade_q(ds):
    dmin=min(ds,key=fv)
    t=mul((TH,F(0)),inv(dmin)); n=0
    while n<400:
        b=[d for d in ds if cd_lt(mul(d,t))]
        if not b: return t,n,dmin
        nt=max((nextOp_q(d,t) for d in b), key=fv)
        t=nt; n+=1
    return None,n,dmin

print()
print("="*74)
print("B. R ENVELOPE  (R = 8*d_min*t)   commensurable vs incommensurable")
random.seed(3)
def R_comm(trials):
    out=[]
    for _ in range(trials):
        v=sorted(random.sample(range(0,120),8))
        for i in range(8):
            ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
            ds=[F(d) for d in ds]
            t,n=cascade(ds)
            if t is None: continue
            S=float(max(ds)/min(ds)); R=float(8*min(ds)*t)
            out.append((S,R,n))
    return out
def R_incomm(trials):
    out=[]
    for _ in range(trials):
        base=sorted(random.sample(range(0,120),8))
        k=random.randrange(8)
        off=F(random.randint(1,99),100)
        sp=[(F(b),F(0)) for b in base]
        sp[k]=(F(base[k]), off)            # base[k] + (off)*sqrt2  -> incommensurable
        for i in range(8):
            ds=[]
            ok=True
            for j in range(8):
                if j==i: continue
                d=sub(sp[j],sp[i])
                if sign(*d)<0: d=(-d[0],-d[1])
                if sign(*d)==0: ok=False
                ds.append(d)
            if not ok: continue
            t,n,dmin=cascade_q(ds)
            if t is None: continue
            S=max(fv(d) for d in ds)/fv(dmin); R=8*fv(dmin)*fv(t)
            out.append((S,R,n))
    return out

C=R_comm(60); I=R_incomm(45)
def envelope(rows,label):
    bands={}
    for S,R,n in rows:
        b=min(int(S),12)
        bands.setdefault(b,[]).append(R)
    print(f"   {label}: {len(rows)} runner-instances, max R = {max(r for _,r,_ in rows):.4f}, "
          f"max moves = {max(n for _,_,n in rows)}")
    print(f"     {'S band':>8} {'n':>6} {'max R':>10} {'mean R':>10}")
    for b in sorted(bands):
        v=bands[b]
        print(f"     {b:>4}-{b+1:<3} {len(v):>6} {max(v):>10.4f} {sum(v)/len(v):>10.4f}")
envelope(C,"commensurable  ")
print()
envelope(I,"incommensurable")
