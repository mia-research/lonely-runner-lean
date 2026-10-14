"""The cascade run EXACTLY on irrational readings, in the field Q(sqrt 2).
No floats, no sampling: every comparison, floor and mod is exact."""
from fractions import Fraction as F
from math import isqrt
P=10**40
LO=F(isqrt(2*P*P),P); HI=LO+F(1,P)          # LO < sqrt2 < HI, exact rational bounds

class Q2:
    __slots__=("a","b")
    def __init__(s,a=0,b=0): s.a=F(a); s.b=F(b)          # a + b*sqrt2
    def __add__(s,o): o=q2(o); return Q2(s.a+o.a, s.b+o.b)
    def __sub__(s,o): o=q2(o); return Q2(s.a-o.a, s.b-o.b)
    def __mul__(s,o):
        o=q2(o); return Q2(s.a*o.a + 2*s.b*o.b, s.a*o.b + s.b*o.a)
    def __truediv__(s,o):
        o=q2(o); d=o.a*o.a - 2*o.b*o.b
        assert d!=0
        return s*Q2(o.a/d, -o.b/d)
    def bounds(s):
        x=s.a+s.b*LO; y=s.a+s.b*HI
        return (x,y) if s.b>=0 else (y,x)
    def is_zero(s): return s.a==0 and s.b==0
    def sign(s):
        if s.is_zero(): return 0
        lo,hi=s.bounds()
        if lo>0: return 1
        if hi<0: return -1
        raise RuntimeError("precision")
    def __lt__(s,o): return (s-q2(o)).sign()<0
    def __le__(s,o): return (s-q2(o)).sign()<=0
    def __gt__(s,o): return (s-q2(o)).sign()>0
    def __ge__(s,o): return (s-q2(o)).sign()>=0
    def __eq__(s,o): o=q2(o); return s.a==o.a and s.b==o.b
    def __hash__(s): return hash((s.a,s.b))
    def floor(s):
        lo,hi=s.bounds()
        import math
        f1=math.floor(lo); f2=math.floor(hi)
        if f1!=f2: raise RuntimeError("precision")
        return f1
    def mod(s,m): return s - Q2(m*s.floorDiv(m))
    def floorDiv(s,m): return (s/Q2(m)).floor()
    def __repr__(s):
        if s.b==0: return f"{s.a}"
        return f"{s.a}+{s.b}r2"
    def approx(s): return float(s.a)+float(s.b)*float(LO)
def q2(x): return x if isinstance(x,Q2) else Q2(x,0)

N=8
def cascade(S,cap=200000):
    R=Q2(1); moves=0
    for _ in range(cap):
        out=[]
        for s in S:
            r=(s*R).mod(N)
            if r < Q2(1): out.append((Q2(1)-r)/s)
            elif r > Q2(N-1): out.append((Q2(N+1)-r)/s)
        if not out: return R,moves
        best=out[0]
        for x in out[1:]:
            if x>best: best=x
        R=R+best; moves+=1
    return None,cap

r2=Q2(0,1)
tests=[
 ("one irrational reading",      [Q2(1), Q2(0,1), Q2(2), Q2(3), Q2(5), Q2(6), Q2(7)]),
 ("several irrational",          [Q2(1), Q2(0,1), Q2(1,1), Q2(3), Q2(2,1), Q2(6), Q2(4,2)]),
 ("spread just past 7",          [Q2(1), Q2(2,F(1,3)), Q2(3,F(1,5)), Q2(4), Q2(5,F(1,7)), Q2(6,F(1,4)), Q2(6,F(1,2))]),
 ("AP perturbed irrationally",   [Q2(1), Q2(2,F(1,100)), Q2(3), Q2(4,F(-1,100)), Q2(5), Q2(6), Q2(7,F(1,50))]),
]
for name,S in tests:
    S=sorted(S, key=lambda z: z.approx())
    R,mv=cascade(S)
    if R is None: print(f"  {name:28s} DID NOT HALT in cap"); continue
    irr = (R.b!=0)
    # verify the halt EXACTLY
    ok=all(Q2(1) <= (s*R).mod(N) <= Q2(N-1) for s in S)
    print(f"  {name:28s} halts in {mv:3d} moves   R = {R}   (~{R.approx():.6f})")
    print(f"      R irrational: {irr}     halt verified exactly: {ok}")

print()
print("=== cases where the cascade actually runs: an irrational reading past 7 ===")
cases=[
 ("1..6 and 7+r2/10",   [Q2(1),Q2(2),Q2(3),Q2(4),Q2(5),Q2(6),Q2(7,F(1,10))]),
 ("1..6 and 7+r2/4",    [Q2(1),Q2(2),Q2(3),Q2(4),Q2(5),Q2(6),Q2(7,F(1,4))]),
 ("1,2,3,4,5,6+r2/9,7+r2/3",[Q2(1),Q2(2),Q2(3),Q2(4),Q2(5),Q2(6,F(1,9)),Q2(7,F(1,3))]),
 ("irrational mid + tail",[Q2(1),Q2(2,F(1,7)),Q2(3),Q2(4,F(1,11)),Q2(5),Q2(6),Q2(7,F(1,6))]),
]
for name,S in cases:
    S=sorted(S,key=lambda z:z.approx())
    R,mv=cascade(S)
    if R is None: print(f"  {name:26s} no halt"); continue
    ok=all(Q2(1) <= (s*R).mod(N) <= Q2(N-1) for s in S)
    print(f"  {name:26s} moves {mv:3d}  R = {R}  (~{R.approx():.8f})  irrational: {R.b!=0}  exact halt: {ok}")

print()
print("=== BOUND the irrational, and see whether the isolation point stays bounded ===")
print("    readings 1..6 and s7 = 7 + t*sqrt2,  t ranging over a bounded interval")
vals=[]
for num in range(1,41):
    t=F(num,40)                      # t in (0, 1], so s7 in (7, 7+sqrt2] ~ (7, 8.414]
    S=[Q2(1),Q2(2),Q2(3),Q2(4),Q2(5),Q2(6),Q2(7,t)]
    R,mv=cascade(S)
    if R is None: vals.append((float(t),None,None)); continue
    vals.append((float(t),R.approx(),mv))
good=[v for v in vals if v[1] is not None]
print(f"    halted on {len(good)} of {len(vals)}")
print(f"    R ranges over [{min(v[1] for v in good):.6f}, {max(v[1] for v in good):.6f}]")
print(f"    moves range  [{min(v[2] for v in good)}, {max(v[2] for v in good)}]")
print(f"    sample: {[(round(t,3), round(r,4)) for t,r,_ in good[:8]]}")
