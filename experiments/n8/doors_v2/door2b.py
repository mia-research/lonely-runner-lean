import random
from math import gcd
from fractions import Fraction as F
def inway(d,P,Q):
    r=(d*P)%Q; return 8*min(r,Q-r)<Q
def nextop(d,P,Q):
    num=8*d*P-Q; den=8*Q; k=-((-num)//den); g=gcd(8*k+1,8*d); return ((8*k+1)//g,(8*d)//g)
def move(ds,P,Q):
    bP,bQ=P,Q
    for d in ds:
        if inway(d,P,Q):
            nP,nQ=nextop(d,P,Q)
            if nP*bQ>bP*nQ: bP,bQ=nP,nQ
    return bP,bQ
def cascade(ds,cap=4000):
    m=min(ds); P,Q=1,8*m; g=gcd(P,Q); P,Q=P//g,Q//g; mv=0
    while mv<cap:
        P2,Q2=move(ds,P,Q)
        if (P2,Q2)==(P,Q): return mv,P,Q
        P,Q=P2,Q2; mv+=1
    return None,P,Q
def primitive(s):
    g=0
    for x in s: g=gcd(g,x)
    return g==1

print("=== DOOR 2: the arrival instant in the NEAREST RUNNER'S OWN LAPS, tau = m*t ===")
print("   (your scale statement: the cascade should arrive within a bounded number of")
print("    laps of the nearest runner, however far out of scale the others are)")
random.seed(41)
for hi in (25,50,100,200,400):
    mxtau=F(0); argt=None; mxmv=0; argm=None; n=0; seen=set()
    for _ in range(30000):
        s=tuple(sorted(random.sample(range(1,hi+1),7)))
        if s in seen or not primitive(s): continue
        seen.add(s); n+=1
        mv,P,Q=cascade(list(s))
        if mv is None: print("   NO ARRIVAL:",s); continue
        tau=F(min(s)*P,Q)
        if tau>mxtau: mxtau,argt=tau,s
        if mv>mxmv: mxmv,argm=mv,s
    # targeted: tiny min, everything else clustered high (the shape that maximised moves)
    for _ in range(30000):
        lo=random.choice([1,2,3])
        rest=sorted(random.sample(range(max(2,hi//2),hi+1),6))
        s=tuple([lo]+rest)
        if len(set(s))<7 or s in seen or not primitive(s): continue
        seen.add(s); n+=1
        mv,P,Q=cascade(list(s))
        if mv is None: print("   NO ARRIVAL:",s); continue
        tau=F(min(s)*P,Q)
        if tau>mxtau: mxtau,argt=tau,s
        if mv>mxmv: mxmv,argm=mv,s
    print(f"  [1,{hi:3d}] sets={n:6d}  max tau={float(mxtau):7.4f} ({mxtau}) at {argt}")
    print(f"              max moves={mxmv} at {argm}")
