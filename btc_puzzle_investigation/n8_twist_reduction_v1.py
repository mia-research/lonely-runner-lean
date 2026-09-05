#!/usr/bin/env python3
"""
n8_twist_reduction_v1.py -- 2026-09-02
Verifies the reduction chain of NOTE_n8_twist_reduction_v1.md.  Exact integer.
ARM B  branch condition is exactly  #E(F_p) ODD  (p = 7 mod 12)
ARM R  sum_{E(F_p)} chi2(G_R) == (h1*h1)[R]   and   sum_{E'(F_p)} chi2(G_R) == h2[R],  ALL R
ARM W  for R != O:   W(R) = sum_x chi2( g_R(x) * (x^3+B) ) == 0
"""
import sys
B=7
def leg(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
def tonelli(a,p):
    a%=p
    if a==0: return 0
    return pow(a,(p+1)//4,p) if p%4==3 else None
def pts(p):
    P=[]
    for x in range(p):
        r=(x*x%p*x+B)%p
        if r==0: P.append((x,0))
        elif leg(r,p)==1:
            y=tonelli(r,p); P.append((x,y)); P.append((x,(-y)%p))
    return P
def eadd(A,C,p):
    if A is None: return C
    if C is None: return A
    x1,y1=A; x2,y2=C
    if x1==x2 and (y1+y2)%p==0: return None
    lam=(3*x1*x1)%p*pow(2*y1,p-2,p)%p if A==C else (y2-y1)%p*pow((x2-x1)%p,p-2,p)%p
    x3=(lam*lam-x1-x2)%p; return (x3,(lam*(x1-x3)-y1)%p)
class F2:
    def __init__(s,p):
        s.p=p; u=2
        while leg(u,p)!=-1: u+=1
        s.u=u
    def mul(s,a,b):
        p,u=s.p,s.u; return ((a[0]*b[0]+u*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
    def add(s,a,b): return ((a[0]+b[0])%s.p,(a[1]+b[1])%s.p)
    def sub(s,a,b): return ((a[0]-b[0])%s.p,(a[1]-b[1])%s.p)
    def neg(s,a): return ((-a[0])%s.p,(-a[1])%s.p)
    def sq(s,a): return s.mul(a,a)
    def inv(s,a):
        p,u=s.p,s.u; d=(a[0]*a[0]-u*a[1]*a[1])%p; di=pow(d,p-2,p)
        return (a[0]*di%p,(-a[1])%p*di%p)
    def pw(s,a,k):
        r=(1,0)
        while k:
            if k&1: r=s.mul(r,a)
            a=s.sq(a); k>>=1
        return r
def eadd2(F,A,C):
    if A is None: return C
    if C is None: return A
    x1,y1=A; x2,y2=C
    if x1==x2 and F.add(y1,y2)==(0,0): return None
    lam=F.mul(F.mul((3,0),F.sq(x1)),F.inv(F.mul((2,0),y1))) if A==C else F.mul(F.sub(y2,y1),F.inv(F.sub(x2,x1)))
    x3=F.sub(F.sub(F.sq(lam),x1),x2)
    return (x3,F.sub(F.mul(lam,F.sub(x1,x3)),y1))
def run(p):
    P=pts(p); n=len(P)+1
    if n%2==0: return None
    pl=[None]+P; idx={q:i for i,q in enumerate(pl)}
    def smul(k,pt):
        r=None;a=pt
        while k:
            if k&1: r=eadd(r,a,p)
            a=eadd(a,a,p); k>>=1
        return r
    h1=[0]*n
    for (x,y) in P: h1[idx[(x,y)]]+=leg(y,p)
    conv=[0]*n
    for i in range(n):
        if h1[i]==0: continue
        for j in range(n):
            if h1[j]==0: continue
            s=eadd(pl[i],pl[j],p); conv[idx[s] if s else 0]+=h1[i]*h1[j]
    F=F2(p); q=p*p; half=(q-1)//2
    sq={}
    for a in range(p):
        for b in range(p): sq[F.sq((a,b))]=(a,b)
    E2=[]
    for a in range(p):
        for b in range(p):
            x=(a,b); r=F.add(F.mul(F.sq(x),x),(B%p,0)); y=sq.get(r)
            if y is None: continue
            for yy in (y,F.neg(y)):
                E2.append((x,yy))
                if yy==(0,0): break
    E2=list(dict.fromkeys(E2))
    frob2=lambda Q:((Q[0][0],(-Q[0][1])%p),(Q[1][0],(-Q[1][1])%p))
    Etw=[None]+[Q for Q in E2 if frob2(Q)==(Q[0],F.neg(Q[1]))]
    h2=[0]*n
    for Q in E2:
        if Q[1]==(0,0): continue
        c=1 if F.pw(Q[1],half)==(1,0) else -1
        T=eadd2(F,Q,frob2(Q)); h2[0 if T is None else idx[(T[0][0],T[1][0])]]+=c
    okR=okW=True
    for k in range(n):
        R=pl[k]; A0=smul((n+1)//2,R) if R is not None else None
        L=0
        for C in pl:
            Pp=eadd(A0,C,p); Pm=eadd(A0,None if C is None else (C[0],(-C[1])%p),p)
            if Pp is None or Pm is None: continue
            L+=leg(Pp[1]*Pm[1]%p,p)
        A0q=None if A0 is None else ((A0[0],0),(A0[1],0)); Rr=0
        for C in Etw:
            Pp=(A0q if C is None else (C if A0q is None else eadd2(F,A0q,C)))
            if Pp is None or Pp[1]==(0,0): continue
            Nm=F.mul(Pp[1],(Pp[1][0],(-Pp[1][1])%p)); Rr+=leg(Nm[0],p)
        okR &= (L==conv[k] and Rr==h2[k])
        if k>0:
            W=0
            for x in range(p):
                u=(x*x%p*x+B)%p
                if u==0: continue
                y=sq.get((u,0)); C=((x,0),y)
                Pp=eadd2(F,A0q,C); Pm=eadd2(F,A0q,(C[0],F.neg(C[1])))
                if Pp is None or Pm is None: continue
                g=F.mul(Pp[1],Pm[1])
                if g[1]!=0: okW=False; break
                W+=leg(g[0]*u%p,p)
            okW &= (W==0)
    return n,okR,okW,all(conv[k]==h2[k] for k in range(1,n)),h2[0]-conv[0]
if __name__=="__main__":
    LIM=int(sys.argv[1]) if len(sys.argv)>1 else 110
    print("%5s %5s | %-22s | %-24s | %-18s | %s" % ("p","#E","ARM R (both sides)","ARM W (Weil sum = 0)","N8 off O","f[O] vs 2p"))
    for p in range(13,LIM):
        if p%12!=7 or not all(p%d for d in range(2,int(p**.5)+1)) or B%p==0: continue
        r=run(p)
        if r is None: print("%5d %5s | %-22s |" % (p,"even","SKIP: #E even => m=-2 branch")); continue
        n,okR,okW,okN,fO=r
        print("%5d %5d | %-22s | %-24s | %-18s | %d vs %d %s" % (p,n,okR,okW,okN,fO,2*p,"OK" if fO==2*p else "NO"))
