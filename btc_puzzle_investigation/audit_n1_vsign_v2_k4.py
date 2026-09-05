#!/usr/bin/env python3
"""Full V_1..V_k reconstruction over F_{p^k} -> exact e1..e4 in Z[zeta_n].
Checks, EXACTLY (integer identities in Z[x]/Phi_n):
  F1  : e2 = (V1^2+V2)/2                       [Newton with P_k = -V_k]
  F2  : e3 = -p*e1 (SIN, p=3 mod 4) / +p*e1 (COS, p=1 mod 4)   and e4 = p^2
and then the stratum dictionary  e2 = -2p-4pv (SIN) / +2p+4pv (COS).
"""
import sys, time
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import (is_prime, legendre, curve_order, dlog_table,
                                    tonelli, ec_add)
from audit_n1_vsign_v2_minpoly import red, mulF
B=7

# ---- F_p[t]/(f), f irreducible of degree k ----
def pmul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b): c[i+j]=(c[i+j]+ai*bj)%p
    return c
def pmod(a,f,p):
    a=a[:]
    df=len(f)-1
    inv=pow(f[-1],p-2,p)
    while len(a)-1>=df:
        d=len(a)-1-df
        c=a[-1]*inv%p
        for i in range(df+1): a[d+i]=(a[d+i]-c*f[i])%p
        while a and a[-1]==0: a.pop()
    return a if a else [0]
def ppowx(e,f,p):
    """x^e mod f"""
    r=[1]; b=[0,1]
    while e:
        if e&1: r=pmod(pmul(r,b,p),f,p)
        b=pmod(pmul(b,b,p),f,p); e>>=1
    return r
def pgcd(a,b,p):
    a=a[:];b=b[:]
    while b and any(b):
        inv=pow(b[-1],p-2,p)
        while len(a)>=len(b) and any(a):
            d=len(a)-len(b); c=a[-1]*inv%p
            for i in range(len(b)): a[d+i]=(a[d+i]-c*b[i])%p
            while a and a[-1]==0: a.pop()
            if not a: a=[0]
        a,b=b,a
    return a
def find_irred(p,k):
    """Irreducible monic f of degree k over F_p, via sympy's exact test."""
    import itertools, sympy
    X=sympy.Symbol('X')
    for tail in itertools.product(range(p),repeat=k):
        if tail[0]==0: continue
        f=list(tail)+[1]
        poly=sympy.Poly(list(reversed(f)),X,modulus=p)
        if poly.is_irreducible: return f
    raise RuntimeError
def _pf(m):
    r=[];d=2
    while d*d<=m:
        while m%d==0: r.append(d);m//=d
        d+=1
    if m>1: r.append(m)
    return r

class FF:
    def __init__(self,p,k):
        self.p=p;self.k=k
        self.f=[0,0,1] if False else find_irred(p,k)
    def mul(self,a,b):
        return tuple(_pad(pmod(pmul(list(a),list(b),self.p),self.f,self.p),self.k))
    def add(self,a,b): return tuple((x+y)%self.p for x,y in zip(a,b))
    def sub(self,a,b): return tuple((x-y)%self.p for x,y in zip(a,b))
    def neg(self,a):   return tuple((-x)%self.p for x in a)
    def pw(self,a,e):
        r=self.one()
        while e:
            if e&1: r=self.mul(r,a)
            a=self.mul(a,a); e>>=1
        return r
    def one(self): return tuple([1]+[0]*(self.k-1))
    def zero(self): return tuple([0]*self.k)
    def inv(self,a): return self.pw(a,self.p**self.k-2)
    def frob(self,a): return self.pw(a,self.p)
def _pad(a,k): return list(a)+[0]*(k-len(a))

def ecadd(F,P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and F.add(y1,y2)==F.zero(): return None
    if P==Q:
        num=F.mul(_c(F,3),F.mul(x1,x1)); den=F.mul(_c(F,2),y1)
    else:
        num=F.sub(y2,y1); den=F.sub(x2,x1)
    lam=F.mul(num,F.inv(den))
    x3=F.sub(F.sub(F.mul(lam,lam),x1),x2)
    y3=F.sub(F.mul(lam,F.sub(x1,x3)),y1)
    return (x3,y3)
def _c(F,c): return tuple([c%F.p]+[0]*(F.k-1))

def hist(p,k,n,dl):
    if k==1:
        from audit_n1_vsign_v2_core import hist_k1
        return hist_k1(p,n,dl,B)
    F=FF(p,k); q=p**k; half=(q-1)//2
    import itertools
    sq={}
    for tup in itertools.product(range(p),repeat=k):
        sq[F.mul(tup,tup)]=tup
    h=[0]*n; Bq=_c(F,B)
    for tup in itertools.product(range(p),repeat=k):
        x=tup
        r=F.add(F.mul(F.mul(x,x),x),Bq)
        if r==F.zero(): continue
        y=sq.get(r)
        if y is None: continue
        for yy in (y,F.neg(y)):
            c=1 if F.pw(yy,half)==F.one() else -1
            P=(x,yy); T=P; Q=P
            for _ in range(k-1):
                Q=(F.frob(Q[0]),F.frob(Q[1])); T=ecadd(F,T,Q)
            if T is None: d=0
            else:
                assert all(t==0 for t in T[0][1:]) and all(t==0 for t in T[1][1:])
                d=dl[(T[0][0],T[1][0])]
            h[d]+=c
    return h

def run(p,kmax):
    n=curve_order(p,B); assert is_prime(n)
    dl=dlog_table(p,n,B)
    V=[]
    for k in range(1,kmax+1):
        t0=time.time(); hk=hist(p,k,n,dl); V.append(red(hk+[0]*0,n) if len(hk)==n else None)
        V[-1]=red(hk,n)
        print(f"  k={k}: |h| sum={sum(hk)}  ({time.time()-t0:.1f}s)",flush=True)
    def M(*xs):
        r=[1]+[0]*(n-2)
        for x in xs: r=mulF(r,x,n)
        return r
    def S(*terms):
        out=[0]*(n-1)
        for co,vec in terms:
            for i in range(n-1): out[i]+=co*vec[i]
        return out
    V1,V2=V[0],V[1]
    e1=[-x for x in V1]
    e2num=S((1,M(V1,V1)),(1,V2))          # 2*e2
    assert all(x%2==0 for x in e2num), "e2 not in Z[zeta]"
    e2=[x//2 for x in e2num]
    res={'n':n,'e1':e1,'e2':e2}
    if kmax>=3:
        V3=V[2]
        # e3 = (-V1^3 - 3 V1 V2 - 2 V3)/6
        t=S((-1,M(V1,V1,V1)),(-3,M(V1,V2)),(-2,V3))
        assert all(x%6==0 for x in t), "e3 not integral"
        e3=[x//6 for x in t]
        want = [(-p if p%4==3 else p)*x for x in e1]
        res['e3_ok']=(e3==want); res['e3']=e3
    if kmax>=4:
        V4=V[3]
        # e4 = (V1^4 + 6 V1^2 V2 + 3 V2^2 + 8 V1 V3 + 6 V4)/24
        t=S((1,M(V1,V1,V1,V1)),(6,M(V1,V1,V2)),(3,M(V2,V2)),(8,M(V1,V[2])),(6,V4))
        assert all(x%24==0 for x in t), "e4 not integral"
        e4=[x//24 for x in t]
        want=[p*p]+[0]*(n-2)
        res['e4_ok']=(e4==want); res['e4']=e4
    return res

if __name__=="__main__":
    p=int(sys.argv[1]); kmax=int(sys.argv[2])
    print(f"p={p} kmax={kmax}")
    r=run(p,kmax)
    n=r['n']
    print("  n =",n," (n-1)/6 =",(n-1)//6)
    print("  e1 =",r['e1'][:8],"...")
    print("  e2 =",r['e2'][:8],"...")
    if 'e3_ok' in r: print("  FORCED e3 = %sp*e1 : %s"%('-' if p%4==3 else '+', r['e3_ok']))
    if 'e4_ok' in r: print("  FORCED e4 = p^2      :",r['e4_ok'], " e4 =",r['e4'][:4])
