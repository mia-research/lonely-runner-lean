#!/usr/bin/env python3
# N8 / M21 probe: structure of  f = h2 - h1*h1  (convolution over Z/n).
# h1[d] = chi2(y_P) for P=[d]G in E(F_p);  h2[d] = sum over Q in E(F_p^2) with Tr(Q)=[d]G of chi2^{(2)}(y_Q).
# Claim under test: fhat(a) = -2*leg*p for all a != 0, leg = chi2(-1).
B=7
def leg(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
def tonelli(a,p):
    a%=p
    if a==0: return 0
    if p%4==3: return pow(a,(p+1)//4,p)
    q=p-1; s=0
    while q%2==0: q//=2; s+=1
    z=2
    while leg(z,p)!=-1: z+=1
    m,c,t,r=s,pow(z,q,p),pow(a,q,p),pow(a,(q+1)//2,p)
    while t!=1:
        i,t2=0,t
        while t2!=1: t2=t2*t2%p; i+=1
        b=pow(c,1<<(m-i-1),p); m,c,t,r=i,b*b%p,t*b%b*b%p if False else t*b%p*b%p,r*b%p
    return r
def pts(p):
    P=[]
    for x in range(p):
        r=(x*x%p*x+B)%p
        if leg(r,p)==1:
            y=tonelli(r,p)
            P.append((x,y)); P.append((x,(-y)%p))
        elif r==0: P.append((x,0))
    return P
def eadd(Pt,Q,p):
    if Pt is None: return Q
    if Q is None: return Pt
    x1,y1=Pt; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if Pt==Q: lam=(3*x1*x1)%p*pow(2*y1,p-2,p)%p
    else: lam=(y2-y1)%p*pow((x2-x1)%p,p-2,p)%p
    x3=(lam*lam-x1-x2)%p; return (x3,(lam*(x1-x3)-y1)%p)
class F2:
    """F_p^2 = F_p[t]/(t^2-u), u a non-residue."""
    def __init__(s,p):
        s.p=p; u=2
        while leg(u,p)!=-1: u+=1
        s.u=u
    def mul(s,a,b):
        p,u=s.p,s.u
        return ((a[0]*b[0]+u*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
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
    def frob(s,a): return (a[0],(-a[1])%s.p)      # t -> -t
def eadd2(F,P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and F.add(y1,y2)==(0,0): return None
    if P==Q:
        num=F.mul((3,0),F.sq(x1)); lam=F.mul(num,F.inv(F.mul((2,0),y1)))
    else:
        lam=F.mul(F.sub(y2,y1),F.inv(F.sub(x2,x1)))
    x3=F.sub(F.sub(F.sq(lam),x1),x2)
    return (x3,F.sub(F.mul(lam,F.sub(x1,x3)),y1))

def run(p):
    P=pts(p); n=len(P)+1
    # generator
    G=None
    for pt in P:
        acc=None; k=0; seen=[]
        cur=None
        for i in range(1,n+1):
            cur=eadd(cur,pt,p)
            if cur is None: k=i; break
        if k==n: G=pt; break
    dl={}; cur=None
    for d in range(n):
        dl[cur]=d; cur=eadd(cur,G,p)
    h1=[0]*n
    for (x,y) in P:
        if y==0: continue
        h1[dl[(x,y)]]+=leg(y,p)
    F=F2(p); q=p*p; half=(q-1)//2
    sq={}
    for a in range(p):
        for b in range(p): sq[F.sq((a,b))]=(a,b)
    h2=[0]*n
    Bq=(B%p,0)
    for a in range(p):
        for b in range(p):
            x=(a,b); r=F.add(F.mul(F.sq(x),x),Bq)
            if r==(0,0): continue
            y=sq.get(r)
            if y is None: continue
            for yy in (y,F.neg(y)):
                if yy==(0,0): continue
                c=1 if F.pw(yy,half)==(1,0) else -1
                T=eadd2(F,(x,yy),(F.frob(x),F.frob(yy)))
                if T is None: d=0
                else:
                    assert T[0][1]==0 and T[1][1]==0
                    d=dl[(T[0][0],T[1][0])]
                h2[d]+=c
    conv=[0]*n
    for i in range(n):
        if h1[i]==0: continue
        for j in range(n): conv[(i+j)%n]+=h1[i]*h1[j]
    f=[h2[d]-conv[d] for d in range(n)]
    lg=leg(-1,p)
    return n,lg,h1,h2,conv,f

for p in (43,61,67,79,97):
    n,lg,h1,h2,conv,f=run(p)
    off=set(f[1:]); 
    print(f"p={p:3d} n={n:3d} leg={lg:+d} | f[0]={f[0]:5d} | f[d!=0] distinct={sorted(off)} | "
          f"f[0]-f[1]={f[0]-f[1]:5d}  (-2*leg*p={-2*lg*p:5d})  sum h1={sum(h1)} sum h2={sum(h2)}")
