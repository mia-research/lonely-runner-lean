import random
def nm(p): x,y=p; return x*x-x*y+y*y
def mul(a,b):
    (x,y),(c,d)=a,b; return (x*c-y*d, x*d+y*c-y*d)
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def rnd(p,N):           # nearest integer to p/N, exact (round half up)
    q=p//N; r=p-q*N
    return q+1 if 2*r>=N else q
def divround(a,b):
    (x,y)=a;(c,d)=b;N=nm(b);cc=(c-d,-d);px,py=mul((x,y),cc)
    return (rnd(px,N),rnd(py,N))
def zgcd(a,b):
    while nm(b)!=0:
        q=divround(a,b);a,b=b,sub(a,mul(q,b))
    return a
def units():
    base=[(1,0)];p=(1,0)
    for _ in range(2): p=(-p[1],p[0]-p[1]);base.append(p)
    return base+[(-a,-b) for a,b in base]
U=units()
def primary(p):
    for u in U:
        r=mul(p,u)
        if r[0]%3==2 and r[1]%3==0: return r
def cru(l):
    for _ in range(500):
        g=random.randrange(2,l);s=pow(g,(l-1)//3,l)
        if s!=1 and (s*s+s+1)%l==0: return s
def sextic28(pp,l):
    x,y=pp;w0=(-x*pow(y,-1,l))%l
    if (w0*w0+w0+1)%l!=0: w0=(-1-w0)%l
    zeta=(-w0*w0)%l;val=pow(28%l,(l-1)//6,l)
    return next(j for j in range(6) if pow(zeta,j,l)==val)
z6={0:(1,0),1:(1,1),2:(0,1),3:(-1,0),4:(-1,-1),5:(0,-1)}
def a_cm(l):
    s=cru(l);pi=zgcd((l,0),(-s,1));pp=primary(pi)
    chi=z6[(5*sextic28(pp,l)+3)%6];fro=mul(chi,pp)
    return 2*fro[0]-fro[1]
def isprime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in(1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

