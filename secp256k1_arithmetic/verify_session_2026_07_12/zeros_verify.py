import random, math
import mpmath as mp
# --- inlined helpers from amicable_sweep.py ---
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

# --- end helpers ---
mp.mp.dps=20
N=21168; rootN=mp.sqrt(N); c=2*mp.pi/rootN
def ap(p):
    if p in (2,3,7): return 0
    if p%3==2: return 0
    return a_cm(p)
M=900
spf=list(range(M+1))
for i in range(2,int(M**.5)+1):
    if spf[i]==i:
        for j in range(i*i,M+1,i):
            if spf[j]==j: spf[j]=i
apc={}
def a_prime(p):
    if p not in apc: apc[p]=ap(p)
    return apc[p]
a=[0]*(M+1); a[1]=1
def a_pk(p,k):
    vals=[1,a_prime(p)]; bad=p in(2,3,7)
    for e in range(2,k+1):
        vals.append(0 if bad else a_prime(p)*vals[-1]-p*vals[-2])
    return vals[k]
for n in range(2,M+1):
    p=spf[n]; m=n; k=0
    while m%p==0: m//=p; k+=1
    a[n]=a_pk(p,k)*a[m]
cn=[None]+[c*n for n in range(1,M+1)]
an=[mp.mpf(x) for x in a]
def Z(t):
    s=mp.mpc(0); sexp=1+mp.mpc(0,t)
    for n in range(1,M+1):
        x=cn[n]
        if x>45 and an[n]==0: continue
        s+= an[n]*mp.power(x,-sexp)*mp.gammainc(sexp,x)
    return 2*s.real
# fine grid + strict in-bracket bisection (no findroot escape)
step=mp.mpf('0.02'); T=16
prev_t=step; prev=Z(prev_t); zeros=[]
t=prev_t
while t<T:
    t2=t+step; v2=Z(t2)
    if prev*v2<0:
        z=mp.findroot(Z, (t, t2), solver='bisect', tol=mp.mpf(10)**-24)
        if t<=z<=t2: zeros.append(z)
    prev=v2; t=t2
# dedupe within 1e-6
clean=[]
for z in zeros:
    if not clean or abs(z-clean[-1])>mp.mpf('1e-6'): clean.append(z)
print('L(1)=',mp.nstr(Z(0)*c,15))
print('distinct zeros gamma (arith s=1+i*gamma), to 1e-6:')
for i,z in enumerate(clean,1):
    print(f'  gamma_{i} = {mp.nstr(z,12)}   |Z|={mp.nstr(abs(Z(z)),2)}')
print('count:',len(clean))
