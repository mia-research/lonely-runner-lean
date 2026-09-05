import random
# ---------- fully independent brute-force point count a_l for y^2=x^3+7 ----------
def a_brute(l):
    qr=[0]*l
    for i in range(l): qr[(i*i)%l]+=1
    cnt=1
    for x in range(l): cnt+=qr[(x*x*x+7)%l]
    return l+1-cnt

# ---------- thread-A closed form a_l (independent of point counts) ----------
def mulw(p): x,y=p; return (-y,x-y)
def units():
    b=[(1,0)];p=(1,0)
    for _ in range(2): p=mulw(p); b.append(p)
    return b+[(-a,-c) for a,c in b]
U=units()
def mul(a,b):
    (x,y),(c,d)=a,b; return (x*c-y*d,x*d+y*c-y*d)
def primary(p):
    for u in U:
        r=mul(p,u)
        if r[0]%3==2 and r[1]%3==0: return r
def nm(p): x,y=p; return x*x-x*y+y*y
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def rnd(p,N):
    q=p//N; r=p-q*N
    return q+1 if 2*r>=N else q
def divround(a,b):
    (x,y)=a;(c,d)=b;N=nm(b);cc=(c-d,-d);px,py=mul((x,y),cc)
    return (rnd(px,N),rnd(py,N))
def zgcd(a,b):
    while nm(b)!=0:
        q=divround(a,b);a,b=b,sub(a,mul(q,b))
    return a
def cru(l):
    for _ in range(500):
        g=random.randrange(2,l);s=pow(g,(l-1)//3,l)
        if s!=1 and (s*s+s+1)%l==0: return s
z6={0:(1,0),1:(1,1),2:(0,1),3:(-1,0),4:(-1,-1),5:(0,-1)}
def sext28(pp,l):
    x,y=pp;w0=(-x*pow(y,-1,l))%l
    if (w0*w0+w0+1)%l!=0: w0=(-1-w0)%l
    zeta=(-w0*w0)%l;val=pow(28%l,(l-1)//6,l)
    return next(j for j in range(6) if pow(zeta,j,l)==val)
def a_formula(l):
    s=cru(l);pp=primary(zgcd((l,0),(-s,1)))
    chi=z6[(5*sext28(pp,l)+3)%6]
    fro=mul(chi,pp); return 2*fro[0]-fro[1]
def sympr(n): return n>1 and all(n%p for p in range(2,int(n**.5)+1))

# ===== AUDIT 1: thread A, HELD-OUT brute vs formula on [3001,5000] (never fit) =====
print("=== AUDIT 1: thread A closed-form a_l vs brute point count, HELD-OUT primes 3001-5000 ===")
mism=[]; nchk=0; nzero_ok=0
for l in range(3001,5000):
    if not sympr(l) or l in (2,3,7): continue
    ab=a_brute(l); nchk+=1
    if l%3==2:
        if ab!=0: mism.append(('inert nonzero',l,ab))
        else: nzero_ok+=1
    else:
        af=a_formula(l)
        if af!=ab: mism.append((l,af,ab))
print(f"  primes checked: {nchk}; inert(=2mod3) a_l=0 confirmed: {nzero_ok}; mismatches: {len(mism)}")
for x in mism[:8]: print("   MISMATCH",x)

# ===== AUDIT 2: thread B, closure density from BRUTE counts only =====
print("\n=== AUDIT 2: thread B amicable closure via BRUTE point counts (independent of thread A) ===")
X=25000
sieve=bytearray([1])*(X+1); sieve[0]=sieve[1]=0
for i in range(2,int(X**.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
def isp(n):
    if n<2: return False
    if n<=X: return sieve[n]==1
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
den=0; closed=0; fixed=0; twocyc=0
for l in range(11,X):
    if sieve[l]!=1 or l%3!=1: continue
    ab=a_brute(l); n=l+1-ab
    if n<=7 or n in (2,3,7) or not isp(n): continue
    den+=1
    En = n+1 if n%3==2 else n+1-a_brute(n)
    if En==l:
        closed+=1
        if n==l: fixed+=1
        else: twocyc+=1
import math
for lbl,c in [("all closures",closed),("2-cycles only",twocyc)]:
    r=c/den; se=math.sqrt(r*(1-r)/den)
    print(f"  {lbl:15}: {c}/{den} = {r:.4f} +/- {se:.4f}")
print(f"  fixed points (l=n): {fixed};  13/50={13/50:.4f}")

# ===== AUDIT 3: thread C three-term ASD with BRUTE a_l =====
print("\n=== AUDIT 3: thread C three-term ASD  b_{l^2}-a_l b_l + l mod l^2, BRUTE a_l ===")
import math as _m
def b_(mm): return 7**((mm-1)//6)*_m.comb((mm-1)//2,(mm-1)//6)
allzero=True; l3=[]
for l in [13,19,31,37,43,61,67,73,79,97,103,109]:
    ab=a_brute(l)
    asd=b_(l*l)-ab*b_(l)+l
    if asd%(l*l)!=0: allzero=False; print("   FAIL mod l^2 at",l)
    if asd%(l**3)==0: l3.append(l)
print(f"  three-term ASD == 0 mod l^2 at all tested split primes: {allzero}")
print(f"  l^3-upgrades (== 0 mod l^3): {l3}   (P2 recorded {{37,61}})")

# ===== AUDIT 4: uniqueness of chi factorization exponents (e1,e2) =====
print("\n=== AUDIT 4: is the (e1,e2)=(5,1) local factorization UNIQUE? ===")
def dlog7(r): return next(j for j in range(6) if pow(3,j,7)==r%7)
from collections import defaultdict
dat=[]
for l in range(11,4000):
    if not sympr(l) or l%3!=1 or l in(2,3,7): continue
    s=cru(l);pp=primary(zgcd((l,0),(-s,1)));x,y=pp
    m=(5*sext28(pp,l)+3)%6
    dat.append(((x%4,y%4), m, dlog7((x+2*y)%7), dlog7((x+4*y)%7)))
works=[]
for e1 in range(6):
    for e2 in range(6):
        cls=defaultdict(set)
        for key,m,k1,k2 in dat: cls[key].add((m-e1*k1-e2*k2)%6)
        if all(len(v)==1 for v in cls.values()): works.append((e1,e2))
print("  (e1,e2) pairs giving a valid mod-4 factorization:", works)
print("DONE")
