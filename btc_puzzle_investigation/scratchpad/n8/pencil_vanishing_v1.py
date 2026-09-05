"""
N8 core mechanism test.  Exact integers only.

For R in E(F_p), the effective F_p-rational degree-2 divisors D with sum(D) = R are exactly the
fibres of phi_R : E -> P^1 given by the linear system |(R)+(O)|  --  there are p+1 of them.
Each is either  {P,P'} both in E(F_p)  (split),  {Q, Frob Q}  with Q in E(F_p^2)\E(F_p)  (inert),
or the special divisor (O)+(R).

Norm of y along the fibre:
  split : y_P * y_P'   in F_p        -> chi2(y_P)*chi2(y_P')
  inert : y_Q * y_Q^p = N(y_Q)       -> chi2(N(z)) = z^((p^2-1)/2) = chi2^{(2)}(z)   [checked]
  (O)+(R): y has a pole -> contributes 0

TEST:      H(R) := Sp(R) + I(R)  ==  0   for every R != O ?
(this is the record's  "sum_lambda chi_2(G_R(lambda)) = 0",  the core of #26 / P19)
plus the count identity  #split + #inert + 1 == p+1.

ARMS:  n ODD (j=0 and non-j=0)  vs  n EVEN (control -- must fail).
"""
import sys

def leg(a, p):
    a %= p
    return 0 if a == 0 else (1 if pow(a, (p-1)//2, p) == 1 else -1)

def pts(p, A, B):
    return [(x, y) for x in range(p) for y in range(p) if (y*y - (x*x*x + A*x + B)) % p == 0]

def add(P, Q, p, A):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1 == x2 and (y1+y2) % p == 0: return None
    lam = ((3*x1*x1+A)*pow(2*y1,-1,p) if P == Q else (y2-y1)*pow(x2-x1,-1,p)) % p
    x3 = (lam*lam - x1 - x2) % p
    return (x3, (lam*(x1-x3) - y1) % p)
def neg(P, p): return None if P is None else (P[0], (-P[1]) % p)

# ---- F_{p^2} = F_p[t]/(t^2 - r) ----
def m2(a,b,p,r): return ((a[0]*b[0] + r*a[1]*b[1]) % p, (a[0]*b[1] + a[1]*b[0]) % p)
def s2(a,b,p):   return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)
def n2(a,p):     return ((-a[0]) % p, (-a[1]) % p)
def i2(a,p,r):
    d = pow((a[0]*a[0] - r*a[1]*a[1]) % p, -1, p)
    return (a[0]*d % p, (-a[1])*d % p)
def pw2(a,e,p,r):
    R=(1,0)
    while e:
        if e&1: R=m2(R,a,p,r)
        a=m2(a,a,p,r); e>>=1
    return R
def add2(P,Q,p,A,r):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and s2(y1,y2,p)==(0,0): return None
    if P==Q:
        xx=m2(x1,x1,p,r); num=s2((3*xx[0]%p,3*xx[1]%p),(A,0),p); den=(2*y1[0]%p,2*y1[1]%p)
    else:
        num=s2(y2,n2(y1,p),p); den=s2(x2,n2(x1,p),p)
    lam=m2(num,i2(den,p,r),p,r)
    x3=s2(s2(m2(lam,lam,p,r),n2(x1,p),p),n2(x2,p),p)
    return (x3, s2(m2(lam,s2(x1,n2(x3,p),p),p,r),n2(y1,p),p))
def frob(P,p):
    if P is None: return None
    (a,b),(c,d)=P
    return ((a,(-b)%p),(c,(-d)%p))

def run(p,A,B,tag):
    E = pts(p,A,B); n = len(E)+1
    r = next(u for u in range(2,p) if leg(u,p)==-1)
    # E(F_p^2)
    sq={}
    for y0 in range(p):
        for y1 in range(p): sq.setdefault(m2((y0,y1),(y0,y1),p,r),[]).append((y0,y1))
    E2=[]
    for x0 in range(p):
        for x1 in range(p):
            x=(x0,x1); x3=m2(m2(x,x,p,r),x,p,r)
            rhs=s2(s2(x3,(A*x0%p,A*x1%p),p),(B,0),p)
            for y in sq.get(rhs,()): E2.append((x,y))
    inF=lambda Q: Q[0][1]==0 and Q[1][1]==0
    E2only=[Q for Q in E2 if not inF(Q)]
    EXP2=(p*p-1)//2

    bad=[]; badcount=[]
    for R in E:                                  # R != O
        # split (unordered), both != O
        Sp=0; nsplit=0; seen=set()
        for P in E:
            Pp = add(R, neg(P,p), p, A)          # P' = R - P
            if Pp is None: continue              # excludes the divisor (O)+(R)
            key=tuple(sorted([P,Pp]))
            if key in seen: continue
            seen.add(key); nsplit+=1
            Sp += leg(P[1],p)*leg(Pp[1],p)
        # inert
        I=0; ninert=0
        for Q in E2only:
            Nm = add2(Q, frob(Q,p), p, A, r)
            Rq = None if Nm is None else (Nm[0][0], Nm[1][0])
            if Rq == R:
                ninert+=1
                I += 1 if pw2(Q[1],EXP2,p,r)==(1,0) else -1
        assert ninert%2==0
        I//=2; ninert//=2
        if Sp-I != 1: bad.append((R,Sp,I,Sp-I))
        if nsplit+ninert+1 != p+1: badcount.append((R,nsplit,ninert))
    print(f"{tag} p={p:3d} A={A} B={B} n={n:3d} ({'ODD ' if n%2 else 'EVEN'})  "
          f"Sp-I==1 for {len(E)-len(bad)}/{len(E)} R!=O   count p+1 ok:{len(badcount)==0}"
          + ("" if not bad else f"   e.g. {bad[:2]}"), flush=True)

if __name__=="__main__":
    print("ARM 1 -- n ODD, j=0")
    for (p,A,B) in [(11,0,4),(13,0,1),(17,0,2),(19,0,3),(23,0,5)]:
        if (len(pts(p,A,B))+1)%2==1: run(p,A,B,"  j=0   ")
    print("ARM 2 -- n ODD, non-j=0")
    for (p,A,B) in [(11,1,1),(13,2,3),(17,1,5),(19,3,1),(23,1,4),(29,2,1),(31,5,2)]:
        if (len(pts(p,A,B))+1)%2==1: run(p,A,B,"  nonj0 ")
    print("ARM 3 -- n EVEN (control: must FAIL)")
    for (p,A,B) in [(11,1,6),(13,1,1),(17,2,2),(19,1,2),(23,3,3)]:
        if (len(pts(p,A,B))+1)%2==0: run(p,A,B,"  even-n")
