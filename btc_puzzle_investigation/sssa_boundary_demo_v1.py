#!/usr/bin/env python3
"""
Grounding the lift analysis: run the SSSA / Smart p-adic-elliptic-log DLP attack and
show the EXACT boundary that walls secp256k1.
  - anomalous (#E(F_p)=p, char==order): the p-adic log linearizes -> d recovered.
  - non-anomalous (gcd(#E,p)=1, as secp): the SAME machine returns garbage.
This is the concrete face of "the amicable pair is characteristic-crossed anomalous":
the linearization exists only when the group order IS the characteristic; secp's
order n lives in the OTHER characteristic, unreachable without a char-0 lift = the DLP.
Exact integer arithmetic; projective group law over Z/p^2 (no division in the law).
Control: projective law verified against affine.
"""
import random

# ---- projective group law for Y^2 Z = X^3 + aXZ^2 + bZ^3 over Z/m (Cohen 1993) ----
def dbl(Pt,a,m):
    X,Y,Z=Pt
    if Z%m==0: return (0,1,0)
    W=(a*Z*Z+3*X*X)%m; S=(Y*Z)%m; B=(X*Y*S)%m; H=(W*W-8*B)%m
    X2=(2*H*S)%m; Y2=(W*(4*B-H)-8*Y*Y*S*S)%m; Z2=(8*S*S*S)%m
    return (X2%m,Y2%m,Z2%m)
def add(P1,P2,a,m):
    X1,Y1,Z1=P1; X2,Y2,Z2=P2
    if Z1%m==0: return P2
    if Z2%m==0: return P1
    U1=(Y2*Z1)%m; U2=(Y1*Z2)%m; V1=(X2*Z1)%m; V2=(X1*Z2)%m
    if (V1-V2)%m==0:
        return dbl(P1,a,m) if (U1-U2)%m==0 else (0,1,0)
    U=(U1-U2)%m; V=(V1-V2)%m; W=(Z1*Z2)%m
    A=(U*U*W-V*V*V-2*V*V*V2)%m
    X3=(V*A)%m; Y3=(U*(V*V*V2-A)-V*V*V*U2)%m; Z3=(V*V*V*W)%m
    return (X3%m,Y3%m,Z3%m)
def mul(k,Pt,a,m):
    R=(0,1,0)
    while k>0:
        if k&1: R=add(R,Pt,a,m)
        Pt=dbl(Pt,a,m); k>>=1
    return R

def order_Fp(a,b,p):
    cnt=1  # infinity
    for x in range(p):
        rhs=(x*x*x+a*x+b)%p
        cnt+=1+pow(rhs,(p-1)//2,p) if rhs else 1  # QR count via Legendre (+ the 0 case)
    # recompute cleanly:
    cnt=1
    for x in range(p):
        rhs=(x*x*x+a*x+b)%p
        if rhs==0: cnt+=1
        elif pow(rhs,(p-1)//2,p)==1: cnt+=2
    return cnt

def find_anomalous(plo,phi):
    import sympy
    for p in sympy.primerange(plo,phi):
        for b in range(1,12):
            for a in range(0,4):
                if (4*a**3+27*b*b)%p==0: continue
                if order_Fp(a,b,p)==p: return p,a,b
    return None

def sssa(a,b,p,order,Px,Py,Qx,Qy):
    """Recover d via the p-adic elliptic log using [order]-multiplication.
       Correct only when order==p (anomalous). Works mod p^4 to keep the formal
       parameter t=-X/Y to enough precision (t has v_p=1; V^3~p^3 needs > p^2)."""
    m=p**4
    def liftpt(x0,y0):
        # Hensel-lift y from mod p to mod m: Newton y <- y-(y^2-rhs)/(2y)
        rhs=(x0**3+a*x0+b)%m; y=y0%m
        prec=p
        while prec<m:
            prec*=prec
            y=(y-(y*y-rhs)*pow((2*y)%m,-1,m))%m
        assert (y*y-rhs)%m==0
        return (x0%m,y,1)
    Pt=liftpt(Px,Py); Qt=liftpt(Qx,Qy)
    Rp=mul(order,Pt,a,m); Rq=mul(order,Qt,a,m)
    def tparam(R):
        X,Y,Z=R
        return (-X*pow(Y%m,-1,m))%m   # t=-X/Y mod p^4 ; v_p(t) should be 1
    tp=tparam(Rp); tq=tparam(Rq)
    if tp%p!=0 or tq%p!=0:   # [order]P not in formal group => char ∤ order
        return None,(tp%p,tq%p)
    lp=(tp//p)%p; lq=(tq//p)%p
    if lp%p==0: return None,(tp,tq)
    d=(lq*pow(lp,p-2,p))%p
    return d,(tp,tq)

random.seed(1)
# ---- control: projective vs affine on a random curve ----
p=1009; a,b=2,3
def aff_add(P,Q):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return None
    if P==Q: s=(3*x1*x1+a)*pow(2*y1,p-2,p)%p
    else: s=(y2-y1)*pow((x2-x1)%p,p-2,p)%p
    x3=(s*s-x1-x2)%p;y3=(s*(x1-x3)-y1)%p;return(x3,y3)
# pick a point (brute-force a valid (x,y))
G0=None
for x0 in range(1,p):
    r=(x0**3+a*x0+b)%p
    for y0 in range(1,p):
        if (y0*y0)%p==r: G0=(x0,y0); break
    if G0: break
aff=None;proj=(0,1,0);ok=True
for k in range(1,20):
    aff=aff_add(aff,G0)
    proj=add(proj,(G0[0],G0[1],1),a,p)
    ax,ay=aff; PX,PY,PZ=proj; iz=pow(PZ,p-2,p)
    if (ax*1-PX*iz)%p!=0 or (ay-PY*iz)%p!=0: ok=False
print(f"[CONTROL] projective law == affine law over F_{p}: {ok}")

# ---- anomalous curve: SSSA should recover d ----
res=find_anomalous(50,400)
print(f"\nanomalous search -> p,a,b = {res}")
p,a,b=res
n=order_Fp(a,b,p)
print(f"  #E(F_{p}) = {n}  (== p ? {n==p}  => anomalous)")
# generator + secret
def apts():
    L=[]
    for x in range(p):
        r=(x**3+a*x+b)%p
        for y in range(p):
            if (y*y)%p==r: L.append((x,y))
    return L
pts=apts(); G=random.choice([q for q in pts if q[1]!=0])
d=random.randrange(2,p)
# Q=[d]G via affine
Q=None
for _ in range(d): Q=aff_add(Q,G)
rec,zs=sssa(a,b,p,n,G[0],G[1],Q[0],Q[1])
print(f"  secret d={d}; SSSA recovered = {rec}; match={rec==d}")

# ---- non-anomalous curve (gcd(#E,p)=1, like secp): SAME machine must FAIL ----
p2=1009; a2,b2=0,7   # y^2=x^3+7 over F_1009 (j=0, like secp)
n2=order_Fp(a2,b2,p2)
print(f"\nnon-anomalous (secp-shape) y^2=x^3+7 over F_{p2}: #E={n2}, gcd(#E,p)={__import__('math').gcd(n2,p2)}, anomalous? {n2==p2}")
pts2=[]
for x in range(p2):
    r=(x**3+a2*x+b2)%p2
    for y in range(p2):
        if (y*y)%p2==r: pts2.append((x,y))
# use a generator of prime order dividing n2
import sympy
fac=sorted(sympy.factorint(n2).items())
ell=fac[-1][0]  # largest prime factor
G2=None
for cand in pts2:
    R=None
    for _ in range(n2//ell): R=aff_add(R,cand)
    if R is not None: G2=R; break
d2=random.randrange(2,ell)
Q2=None
for _ in range(d2): Q2=aff_add(Q2,G2)
def aff_add2(P,Q):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p2==0:return None
    if P==Q: s=(3*x1*x1+a2)*pow(2*y1,p2-2,p2)%p2
    else: s=(y2-y1)*pow((x2-x1)%p2,p2-2,p2)%p2
    x3=(s*s-x1-x2)%p2;y3=(s*(x1-x3)-y1)%p2;return(x3,y3)
Q2=None
for _ in range(d2): Q2=aff_add2(Q2,G2)
rec2,zs2=sssa(a2,b2,p2,n2,G2[0],G2[1],Q2[0],Q2[1])
print(f"  order of G2 = {ell}; secret d2={d2} (mod {ell}); SSSA 'recovered' = {rec2}")
print(f"  => the p-adic log carries NO info about d when char ∤ order (the secp wall).")
