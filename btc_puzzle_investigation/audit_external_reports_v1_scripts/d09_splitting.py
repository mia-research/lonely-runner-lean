# ---- Doc 9: oblique-shear splitting. E':y^2=x^3+x+3 over F_43, n=47. ----
# Test: for odd-parity coord (cases 1,2) the 23 values V(a)^2 lie in F_ell for ell = +-1 mod 47
#       (=> Q23 splits into 23 linear factors). For mixed-parity (case3) they do NOT.
from sympy import legendre_symbol
p=43; A=1; Bc=3
def add(P,Q,p,A):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return None
    if P==Q: m=(3*x1*x1+A)*pow(2*y1,-1,p)%p
    else: m=(y2-y1)*pow((x2-x1)%p,-1,p)%p
    x3=(m*m-x1-x2)%p;y3=(m*(x1-x3)-y1)%p;return(x3,y3)
pts=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-(x**3+A*x+Bc))%p==0]
order=len(pts)
# find generator order 47
G=None
for Q in pts:
    if Q is None:continue
    R=Q;k=1
    while R is not None: R=add(R,Q,p,A);k+=1
    if k==47: G=Q;break
n=47
orb={}
R=None
for d in range(1,47):
    R=add(R,G,p,A); orb[d]=R
print("|E'(F_43)|=",order," generator",G," order 47")

def w_case(d,case):
    x,y=orb[d]
    if case==1: return y%p
    if case==2: return (y*(x*x+5))%p
    if case==3: return (y+5*x)%p
def chi2(v):
    v%=p
    return 0 if v==0 else int(legendre_symbol(v,p))

# F_{ell^2} arithmetic to host 47th roots of unity; test membership in F_ell via z^ell==z
def make_field(ell):
    # find nonresidue
    nr=next(c for c in range(2,ell) if pow(c,(ell-1)//2,ell)==ell-1)
    def mul(u,v):
        a,b=u;c,d=v;return((a*c+b*d*nr)%ell,(a*d+b*c)%ell)
    def add2(u,v):return((u[0]+v[0])%ell,(u[1]+v[1])%ell)
    def powe(u,e):
        r=(1,0)
        while e>0:
            if e&1:r=mul(r,u)
            u=mul(u,u);e>>=1
        return r
    return nr,mul,add2,powe
def find_zeta47(ell):
    nr,mul,add2,powe=make_field(ell)
    m=ell*ell-1
    assert m%47==0
    import random
    while True:
        u=(random.randrange(ell),random.randrange(ell))
        if u==(0,0):continue
        z=powe(u,m//47)
        if z!=(1,0): return z,nr,mul,add2,powe

def test(case,ell):
    z,nr,mul,add2,powe=find_zeta47(ell)
    # V(a)=sum chi2(w_d) * z^{a d}; compute in F_{ell^2}
    def V(a):
        s=(0,0)
        for d in range(1,47):
            c=chi2(w_case(d,case))%ell
            term=powe(z,(a*d)%47)
            s=add2(s,(term[0]*c%ell,term[1]*c%ell))
        return s
    inF=0
    for a in range(1,24):
        Va=V(a); Wa=mul(Va,Va)
        # in F_ell iff imag part 0
        if Wa[1]==0: inF+=1
    return inF
for ell,cls in [(283,'+1'),(281,'-1')]:
    print(f"\nell={ell} (class {cls} mod 47):")
    for case in [1,2,3]:
        got=test(case,ell)
        print(f"  case {case}: {got}/23 values V(a)^2 in F_ell  -> {'SPLITS [1^23]' if got==23 else 'does NOT split completely'}")
