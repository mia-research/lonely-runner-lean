import itertools, math
import sympy as sp

# ---- field machinery (reused) ----
def find_irreducible(p, deg):
    if deg == 2:
        for s in range(1, p):
            if pow(s, (p-1)//2, p) != 1:
                return ('shift', s)
    if deg == 3:
        if (p-1) % 3 == 0:
            for s in range(1, p):
                if not any(pow(x,3,p)==s for x in range(p)):
                    return ('shift', s)
        for c1 in range(0, p):
            for c0 in range(1, p):
                if not any((pow(x,3,p) + c1*x + c0) % p == 0 for x in range(p)):
                    return ('trinomial', c1, c0)
    raise RuntimeError

class FF:
    def __init__(self,p,deg,reduce_map):
        self.p=p; self.deg=deg; self.reduce_map=reduce_map
    def one(self):
        e=[0]*self.deg; e[0]=1; return tuple(e)
    def from_int(self,a):
        e=[0]*self.deg; e[0]=a%self.p; return tuple(e)
    def add(self,a,b): return tuple((x+y)%self.p for x,y in zip(a,b))
    def mul(self,a,b):
        p=self.p; deg=self.deg
        res=[0]*(2*deg-1)
        for i,ai in enumerate(a):
            if ai==0: continue
            for j,bj in enumerate(b):
                if bj==0: continue
                res[i+j]=(res[i+j]+ai*bj)%p
        out=list(res[:deg])
        for k in range(len(res)-1, deg-1, -1):
            c = res[k]
            if c:
                shift = k - deg
                for idx, rc in enumerate(self.reduce_map):
                    tgt = idx + shift
                    if tgt < deg:
                        out[tgt] = (out[tgt] + c*rc) % p
                    else:
                        res[tgt] = (res[tgt] + c*rc) % p
        return tuple(out)
    def pw(self,a,k):
        r=self.one(); b=a
        while k>0:
            if k&1: r=self.mul(r,b)
            b=self.mul(b,b); k>>=1
        return r
    def is_zero(self,a): return all(c==0 for c in a)
    def elements(self):
        for tup in itertools.product(range(self.p),repeat=self.deg): yield tup

class F1:
    def __init__(self,p): self.p_=p
    def one(self): return (1,)
    def from_int(self,a): return (a%self.p_,)
    def add(self,a,b): return ((a[0]+b[0])%self.p_,)
    def mul(self,a,b): return ((a[0]*b[0])%self.p_,)
    def pw(self,a,k): return (pow(a[0],k,self.p_),)
    def is_zero(self,a): return a[0]%self.p_==0
    def elements(self):
        for x in range(self.p_): yield (x,)

def make_field(p, deg):
    if deg == 1: return F1(p)
    spec = find_irreducible(p, deg)
    if spec[0]=='shift':
        reduce_map=[spec[1]]+[0]*(deg-1)
    else:
        _,c1,c0=spec; reduce_map=[(-c0)%p,(-c1)%p,0]
    return FF(p,deg,reduce_map)

def count_pts(field,N,const,quartic):
    g=4 if quartic else 2; gg=math.gcd(g,N); exp=N//gg
    b=field.from_int(const); cnt=1
    for x in field.elements():
        x3=field.mul(field.mul(x,x),x)
        rhs=field.add(x3,b)
        if field.is_zero(rhs): cnt+=1; continue
        if field.pw(rhs,exp)==field.one(): cnt+=gg
    return cnt

def c2_of_a(p, a):
    """Middle coeff of char poly X^4 + c2 X^2 + p^2 for A_new of w^4=x^3+a (p=7 mod 12)."""
    f1=make_field(p,1); f2=make_field(p,2)
    C1=count_pts(f1,p-1,a,True); E1=count_pts(f1,p-1,a,False)
    C2=count_pts(f2,p*p-1,a,True); E2=count_pts(f2,p*p-1,a,False)
    a1=E1-C1; a2=E2-C2
    e1=a1; e2=(a1*e1-a2)//2
    return e1, e2

print("="*60)
print("§1: c2(a) universal law at p in {43,67,79}")
print("="*60)
for p in [43, 67, 79]:
    assert p % 12 == 7
    res_c2=set(); nonres_c2=set(); nres=0; nnon=0
    e1_all=set()
    for a in range(1,p):
        is_cr = pow(a,(p-1)//3,p)==1
        e1,e2 = c2_of_a(p,a)
        e1_all.add(e1)
        if is_cr: res_c2.add(e2); nres+=1
        else: nonres_c2.add(e2); nnon+=1
    print(f"\np={p}: cubic residues: {nres} elems, c2 values = {res_c2}  (doc: -2p={-2*p})")
    print(f"      cubic non-res : {nnon} elems, c2 values = {nonres_c2}  (doc: +p={p})")
    print(f"      all e1 (linear coeff) = {e1_all}  (expect {{0}} for supersingular)")

print("\n" + "="*60)
print("§1 eigenvalue root-orders (vs corrected memory: nonres -> [3,3,6,6])")
print("="*60)
u = sp.symbols('u')
for (label, cpoly) in [("residues  m=-2: u^4-2u^2+1", u**4-2*u**2+1),
                        ("non-res   m=+1: u^4+u^2+1", u**4+u**2+1)]:
    fac = sp.factor_list(cpoly)
    roots = sp.roots(cpoly)
    orders=[]
    for r,mult in roots.items():
        # order = smallest k with r^k=1
        k=1; val=r
        while sp.simplify(val-1)!=0 and k<50:
            k+=1; val=sp.simplify(val*r)
        orders += [k]*mult
    print(f"  {label}: root orders {sorted(orders)}  factor={fac}")

print("\n" + "="*60)
print("§2: degree-10 minimal polynomial of V(1) at p=43, n=31")
print("="*60)
p=43; n=31
# Build E(F_43), find generator, order points by discrete log, compute
# V(a) = sum_{d=1}^{n-1} chi_2(y_d) * e_n(a*d)   where y_d is y-coord of [d]G
# chi_2 = Legendre symbol of y mod p; e_n = exp(2pi i /n)

def modinv(a,m): return pow(a,-1,m)
def padd(P,Q,p,A=0):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q:
        lam=(3*x1*x1+A)*modinv(2*y1,p)%p
    else:
        lam=(y2-y1)*modinv((x2-x1)%p,p)%p
    x3=(lam*lam-x1-x2)%p; y3=(lam*(x1-x3)-y1)%p
    return (x3,y3)

# find a generator G of E(F_43): y^2=x^3+7? No -- the cover uses a, but V(a) is on E(F_p).
# The doc's E is the genus-1 quotient E_a: y^2 = x^3 + a with a=1 here? It says n=31 for E(F_43).
# secp curve is b=7 but at p=43 we just need an elliptic curve of prime order 31.
# Try y^2 = x^3 + 7 over F_43:
def curve_points(p,b,A=0):
    pts=[]
    for x in range(p):
        rhs=(x*x*x+A*x+b)%p
        for y in range(p):
            if (y*y)%p==rhs: pts.append((x,y))
    return pts

for btest in range(1,43):
    pts=curve_points(p,btest)
    order=len(pts)+1
    if order==31:
        b_used=btest
        break
print(f"  Using E: y^2 = x^3 + {b_used} over F_43, #E = 31 (prime)")

# find generator
pts=curve_points(p,b_used)
def scalar(k,G,p,A=0):
    R=None
    for _ in range(k): R=padd(R,G,p,A)
    return R
G=pts[0]
# list multiples [d]G for d=1..30
mult=[None]*(n)
cur=None
for d in range(1,n):
    cur=padd(cur,G,p)
    mult[d]=cur

def legendre(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1

# V(a) = sum_{d=1}^{n-1} chi_2(y_d) e_n(a d), exact in CyclotomicField
zeta = sp.exp(2*sp.pi*sp.I/n)
def V(a):
    s=0
    for d in range(1,n):
        yd=mult[d][1]
        s += legendre(yd,p) * zeta**((a*d)%n)
    return sp.simplify(s)

# Galois orbit of V(1): conjugates V(g) for g in (Z/31)^*, then take distinct values
# Build minimal polynomial as product over distinct conjugates
vals=[]
seen=[]
for a in range(1,n):
    va=sp.nsimplify(sp.expand_complex(V(a)))
    vals.append(va)
# distinct
Tsym=sp.symbols('T')
distinct=[]
for v in vals:
    if not any(sp.simplify(v-d)==0 for d in distinct):
        distinct.append(v)
print(f"  #distinct conjugate values of V = {len(distinct)}  (doc claims 10)")

minpoly=1
for v in distinct:
    minpoly*= (Tsym - v)
minpoly=sp.expand(minpoly)
minpoly=sp.nsimplify(minpoly)
minpoly=sp.simplify(minpoly)
print(f"  minimal polynomial P(T) =")
poly_p = sp.Poly(minpoly, Tsym)
print("   ", poly_p.as_expr())
print(f"\n  Document claims: T^10 + 155T^8 + 6138T^6 + 92070T^4 + 555861T^2 + 1060975")
doc_poly = Tsym**10 + 155*Tsym**8 + 6138*Tsym**6 + 92070*Tsym**4 + 555861*Tsym**2 + 1060975
print(f"  Match: {sp.simplify(minpoly - doc_poly)==0}")
print(f"  Irreducible over Q: {sp.Poly(doc_poly,Tsym).is_irreducible}")
