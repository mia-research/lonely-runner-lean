import sympy as sp

# §2: degree-10 minimal polynomial of V(1) at p=43, n=31, using integer arithmetic in Z[zeta_31].
p=43; n=31

def modinv(a,m): return pow(a,-1,m)
def padd(P,Q,p,A=0):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q: lam=(3*x1*x1+A)*modinv(2*y1,p)%p
    else: lam=(y2-y1)*modinv((x2-x1)%p,p)%p
    x3=(lam*lam-x1-x2)%p; y3=(lam*(x1-x3)-y1)%p
    return (x3,y3)

def curve_points(p,b,A=0):
    pts=[]
    for x in range(p):
        rhs=(x*x*x+A*x+b)%p
        for y in range(p):
            if (y*y)%p==rhs: pts.append((x,y))
    return pts

# find E over F_43 with prime order 31
b_used=None
for bt in range(1,43):
    if len(curve_points(p,bt))+1==31:
        b_used=bt; break
pts=curve_points(p,b_used)
print(f"E: y^2=x^3+{b_used} over F_43, #E=31")
G=pts[0]
mult=[None]*n; cur=None
for d in range(1,n):
    cur=padd(cur,G,p); mult[d]=cur

def legendre(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1

leg_y=[0]*n
for d in range(1,n):
    leg_y[d]=legendre(mult[d][1],p)

# Ring Z[zeta_31]: element = list of 31 ints (coeff of zeta^0..zeta^30), zeta^31=1.
def zero(): return [0]*n
def add(a,b): return [a[i]+b[i] for i in range(n)]
def sub(a,b): return [a[i]-b[i] for i in range(n)]
def mul(a,b):
    c=[0]*n
    for i in range(n):
        if a[i]==0: continue
        ai=a[i]
        for j in range(n):
            if b[j]==0: continue
            c[(i+j)%n]+=ai*b[j]
    return c
def to_int(a):
    # element is rational iff a[1..30] all equal; value = a[0]-a[1]
    if all(a[k]==a[1] for k in range(1,n)):
        return a[0]-a[1]
    return None

# V(a) = sum_{d=1}^{n-1} leg_y[d] * zeta^{(a d) mod n}
def V(a):
    v=zero()
    for d in range(1,n):
        v[(a*d)%n]+=leg_y[d]
    return v

# all conjugates
Vs=[V(a) for a in range(1,n)]
# distinct as ring elements: normalize (subtract v[0]-... ) -- compare via canonical form.
def canon(a):
    # subtract a[n-1]? better: reduce using 1+zeta+...+zeta^30=0 -> set representation with a[0..29], a[30]->-(sum)
    # canonical: subtract a[30] from every coord so coord 30 becomes 0
    s=a[n-1]
    return tuple(a[i]-s for i in range(n-1))
distinct=[]
seen=set()
for v in Vs:
    cv=canon(v)
    if cv not in seen:
        seen.add(cv); distinct.append(v)
print(f"#distinct conjugate values of V = {len(distinct)} (doc claims 10)")

# minimal poly = prod (T - V_i), coefficients in the ring; collect as list of ring elements
# poly represented as list of ring elements, index = power of T
poly=[ [1]+[0]*(n-1) ]  # constant poly 1
for v in distinct:
    newpoly=[zero() for _ in range(len(poly)+1)]
    for i,coef in enumerate(poly):
        # multiply coef by (T - v): T-part -> index i+1; -v part -> index i
        newpoly[i+1]=add(newpoly[i+1], coef)
        newpoly[i]=sub(newpoly[i], mul(coef,v))
    poly=newpoly

# extract integer coefficients
T=sp.symbols('T')
deg=len(poly)-1
coeffs_int=[]
ok=True
for i in range(deg+1):
    ci=to_int(poly[i])
    if ci is None:
        ok=False; coeffs_int.append(None)
    else:
        coeffs_int.append(ci)
print(f"All coefficients integer (Galois-invariant): {ok}")
expr=0
for i,ci in enumerate(coeffs_int):
    if ci is not None:
        expr+= ci*T**i
print("Computed minimal polynomial P(T):")
print("  ", sp.Poly(expr,T).as_expr() if ok else coeffs_int)

doc_poly = T**10 + 155*T**8 + 6138*T**6 + 92070*T**4 + 555861*T**2 + 1060975
print("\nDocument claims:")
print("  ", doc_poly)
if ok:
    print("Match:", sp.expand(expr-doc_poly)==0)
    print("Irreducible over Q:", sp.Poly(doc_poly,T).is_irreducible)
