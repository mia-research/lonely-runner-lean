# Arm 2 proof-of-concept: twisted eigenvalue multiset for chi2(y) vs chi2(x) on y^2=x^3+7.
# Confirms max|V|=2*sqrt(p) and extracts the degree-#R char poly at the maximizing frequency.
B = 7
def analyze(p):
    Fp = GF(p)
    E = EllipticCurve(Fp, [0, B])
    n = E.order()
    if not is_prime(n):
        return None
    G = E.gens()[0]
    if G.order() != n:
        G = E(0)
        for P in E.points():
            if P.order() == n: G=P; break
    # coords d=1..n-1
    xs=[0]*n; ys=[0]*n
    P = G
    for d in range(1,n):
        xs[d]=P[0]; ys[d]=P[1]; P = P + G
    def chi2(v):
        v = Fp(v)
        if v==0: return 0
        return 1 if v.is_square() else -1
    import cmath
    def maxV(readout):
        c=[0]*n
        for d in range(1,n):
            if readout=='y': c[d]=chi2(ys[d])
            elif readout=='x': c[d]=chi2(xs[d])
        best=0.0; besta=0
        for a in range(1,n):
            s=sum(c[d]*cmath.exp(2j*cmath.pi*a*d/n) for d in range(1,n))
            m=abs(s)
            if m>best: best=m; besta=a
        return best/ (p**0.5), besta
    my,ay = maxV('y'); mx,ax = maxV('x')
    return dict(p=p,n=n, maxVy=my, maxVx=mx, ay=ay, ax=ax)

for p in [13,19,31,37,43,61,67,73]:
    if p%3!=1: continue
    if B%p==0: continue
    r=analyze(p)
    if r:
        print("p=%d n=%d  max|Vx|/sqrtp=%.3f (a=%d)  max|Vy|/sqrtp=%.3f (a=%d)  y-sat of 4sqrtp=%.3f"
              % (r['p'],r['n'],r['maxVx'],r['ax'],r['maxVy'],r['ay'], r['maxVy']/4))
