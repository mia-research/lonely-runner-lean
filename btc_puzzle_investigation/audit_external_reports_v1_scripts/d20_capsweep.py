import numpy as np, math
from sympy import isprime, legendre_symbol, primerange
def orbit_ys(p,A,B):
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        x1,y1=P;x2,y2=Q
        if x1==x2 and (y1+y2)%p==0:return None
        if P==Q:m=(3*x1*x1+A)*pow(2*y1,-1,p)%p
        else:m=(y2-y1)*pow((x2-x1)%p,-1,p)%p
        x3=(m*m-x1-x2)%p;y3=(m*(x1-x3)-y1)%p;return(x3,y3)
    pts=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-(x**3+A*x+B))%p==0]
    N=len(pts)
    G=None
    for Q in pts:
        if Q is None:continue
        R=Q;k=1
        while R is not None:R=add(R,Q);k+=1
        if k==N:G=Q;break
    orb=[];R=None
    for d in range(1,N):R=add(R,G);orb.append(R)
    return N,[P[1] for P in orb]
def maxratio(p,A,B):
    n,ys=orbit_ys(p,A,B)
    ch=np.array([0 if int(y)%p==0 else int(legendre_symbol(int(y)%p,p)) for y in ys])
    d=np.arange(1,n)
    M=0
    for a in range(1,n):
        V=abs(np.sum(ch*np.exp(2j*math.pi*a*d/n)))
        if V>M:M=V
    return M/math.sqrt(p)
print("=== stress sweep: max ratio |V|/sqrt(p) over MANY curves, p=1 mod 4 ===")
glob=0; where=None
for p in [pp for pp in primerange(13,230) if pp%4==1]:
    pm=0
    for A in range(0,min(p,12)):
        for B in range(1,min(p,12)):
            if (4*A**3+27*B**2)%p==0: continue
            try:
                r=maxratio(p,A,B)
            except Exception: continue
            if r>pm: pm=r
            if r>glob: glob=r; where=(p,A,B)
    print(f"  p={p:3d}: max ratio over curves = {pm:.4f}  {'*** EXCEEDS 2' if pm>=2 else ''}")
print(f"\nGLOBAL max ratio = {glob:.5f} at {where}   (cap is 2.0)")

print("\n=== eigenvalue phase-lock on A_new for a NON-CM curve (p=13, f=x^3+3x+7) ===")
# point count cover C: w^4=f(x) over F_{13} and F_{13^2}; get L-poly, factor out E, inspect A_new quartic
def count_cover(p,A,B,k):
    q=p**k
    # multiplicative characters of order dividing 4 on F_q^*: use discrete log via generator
    # build F_q
    if k==1:
        def to(x):return x%p
        elts=list(range(p))
        def mul(a,b):return (a*b)%p
        def add_(a,b):return(a+b)%p
        nr=None
        gen=None
        # find primitive root
        for g in range(2,p):
            s=set();x=1
            for _ in range(p-1):
                x=x*g%p;s.add(x)
            if len(s)==p-1:gen=g;break
        # discrete log
        dl={};x=1
        for e in range(p-1):
            dl[x%p]=e;x=x*gen%p
        def chi(c,order): # character of given order (order|q-1)
            if c%p==0:return 0
            return np.exp(2j*math.pi*(dl[c%p]%order)/order)
        # N(w^4=c)=sum_{chi^4=1}chi(c) = 1+chi2(c)+chi4(c)+chi4^3(c)
        cnt=0
        for x in range(p):
            c=(x**3+A*x+B)%p
            if c==0: cnt+=1
            else:
                s=0
                for j in range(4):
                    s+= np.exp(2j*math.pi*((dl[c]* j*((p-1)//4))% (p-1))/(p-1)) if (p-1)%4==0 else 0
                cnt+=int(round(s.real))
        cnt+=1 # infinity (gcd(4,3)=1 -> one point)
        return cnt
    else:
        # F_{p^2}
        nr=next(c for c in range(2,p) if pow(c,(p-1)//2,p)==p-1)
        def mul(u,v):a,b=u;c,d=v;return((a*c+b*d*nr)%p,(a*d+b*c)%p)
        els=[(a,b) for a in range(p) for b in range(p)]
        # generator of F_{q}^*
        order=q-1
        def powe(u,e):
            r=(1,0)
            while e>0:
                if e&1:r=mul(r,u)
                u=mul(u,u);e>>=1
            return r
        def ordof(u):
            # factor order
            o=order
            for pr in [2,3]+[x for x in range(5,order+1)]:
                if o%pr==0:
                    pass
            return None
        gen=None
        import sympy
        facs=sympy.factorint(order)
        for a in range(1,p):
            for b in range(0,p):
                u=(a,b)
                if u==(0,0):continue
                ok=True
                for pr in facs:
                    if powe(u,order//pr)==(1,0):ok=False;break
                if ok:gen=u;break
            if gen:break
        dl={};r=(1,0)
        for e in range(order):dl[r]=e;r=mul(r,gen)
        def cube(u):return mul(mul(u,u),u)
        cnt=0
        for xa in range(p):
            for xb in range(p):
                x=(xa,xb)
                c=mul(cube(x),(1,0))
                c=(( (cube(x)[0]+A*x[0])%p , (cube(x)[1]+A*x[1])%p ))
                c=((c[0]+B)%p,c[1]%p)
                if c==(0,0):cnt+=1
                else:
                    e=dl[c];s=0
                    for j in range(4):
                        s+=np.exp(2j*math.pi*((e*j*(order//4))%order)/order)
                    cnt+=int(round(s.real))
        cnt+=1
        return cnt
p,A,B=13,3,7
N1=count_cover(p,A,B,1); N2=count_cover(p,A,B,2)
a1=p+1-N1; a2=p*p+1-N2
print(f"|C(F_13)|={N1}, |C(F_169)|={N2}; a1(cover)={a1}, a2(cover)={a2}")
# E: y^2=x^3+3x+7 point count
def ecount(p,A,B):
    c=1
    for x in range(p):
        r=(x**3+A*x+B)%p
        c+= (1+int(legendre_symbol(r,p))) if r%p!=0 else 1
    return c
NE=ecount(p,A,B); aE=p+1-NE
print(f"|E(F_13)|={NE}, aE={aE}")
# cover L-poly numerator over F_p: from a1,a2 get power sums of the 6 Frobenius roots; subtract E's 2 roots -> A_new 4 roots
# s1 = sum alpha = a1 ; p1(power sum1)=a1 ; p2 = a1^2-2*(coeff)... easier: roots of E are eigen with aE. 
print("(A_new eigenvalue extraction needs full L-poly; see ratio test below)")
