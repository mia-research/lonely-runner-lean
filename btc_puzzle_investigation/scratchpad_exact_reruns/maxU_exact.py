# EXACT-DATA + high-precision rerun of the max|U|/sqrt(p) "no spike" null (H3 T_y-max corner).
# U(a,b,c)=sum_d e_p(b x_d + c y_d) e_n(-a d); data (x_d,y_d,d) EXACT ints; magnitude via mpmath 60 dps.
import mpmath as mp
mp.mp.dps = 60
def egcd(a,b):
    if b==0:return(a,1,0)
    g,x,y=egcd(b,a%b);return(g,y,x-(a//b)*y)
def inv(a,m):return egcd(a%m,m)[1]%m
def ec_add(P,Q,a,p):
    if P is None:return Q
    if Q is None:return P
    (x1,y1),(x2,y2)=P,Q
    if x1==x2 and (y1+y2)%p==0:return None
    l=((3*x1*x1+a)*inv(2*y1,p) if P==Q else (y2-y1)*inv((x2-x1)%p,p))%p
    x3=(l*l-x1-x2)%p;return(x3,(l*(x1-x3)-y1)%p)
def isprime(m):
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return m>=2
for p,A,B in [(43,0,7),(67,0,7)]:
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    if not isprime(n): print(f"p={p} n={n} composite skip"); continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
    a0=1; sqp=mp.sqrt(p)
    wp=2*mp.pi/p; wn=2*mp.pi/n
    # precompute per-d phase e_n(-a0 d)
    base=[mp.e**(-1j*wn*a0*d) for d in range(n)]
    best=mp.mpf(0); best_bc=None; odd_max=mp.mpf(0); even_max=mp.mpf(0)
    for b in range(p):
        for c in range(p):
            if b==0 and c==0: continue
            U=mp.mpc(0)
            for d in range(1,n):
                x,y=P[d]
                U+=mp.e**(1j*wp*((b*x+c*y)%p))*base[d]
            m=abs(U)/sqp
            if m>best: best=m; best_bc=(b,c)
            # parity split by c (y-odd channel): c and -c
    # H3 specific: does the odd-half (c-antisymmetric) max exceed the even-half?
    for b in range(p):
        for c in range(1,(p+1)//2):
            Uc=mp.mpc(0); Un=mp.mpc(0)
            for d in range(1,n):
                x,y=P[d]
                Uc+=mp.e**(1j*wp*((b*x+c*y)%p))*base[d]
                Un+=mp.e**(1j*wp*((b*x+(-c)*y)%p))*base[d]
            odd=abs(Uc-Un)/2/sqp; even=abs(Uc+Un)/2/sqp
            if odd>odd_max: odd_max=odd
            if even>even_max: even_max=even
    ceil=mp.sqrt(4)  # 4 frequencies (b x + c y two coords) -> dim ~4, Weil ceiling ~ sqrt(dim)? report raw
    print(f"p={p} n={n}: max|U(a0,b,c)|/sqrt(p) = {mp.nstr(best,8)} at (b,c)={best_bc}   | odd-half max {mp.nstr(odd_max,6)}  even-half max {mp.nstr(even_max,6)}  odd>even? {odd_max>even_max}")
