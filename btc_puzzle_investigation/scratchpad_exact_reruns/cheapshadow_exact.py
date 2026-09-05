# EXACT-DATA rerun of cheap_partial_shadow: does any CHEAP readout F(P_d) have rho > floor? (mpmath 30dps)
import mpmath as mp, math
mp.mp.dps=30
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
def rho_exact(F, n):   # F[d] for d=1..n-1 (mpmath complex); rho=max_a|Corr|/l2
    l2=mp.sqrt(sum(abs(F[d])**2 for d in range(1,n))/(n-1))
    wn=2*mp.pi/n; best=mp.mpf(0)
    for a in range(1,n):
        C=abs(sum(F[d]*mp.e**(-1j*wn*a*d) for d in range(1,n)))/n
        if C>best: best=C
    return best/l2 if l2>0 else mp.mpf(0)
for p,A,B in [(43,0,7),(67,0,7),(163,0,7)]:
    pts=[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x-A*x-B)%p==0]
    n=len(pts)+1
    if not isprime(n): continue
    G=pts[0];P=[None]*n;Q=None
    for d in range(1,n):Q=ec_add(Q,G,A,p);P[d]=Q
    X={d:P[d][0] for d in range(1,n)}; Y={d:P[d][1] for d in range(1,n)}
    readouts={
      'y-sign(half)': lambda x,y: mp.mpf(1) if y<mp.mpf(p)/2 else mp.mpf(-1),
      'y mod 2':      lambda x,y: mp.mpf(1) if y%2 else mp.mpf(-1),
      'x-half':       lambda x,y: mp.mpf(1) if x<mp.mpf(p)/2 else mp.mpf(-1),
      'sign(xy)':     lambda x,y: mp.mpf(1) if (x*y%p)<mp.mpf(p)/2 else mp.mpf(-1),
      '(xy) mod 2':   lambda x,y: mp.mpf(1) if (x*y)%2 else mp.mpf(-1),
      'yhalf*xpar':   lambda x,y: (mp.mpf(1) if y<mp.mpf(p)/2 else mp.mpf(-1))*(mp.mpf(1) if x%2 else mp.mpf(-1)),
      'e_p(y)':       lambda x,y: mp.e**(2j*mp.pi*y/p),
      'e_p(x+y)':     lambda x,y: mp.e**(2j*mp.pi*((x+y)%p)/p),
    }
    floor=math.sqrt(math.log(n))/math.sqrt(n)
    res={}
    for nm,f in readouts.items():
        F={d:f(X[d],Y[d]) for d in range(1,n)}
        res[nm]=float(rho_exact(F,n))
    best=max(res,key=lambda k:res[k])
    print(f"p={p} n={n}: floor~{floor:.3f}  best cheap rho={res[best]:.4f} ('{best}')  all: "+", ".join(f"{k}={v:.3f}" for k,v in sorted(res.items(),key=lambda kv:-kv[1])[:4]))
