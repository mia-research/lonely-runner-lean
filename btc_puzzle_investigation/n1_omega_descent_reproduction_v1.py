# EXACT omega-descent test: V1(a)=V1(lambda*a), lambda order 3 mod n.  No float in signal path.
def leg(a,p):
    a%=p
    return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
def ec_points(p,b=7):
    return [(x,y) for x in range(p) for y in range(p) if (y*y-(x*x*x+b))%p==0]
def ec_add(P,Q,p):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    m=((3*x1*x1)*pow(2*y1%p,p-2,p) if P==Q else (y2-y1)*pow((x2-x1)%p,p-2,p))%p
    x3=(m*m-x1-x2)%p
    return (x3,(m*(x1-x3)-y1)%p)
def isprime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True
def prim_root(n):  # n prime
    facs=set(); m=n-1; d=2
    while d*d<=m:
        while m%d==0: facs.add(d); m//=d
        d+=1
    if m>1: facs.add(m)
    for g in range(2,n):
        if all(pow(g,(n-1)//q,n)!=1 for q in facs): return g
def cyclo_eq(u,v,n):
    d0=u[0]-v[0]
    return all(u[i]-v[i]==d0 for i in range(n))

print("p    N    lam  mu   descent V1(a)=V1(lam a)   control mu (must break)")
found=0
for p in range(19,400):
    if p%12!=7 or not isprime(p): continue
    pts=ec_points(p); N=len(pts)+1
    if not isprime(N) or N%3!=1: continue
    G=pts[0]
    ypt=[None]*N; cur=None
    for k in range(1,N):
        cur=ec_add(cur,G,p); ypt[k]=cur[1]
    assert ec_add(cur,G,p) is None, "G not order N"
    def V1(a):
        vec=[0]*N
        for k in range(1,N):
            c=leg(ypt[k],p)
            if c: vec[(a*k)%N]-=c
        return vec
    V=[None]+[V1(a) for a in range(1,N)]
    lam=pow(prim_root(N),(N-1)//3,N)
    assert pow(lam,3,N)==1 and lam!=1
    ok=sum(cyclo_eq(V[a],V[(lam*a)%N],N) for a in range(1,N))
    forb={1,lam,pow(lam,2,N)}
    mu=next(c for c in range(2,N) if c not in forb)
    brk=sum(not cyclo_eq(V[a],V[(mu*a)%N],N) for a in range(1,N))
    print(f"{p:<4} {N:<4} {lam:<4} {mu:<4} {ok}/{N-1} {'PASS' if ok==N-1 else 'FAIL'}                {brk}/{N-1} {'fires' if brk>0 else 'DEAD'}")
    found+=1
    if found>=6: break
