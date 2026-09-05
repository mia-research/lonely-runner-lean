# Exact symbolic verification of the c2(a) law proof chain.
# All arithmetic exact: F_{p^2} via F_p[t]/(t^2 - ns), characters land in Z[zeta_12].
# NO FLOAT in the signal path (project rule).

# ---- Z[zeta_12] ring: element = [a0,a1,a2,a3] = a0 + a1 z + a2 z^2 + a3 z^3, z^4 = z^2 - 1 ----
def zadd(a,b): return [a[i]+b[i] for i in range(4)]
def zsub(a,b): return [a[i]-b[i] for i in range(4)]
def zmul(a,b):
    r=[0,0,0,0,0,0,0]
    for i in range(4):
        if a[i]==0: continue
        for j in range(4):
            if b[j]==0: continue
            r[i+j]+=a[i]*b[j]
    # reduce z^4 = z^2 - 1, z^5 = z^3 - z, z^6 = z^4 - z^2 = -1
    # do it by repeated reduction of top terms
    for k in range(6,3,-1):
        c=r[k]
        if c:
            r[k]=0
            # z^k = z^{k-4} * z^4 = z^{k-4}*(z^2 - 1) => + c at (k-4+2), - c at (k-4)
            r[k-2]+=c
            r[k-4]-=c
    return r[:4]
Z0=[0,0,0,0]; Z1=[1,0,0,0]
def zpow(a,k):
    r=Z1[:]; b=a[:]
    while k>0:
        if k&1: r=zmul(r,b)
        b=zmul(b,b); k>>=1
    return r
def zconj(a):
    # complex conjugation: zeta_12 -> zeta_12^{-1} = zeta_12^{11}
    z11=zpow([0,1,0,0],11)
    # apply as substitution z -> z^{11}: a0 + a1 z^11 + a2 z^22 + a3 z^33
    res=[a[0] if False else 0]*1
    r=[a[0],0,0,0]
    r=zsmul(a[0],Z1)
    r=zadd(r, zsmul(a[1], zpow([0,1,0,0],11)))
    r=zadd(r, zsmul(a[2], zpow([0,1,0,0],22)))
    r=zadd(r, zsmul(a[3], zpow([0,1,0,0],33)))
    return r
def zsmul(s,a): return [s*a[0],s*a[1],s*a[2],s*a[3]]
def zeq(a,b): return all(a[i]==b[i] for i in range(4))
def zisrat(a):
    return a[1]==0 and a[2]==0 and a[3]==0
# primitive roots inside the ring:
Z = [0,1,0,0]         # zeta_12
I = zpow(Z,3)         # i = zeta^3
OMEGA = zpow(Z,4)     # omega = zeta^4  (primitive cube root)
# sanity
assert zeq(zmul(I,I), [-1,0,0,0]), I
assert zeq(zpow(OMEGA,3), Z1)
assert zeq(zadd(zadd(zpow(OMEGA,2),OMEGA),Z1), Z0)

def isqrt_field(p):
    # find a non-square ns in F_p for F_{p^2}=F_p[t]/(t^2-ns)
    for ns in range(2,p):
        if pow(ns,(p-1)//2,p)==p-1:
            return ns
    raise RuntimeError

def build_Fp2(p):
    ns=isqrt_field(p)
    # elements (a,b) = a + b t, t^2 = ns
    def mul(u,v):
        a,b=u; c,d=v
        return ((a*c + b*d*ns)%p, (a*d+b*c)%p)
    def add(u,v): return ((u[0]+v[0])%p,(u[1]+v[1])%p)
    els=[(a,b) for a in range(p) for b in range(p)]
    # find generator of F_{p^2}^*
    order=p*p-1
    import sympy
    fac=sympy.factorint(order)
    def is_gen(g):
        for q in fac:
            if pow_el(g,order//q,mul)== (1,0): return False
        return True
    def pow_el(g,k,mul):
        r=(1,0); b=g
        while k>0:
            if k&1: r=mul(r,b)
            b=mul(b,b); k>>=1
        return r
    g=None
    for a in range(p):
        for b in range(1,p):
            cand=(a,b)
            if is_gen(cand): g=cand; break
        if g: break
    # discrete log table
    dlog={}
    cur=(1,0)
    for k in range(order):
        dlog[cur]=k
        cur=mul(cur,g)
    return ns,mul,add,g,dlog,order

def prove_for_prime(p):
    assert p%12==7
    ns,mul,add,g,dlog,order = build_Fp2(p)
    # characters: chi3(g^k)=omega^k, chi4(g^k)=i^k ; chi(0)=0
    def chi3(u):
        if u==(0,0): return Z0
        return zpow(OMEGA, dlog[u]%3)
    def chi3bar(u):
        if u==(0,0): return Z0
        return zpow(OMEGA, (2*dlog[u])%3)
    def chi4(u):
        if u==(0,0): return Z0
        return zpow(I, dlog[u]%4)
    # embed a in F_p -> F_{p^2}
    def emb(a): return (a%p,0)
    def cube(u): return mul(mul(u,u),u)

    # (i) verify chi4(a)=1 for all a in F_p^*
    ok_chi4=all(zeq(chi4(emb(a)),Z1) for a in range(1,p))

    # T(a) = sum_{x in F_{p^2}} chi4(x^3 + a)   (exact ring element)
    allx=[(a,b) for a in range(p) for b in range(p)]
    def T(a):
        s=Z0[:]
        ae=emb(a)
        for x in allx:
            val=add(cube(x),ae)
            s=zadd(s, chi4(val))
        return s

    # Jacobi sums J1=J(chi3,chi4)=sum_{x} chi3(x) chi4(1-x), J2=J(chi3bar,chi4)
    one=(1,0)
    def jac(cha,chb):
        s=Z0[:]
        for x in allx:
            if x==(0,0): continue
            omx=((1-x[0])%p, (-x[1])%p)
            s=zadd(s, zmul(cha(x), chb(omx)))
        return s
    J1=jac(chi3,chi4); J2=jac(chi3bar,chi4)

    # sign law check
    negp=[-p,0,0,0]
    sign_ok = zeq(J1,negp) and zeq(J2,negp)

    # reduction check: T(a) == chi3(a) J1 + chi3bar(a) J2   for all a in F_p^*
    red_ok=True
    c2_from_T={}
    for a in range(1,p):
        Ta=T(a)
        rhs=zadd(zmul(chi3(emb(a)),J1), zmul(chi3bar(emb(a)),J2))
        if not zeq(Ta,rhs): red_ok=False
        # c2 = Re(T(a)) = (T + conj T)/2 ; T should already be rational here
        # compute (T + conj(T)) and check even, /2
        tc=zadd(Ta, zconj(Ta))
        # tc must be rational
        assert zisrat(tc), (a,tc)
        c2_from_T[a]= tc[0]//2

    # independent c2 from the sign law + trace formula: c2 = -p*(chi3(a)+chi3bar(a))
    # chi3(a)+chi3bar(a) is rational: 2 if residue else -1
    c2_pred={}
    for a in range(1,p):
        s=zadd(chi3(emb(a)),chi3bar(emb(a)))
        assert zisrat(s)
        c2_pred[a]= -p*s[0]

    # cross-check both against point-count c2 (residue -> -2p, nonres -> +p)
    match_all=True
    for a in range(1,p):
        is_cr = pow(a,(p-1)//3,p)==1
        c2_true = -2*p if is_cr else p
        if not (c2_from_T[a]==c2_true==c2_pred[a]):
            match_all=False
    return dict(p=p, chi4_a_is_1=ok_chi4, sign_law_J=(J1,J2), sign_ok=sign_ok,
               reduction_ok=red_ok, c2_all_match=match_all)

for p in [43, 67]:
    r=prove_for_prime(p)
    print(f"p={p}:")
    print(f"  chi4(a)=1 for all a in F_p^*      : {r['chi4_a_is_1']}")
    print(f"  J(chi3,chi4)=J(chi3bar,chi4)=-p   : {r['sign_ok']}   (J1={r['sign_law_J'][0]}, J2={r['sign_law_J'][1]})")
    print(f"  T(a)=chi3(a)J1+chi3bar(a)J2 (all a): {r['reduction_ok']}")
    print(f"  c2 chain == point-count c2 (all a) : {r['c2_all_match']}")
    print()
