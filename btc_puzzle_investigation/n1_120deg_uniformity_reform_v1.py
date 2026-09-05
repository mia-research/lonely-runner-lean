import itertools, sys
from fractions import Fraction as Fr
P_PRIME=int(sys.argv[1]) if len(sys.argv)>1 else 43
p=P_PRIME; b=7
def isprime(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def leg(a):
    a%=p; return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
def add_Fp(P,Q):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return None
    m=((3*x1*x1)*pow(2*y1%p,p-2,p) if P==Q else (y2-y1)*pow((x2-x1)%p,p-2,p))%p
    x3=(m*m-x1-x2)%p;return(x3,(m*(x1-x3)-y1)%p)
ptsFp=[(x,y) for x in range(p) for y in range(p) if (y*y-(x*x*x+b))%p==0]
n=len(ptsFp)+1; assert isprime(n) and n%3==1
G=ptsFp[0]; idx={None:0}; cur=None; cyc=[None]*n
for k in range(1,n):
    cur=add_Fp(cur,G); idx[cur]=k; cyc[k]=cur
# ---- F_{p^m} (closure-safe) ----
def make_field(m):
    def mk_mul(fp):
        def mul(A,B):
            C=[0]*(2*m-1)
            for i in range(m):
                ai=A[i]
                if ai:
                    for j in range(m): C[i+j]+=ai*B[j]
            for d in range(2*m-2,m-1,-1):
                c=C[d]%p
                if c:
                    for j in range(m): C[d-m+j]-=c*fp[j]
                C[d]=0
            return tuple(x%p for x in C[:m])
        return mul
    def mk_pow(mul):
        def powe(A,e):
            R=tuple([1]+[0]*(m-1)); B=A
            while e:
                if e&1:R=mul(R,B)
                B=mul(B,B);e>>=1
            return R
        return powe
    fp=None
    for consts in itertools.product(range(p),repeat=m):
        mul=mk_mul(list(consts)); powe=mk_pow(mul); x=tuple([0,1]+[0]*(m-2))
        if powe(x,p**m)!=x: continue
        if all(powe(x,p**(m//q))!=x for q in (2,3) if m%q==0): fp=list(consts); break
    mul=mk_mul(fp); powe=mk_pow(mul); emb=lambda c:tuple([c%p]+[0]*(m-1))
    sq={}; squares=set()
    for e in itertools.product(range(p),repeat=m):
        s=mul(e,e); squares.add(s)
        if s not in sq: sq[s]=e
    return {'m':m,'mul':mul,'pow':powe,'emb':emb,'zero':tuple([0]*m),'sq':sq,'squares':squares}
def add_ext(A,B,fl):
    if A is None:return B
    if B is None:return A
    m=fl['m'];mul=fl['mul'];powe=fl['pow'];emb=fl['emb']
    x1,y1=A;x2,y2=B
    if x1==x2 and all((y1[i]+y2[i])%p==0 for i in range(m)):return None
    if A==B: num=mul(emb(3),mul(x1,x1));den=mul(emb(2),y1)
    else: num=tuple((y2[i]-y1[i])%p for i in range(m));den=tuple((x2[i]-x1[i])%p for i in range(m))
    mm=mul(num,powe(den,p**m-2))
    x3=tuple((mul(mm,mm)[i]-x1[i]-x2[i])%p for i in range(m))
    y3=tuple((mul(mm,tuple((x1[i]-x3[i])%p for i in range(m)))[i]-y1[i])%p for i in range(m))
    return (x3,y3)
def norm_idx(Q,fl):
    m=fl['m'];powe=fl['pow']; S=None;X,Y=Q
    for i in range(m):
        S=add_ext(S,(X,Y),fl)
        if i<m-1:X,Y=powe(X,p),powe(Y,p)
    if S is None:return 0
    x,y=S; assert all(x[i]==0 for i in range(1,m)) and all(y[i]==0 for i in range(1,m))
    return idx[(x[0],y[0])]
def Vm(a,fl):  # returns p_m = -sum tf = vec
    m=fl['m'];mul=fl['mul'];emb=fl['emb'];sq=fl['sq'];squares=fl['squares'];zero=fl['zero']
    vec=[0]*n; be=emb(b)
    for xs in itertools.product(range(p),repeat=m):
        x=tuple(xs); x3=mul(mul(x,x),x); rhs=tuple((x3[i]+be[i])%p for i in range(m))
        if rhs==zero or rhs not in squares: continue
        y0=sq[rhs]
        for y in (y0,tuple((-c)%p for c in y0)):
            c2=1 if y in squares else -1
            vec[(a*norm_idx((x,y),fl))%n]-=c2
    return vec
def V1(a):
    vec=[0]*n
    for k in range(1,n):
        c=leg(cyc[k][1])
        if c: vec[(a*k)%n]-=c
    return vec
# ===== Q(zeta_n) in power basis deg n-1, Phi_n = [1]*n =====
PHI=[Fr(1)]*n  # 1+z+...+z^{n-1}, degree n-1
def ptrim(A):
    A=list(A)
    while len(A)>1 and A[-1]==0: A.pop()
    return A
def padd(A,B):
    r=[Fr(0)]*max(len(A),len(B))
    for i,c in enumerate(A):r[i]+=c
    for i,c in enumerate(B):r[i]+=c
    return ptrim(r)
def psub(A,B):
    r=[Fr(0)]*max(len(A),len(B))
    for i,c in enumerate(A):r[i]+=c
    for i,c in enumerate(B):r[i]-=c
    return ptrim(r)
def pmul(A,B):
    r=[Fr(0)]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        if a:
            for j,bb in enumerate(B): r[i+j]+=a*bb
    return ptrim(r)
def pmod(A,M):  # A mod M, M monic-ish (leading nonzero)
    A=ptrim(A)[:]; dM=len(M)-1; lcM=M[-1]
    while len(A)-1>=dM and not(len(A)==1 and A[0]==0):
        d=len(A)-1; c=A[-1]/lcM
        for i in range(len(M)): A[d-dM+i]-=c*M[i]
        A=ptrim(A)
    return A
def rmul(A,B): return pmod(pmul(A,B),PHI)      # Q(zeta_n) mult
def rfromvec(v):  # length-n int -> power basis deg n-1
    A=[Fr(v[j]) for j in range(n)]
    return pmod(A,PHI)
def rinv(A):  # inverse mod PHI via ext-euclid over Q[z]
    A=pmod(A,PHI); 
    # extended gcd(A, PHI)
    r0,r1=PHI[:],A[:]; s0,s1=[Fr(0)],[Fr(1)]
    while not(len(r1)==1 and r1[0]==0):
        # q = r0 // r1
        r0=ptrim(r0);r1=ptrim(r1)
        q=[Fr(0)]*(max(1,len(r0)-len(r1)+1)); rem=r0[:]
        while len(rem)-1>=len(r1)-1 and not(len(rem)==1 and rem[0]==0):
            d=len(rem)-len(r1); c=rem[-1]/r1[-1]; q[d]+=c
            for i in range(len(r1)): rem[d+i]-=c*r1[i]
            rem=ptrim(rem)
        r0,r1=r1,rem; s0,s1=s1,psub(s0,pmul(q,s1))
    # r0 = gcd (constant); s0 * A = gcd mod PHI
    g=r0[0]; inv=[c/g for c in s0]
    return pmod(inv,PHI)
RONE=[Fr(1)]; RZERO=[Fr(0)]
# ===== K = Q(zeta_n)[w]/(w^2+w+1),  element (a,b)=a+bw =====
def Kadd(X,Y):return (padd(X[0],Y[0]),padd(X[1],Y[1]))
def Ksub(X,Y):return (psub(X[0],Y[0]),psub(X[1],Y[1]))
def Kmul(X,Y):
    a,bb=X;c,d=Y
    ac=rmul(a,c);bd=rmul(bb,d);ad=rmul(a,d);bc=rmul(bb,c)
    return (psub(ac,bd), psub(padd(ad,bc),bd))   # (ac-bd)+(ad+bc-bd)w
def Kinv(X):
    a,bb=X
    N=padd(psub(rmul(a,a),rmul(a,bb)),rmul(bb,bb))  # a^2-ab+b^2
    Ni=rinv(N)
    return (rmul(psub(a,bb),Ni), rmul([ -c for c in bb],Ni))
def Kfrom(a):return (a,RZERO)          # a in Q(zeta_n)
W=(RZERO,RONE)                          # zeta_3 = w
def Kis0(X):return ptrim(X[0])==[Fr(0)] and ptrim(X[1])==[Fr(0)]
Wpow=[Kfrom(RONE),W,Ksub(Ksub(Kfrom(RZERO),Kfrom(RONE)),W)]  # w^0,w^1,w^2=-1-w
def wpow(k):return Wpow[k%3]
# ===== poly over K (list of K low-to-high) =====
def Kpoly_trim(Pl):
    Pl=list(Pl)
    while len(Pl)>1 and Kis0(Pl[-1]):Pl.pop()
    return Pl
def Kpoly_mod(A,B):
    A=[x for x in A];B=Kpoly_trim(B); dB=len(B)-1; lcI=Kinv(B[-1])
    while len(A)-1>=dB and not(len(A)==1 and Kis0(A[0]) and len(A)==1):
        A=Kpoly_trim(A)
        if len(A)-1<dB: break
        d=len(A)-1; c=Kmul(A[-1],lcI)
        for i in range(len(B)): A[d-dB+i]=Ksub(A[d-dB+i],Kmul(c,B[i]))
        A=Kpoly_trim(A)
        if len(A)==1 and Kis0(A[0]):break
    return Kpoly_trim(A)
def Kpoly_gcd(A,B):
    A=Kpoly_trim(A);B=Kpoly_trim(B)
    while not(len(B)==1 and Kis0(B[0])):
        A,B=B,Kpoly_mod(A,B)
    return Kpoly_trim(A)
def Kdeg(A):
    A=Kpoly_trim(A); return -1 if (len(A)==1 and Kis0(A[0])) else len(A)-1



# ---- Reformulation test: L^{(3)}(T) = L*(s)L*(z3 s)L*(z3^2 s)|_{s^3=T} is a PERFECT SQUARE  <=>  120 law
def isprime2(m):
    if m<2:return False
    i=2
    while i*i<=m:
        if m%i==0:return False
        i+=1
    return True
def prim_root(l):
    facs=set(); mm=l-1; d=2
    while d*d<=mm:
        while mm%d==0: facs.add(d); mm//=d
        d+=1
    if mm>1: facs.add(mm)
    for g in range(2,l):
        if all(pow(g,(l-1)//q,l)!=1 for q in facs): return g
def find_ell(k):
    t=2
    while True:
        l=t*3*k+1
        if isprime2(l): return l
        t+=1
def img(vec,w,l):
    r=0; wp=1
    for j in range(n):
        r=(r+vec[j]*wp)%l; wp=wp*w%l
    return r
def pmul_l(A,B,l):
    r=[0]*(len(A)+len(B)-1)
    for i,a in enumerate(A):
        if a:
            for j,b in enumerate(B): r[i+j]=(r[i+j]+a*b)%l
    return r
def pderiv_l(A,l): return [(i*A[i])%l for i in range(1,len(A))]
def gcd_deg_l(A,B,l):
    def trim(P):
        P=[c%l for c in P]
        while len(P)>1 and P[-1]==0:P.pop()
        return P
    A=trim(A);B=trim(B)
    while not(len(B)==1 and B[0]==0):
        A=trim(A);B=trim(B)
        if len(A)<len(B):A,B=B,A
        while len(A)>=len(B) and not(len(A)==1 and A[0]==0):
            c=A[-1]*pow(B[-1],l-2,l)%l; d=len(A)-len(B)
            for i in range(len(B)): A[d+i]=(A[d+i]-c*B[i])%l
            A=trim(A)
        A,B=B,A
    return len(trim(A))-1
def L3_and_square(e1,e2,e3,e4,z3,l):
    # L*(s) coeffs low->high in s: [1,-e1,e2,-e3,e4]
    def Lstar(rot):
        c=[1,(-e1*rot)%l,(e2*rot*rot)%l,(-e3*pow(rot,3,l))%l,(e4*pow(rot,4,l))%l]
        return c
    L1=Lstar(1); L2=Lstar(z3); L3=Lstar((z3*z3)%l)
    prod=pmul_l(pmul_l(L1,L2,l),L3,l)  # degree 12 in s
    # must be supported on s^{0,3,6,9,12}
    supp_ok=all(prod[k]%l==0 for k in range(len(prod)) if k%3!=0)
    L3T=[prod[3*k]%l for k in range(5)]  # degree 4 in T
    # perfect square?  deg gcd(L3T, L3T') == 2  and squarefree-part deg 2
    g=gcd_deg_l(L3T,pderiv_l(L3T,l),l)
    return supp_ok, g, L3T
lam=next(c for c in range(2,n) if pow(c,3,n)==1 and c!=1)
seen=set(); reps=[]
for a in range(1,n):
    if a in seen: continue
    reps.append(a); x=a
    for _ in range(3): seen.add(x); x=(x*lam)%n
chi=leg(-1); l=find_ell(n); g0=prim_root(l); w=pow(g0,(l-1)//n,l); z3=pow(g0,(l-1)//3,l); i2=pow(2,l-2,l)
F2=make_field(2)
ok_law=0; ctrl_break=0; supp_all=True
for a in reps:
    p1=V1(a); p2=Vm(a,F2)
    e1=img(p1,w,l); P2=img(p2,w,l); e2=(e1*e1-P2)*i2%l; e3=chi*p%l*e1%l; e4=p*p%l
    supp,g,_=L3_and_square(e1,e2,e3,e4,z3,l)
    supp_all = supp_all and supp
    if g==2: ok_law+=1
    # CONTROL: perturb e2 -> e2+1 (breaks the pure structure); should NOT be perfect square
    supp2,g2,_=L3_and_square(e1,(e2+1)%l,e3,e4,z3,l)
    if g2<2: ctrl_break+=1
print(f"p={p:<4}(p%12={p%12}) n={n:<4} reps={len(reps)}: L^(3) supported on s^(3k):{supp_all}  perfect-square(deg gcd=2) all cells:{ok_law==len(reps)} ({ok_law}/{len(reps)})  |  control(e2+1) NOT square:{ctrl_break}/{len(reps)}",flush=True)
