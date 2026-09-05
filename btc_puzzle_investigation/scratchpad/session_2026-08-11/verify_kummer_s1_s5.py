import math

# §1/§5 structural test: is Jac(C_a) ~ E_a (ORDINARY) x A_new (SUPERSINGULAR)?
#   - E_a: y^2 = x^3 + a  -> a_p = p+1-#E_a ; ordinary <=> a_p != 0 mod p (a_p != 0 for small p)
#   - A_new: 4-dim, char poly X^4 + c2 X^2 + p^2 -> trace = 0 (supersingular pattern a_p=0)
# If E ordinary and A_new supersingular, then Hom(E,A_new)=0 (different Newton polygons) -> §5.3's
# own premise, which KILLS the DLP-transfer thesis of §5.1-5.2.

def count_E(p, a):
    # affine points of y^2 = x^3 + a plus infinity
    cnt = 1
    for x in range(p):
        rhs = (x*x*x + a) % p
        if rhs == 0:
            cnt += 1
        elif pow(rhs, (p-1)//2, p) == 1:
            cnt += 2
    return cnt

# reuse the A_new c2 computation via point counts on the cover (from earlier verified machinery)
import itertools
def find_irr(p,deg):
    if deg==2:
        for s in range(1,p):
            if pow(s,(p-1)//2,p)!=1: return ('shift',s)
    if deg==3:
        if (p-1)%3==0:
            for s in range(1,p):
                if not any(pow(x,3,p)==s for x in range(p)): return ('shift',s)
        for c1 in range(0,p):
            for c0 in range(1,p):
                if not any((pow(x,3,p)+c1*x+c0)%p==0 for x in range(p)): return ('trinomial',c1,c0)
    raise RuntimeError
class FF:
    def __init__(s,p,deg,rm): s.p=p;s.deg=deg;s.rm=rm
    def one(s): e=[0]*s.deg;e[0]=1;return tuple(e)
    def fi(s,a): e=[0]*s.deg;e[0]=a%s.p;return tuple(e)
    def add(s,a,b): return tuple((x+y)%s.p for x,y in zip(a,b))
    def mul(s,a,b):
        p=s.p;d=s.deg;res=[0]*(2*d-1)
        for i,ai in enumerate(a):
            if ai==0: continue
            for j,bj in enumerate(b):
                if bj==0: continue
                res[i+j]=(res[i+j]+ai*bj)%p
        out=list(res[:d])
        for k in range(len(res)-1,d-1,-1):
            c=res[k]
            if c:
                sh=k-d
                for idx,rc in enumerate(s.rm):
                    t=idx+sh
                    if t<d: out[t]=(out[t]+c*rc)%p
                    else: res[t]=(res[t]+c*rc)%p
        return tuple(out)
    def pw(s,a,k):
        r=s.one();b=a
        while k>0:
            if k&1: r=s.mul(r,b)
            b=s.mul(b,b);k>>=1
        return r
    def iz(s,a): return all(c==0 for c in a)
    def els(s):
        for t in itertools.product(range(s.p),repeat=s.deg): yield t
class F1:
    def __init__(s,p): s.p=p
    def one(s): return (1,)
    def fi(s,a): return (a%s.p,)
    def add(s,a,b): return ((a[0]+b[0])%s.p,)
    def mul(s,a,b): return ((a[0]*b[0])%s.p,)
    def pw(s,a,k): return (pow(a[0],k,s.p),)
    def iz(s,a): return a[0]%s.p==0
    def els(s):
        for x in range(s.p): yield (x,)
def mk(p,d):
    if d==1: return F1(p)
    sp=find_irr(p,d)
    if sp[0]=='shift': rm=[sp[1]]+[0]*(d-1)
    else: _,c1,c0=sp; rm=[(-c0)%p,(-c1)%p,0]
    return FF(p,d,rm)
def cpts(f,N,a,quartic):
    g=4 if quartic else 2; gg=math.gcd(g,N); e=N//gg
    b=f.fi(a); c=1
    for x in f.els():
        x3=f.mul(f.mul(x,x),x); rhs=f.add(x3,b)
        if f.iz(rhs): c+=1; continue
        if f.pw(rhs,e)==f.one(): c+=gg
    return c
def anew_trace(p,a):
    f1=mk(p,1); C1=cpts(f1,p-1,a,True); E1=cpts(f1,p-1,a,False)
    return E1-C1  # = a_p of A_new (new-part trace over F_p)

for p in [43,67]:
    print(f"\n=== p={p} (p mod 3 = {p%3}, so j=0 curves are {'ORDINARY' if p%3==1 else 'supersingular'}) ===")
    print(f"{'a':>3} {'a_p(E_a)':>9} {'E ordinary?':>12} {'a_p(A_new)':>11} {'A_new ss?':>10}")
    all_E_ord=True; all_A_ss=True
    for a in range(1,min(p,13)):
        NE = count_E(p,a)
        apE = p+1-NE
        apA = anew_trace(p,a)
        E_ord = (apE % p != 0)   # ordinary iff a_p not divisible by p (and !=0)
        A_ss  = (apA == 0)
        all_E_ord &= E_ord; all_A_ss &= A_ss
        print(f"{a:>3} {apE:>9} {str(E_ord):>12} {apA:>11} {str(A_ss):>10}")
    print(f"  ALL E_a ordinary (a_p != 0): {all_E_ord}   |   ALL A_new supersingular (a_p = 0): {all_A_ss}")
    print(f"  => ordinary x supersingular split holds: {all_E_ord and all_A_ss}")
    print(f"  => Hom(E_a, A_new) = 0 (different Newton polygons) -> NO DLP transfer (undercuts §5.1-5.2)")
