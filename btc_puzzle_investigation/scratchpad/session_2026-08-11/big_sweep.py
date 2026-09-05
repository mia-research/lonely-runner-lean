import itertools, math

def find_irreducible(p, deg):
    if deg == 2:
        for s in range(1, p):
            if pow(s, (p-1)//2, p) != 1:
                return ('shift', s)
    if deg == 3:
        # try x^3 - s first (works when p = 2 mod 3, cubing not a bijection... actually
        # need s that's NOT a cube; only possible when gcd(3,p-1)=3, i.e. p=1 mod 3)
        if (p-1) % 3 == 0:
            for s in range(1, p):
                if not any(pow(x,3,p)==s for x in range(p)):
                    return ('shift', s)
        # p = 2 mod 3: every element is a cube, x^3-s always reducible.
        # fall back to general trinomial x^3 + c1*x + c0 with no root in F_p.
        for c1 in range(0, p):
            for c0 in range(1, p):
                if not any((pow(x,3,p) + c1*x + c0) % p == 0 for x in range(p)):
                    return ('trinomial', c1, c0)
    raise RuntimeError

class FF:
    """F_{p^deg} = F_p[x]/(modulus). `reduce_map` gives x^deg reduced to a
    length-deg coefficient vector (for x^0..x^{deg-1})."""
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
        # reduce degree >= deg terms one at a time using x^deg = reduce_map (coeffs of x^0..x^{deg-1})
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

def count(field, N, lin_coef, const, quartic):
    g=4 if quartic else 2
    gg=math.gcd(g,N); exp=N//gg
    a_ff=field.from_int(lin_coef); b_ff=field.from_int(const)
    cnt=1
    for x in field.elements():
        x3=field.mul(field.mul(x,x),x)
        lin = field.mul(a_ff,x) if lin_coef!=0 else field.from_int(0)
        rhs=field.add(field.add(x3,lin),b_ff)
        if field.is_zero(rhs):
            cnt+=1; continue
        v=field.pw(rhs,exp)
        if v==field.one(): cnt+=gg
    return cnt

def newton(a1,a2,a3):
    e1=a1
    e2r=(e1*a1-a2)
    if e2r%2!=0: return e1,None,None
    e2=e2r//2
    e3r=(e2*a1-e1*a2+a3)
    if e3r%3!=0: return e1,e2,None
    e3=e3r//3
    return e1,e2,e3

def perfect_square_check(e1,e2,e3,p):
    import numpy as np
    e4=p*p
    coeffs=[1,-e1,e2,-e3,e4]
    roots_of_L=np.roots(list(reversed(coeffs)))
    alphas=1.0/roots_of_L
    cubed=[al**3 for al in alphas]
    tol=1e-4
    used=[False]*4; pairs=[]
    for i in range(4):
        if used[i]: continue
        grp=[i]
        for j in range(i+1,4):
            if not used[j] and abs(cubed[i]-cubed[j])<tol*max(1,abs(cubed[i])):
                grp.append(j); used[j]=True
        used[i]=True; pairs.append(grp)
    return len(pairs)<=2

def make_field(p, deg):
    spec = find_irreducible(p, deg)
    if spec[0] == 'shift':
        s = spec[1]
        reduce_map = [s] + [0]*(deg-1)
    else:  # trinomial: x^3 + c1 x + c0 -> x^3 = -c0 - c1 x
        _, c1, c0 = spec
        reduce_map = [(-c0) % p, (-c1) % p, 0]
    return FF(p, deg, reduce_map)

def analyze(p, lin_coef, const_val):
    f1=F1(p)
    f2=make_field(p,2)
    f3=make_field(p,3)
    C1=count(f1,p-1,lin_coef,const_val,True); E1=count(f1,p-1,lin_coef,const_val,False)
    C2=count(f2,p*p-1,lin_coef,const_val,True); E2=count(f2,p*p-1,lin_coef,const_val,False)
    C3=count(f3,p**3-1,lin_coef,const_val,True); E3=count(f3,p**3-1,lin_coef,const_val,False)
    a1=E1-C1; a2=E2-C2; a3=E3-C3
    # Hasse sanity check on E (genus1) at all 3 levels -- catch singular curves / bugs
    for k,(q,Ek) in enumerate([(p,E1),(p*p,E2),(p**3,E3)],1):
        if abs(q+1-Ek) > 2*math.sqrt(q)+0.5:
            return None  # skip: likely singular curve or edge case
    e1,e2,e3 = newton(a1,a2,a3)
    if e2 is None or e3 is None:
        return None
    persq = perfect_square_check(e1,e2,e3,p)
    return dict(e1=e1,e2=e2,e3=e3,persq=persq)

results = {'CM':[], 'nonCM':[]}
primes_by_class = {
    7:  [19,31,43],
    11: [11,23,47],
    1:  [13,37,61],
    5:  [5,17,29,41],
}
a_values = [1,2,3]

for cls, primes in primes_by_class.items():
    for p in primes:
        for a in a_values:
            r_cm = analyze(p, 0, a)
            r_ncm = analyze(p, 1, a)
            if r_cm is not None:
                results['CM'].append((p,cls,a,r_cm))
            if r_ncm is not None:
                results['nonCM'].append((p,cls,a,r_ncm))
        print(f"done p={p} (class {cls} mod 12)")

print("\n=== SUMMARY ===")
for fam in ['CM','nonCM']:
    n = len(results[fam])
    npersq = sum(1 for _,_,_,r in results[fam] if r['persq'])
    print(f"{fam}: {npersq}/{n} perfect-square  ({100*npersq/n:.1f}%)")

print("\nBy mod-12 class:")
for fam in ['CM','nonCM']:
    for cls in [7,11,1,5]:
        sub = [r for p,c,a,r in results[fam] if c==cls]
        if not sub: continue
        npersq = sum(1 for r in sub if r['persq'])
        print(f"  {fam} p={cls}mod12: {npersq}/{len(sub)} perfect-square")

print("\nFull detail (p, class, a, e1,e2,e3, perfect_square):")
for fam in ['CM','nonCM']:
    print(f"-- {fam} --")
    for p,cls,a,r in results[fam]:
        print(f"  p={p} (mod12={cls}) a={a}: e1={r['e1']} e2={r['e2']} e3={r['e3']}  persq={r['persq']}")
