import itertools, math, sys
import sympy as sp

def find_irreducible(p, deg):
    if deg == 2:
        for s in range(1, p):
            if pow(s, (p-1)//2, p) != 1:
                return ('shift', s)
    if deg == 3:
        if (p-1) % 3 == 0:
            for s in range(1, p):
                if not any(pow(x,3,p)==s for x in range(p)):
                    return ('shift', s)
        for c1 in range(0, p):
            for c0 in range(1, p):
                if not any((pow(x,3,p) + c1*x + c0) % p == 0 for x in range(p)):
                    return ('trinomial', c1, c0)
    raise RuntimeError

class FF:
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
        for k in range(len(res)-1, deg-1, -1):
            c = res[k]
            if c:
                shift = k - deg
                for idx, rc in enumerate(self.reduce_map):
                    tgt = idx + shift
                    if tgt < deg: out[tgt]=(out[tgt]+c*rc)%p
                    else: res[tgt]=(res[tgt]+c*rc)%p
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

def make_field(p, deg):
    if deg == 1: return F1(p)
    spec = find_irreducible(p, deg)
    if spec[0]=='shift': reduce_map=[spec[1]]+[0]*(deg-1)
    else: _,c1,c0=spec; reduce_map=[(-c0)%p,(-c1)%p,0]
    return FF(p,deg,reduce_map)

def count_pts(field,N,const,quartic):
    g=4 if quartic else 2; gg=math.gcd(g,N); exp=N//gg
    b=field.from_int(const); cnt=1
    for x in field.elements():
        x3=field.mul(field.mul(x,x),x)
        rhs=field.add(x3,b)
        if field.is_zero(rhs): cnt+=1; continue
        if field.pw(rhs,exp)==field.one(): cnt+=gg
    return cnt

def c2_of_a(p, a, f1, f2):
    C1=count_pts(f1,p-1,a,True); E1=count_pts(f1,p-1,a,False)
    C2=count_pts(f2,p*p-1,a,True); E2=count_pts(f2,p*p-1,a,False)
    a1=E1-C1; a2=E2-C2
    e1=a1; e2=(a1*e1-a2)//2
    return e1, e2

print("§1: c2(a) universal law", flush=True)
for p in [43, 67, 79]:
    f1=make_field(p,1); f2=make_field(p,2)
    res_c2=set(); nonres_c2=set(); nres=0; nnon=0; e1_all=set()
    for a in range(1,p):
        is_cr = pow(a,(p-1)//3,p)==1
        e1,e2 = c2_of_a(p,a,f1,f2)
        e1_all.add(e1)
        if is_cr: res_c2.add(e2); nres+=1
        else: nonres_c2.add(e2); nnon+=1
    print(f"p={p}: residues {nres} elems c2={res_c2} (doc -2p={-2*p}) | nonres {nnon} elems c2={nonres_c2} (doc +p={p}) | e1={e1_all}", flush=True)

print("\n§1 eigenvalue root-orders (corrected-memory check):", flush=True)
u = sp.symbols('u')
for label,cpoly in [("residues m=-2: u^4-2u^2+1",u**4-2*u**2+1),
                    ("nonres  m=+1: u^4+u^2+1",u**4+u**2+1)]:
    roots=sp.roots(cpoly); orders=[]
    for r,mult in roots.items():
        k=1; val=r
        while sp.simplify(val-1)!=0 and k<50: k+=1; val=sp.simplify(val*r)
        orders+=[k]*mult
    print(f"  {label}: root orders {sorted(orders)}  (memory: nonres->[3,3,6,6], res->[1,1,2,2])", flush=True)
