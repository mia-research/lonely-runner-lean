#!/usr/bin/env python3
"""
METHOD 4 (replaces O(q) brute over a tiny window): CM/Cornacchia point counting for
y^2 = x^3 + 7 (j=0). #E(F_q) via 4q = L^2 + 27 M^2 gives six candidate sextic-twist
traces; disambiguate the ONE for b=7 by a random-point order test. O(polylog) per prime
=> reach start primes ~1e6 (vs Method E's <2e4) to hunt length-3 aliquot cycles in the
Silverman-Stange-EXCLUDED j=0 case.

Controls: (a) CM count must match a direct O(q) count on small primes; (b) machinery
must reproduce the amicable pair 67<->79.
"""
from sympy import isprime, primerange
from sympy.solvers.diophantine.diophantine import cornacchia

B = 7
def ec_add(P, Q, q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%q==0: return None
    if P==Q:
        s=(3*x1*x1)*pow(2*y1%q,-1,q)%q
    else:
        s=(y2-y1)*pow((x2-x1)%q,-1,q)%q
    x3=(s*s-x1-x2)%q; y3=(s*(x1-x3)-y1)%q
    return (x3,y3)
def ec_mul(k,P,q):
    R=None; Q=P
    while k>0:
        if k&1: R=ec_add(R,Q,q)
        Q=ec_add(Q,Q,q); k>>=1
    return R

def count_direct(q):                      # O(q) reference
    s=0; e=(q-1)//2
    for x in range(q):
        v=(x*x%q*x+B)%q
        s+= 0 if v==0 else (1 if pow(v,e,q)==1 else -1)
    return q+1+s

def candidate_traces(q):
    """six sextic-twist traces of a j=0 curve at split q from the Eisenstein norm
    form q = a^2 - ab + b^2.  Get a primitive q = A^2 + 3 B^2 (Cornacchia; always
    primitive for q==1 mod 3), then a=A+B, b=2B gives a^2-ab+b^2=q, and the traces
    are 2Re(u*pi), u in mu_6:  { +-(2a-b), +-(a+b), +-(2b-a) }."""
    try:
        reps=cornacchia(1,3,q)             # q = A^2 + 3 B^2, primitive
    except Exception:
        return None
    if not reps: return None
    A,Bv=next(iter(reps))
    a=A+Bv; b=2*Bv                          # a^2-ab+b^2 == q
    base={2*a-b, a+b, 2*b-a}
    sols=set()
    for t in base: sols.add(t); sols.add(-t)
    lim=2*int(q**0.5)+2
    return sorted({t for t in sols if abs(t)<=lim})

def _rand_point(q, rng):
    for _ in range(60):
        x=rng.randrange(q); v=(x*x%q*x+B)%q
        if v==0: continue
        if pow(v,(q-1)//2,q)==1:
            y=pow(v,(q+1)//4,q) if q%4==3 else _tonelli(v,q)
            if y is not None and (y*y-v)%q==0: return (x,y)
    return None

def count_cm(q):
    """#E via exact CM trace candidates + group-EXPONENT recovery. Point-killing gives
    the exponent E_g (=lcm of point orders), not the order. For E(F_q)=Z/d1 x Z/d2 with
    d1|d2=E_g, #E=d1*E_g with d1|E_g -> unique among the six trace candidates (fixes the
    non-cyclic-group ambiguity, e.g. q=181: Z/4 x Z/52)."""
    if q % 3 == 2:                # inert prime: j=0 curve is supersingular, a=0
        return q + 1
    from math import lcm
    from sympy import factorint
    cands=candidate_traces(q)
    if not cands: return None
    orders=sorted({q+1-a for a in cands})
    import random
    rng=random.Random(q)
    Eg=1
    for _ in range(8):
        R=_rand_point(q, rng)
        if R is None: continue
        killers=[N for N in orders if ec_mul(N,R,q) is None]
        if not killers: continue
        K=killers[0]                              # any multiple of ord(R)
        o=K
        for p in factorint(K):
            while o % p == 0 and ec_mul(o//p, R, q) is None:
                o//=p
        Eg=lcm(Eg, o)                             # accumulate the exponent d2
    sel=[N for N in orders if N % Eg == 0 and Eg % (N//Eg) == 0]   # d1|d2 constraint
    if len(sel)==1: return sel[0]
    mult=[N for N in orders if N % Eg == 0]
    return min(mult, key=lambda N: abs(N-(q+1))) if mult else None

def _tonelli(nn,p):
    if pow(nn,(p-1)//2,p)!=1: return None
    if p%4==3: return pow(nn,(p+1)//4,p)
    s=p-1; e=0
    while s%2==0: s//=2; e+=1
    n2=2
    while pow(n2,(p-1)//2,p)!=p-1: n2+=1
    x=pow(nn,(s+1)//2,p); b=pow(nn,s,p); g=pow(n2,s,p); r=e
    while True:
        t=b; m=0
        for m in range(r):
            if t==1: break
            t=t*t%p
        if m==0: return x
        gs=pow(g,1<<(r-m-1),p); g=gs*gs%p; x=x*gs%p; b=b*g%p; r=m

print("=== METHOD 4: CM/Cornacchia aliquot search (j=0) ===\n")
# control (a): CM vs direct on small primes
ok=True
for q in list(primerange(11,400)):
    if q in (2,3,7): continue
    cd=count_cm(q); dr=count_direct(q)
    if cd!=dr: ok=False; print(f"  MISMATCH q={q}: cm={cd} direct={dr}")
print(f"[CTRL a] CM == direct on primes 11..400: {ok}")
# control (b): amicable pair
print(f"[CTRL b] #E(F_67)={count_cm(67)} (expect 79); #E(F_79)={count_cm(79)} (expect 67)\n")

def chain(q0, maxlen=14, bound=10**12):
    seen={q0:0}; ch=[q0]; cur=q0
    for _ in range(maxlen):
        if cur in (2,3,7) or cur>bound or cur%3!=1: return ch,"stop"
        m=count_cm(cur)
        if m is None or not isprime(m): return ch,"terminate"
        if m in seen: return ch[seen[m]:], f"cycle-{len(ch)-seen[m]}"
        seen[m]=len(ch); ch.append(m); cur=m
    return ch,"maxlen"

print("searching start primes up to 1,000,000 for length>=3 aliquot cycles ...")
longest=1; found=[]
cnt=0
for q0 in primerange(5, 1_000_000):
    if q0%3!=1 or q0==7: continue
    cnt+=1
    ch,kind=chain(q0)
    if kind.startswith("cycle-"):
        L=int(kind.split("-")[1]); longest=max(longest,L)
        if L>=3: found.append(ch)
print(f"  scanned {cnt} split primes; longest cycle length = {longest}; "
      f"length>=3 cycles: {len(found)}")
for ch in found[:10]: print("   ", " -> ".join(map(str,ch)))
if not found:
    print("  none. Scoped null: no length-3 aliquot cycle for y^2=x^3+7 among ~1e6")
    print("  start primes -- j=0 empirically obeys the j!=0 theorem's conclusion here,")
    print("  over a window 50x wider than Method E. Not a proof of nonexistence.")
