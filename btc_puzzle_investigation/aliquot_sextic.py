"""Aliquot cycle / longer-amicability analysis for E: y^2=x^3+7 (secp256k1's curve).
Build q -> #E(F_q) via ZZ[omega] generator (Gauss reduction) + sextic class of 7,
calibrated on small primes, then iterate from p. Exact integer arithmetic."""
import math
from fractions import Fraction
from sympy import isprime

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def Q(v): a,b=v; return a*a - a*b + b*b
def mul(x,y):
    (a,b),(c,d) = x,y; return (a*c-b*d, a*d+b*c-b*d)
def tr(z): return 2*z[0]-z[1]                 # z + conj(z)
units = [(1,0),(0,1),(-1,-1),(-1,0),(0,-1),(1,1)]   # 1, w, w^2, -1, -w, -w^2

def cbrt1(q):                                  # primitive cube root of unity mod q
    for g in range(2,200):
        r = pow(g,(q-1)//3,q)
        if r != 1 and (r*r+r+1) % q == 0: return r
    return None

def gen_norm(q):                               # (a,b) with a^2-ab+b^2=q, via Gauss reduction
    r = cbrt1(q); b1=(q,0); b2=(-r,1)         # a+b*r=0 mod q needs a=-r when b=1
    def twoB(u,v): return 2*u[0]*v[0]-u[0]*v[1]-u[1]*v[0]+2*u[1]*v[1]
    while True:
        if Q(b2) < Q(b1): b1,b2 = b2,b1
        if Q(b1)==0: break
        m = round(Fraction(twoB(b1,b2), 2*Q(b1)))
        if m==0: break
        b2 = (b2[0]-m*b1[0], b2[1]-m*b1[1])
    return b1

def primary(z):                                # unit*z with a=2,b=0 mod 3
    for u in units:
        w = mul(u,z)
        if w[0]%3==2 and w[1]%3==0: return w
    return None

def sextic(cst, pip, q):                        # [cst/pi]_6 exponent, basis zeta6=-w^2 over F_q
    rpi = (-pip[0]*pow(pip[1],-1,q)) % q         # omega -> rpi with pi = 0
    s = pow(cst % q, (q-1)//6, q); z6 = (-(rpi*rpi)) % q; c=1
    for k in range(6):
        if c==s: return k
        c = c*z6 % q

def ap_brute(q):
    c=1
    for x in range(q):
        r=(x*x*x+7)%q; c += 1 if r==0 else (2 if pow(r,(q-1)//2,q)==1 else 0)
    return q+1-c

# unit index (in `units`) <-> power of zeta6=-w^2 :  1,w,w^2,-1,-w,-w^2  =  z6^{0,2,4,3,5,1}
u2z = [0,2,4,3,5,1]; z2u = [0,5,1,3,2,4]

# collect (pi_primary, target-epsilon-as-z6) over small primes, then find constant cst & offset
small=[]
for q in range(11, 500):
    if not isprime(q) or q%3!=1: continue
    a = ap_brute(q); pip = primary(gen_norm(q))
    ui = next((i for i,uu in enumerate(units) if tr(mul(uu,pip))==a), None)
    if ui is not None: small.append((q, pip, u2z[ui]))
# exact rule (verified on all small primes):  epsilon = zeta6^(3 - [4D/pi]_6),  4D = 28
ok = all((3 - sextic(28,pip,q)) % 6 == eps for (q,pip,eps) in small)
print(f"calibration: rule  eps = zeta6^(3-[28/pi]_6)  holds on all {len(small)} small primes ? {ok}")

def numE(q):                                    # #E(F_q), q prime
    if q%3==2: return q+1                        # supersingular for j=0
    pip = primary(gen_norm(q)); eps = (3 - sextic(28,pip,q)) % 6
    return q+1 - tr(mul(units[z2u[eps]], pip))

# sanity: numE(p) must equal n
print(f"check numE(p) == n ? {numE(p)==n}")

# ---- the aliquot trajectory from p:  p -> n -> #E(F_n) -> ...  ----
print("\n=== aliquot trajectory  q_{i+1} = #E(F_{q_i})  starting at p ===")
seq=[p]; cur=p; seen={p:0}
for i in range(1, 12):
    nxt = numE(cur)
    isp = isprime(nxt)
    print(f"  q_{i} = #E(F_(q_{i-1}))  prime={isp}  ==p?{nxt==p}  ==n?{nxt==n}  mod3={nxt%3}  bits={nxt.bit_length()}")
    if nxt in seen:
        print(f"  >>> CYCLE: q_{i} repeats q_{seen[nxt]}  (aliquot cycle length {i-seen[nxt]})"); break
    seen[nxt]=i; seq.append(nxt)
    if not isp:
        print(f"  >>> trajectory leaves the primes at step {i} (q_{i} composite) -> no prime aliquot cycle through p"); break
    cur = nxt

# ---- independent verification that #E(F_n)=p (genuine amicable pair) ----
print("\n=== independent check of #E(F_n)=p (amicable pair p<->n) ===")
t = p+1-n
print(f"  a_n = n+1-#E(F_n) should be n+1-p = 2-t.  numE(n) gives #E(F_n) = {'p' if numE(n)==p else numE(n)}")
qr7 = pow(7, (n-1)//2, n)                       # (7/n): if +1 then (0,sqrt7) is an order-3 pt => 3|#E(F_n)
print(f"  (7/n) = {'+1' if qr7==1 else '-1'};  3|#E(F_n)? {'yes -> would forbid #E=p' if qr7==1 else 'no -> consistent with #E(F_n)=p (3 does not divide p)'}")
# structural reason: Frobenius at n is pi_En = 1-pi = -(pi-1); then (pi_En - 1) = -pi, N(-pi)=p
_f = math.isqrt((4*p - t*t)//3); pi = ((t+_f)//2, _f)   # Frobenius at p, N=p, tr=t
pi_En = (1-pi[0], -pi[1]); print(f"  Frobenius at n = 1-pi;  N(pi_En - 1) = N(-pi) = p ? {Q((pi_En[0]-1, pi_En[1]))==p}")

# ---- sextic class of 7 at the TWIST primes (factors of n_t = 2(p+1)-n) ----
print("\n=== sextic class [7/p]_6 at the twist primes (n_t = 3^2*13^2*3319*22639*C) ===")
C = (2*(p+1)-n)//(9*169*3319*22639)
for q in [13, 3319, 22639, C]:
    lab = f"{q}" if q < 10**6 else f"C(216-bit cofactor)"
    if q%3==1:
        pip=primary(gen_norm(q)); print(f"  q={lab:22s} (=1 mod3): [7/pi_q]_6 = zeta6^{sextic(7,pip,q)}")
    else:
        print(f"  q={lab:22s} (=2 mod3): inert; sixth roots live in F_q^2")
