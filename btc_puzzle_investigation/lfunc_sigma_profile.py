"""Q3 of the L-functions triangle: does the log|S(s)| vertical variance track the
L-DEGREE (framework claim, via kappa_infty = #Gamma-factors) or the Selberg
orthonormality constant n_L (= #primitive factors)?  Test on four L-functions of
known degree, incl. secp256k1's own CM Hecke L.  Coefficients exact (int); the
value-distribution measurement uses float (NOT the key signal path)."""
import math, cmath, random
from sympy import primerange

# ---- analytically-normalized prime coefficients a~_p for four L-functions ----
# deg1 primitive: zeta ;  deg1 primitive: L(chi_-3) ;  deg2 REDUCIBLE: zeta_K=zeta*L(chi) ;
# deg2 PRIMITIVE: L(E,psi), E: y^2=x^3+7  (the secp256k1 curve, CM Hecke).
def chi(p): return 0 if p%3==0 else (1 if p%3==1 else -1)

def ap_curve(p):                      # a_p for y^2=x^3+7 (exact, small p brute is fine here)
    if p in (2,3,7): return None      # bad reduction
    c=0
    for x in range(p):
        c += 1 + (1 if pow((x*x*x+7)%p,(p-1)//2,p)==1 else -1) if (x*x*x+7)%p else 1
    return p+1-(c+1)                   # +1 for point at infinity

X = 40000
primes = [p for p in primerange(5, X) if p not in (7,)]
L = {'zeta(deg1,prim)':[], 'L(chi_-3)(deg1,prim)':[], 'zeta_K(deg2,REDUC)':[], 'L(E,psi)(deg2,PRIM)':[]}
degree = {'zeta(deg1,prim)':1,'L(chi_-3)(deg1,prim)':1,'zeta_K(deg2,REDUC)':2,'L(E,psi)(deg2,PRIM)':2}
for p in primes:
    a = ap_curve(p)
    if a is None: continue
    sp = math.sqrt(p)
    L['zeta(deg1,prim)'].append((p, 1.0))
    L['L(chi_-3)(deg1,prim)'].append((p, float(chi(p))))
    L['zeta_K(deg2,REDUC)'].append((p, float(1+chi(p))))     # a_p = 1+chi(p) in {0,2}
    L['L(E,psi)(deg2,PRIM)'].append((p, a/sp))               # analytic normalization a_p/sqrt(p)

# ---- (1) Selberg orthonormality constant  n_L = mean_{p<=X} |a~_p|^2 ----
print(f"primes used: {len(L['zeta(deg1,prim)'])}  (up to {X})")
print("\n=== (1) Selberg constant  n_L = mean |a~_p|^2   (= #primitive factors, NOT degree) ===")
nL = {}
for name, seq in L.items():
    m = sum(v*v for _,v in seq)/len(seq); nL[name]=m
    print(f"  {name:22s}  degree={degree[name]}   mean|a~_p|^2 = {m:.4f}")

# ---- (2) actual log|S| vertical variance:  Var_t( Re S_X(sigma+it) ),  S=sum a~_p p^{-s} ----
# analytic model gives Var = (1/2) sum |a~_p|^2 p^{-2sigma};  confirm by Monte-Carlo over t.
print("\n=== (2) vertical variance of Re S(sigma+it), ratio to zeta  (-> tracks n_L) ===")
def analytic_var(seq, sig): return 0.5*sum(v*v * p**(-2*sig) for p,v in seq)
print(f"  {'sigma':>6} | " + " | ".join(f"{n.split('(')[0]:>8}" for n in L))
for sig in [0.75, 0.65, 0.60, 0.55]:
    base = analytic_var(L['zeta(deg1,prim)'], sig)
    row = " | ".join(f"{analytic_var(seq,sig)/base:8.3f}" for seq in L.values())
    print(f"  {sig:>6} | {row}    (ratios; zeta=1.000)")

# Monte-Carlo confirmation at sigma=0.75 that the phases decorrelate to the analytic value
print("\n=== Monte-Carlo check (sigma=0.75): empirical Var_t vs analytic (1/2)sum|a~|^2 p^-2sig ===")
rng = random.Random(1); ts = [rng.uniform(1e4, 1e6) for _ in range(400)]
for name, seq in L.items():
    vals = []
    for t in ts:
        s = sum(v * math.cos(t*math.log(p)) * p**(-0.75) for p,v in seq)  # Re sum a~_p p^{-sig-it}
        vals.append(s)
    mean = sum(vals)/len(vals); emp = sum((x-mean)**2 for x in vals)/len(vals)
    print(f"  {name:22s}  empirical Var={emp:8.4f}   analytic={analytic_var(seq,0.75):8.4f}")

print("\n=== verdict ===")
print(f"  n_L: zeta={nL['zeta(deg1,prim)']:.2f}  L(chi)={nL['L(chi_-3)(deg1,prim)']:.2f}  "
      f"zeta_K={nL['zeta_K(deg2,REDUC)']:.2f}  L(E,psi)={nL['L(E,psi)(deg2,PRIM)']:.2f}")
print("  The primitive degree-2 CM Hecke L(E,psi) has n_L=1 (SAME as zeta), NOT 2.")
print("  Only the REDUCIBLE zeta_K = zeta*L(chi) shows 2x. So the log|S| sigma-variance")
print("  tracks the SELBERG constant n_L (#primitive factors), not the degree/kappa_infty.")
