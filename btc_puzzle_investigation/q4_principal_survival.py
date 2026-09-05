"""Q4 of the L-triangle: principal-character survival under the Eisenstein phi(m)-averaging.
P_m f(x) = Phi(m)^-1 sum_{r in (Z[w]/m)^*} f(x+r)  (additive translation by units, the CM
analogue of the rational (P_n g)(y)=phi(n)^-1 sum_{(r,n)=1} g(y+2pi r/n)).
Eigenvalue on additive-character mode beta = c_(m)(beta)/Phi(m),  c_(m)(beta)=sum_r e^{2pi i Tr(r*beta)/m}.
Claim: ONLY beta=0 (principal/trivial character) has |lambda|=1 (infinite lifetime = zeta_K pole);
all non-principal decay; the UNIT modes (mu6 sextic orbit) are the distinguished survivors
(lambda = mu_K(m)/Phi(m)), the CM analogue of the rational k=+-1.  Exact; float only for |.|."""
import cmath
from math import gcd

def normf(a,b): return a*a - a*b + b*b            # N(a+b w)
def trf(a,b):   return 2*a - b                    # Tr(a+b w) = (a+bw)+(a+bw^2)
def mul(x,y):
    (a,b),(c,d) = x,y; return (a*c - b*d, a*d + b*c - b*d)   # w^2 = -1-w

def units(m):  return [(a,b) for a in range(m) for b in range(m) if gcd(normf(a,b), m)==1]
def Phi(m):    return len(units(m))
def csum(m, beta, U):                              # Eisenstein Ramanujan sum c_(m)(beta)
    s = 0j
    for r in U:
        s += cmath.exp(2j*cmath.pi*(trf(*mul(r,beta)) % m)/m)
    return s
def mu_K(m):                                       # CM Mobius = c_(m)(unit)
    U = units(m); return csum(m,(1,0),U)

mu6 = [(1,0),(0,1),(-1%1,0)]  # placeholder; build properly below
def mu6_orbit(m): return [ (u[0]%m, u[1]%m) for u in [(1,0),(0,1),(-1,-1),(-1,0),(0,-1),(1,1)] ]

print("=== eigenvalue lambda(beta) = c_(m)(beta)/Phi(m) of the unit-averaging operator ===")
for m in [5, 7, 13]:
    U = units(m); ph = len(U)
    lam = lambda beta: csum(m,beta,U)/ph
    l0  = lam((0,0))
    lu  = lam((1,0))
    # max |lambda| over all non-principal beta
    worst = max((abs(lam((a,b))) for a in range(m) for b in range(m) if (a,b)!=(0,0)))
    typ = "inert" if m%3==2 else ("split" if m%3==1 else "ramified")
    print(f"  m={m:2d} ({typ}, Phi={ph:3d}, N={normf(m,0) if False else m*m}):")
    print(f"     principal  beta=(0,0): lambda = {l0.real:+.4f}  |lambda|={abs(l0):.4f}   <- SURVIVES (=1)")
    print(f"     unit       beta=(1,0): lambda = {lu.real:+.4f}  |lambda|={abs(lu):.4f}   (= mu_K(m)/Phi = {mu_K(m).real:+.0f}/{ph})")
    print(f"     max |lambda| over ALL non-principal beta = {worst:.4f}  (<1 => every non-principal mode decays)")

print("\n=== mu6-invariance of the unit survivor (sextic core = analogue of rational k=+-1) ===")
m = 13; U = units(m); ph = len(U)
for u in mu6_orbit(m):
    lu = csum(m,u,U)/ph
    print(f"  beta = {str(u):8s}: lambda = {lu.real:+.4f}{lu.imag:+.4f}i   |lambda|={abs(lu):.4f}")
print("  => all six mu6-associates share |lambda| (6-fold sextic core), vs the 2-fold +-1 rational case.")

print("\n=== multiplicativity  c_(m1 m2) = c_(m1) c_(m2)  (Euler skeleton, gcd=1) ===")
for (m1,m2) in [(5,7),(7,13),(5,13)]:
    M = m1*m2; UM=units(M); U1=units(m1); U2=units(m2)
    beta=(1,0)
    lhs = csum(M,beta,UM); rhs = csum(m1,beta,U1)*csum(m2,beta,U2)
    print(f"  m1={m1},m2={m2}: c_(m1m2)(1)={lhs.real:+.1f}  vs  c_(m1)c_(m2)={rhs.real:+.1f}  match={abs(lhs-rhs)<1e-6}")

print("\n=== interpretation ===")
print("  beta=0 principal mode = unique infinite-lifetime survivor (lambda=1) = zeta_{Q(sqrt-3)} pole")
print("  (principal ray-class character).  secp256k1's psi is a NON-principal Hecke character")
print("  => a decaying mode (|lambda|<1).  The rational k=+-1 (2-fold) survivor lifts to the")
print("  mu6 (6-fold) unit orbit with lambda = mu_K(m)/Phi(m).  Q4 confirmed for Z[omega].")
