"""I-III edge of the L-triangle: the vertical-ZFR low-prime common-mode rank, Dirichlet
vs CM.  Feature g(chi, p0) = chi(p0) over small primes p0, family = characters of F_q*
that are TRIVIAL ON THE UNIT GROUP (ray-class characters).  The covariance over small
primes blocks by residue class in F_q*/(F_q*)^d, so its rank = #classes hit (<= d).
Prediction: Dirichlet units {+-1} => d=2 => rank 2 (the paper's common mode);
CM units mu6 => d=6 => rank 6.  Coefficients exact; SVD in float (not the key path)."""
import cmath
from sympy import isprime, primitive_root, primerange

def analyze(q, d, smallprimes):
    g = primitive_root(q)
    ind = {}                                   # discrete log base g in F_q*
    cur = 1
    for e in range(q-1): ind[cur] = e; cur = cur*g % q
    P = [p for p in smallprimes if p % q != 0]
    # sub-family of characters chi_k trivial on the order-d unit subgroup  <=>  d | k
    ks = [k for k in range(0, q-1) if k % d == 0 and k != 0]
    # feature matrix G[row=k, col=p0] = chi_k(p0) = exp(2pi i k*ind(p0)/(q-1))
    import statistics
    cols = len(P)
    # covariance C[p0,p0'] = sum_k chi_k(p0) conj(chi_k(p0')) ; blocks by (F_q*)^d class
    C = [[0j]*cols for _ in range(cols)]
    for a in range(cols):
        for b in range(cols):
            s = 0j
            for k in ks:
                s += cmath.exp(2j*cmath.pi*k*(ind[P[a]%q]-ind[P[b]%q])/(q-1))
            C[a][b] = s
    # rank via eigenvalues (Hermitian) using numpy
    import numpy as np
    ev = np.linalg.eigvalsh(np.array(C))
    ev = sorted(abs(ev), reverse=True)
    tol = max(ev)*1e-9
    rank = sum(1 for x in ev if x > tol)
    # also #distinct d-th-power classes among the small primes
    classes = len({ind[p%q] % d for p in P})
    return rank, classes, ev[:8]

sp = list(primerange(2, 400))
print("=== common-mode rank of the ray-class (unit-trivial) feature covariance ===")
print("  d = |unit group|:  Dirichlet {+-1}=2,  CM mu6=6.  rank should equal #classes hit (<=d).")
for q in [79, 127, 199, 337]:                 # primes q = 1 mod 6 (so both 2|q-1 and 6|q-1)
    if (q-1) % 6: continue
    print(f"\n q = {q}:")
    for d, lab in [(2,'Dirichlet  +-1 (quadratic)'), (6,'CM         mu6 (sextic)  ')]:
        rank, classes, top = analyze(q, d, sp)
        print(f"   {lab}: d={d}  common-mode RANK = {rank}  (#residue-classes hit = {classes})"
              f"  top eig ~ {[round(x,1) for x in top[:d+1]]}")

print("\n=== verdict (HONEST: the prediction FAILED) ===")
print("  The covariance rank came out (q-1)/d - 1 (38/53/70/75 and 12/20/32/46), which GROWS")
print("  with q -- it is just the full rank of the character sub-family, NOT a finite-rank")
print("  (q-independent) common mode. So this construction does NOT reproduce the paper's")
print("  rank-2 Pi, and the 'rank = |units|' idea is disproved by its own output.")
print("  What IS true: Dirichlet/quadratic uses d=2 (units {+-1}), CM/sextic uses d=6 (mu6) --")
print("  the 2 vs 6 lives in d, but it does NOT surface as the covariance RANK here.")
print("  To reproduce the paper's rank-2 finite-rank common mode I need its EXACT g_{p0}(q,j)")
print("  feature + how Pi is extracted (pooled/normalized across q). Flagged, not resolved.")
