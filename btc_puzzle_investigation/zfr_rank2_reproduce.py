"""Faithful reproduction of Vertical-ZFR Appendix B, Table 4 (the rank-2 common mode).
Exact paper construction: Q=100, q prime in [Q/2,Q]; ALL non-principal chi_j mod q;
feature matrix F[(q,j), p0] = (chi_j(p0) - mu_{p0}(q))/sqrt(q-1), columns p0 in P0={2..29}.
SVD -> singular spectrum; PR = (sum s^2)^2 / sum s^4 on the eigenvalues s_i^2.
Paper claims: sigma/sigma1 = 1, 0.987, 0.312, 0.298 ; PR ~ 1.97 (rank 2).
Orthogonality predicts: FLAT spectrum, PR ~ |P0| = 10.  Let the computation decide."""
import numpy as np, cmath
from sympy import primerange, primitive_root, isprime

P0 = [2,3,5,7,11,13,17,19,23,29]           # first 10 primes (paper's low-prime features)
Q  = 100
qs = [q for q in primerange(Q//2, Q+1)]    # q prime in [50,100]
print(f"moduli q in [{Q//2},{Q}]: {qs}  (|P0|={len(P0)} small primes)")

rows = []
for q in qs:
    g = primitive_root(q)
    ind = {}; cur = 1
    for e in range(q-1): ind[cur % q] = e; cur = cur*g % q
    inv = 1.0/np.sqrt(q-1)
    for j in range(1, q-1):                 # all NON-principal characters chi_j
        # mu_{p0}(q) = -1 if p0|q else 0 ; p0<q prime => 0
        row = [cmath.exp(2j*cmath.pi*j*ind[p0 % q]/(q-1)) * inv for p0 in P0]
        rows.append(row)
F = np.array(rows)                          # (|I_Q|) x 10
print(f"feature matrix F: {F.shape}")

# SVD singular spectrum
U,S,Vh = np.linalg.svd(F, full_matrices=False)
s = S/S[0]
print("\n=== singular spectrum sigma_i/sigma_1  (paper Table 4: 1, 0.987, 0.312, 0.298) ===")
print("  " + "  ".join(f"{x:.3f}" for x in s))
lam = S**2
PR = (lam.sum()**2)/(lam**2).sum()
var2 = (lam[0]+lam[1])/lam.sum()
print(f"\n  variance in top-2 singular subspace = {var2:.3f}   (paper: 0.97)")
print(f"  participation ratio PR = {PR:.3f}   (paper: 1.97;  orthogonality predicts ~{len(P0)})")

# the exact Gram, to confirm the orthogonality structure
G = F.conj().T @ F
evG = np.sort(np.linalg.eigvalsh(G))[::-1]
print("\n=== Gram F*F eigenvalues (orthogonality => ~flat: nine near max, one depressed) ===")
print("  " + "  ".join(f"{x:.2f}" for x in evG))
print(f"  ratio max/min = {evG[0]/evG[-1]:.2f}   (rank-2 would need a HUGE ratio; flat ~ 1.2)")
