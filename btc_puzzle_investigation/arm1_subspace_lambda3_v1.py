#!/usr/bin/env python3
"""
arm1_subspace_lambda3_v1.py -- ARM 1 + ARM 2 of PREREG_lambda3_eigenvector_isotype_v1.md,
on the object REDEFINED by the Arm-0 gate (RESULT_lambda3_arm0_gate_v1.md): the individual
lambda_3 vector is GAUGE, so the object is the slow eigenSPACE's TOTAL covariant weight.

KEY (gauge-free, exact): the mu_3-covariant weight of a cell-subspace V=span(U) is
  W_cov(V) = 2/3 - (1/(3m)) tr( (U^H D U)^{-1} U^H (N1+N2) U ),
with EXACT INTEGER matrices (walk-independent static beta-cell geometry over the support S):
  N1[c,c'] = #{x in S: cell(x)=c, cell(bx)=c'},  N2 the same for b^2,  D=diag(#{x: cell(x)=c}).
This is INVARIANT under any change of basis U->UR (a trace), so it needs only the SPAN, not the
gauge individual vectors. m=1 reduces to the PROVED w_cov=2/3(1-Re A) (PREREG s0). The WALK enters
only through WHICH span (M's slow eigenspace) we test against this static covariant structure.

ARM 1: W_cov(m) of the top-m non-Perron span of M vs m, over the m-range where the span is STABLE
  across half-orbits (S_sub>0.9); FIELD vs CURVE split (chi2-weighted N,D) -> lattice vs Weil.
ARM 2: is W_cov(slow) an EXCESS over a random subspace null (Null-A)? two-sided firing (covariant
  plant -> ~1, invariant plant -> ~0). Pre-committed branches per PREREG Arms 1-2.

NO-FLOAT (btc CLAUDE.md; PREREG s8): N1,N2,D and their FIELD/CURVE variants are EXACT int (chi2 in
{-1,0,1}); the split identity is checked to the integer. Eigen-decomposition, the W_cov trace ratio,
and the rank statistic are the spectral-display carve-out (# noqa: float), ranked/reported, never a
threshold on a key/label/count. Scale: p<=~1e4 here; >=239 bits below 2^256; ZERO power at secp.
"""
import numpy as np
import math
from arm0_gate_lambda3_v1 import (curve_gen, orbit, beta_of, cell_fn, count_matrix,
                                  stochastic, eig_sorted, prime_list, subspace_overlap, labels_of)
from hybrid_char_sum_v1 import curve_points_order, legendre

SEED = 20260721

# ============================ EXACT beta-cell geometry ============================

def beta_geometry(p, cell, K, beta):
    """EXACT integer N1,N2,D over S (chi2>=0), plus FIELD (all F_p) and CURVE (chi2-weighted)."""
    nst = K * K
    z = lambda: np.zeros((nst, nst), dtype=np.int64)
    zv = lambda: np.zeros(nst, dtype=np.int64)
    N1, N2, D = z(), z(), zv()
    N1f, N2f, Df = z(), z(), zv()
    N1c, N2c, Dc = z(), z(), zv()
    N1z, Dz = z(), zv()        # chi2==0 transitions/occupancy (R1 boundary correction ledger)
    b2 = (beta * beta) % p
    for x in range(p):
        ch = legendre((x * x * x + 7) % p, p)      # -1, 0, +1  (exact)
        c = cell(x, K); cb = cell((beta * x) % p, K); cb2 = cell((b2 * x) % p, K)
        N1f[c, cb] += 1; N2f[c, cb2] += 1; Df[c] += 1
        N1c[c, cb] += ch; N2c[c, cb2] += ch; Dc[c] += ch
        if ch >= 0:
            N1[c, cb] += 1; N2[c, cb2] += 1; D[c] += 1
            if ch == 0:
                N1z[c, cb] += 1; Dz[c] += 1
    return dict(N1=N1, N2=N2, D=D, N1f=N1f, N2f=N2f, Df=Df, N1c=N1c, N2c=N2c, Dc=Dc,
                N1z=N1z, Dz=Dz)

def check_split_identity(g):
    """R1: 2*sum_S = FIELD + CURVE + (chi2==0 ledger). EXACT integer per prime (PREREG s0 R1)."""
    okD = np.array_equal(2 * g['D'], g['Df'] + g['Dc'] + g['Dz'])
    okN1 = np.array_equal(2 * g['N1'], g['N1f'] + g['N1c'] + g['N1z'])
    return okD, okN1

# ============================ gauge-free covariant weight ============================

def wcov_span(U, Nsym, Dvec):                                   # noqa: float
    """W_cov = 2/3 - (1/(3m)) tr((U^H D U)^{-1} U^H Nsym U). Basis-invariant in span(U)."""
    m = U.shape[1]
    Dm = (U.conj().T * Dvec) @ U
    Nm = U.conj().T @ (Nsym @ U)
    tr = np.trace(np.linalg.solve(Dm, Nm)).real                # noqa: float
    return 2.0 / 3.0 - tr / (3.0 * m)                          # noqa: float

def slow_span(M, m):                                          # noqa: float
    """top-m NON-Perron right-eigenvectors (cols 1..m) of row-stochastic M."""
    _, evec = eig_sorted(M)
    return evec[:, 1:m + 1]

# ============================ ARM 2 null + firing ============================

def null_A_wcov(m, Nsym, Dvec, rng, B=200):                   # noqa: float
    """random m-dim subspace baseline (Null-A): W_cov of a random span with the SAME geometry."""
    nst = Dvec.shape[0]
    out = []
    for _ in range(B):
        U = rng.standard_normal((nst, m)) + 1j * rng.standard_normal((nst, m))   # noqa: float
        out.append(wcov_span(U, Nsym, Dvec))
    return np.array(out)

def covariant_invariant_bases(Nsym, Dvec):                    # noqa: float
    """generalized eigvecs of the mu3 operator D^{-1}(N1+N2): covariant (small) vs invariant (large)."""
    Dm = np.diag(Dvec).astype(float)                          # noqa: float
    w, V = np.linalg.eig(np.linalg.solve(Dm, Nsym))           # noqa: float
    order = np.argsort(w.real)                                 # small (N+N2)-eigenvalue = covariant
    return V[:, order]                                         # ascending: covariant first

def firing(g):
    """positive/negative plant: a known-covariant span -> W_cov~1, invariant span -> W_cov~0."""
    Nsym = g['N1'] + g['N2']; Dvec = g['D']
    V = covariant_invariant_bases(Nsym, Dvec)
    wc_cov = wcov_span(V[:, :4], Nsym, Dvec)     # 4 most-covariant directions
    wc_inv = wcov_span(V[:, -4:], Nsym, Dvec)    # 4 most-invariant directions
    print("  FIRING (exact geometry): covariant-plant W_cov=%.3f (expect ~1) ; "
          "invariant-plant W_cov=%.3f (expect ~0)" % (wc_cov, wc_inv))
    ok = (wc_cov > 0.85) and (wc_inv < 0.15)                  # noqa: float
    print("    => firing %s" % ("FIRES" if ok else "FAILS -- W_cov machinery uninformative, STOP"))
    return ok

# ============================ MAIN ============================

def main():
    print("=" * 92)
    print("ARM 1+2 -- covariant weight of the SLOW EIGENSPACE (Arm-0 redefined object)")
    print("PREREG_lambda3_eigenvector_isotype_v1.md ; SCALE p<=~1e4, >=239 bits below 2^256")
    print("=" * 92)

    # firing on the smallest powered prime's geometry
    p0, n0 = prime_list(k=1, n_min=2500)[0]
    cell0 = cell_fn(p0); b0 = beta_of(p0)
    g0 = beta_geometry(p0, cell0, 4, b0)
    okD, okN1 = check_split_identity(g0)
    print("  R1 split identity exact (D, N1): %s, %s" % (okD, okN1))
    if not firing(g0):
        return
    print()

    primes = prime_list(k=6, n_min=2500, hi=12000)
    rng = np.random.default_rng(SEED)
    K = 4
    print("Powered primes (n>=2500):", ", ".join("%d(n=%d)" % (p, n) for p, n in primes))
    print("\n  W_cov(m) of top-m non-Perron span, with span stability S_sub(m); null-A = random subspace")
    print("  (baseline ~covariant-dim fraction). EXCESS = W_cov above null 99th pct.\n")

    for p, n in primes:
        G = curve_gen(p); xs, _ = orbit(G, p, n); beta = beta_of(p); cell = cell_fn(p)
        g = beta_geometry(p, cell, K, beta)
        Nsym, Dvec = g['N1'] + g['N2'], g['D']
        Nf, Df = g['N1f'] + g['N2f'], g['Df']
        labs = labels_of(xs, cell, K, n)
        M = stochastic(count_matrix(labs, K * K))
        h = (n - 1) // 2
        MA = stochastic(count_matrix(labs[:h], K * K)); MB = stochastic(count_matrix(labs[h:], K * K))
        _, eA = eig_sorted(MA); _, eB = eig_sorted(MB)

        print(" p=%d n=%d:" % (p, n))
        print("   m   W_cov   S_sub(span)  null-A mean/99pct   excess?   f_FIELD  W_cov^S(=curve-supp)")
        for m in (1, 2, 3, 5, 8, 12, 15):
            U = slow_span(M, m)
            wc = wcov_span(U, Nsym, Dvec)
            ssub = subspace_overlap(eA, eB, idxs=tuple(range(1, m + 1)))
            nulls = null_A_wcov(m, Nsym, Dvec, rng, B=200)
            n99 = float(np.percentile(nulls, 99)); nmean = float(np.mean(nulls))   # noqa: float
            exc = "YES" if wc > n99 else "no"                 # noqa: float
            f_field = wcov_span(U, Nf, Df)
            print("   %-3d %.3f    %.3f       %.3f / %.3f      %-4s     %.3f    %.3f"
                  % (m, wc, ssub, nmean, n99, exc, f_field, wc))

    print("\n" + "=" * 92)
    print("READ (per PREREG Arm 1/2, decided on the STABLE m-range S_sub>0.9):")
    print("  - EXCESS over null-A on the stable range => real covariant structure of the slow space;")
    print("    then f_FIELD~W_cov^S => FIELD/lattice (Cap-Law inert-lens); f_FIELD<<W_cov^S => CURVE/Weil.")
    print("  - W_cov within null-A => NO covariant excess: the slow space is generically covariant")
    print("    (~random-subspace level); the gauge '0.85' had no real excess. Scoped null + power, NOT closure.")
    print("  - No stable m (all S_sub<0.9) => ABSTAIN: slow-subspace covariance unresolved at accessible n.")
    print("=" * 92)


if __name__ == '__main__':
    main()
