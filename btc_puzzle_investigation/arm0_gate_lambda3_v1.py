#!/usr/bin/env python3
"""
arm0_gate_lambda3_v1.py -- ARM 0 (GATE) of PREREG_lambda3_eigenvector_isotype_v1.md.

QUESTION (well-definedness only; NO hypothesis tested here):
  Is "the lambda_3 eigenvector" of the d->d+1 cell-walk transfer operator M a
  WELL-DEFINED object, or is it gauge -- a near-degenerate eigenspace (individual
  vector defined only up to rotation) or a K (cell-resolution) artifact?
A failed gate REDEFINES the object (individual vector -> slow eigenspace, or a
single-K value -> a K-curve); it does not proceed on a gauge quantity.

OBJECT (PREREG s1): E:y^2=x^3+7 / F_p, p=1 mod 3, n=#E prime; x_d=x([d]G);
  cell(x,K) = exact Eisenstein reduced-basis KxK bin; M = row-stochastic transfer
  of the label sequence L_d=cell(x_d,K) along d->d+1. |l1|>=|l2|>=|l3|>=|l4|...

STATISTICS (PREREG Arm 0):
  gaps D23=|l2|-|l3|, D34=|l3|-|l4|; real/complex flag (|Im l3|, conjugate pair);
  noise band sigma_gap (half-orbit split + B block-bootstrap of the label seq);
  eigenvector stability S = |<v3_A, v3_B>| across half-orbits (+ subspace overlap
  S_sub of the {v2,v3} slow pair, gauge-independent); K-convergence of the
  covariant weight w_cov(K)=2/3*(1-Re A) over K in {4,6,8,10}, guarded to cells
  with n/K^2 >= 20 samples/source-state.

FIRING (PREREG Arm 0, mandatory): two synthetic plants run through the SAME
  pipeline -- a well-separated chain (must read D23 >> sigma, S ~ 1) and an exactly
  degenerate tensor chain C1 (x) C1 (must read D23 within sigma, individual S low,
  subspace S_sub ~ 1). If the gate cannot tell these apart, Arm 0 is uninformative.

PRE-COMMITTED BRANCHES (PREREG Arm 0): GATE-PASS / GATE-FAIL(degenerate,gauge) /
  GATE-FAIL(K-drift) / ABSTAIN. Printed verbatim against the thresholds
  (3*sigma_gap, S>0.9, K-conv |w(10)-w(8)|<|w(6)-w(4)| and <0.1) fixed in the prereg.

NO-FLOAT (btc CLAUDE.md; PREREG s8): the STATE-DEFINING path is EXACT --
  cell labels (cell_fn, Fraction) and transition COUNTS (Python int / int64). The
  row-normalization, np.linalg.eig, gaps, A, w_cov and every statistic are the
  documented spectral-DISPLAY carve-out (marked '# noqa: float'): monotone sizes
  ranked/reported, never a threshold on a key/label/count. No key, (n,k,D) or
  target is in the path; p <= ~10^5 (>= 239 binary orders below 2^256 -- ZERO power
  at secp; every number here is scoped to this p-range, K-set, this M, first gen).
"""
import numpy as np
import math
from sympy import isprime
from conservation_spectrum_v2 import curve_gen, orbit, beta_of, cell_fn
from hybrid_char_sum_v1 import curve_points_order, legendre

SEED = 20260721
TOL = 1e-9          # noqa: float  (spectral zero-tolerance; display only, not a data threshold)

# =========================================================================
# EXACT signal path  (labels + integer counts; no float touches a label/count)
# =========================================================================

def prime_list(k=12, lo=400, hi=200000, n_min=0):
    """k smallest primes p>lo with p=1 mod 3, p not in {2,3,7}, #E(F_p) prime, and n>=n_min."""
    out = []
    p = lo + 1
    while len(out) < k and p < hi:
        if isprime(p) and p % 3 == 1 and p not in (2, 3, 7):
            n = curve_points_order(p)
            if isprime(n) and n >= n_min:
                out.append((p, n))
        p += 1
    return out

def support_x(p):
    """S = {x in F_p : chi2(x^3+7) >= 0}  (QR or zero) -- the code's legendre>=0 support."""
    return [x for x in range(p) if legendre((x * x * x + 7) % p, p) >= 0]

def labels_of(xs, cell, K, n):
    """exact int label sequence L_d = cell(x_d, K), d=1..n-1 (all finite at prime order)."""
    return [cell(xs[d], K) for d in range(1, n)]

def count_matrix(labs, nst):
    """EXACT integer transition-count matrix (int64; counts < 2^53 at n<=~10^5)."""
    C = np.zeros((nst, nst), dtype=np.int64)
    for t in range(len(labs) - 1):
        C[labs[t], labs[t + 1]] += 1
    return C

def block_bootstrap_labels(labs, rng):
    """moving-block bootstrap of the label sequence (block len = isqrt(len); exact resample)."""
    m = len(labs)
    L = max(1, math.isqrt(m))
    nb = (m + L - 1) // L
    starts = rng.integers(0, max(1, m - L + 1), size=nb)
    out = []
    for s in starts:
        out.extend(labs[int(s):int(s) + L])
    return out[:m]

# =========================================================================
# Spectral DISPLAY carve-out  (float; ranked/reported only)   # noqa: float
# =========================================================================

def stochastic(C):                                              # noqa: float
    rs = C.sum(1, keepdims=True)
    rs = np.where(rs == 0, 1, rs)
    return C / rs                                               # noqa: float

def eig_sorted(M):                                             # noqa: float
    ev, evec = np.linalg.eig(M)                                # noqa: float
    order = np.argsort(-np.abs(ev))
    return ev[order], evec[:, order]

def unit(v):                                                   # noqa: float
    nrm = np.linalg.norm(v)
    return v / nrm if nrm > 0 else v                           # noqa: float

def covariant_A(v, Sx, cell, K, beta, p):                     # noqa: float
    """A = sum_S phi(beta x) conj(phi(x)) / sum_S |phi(x)|^2 ,  phi(x)=v[cell(x,K)]."""
    num = 0j
    den = 0.0                                                  # noqa: float
    for x in Sx:
        phix = v[cell(x, K)]
        phibx = v[cell((beta * x) % p, K)]
        num += phibx * np.conj(phix)
        den += abs(phix) ** 2                                  # noqa: float
    return num / den if den > 0 else 0j                        # noqa: float

def w_cov_of(A):                                               # noqa: float
    """PROVED (PREREG s0): w_cov = 2/3 (1 - Re A)."""
    return (2.0 - 2.0 * A.real) / 3.0                          # noqa: float

def gaps_flags(ev):                                           # noqa: float
    a = np.abs(ev)
    l1, l2, l3, l4 = a[0], a[1], a[2], a[3]
    d23, d34 = l2 - l3, l3 - l4
    im3 = abs(ev[2].imag)
    conj23 = abs(ev[1] - np.conj(ev[2])) < 1e-6 * (abs(ev[1]) + 1e-12)   # noqa: float
    conj34 = abs(ev[2] - np.conj(ev[3])) < 1e-6 * (abs(ev[2]) + 1e-12)   # noqa: float
    return dict(l1=l1, l2=l2, l3=l3, l4=l4, d23=d23, d34=d34,
                im3=im3, conj_pair=bool(conj23 or conj34))

def subspace_overlap(evecA, evecB, idxs=(1, 2)):              # noqa: float
    """gauge-independent overlap of the slow {v2,v3} subspaces in [0,1]: ||Q_A^H Q_B||_F/sqrt(dim),
    Q = ORTHONORMAL basis (QR) of span(v2,v3) -- eigenvectors of the non-normal M are NOT orthonormal,
    so a raw u u^H sum is not a projector. =1 iff subspaces coincide, 0 if orthogonal."""
    QA = np.linalg.qr(evecA[:, list(idxs)])[0]               # noqa: float
    QB = np.linalg.qr(evecB[:, list(idxs)])[0]               # noqa: float
    return float(np.linalg.norm(QA.conj().T @ QB) / math.sqrt(len(idxs)))   # noqa: float

# =========================================================================
# GATE
# =========================================================================

def gate_one(p, n, xs, beta, cell, K, B=200):
    """all Arm-0 statistics for one (p,K). Returns a dict of float displays."""
    labs = labels_of(xs, cell, K, n)
    nst = K * K
    C = count_matrix(labs, nst)                      # EXACT
    ev, evec = eig_sorted(stochastic(C))             # carve-out
    gf = gaps_flags(ev)
    Sx = support_x(p)
    A = covariant_A(evec[:, 2], Sx, cell, K, beta, p)
    wcov = w_cov_of(A)

    # half-orbit stability
    h = (n - 1) // 2
    evA = eig_sorted(stochastic(count_matrix(labs[:h], nst)))[1]
    evB = eig_sorted(stochastic(count_matrix(labs[h:], nst)))[1]
    S = float(abs(np.vdot(unit(evA[:, 2]), unit(evB[:, 2]))))     # noqa: float
    S_sub = subspace_overlap(evA, evB)

    # bootstrap noise band on the gaps
    rng = np.random.default_rng(SEED + p * 1000 + K)
    d23s, d34s = [], []
    for _ in range(B):
        bl = block_bootstrap_labels(labs, rng)
        evb = eig_sorted(stochastic(count_matrix(bl, nst)))[0]
        g = gaps_flags(evb)
        d23s.append(g['d23']); d34s.append(g['d34'])
    sig23 = float(np.std(d23s)); sig34 = float(np.std(d34s))     # noqa: float

    return dict(K=K, nst=nst, samp_per_row=(n - 1) / nst,        # noqa: float
                wcov=wcov, A=A, S=S, S_sub=S_sub,
                sig23=sig23, sig34=sig34, **gf)

def k_convergence(p, n, xs, beta, cell, Ks=(4, 6, 8, 10), B=80):
    """w_cov(K) with the n/K^2>=20 guard; returns {K: (wcov, ok)}."""
    out = {}
    for K in Ks:
        ok = (n - 1) >= 20 * K * K
        if not ok:
            out[K] = (None, False); continue
        r = gate_one(p, n, xs, beta, cell, K, B=B)
        out[K] = (r['wcov'], True)
    return out

# =========================================================================
# FIRING (mandatory positive/negative controls for the gate machinery)
# =========================================================================

def sample_chain(T, n, rng, s0=0):
    """sample a length-n label path from stochastic T (synthetic plant; RNG carve-out)."""
    st = s0
    out = [st]
    for _ in range(n - 1):
        st = int(rng.choice(T.shape[0], p=T[st]))    # noqa: float
        out.append(st)
    return out

def holding_chain(holds):                                       # noqa: float
    """diag(holds) + rank-1 uniform off-mass: row-stochastic, real well-spaced spectrum near `holds`.
    Eigenvector of the r-th slow mode ~ e_r (basis vector) when holds are distinct -> STABLE."""
    m = len(holds)
    T = np.empty((m, m))
    for i in range(m):
        off = (1.0 - holds[i]) / m                              # noqa: float
        T[i, :] = off
        T[i, i] = holds[i] + off                                # noqa: float
    return T

def _S_pair(labs, nst):                                         # noqa: float
    """half-orbit stability of the individual v3 and of the slow {v2,v3} subspace."""
    h = len(labs) // 2
    a = eig_sorted(stochastic(count_matrix(labs[:h], nst)))[1]
    b = eig_sorted(stochastic(count_matrix(labs[h:], nst)))[1]
    return float(abs(np.vdot(unit(a[:, 2]), unit(b[:, 2])))), subspace_overlap(a, b)  # noqa: float

def firing(nst=16):
    """Mandatory gate control. Plants with a CONTROLLED spectrum, swept over n to calibrate power:
    find n* = smallest n at which the gate resolves a WELL-DEFINED v3 (SEP: S>0.9) AND flags an
    exactly-degenerate one (DEGEN: individual S<0.9 but subspace S_sub>0.9). Real primes need n>=n*."""
    rng = np.random.default_rng(SEED)
    # SEP: top modes well separated (|l2|~.95, |l3|~.80, gap~.15), rest clustered low
    sep = holding_chain([0.95, 0.80, 0.62, 0.45] + [0.30] * (nst - 4))   # noqa: float
    # DEGEN: C1 (x) C1 with C1 real-spectrum -> EXACT degenerate pair at positions 2,3
    k1 = math.isqrt(nst)
    C1 = holding_chain([0.90, 0.55, 0.25, 0.10][:k1] + [0.15] * (k1 - 4 if k1 > 4 else 0))  # noqa: float
    deg = np.kron(C1, C1)                                        # noqa: float

    gsep = gaps_flags(eig_sorted(sep)[0]); gdeg = gaps_flags(eig_sorted(deg)[0])
    print("  FIRING analytic (exact operators, %d states):" % nst)
    print("    SEP  : |l2|=%.3f |l3|=%.3f |l4|=%.3f  D23=%.3f D34=%.3f  (distinct |l|, well separated)"
          % (gsep['l2'], gsep['l3'], gsep['l4'], gsep['d23'], gsep['d34']))
    print("    DEGEN: |l2|=%.3f |l3|=%.3f  D23=%.2e  (exact tensor degeneracy at pos 2-3)"
          % (gdeg['l2'], gdeg['l3'], gdeg['d23']))
    print("  FIRING sampled sweep -- S(v3 individual) | S_sub(slow subspace, [0,1]):")
    print("      n        SEP:S   S_sub     DEGEN:S  S_sub    note")
    nstar = None; gauge_ok = False
    for n in (400, 1000, 2500, 6000, 15000, 40000):
        Ss, Ssub_s = _S_pair(sample_chain(sep, n, rng), nst)
        Sd, Ssub_d = _S_pair(sample_chain(deg, n, rng), nst)
        sep_res = Ss > 0.9                                        # noqa: float
        gauge_flag = (Ssub_d > 0.9) and (Ssub_d - Sd > 0.15)     # noqa: float
        if nstar is None and sep_res:
            nstar = n
        if nstar is not None and n >= nstar and gauge_flag:
            gauge_ok = True
        note = []
        if sep_res: note.append("SEP-well-def")
        if gauge_flag: note.append("DEGEN-gauge-flagged")
        if n == nstar: note.append("<-n*")
        print("    %7d    %.3f   %.3f      %.3f   %.3f    %s"
              % (n, Ss, Ssub_s, Sd, Ssub_d, " ".join(note) or "underpowered"))
    ok = (nstar is not None) and gauge_ok
    print("    => firing %s"
          % ("FIRES: SEP's well-defined v3 resolves (S>0.9) and DEGEN reads S_sub>>S"
             " (subspace stable, individual gauge)"
             if ok else "did NOT both resolve+flag within swept n (extend n)"))
    print("       n* = %s (min n for a trustworthy individual-vector verdict)" % nstar)
    return ok, nstar

# =========================================================================
# MAIN
# =========================================================================

def run_gate_table(primes, hdr=True):
    """gate at K=4 on each (p,n); returns (pass_votes, degen_votes, rows)."""
    if hdr:
        print("  p       n      |l2|   |l3|   |l4|   D23     3sig23  S(v3) S_sub Iml3   conj wcov  verdict")
        print("  " + "-" * 92)
    pv = dv = 0
    for p, n in primes:
        G = curve_gen(p); xs, _ = orbit(G, p, n); beta = beta_of(p); cell = cell_fn(p)
        r = gate_one(p, n, xs, beta, cell, 4)
        gatepass = (r['d23'] > 3 * r['sig23']) and (r['d34'] > 3 * r['sig34']) \
            and (r['S'] > 0.9) and (not r['conj_pair'])         # noqa: float
        degen = (r['d23'] <= 3 * r['sig23']) or r['conj_pair'] or (r['S'] <= 0.9)  # noqa: float
        pv += int(gatepass); dv += int(degen)
        print("  %-6d %-6d %.4f %.4f %.4f %+.4f  %.4f  %.3f %.3f %.1e %s  %.3f  %s"
              % (p, n, r['l2'], r['l3'], r['l4'], r['d23'], 3 * r['sig23'],
                 r['S'], r['S_sub'], r['im3'], "Y" if r['conj_pair'] else "n",
                 r['wcov'], "PASS" if gatepass else "gauge"))
    return pv, dv


def main():
    print("=" * 92)
    print("ARM 0 GATE -- lambda_3 cell-walk eigenvector well-definedness")
    print("PREREG_lambda3_eigenvector_isotype_v1.md ; SCALE: p<=~1e5, >=239 bits below 2^256")
    print("=" * 92)

    ok, nstar = firing()
    print()
    if not ok:
        print("FIRING did not resolve within the swept n -- gate cannot be calibrated. STOP"
              " (no gate verdict; extend n or fix pipeline).")
        return

    committed = prime_list(k=12)
    underp = [(p, n) for p, n in committed if n < nstar]
    print("Committed list (12 smallest p>400, #E prime): "
          + ", ".join("%d(n=%d)" % (p, n) for p, n in committed))
    print("  power: n*=%d (from firing) ; committed primes with n<n* are UNDERPOWERED"
          " (low S there is lack-of-data, NOT proven gauge): %d/12" % (nstar, len(underp)))
    print()

    powered = prime_list(k=8, n_min=nstar, hi=120000)
    if not powered:
        print("No prime-order p<=1.2e5 reaches n>=n*=%d => ABSTAIN: the individual/space" % nstar)
        print("distinction is unresolvable at accessible n. Report band + n-needed. NOT a closure.")
        return
    print("Powered set (n>=n*=%d ; pre-committed power-budget extension up to ~1e5):" % nstar)
    print("  " + ", ".join("%d(n=%d)" % (p, n) for p, n in powered) + "\n")

    pv, dv = run_gate_table(powered)

    # K-convergence on the largest powered prime
    p, n = powered[-1]
    G = curve_gen(p); xs, _ = orbit(G, p, n); beta = beta_of(p); cell = cell_fn(p)
    kc = k_convergence(p, n, xs, beta, cell)
    print("\n  K-convergence of w_cov at p=%d (n=%d): " % (p, n)
          + "  ".join("K=%d:%s" % (K, ("%.3f" % v if okk else "skip(n/K^2<20)"))
                      for K, (v, okk) in kc.items()))
    vals = {K: v for K, (v, okk) in kc.items() if okk and v is not None}
    kconv_ok = None
    if all(K in vals for K in (4, 6, 8, 10)):
        step_hi = abs(vals[10] - vals[8]); step_lo = abs(vals[6] - vals[4])
        kconv_ok = (step_hi < step_lo) and (step_hi < 0.1)      # noqa: float
        print("    |w(10)-w(8)|=%.3f vs |w(6)-w(4)|=%.3f -> K-converges: %s"
              % (step_hi, step_lo, kconv_ok))
    else:
        print("    insufficient well-sampled K cells even at the largest powered prime")

    print("\n" + "=" * 92)
    print("PRE-COMMITTED BRANCH (PREREG Arm 0), decided on the POWERED set (n>=n*):")
    print("  gate-PASS: %d/%d ; gauge/degenerate: %d/%d ; K-converges: %s"
          % (pv, len(powered), dv, len(powered), kconv_ok))
    if kconv_ok is False:
        print("  => GATE-FAIL (K-drift): the '85%' is a coarse-graining artifact of K; the object is")
        print("     the w_cov(K) CURVE. Arm 1 reports the K-trend, not a single covariant value.")
    elif pv >= (len(powered) + 1) // 2 and kconv_ok:
        print("  => GATE-PASS: 'the lambda_3 eigenvector' is a WELL-DEFINED object at n>=n*.")
        print("     Proceed to Arm 1 on the INDIVIDUAL vector v3.")
    elif dv > pv:
        print("  => GATE-FAIL (degenerate/gauge): even at n>=n* the individual v3 is unstable while")
        print("     the slow SUBSPACE is (S_sub>>S). REDEFINE the object to the slow eigenSPACE and")
        print("     its TOTAL covariant weight W_cov. Individual 0.48/0.85 RETRACTED as gauge here.")
    else:
        print("  => ABSTAIN: gap unresolved vs its noise band even on the powered set; report the")
        print("     band + the n needed. Scoped -- individual/space distinction open, NOT a closure.")
    print("=" * 92)


if __name__ == '__main__':
    main()
