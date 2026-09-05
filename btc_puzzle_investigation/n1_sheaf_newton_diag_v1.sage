# n1_sheaf_newton_diag_v1.sage -- characterize the eigenvalue structure of F_a to clarify
# whether the unit-root part is CM (CM-i) or whether the naive ARM CM negative was a
# field-of-definition artifact.  NO p-adic embedding is attempted; instead we read the
# COMPLEX ratio structure, which decides the grouping and whether the common factor within
# each zeta_3-pair is a pi_p-associate.
#
# The obstruction doc states the per-cell multiset is {alpha, omega*alpha, -conj(alpha),
# -omega*conj(alpha)} (omega = zeta_3).  If so:
#   - the two zeta_3-pairs are (alpha, omega*alpha) and (-conj alpha, -omega conj alpha);
#   - within each pair the ratio is omega (order 3);
#   - the common factor of pair 1 is alpha;  CM-i asks: is alpha/pi_p a root of unity?
#   - the common factor of pair 2 is -conj(alpha); CM-i asks: is -conj(alpha)/conj(pi_p) a
#     root of unity (equivalently is alpha/pi_p a root of unity, by conjugation)?
# So CM-i  <=>  alpha/pi_p is a root of unity  <=>  (ARM CM on the pair-common-factor).
# This script reports that directly, plus the full ratio structure for transparency.

src = open('n1_sheaf_cm_type_probe_v1.sage').read()
exec(src.split('if __name__')[0])        # define curve_data/histogram_fast/eigen_from_... w/o main()


def rou(z, max_order):
    """minimal m in 1..max_order with z^m==1 (|z|~1), else None ('unit non-root-of-unity')."""
    if abs(abs(z) - 1) > TOL_MOD:
        return -1                          # not even unit modulus
    for m in range(1, max_order + 1):
        if abs(z ** m - 1) < TOL_PAIR:
            return m
    return None


def characterize(p, kmax=4, a_list=None):
    cd = curve_data(p)
    if cd is None:
        print("p=%d skipped (order not prime)" % p); return
    E1, G, n, dl = cd
    mo = max(12, n)
    pihat = pi_hat_of(p, n); pibar = pihat.conjugate()
    print("=" * 90)
    print("p=%d  n=%d  t=%d  pi_hat=%s  |pi_hat|=%.4f  max_order=%d"
          % (p, n, p + 1 - n, pihat, float(abs(pihat)), mo))
    print("=" * 90)
    if a_list is None:
        # a few orbit representatives + a=0
        lam = find_lambda(E1, G, n, dl, p)
        reps = sorted({(pow(lam, e, n) * a) % n for a in (1, 2, 4) for e in range(3)})
        a_list = [0] + reps[:4]
    H = [histogram_fast(p, k, E1, G, n, dl) for k in range(1, kmax + 1)]
    zn = [CF.zeta(n) ** d for d in range(n)]
    V = [[sum(H[k][d] * zn[(a * d) % n] for d in range(n)) for a in range(n)] for k in range(kmax)]
    for a in a_list:
        ps = [-V[k][a] for k in range(kmax)]
        roots, _ = eigen_from_powersums(ps)
        eigs = [r for r, mm in roots for _ in range(mm)]
        eigs = sorted(eigs, key=lambda z: float(arg(z)))
        print("\n  a=%d : eigenvalues (modulus / arg in units of pi):" % a)
        for z in eigs:
            print("      |.|=%.4f  arg/pi=%+.4f" % (float(abs(z)), float(arg(z) / PI)))
        # 6 pairwise ratios
        print("    pairwise ratios (i->j): modulus, root-of-unity order):")
        for i in range(4):
            row = []
            for j in range(4):
                if i == j:
                    row.append("  --  "); continue
                r = eigs[j] / eigs[i]
                o = rou(r, mo)
                tag = "U%d" % o if (o and o > 0) else ("nr" if o is None else "x")  # nr=non-root unit, x=non-unit
                row.append("%4s" % tag)
            print("      " + " ".join(row))
        # identify the two zeta_3-pairs
        pairs = []
        for i in range(4):
            for j in range(i + 1, 4):
                if abs(eigs[j] / eigs[i] - Z3) < TOL_PAIR or abs(eigs[j] / eigs[i] - Z3 ** 2) < TOL_PAIR:  # noqa: float — ComplexField(212) high-precision root-of-unity ID, tol 1e-50
                    pairs.append((i, j))
        print("    zeta_3-ratio pairs (indices):", pairs)
        # CM-i test: is the common factor of a pair a pi_p-associate?
        for (i, j) in pairs:
            for piv, name in ((pihat, "pi_p"), (pibar, "conj pi_p")):
                u = eigs[i] / piv
                o = rou(u, mo)
                print("      pair(%d,%d) common-factor alpha/%s : |.|=%.4f arg/pi=%+.4f  root-of-unity-order=%s"
                      % (i, j, name, float(abs(u)), float(arg(u) / PI), o))
    print("DONE p=%d" % p)


for p in (43, 67, 79):
    try:
        characterize(p)
    except Exception as ex:
        print("p=%d ERROR %r" % (p, ex))
