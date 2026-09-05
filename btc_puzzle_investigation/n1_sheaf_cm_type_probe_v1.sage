#!/usr/bin/env sage
# n1_sheaf_cm_type_probe_v1.sage -- the VERTICAL (CM-type) probe of the N1 sheaf.
#
# WHAT THIS IS.  The sheaf F_a = L_{chi2(y)} (x) L_{chi_a} on E: y^2 = x^3 + 7, with
# dim H^1_c(E, F_a) = 4 and Frobenius eigenvalues alpha_1..alpha_4 (weight-1 Weil
# numbers, |alpha_i| = sqrt(p)).  ANALYSIS_n1_120deg_uniformity_obstruction_v1.md
# proves every KNOWN cross-cell symmetry of this object is HORIZONTAL (acts in the
# cell index a), hence structurally incapable of the vertical law
#
#     U(a) :  alpha_2(a)/alpha_1(a) = zeta_3                 ... (the "120 deg law")
#
# which is a relation purely in i (within one fiber) at fixed a.  The one isolated
# open step is a CM-type Hecke input (CM-i/ii/iii, obstruction Sec. 4):
#   (CM-i)   does the unit-root rank-2 part carry CM by an order containing Q(omega)?
#   (CM-ii)  are its eigenvalues a Hecke Grossencharacter value psi(p) twisted by chi_a?
#   (CM-iii) does the CM-type force alpha_2/alpha_1 = omega?
# The obstruction doc states the Newton polygon {0,0,1,1} is "consistent with CM but
# does not establish it" -- exactly the untested vertical fact.
#
# WHAT IS ALREADY DONE (do not duplicate).  n1_twisted_eigenvalues_v1.sage computes
# V_k(a) and recovers the four eigenvalues; it prints the phases but (i) does not form
# the per-cell zeta_3 ratio, (ii) does not test the CM Grossencharacter linkage, (iii)
# does not quotient by the lambda-orbit, (iv) runs no CM-type test.  Those four are the
# content of THIS script.  The V_k / histogram / Newton machinery below is copied
# verbatim from n1_twisted_eigenvalues_v1.sage (cited); the new work is in the TEST
# functions and the run() orchestration.
#
# FROZEN HYPOTHESIS (no choices made post-hoc).
#   H_CM   : every eigenvalue alpha_i(a) = pi_p * xi  OR  conj(pi_p) * xi  for some
#            root of unity xi in mu_m (m in {1,2,3,4,6,12}); i.e. the unit-root part of
#            H^1_c(F_a) IS the CM Grossencharacter psi(p) = chi(pi)pi, twisted by a
#            finite-order character.  This is CM-i/ii.  If H_CM holds AND the twist
#            roots of the unit-root pair differ by exactly zeta_3, that is CM-iii and
#            it EXPLAINS the 120 deg law (the ratio is then the CM-type, not a coincidence).
#   H_R    : the 120 deg law holds per cell, i.e. deg gcd(L_a*(T), L_a*(zeta_3 T)) = 2,
#            equivalently exactly two unordered pairs {alpha_i, alpha_j} satisfy
#            alpha_j/alpha_i = zeta_3.  Reproduced p <= 211 in the obstruction doc; this
#            script extends the census AND, crucially, asks whether H_R holds BECAUSE of
#            H_CM (explained) or INDEPENDENTLY of it (real but not the naive CM character).
#
# WHERE.  Model curves only: p = 7 mod 12 (forces omega = zeta_3 in F_p and p = 3 mod 4),
#   n = #E(F_p) prime with n = 1 mod 3, p < ~300 so that the k=4 sweep of E(F_{p^4}) is
#   tractable by naive enumeration.  Nothing here reaches p = 2^256 - 2^32 - 977; the
#   sheaf object is a model-scale verification of a structural conjecture, not a
#   point-local secp256k1 extractor.  (The vertical invariant is NOT independently
#   computable from a single public point at secp scale; this is a verification regime.)
#
# ARMS
#   ARM R  -- per-cell zeta_3-ratio census (the law).  Statistic: # of {i,j} pairs with
#             alpha_j/alpha_i = zeta_3 (exact, tol 1e-20 in CF(212)).  Expected 2/cell.
#             NON-SATURATING: this count is NOT pinned by the weight check (unlike the
#             trace sum_i alpha_i = -V_1(a), which is forced); it is the free part.
#   ARM CM -- CM-type value test.  For each alpha_i, test |alpha_i / pi_hat| = 1 (or its
#             conjugate) and identify the order of the root of unity.  Reports, per cell,
#             the multiset of CM-twist orders {ord(alpha_i/pi_p)}.  Under H_CM these are
#             small (divides 12); a non-root-of-unity is evidence AGAINST the naive CM
#             character (CM-i/ii fail), which would be a genuine redirect.
#   ARM U  -- uniformity.  Is the CM-twist multiset constant across lambda-orbits?
#             Under the obstruction, horizontal symmetry forces L_a* = L_{lambda a} *
#             (omega-descent) -- so within-orbit invariance is a CONSISTENCY check, not a
#             discovery.  ACROSS-orbit variation in the twist multiset is the live signal.
#
# NULL / CONTROL (all must fire; no verdict otherwise).
#   N1 CONSISTENCY (forced by omega-descent)  : charpoly(a) == charpoly(lambda*a) for all
#             a.  Must hold exactly; a violation means a BUG, not a finding.
#   N2 FIRING -- planted non-zeta_3 (ARM R must detect): synthesise a char poly whose
#             roots do NOT pair under zeta_3; ARM R must report 0 such pairs.
#   N3 FIRING -- planted non-CM (ARM CM must detect): synthesise eigenvalues pi_p * z
#             with z NOT a root of unity; ARM CM must report "no small root of unity".
#   N4 WEIGHT: every |alpha_i| = sqrt(p) (tol 1e-12).  Forced; a violation mistypes the
#             object.
#
# PLANT.  N2/N3 above are the firing controls.  There is no planted DLP signal -- this is
#   a structural verification of a sheaf-cohomology conjecture, not an extraction test.
#
# FLOAT / EXACTNESS CARVE-OUT.  Signal path (h_k histograms) is EXACT INTEGER.  Complex
#   eigenvalue arithmetic uses CF(PREC) (default 212 bits ~ 64 dec digits); all TEST
#   decisions are exact-algebraic-in-principle statements checked to a stated tolerance,
#   never IEEE float.  The CM value pi_hat is the exact complex embedding
#   (t + i*sqrt(4p-t^2))/2 of the Frobenius; the unit-ambiguity (mu_6 of associates) is
#   itself roots of unity, so the root-of-unity test is invariant to the associate chosen.
#
# OUTPUT.  stdout table (per prime, per cell: |V_1|/sqrt p, zeta_3-pair count, CM-twist
#   orders, orbit-rep flag); census summary; N1-N4 control verdicts; JSON + SHA-256 sidecar.
#
# No leakage / key-recovery / ECDLP claim is made or attempted.  Scope: model primes.
#
# Source of reused machinery: n1_twisted_eigenvalues_v1.sage (V_k histogram + Newton
# solver), verified identical to the obstruction-doc object at p = 43.
# Related: ANALYSIS_n1_120deg_uniformity_obstruction_v1.md (the obstruction + CM-i/ii/iii);
#          n1_twisted_eigenvalues_v1.sage (eigenvalues only); KNOWN_FACTS_secp256k1_and_keys_v1.md
#          (Hecke Grossencharacter psi((alpha)) = chi(alpha)*alpha, infty-type (1,0)).

import json
import hashlib
import itertools

B = 7                       # curve y^2 = x^3 + B
PREC = 212                  # complex precision in bits (~64 dec digits) for root-of-unity ID
CF = ComplexField(PREC)
RCF = RealField(PREC)
Z3 = CF.zeta(3)             # zeta_3 in CF
PI = CF.pi()
I = CF.gen()
TOL_MOD = RCF(10) ** (-55)  # |.| - 1 tolerance for "unit modulus"
TOL_PAIR = RCF(10) ** (-50) # |ratio - zeta_3| tolerance
TOL_COEFF = RCF(10) ** (-45)  # char-poly coefficient tolerance (consistency)
Z3_ORDERS = (1, 2, 3, 4, 6, 12)   # plausible CM unit group orders


# ---------------------------------------------------------------------------
# REUSED machinery (verbatim logic from n1_twisted_eigenvalues_v1.sage).
# ---------------------------------------------------------------------------

def curve_data(p):
    """E: y^2 = x^3 + B over F_p with PRIME order n; returns (E, G, n, dlog) or None."""
    F = GF(p)
    E = EllipticCurve(F, [0, B])
    n = E.cardinality()
    if not is_prime(n):
        return None
    G = E.gens()[0]
    dl = {}
    Q = E(0)
    for d in range(n):
        dl[Q] = d
        Q = Q + G
    return E, G, n, dl


def histogram(p, k, E1, G, n, dl):
    """h[d] = sum of chi2(y_P) over P in E(F_{p^k}) with Tr_{k/1}(P) = [d]G.  Exact ints."""
    q = p ** k
    Fq = GF(q, 'g')
    Eq = EllipticCurve(Fq, [0, Fq(B)])
    E0 = E1.base_ring()
    h = [0] * n
    half = (q - 1) // 2
    for x in Fq:
        r = x ** 3 + Fq(B)
        if r == 0:
            continue                      # y = 0 => chi2(0) = 0, contributes nothing
        if not r.is_square():
            continue
        y = r.sqrt()
        for yy in (y, -y):
            c = 1 if yy ** half == 1 else -1
            P = Eq(x, yy)
            T = P
            Q = P
            for _ in range(k - 1):
                Q = Eq(Q[0] ** p, Q[1] ** p)
                T = T + Q
            if T == Eq(0):
                d = 0
            else:
                d = dl[E1(E0(T[0]), E0(T[1]))]
            h[d] += c
    return h


def histogram_fast(p, k, E1, G, n, dl):
    """h[d] = sum of chi2(y_P) over P in E(F_{p^k}) with Tr_{k/1}(P) = [d]G.  Exact ints.

    OPTIMIZED replacement for histogram(): instead of sweeping all p^k elements of GF(p^k)
    with a per-element cube / sqrt / k-step Frobenius-trace chain, enumerate E(F_{p^k}) in
    GENERATOR ORDER (one C-backed EC addition per step) and compute the trace-index via the
    precomputed trace-homomorphism constants c_i, where Tr_{k/1}(g_i) = [c_i] G.  Since
    Tr_{k/1} is a group hom, Tr_{k/1}([m_i]g_i) = [sum_i m_i c_i] G, so the trace-index is a
    pure scalar multiply -- no per-point Frobenius chain.  Cost drops from ~p^k Python
    field-element iterations to ~#E(F_{p^k}) C-backed point additions.

    Verified bit-identical to histogram() by verify_histogram() at p in {43,67}, k in {1,2}.
    """
    q = p ** k
    Fq = GF(q, 'g')
    Eq = EllipticCurve(Fq, [0, Fq(B)])
    E0 = E1.base_ring()
    nk = Eq.cardinality()
    # Use abelian_group() for a TRUE independent direct-product basis (Eq.gens() can return a
    # non-minimal/dependent set).  In Sage 10.9 abelian_group() returns a single wrapper group;
    # recover curve points via .element().  NOTE: A.gens() may list generators in a DIFFERENT
    # order than A.invariants() (observed: invs [14,5642] but gens ordered [ord 5642, ord 14]),
    # so each generator MUST be paired with its OWN order, not with invs[i].
    Agrp = Eq.abelian_group()
    gs = [g.element() for g in Agrp.gens()]      # independent curve-point basis
    ords = [int(g.order()) for g in gs]          # each generator's ACTUAL order
    assert prod(ords) == nk, "basis order product mismatch: %d vs #E=%d" % (prod(ords), nk)

    def trace_point(P):
        T = P
        Qp = P
        for _ in range(k - 1):
            Qp = Eq(Qp[0] ** p, Qp[1] ** p)
            T = T + Qp
        return T

    # trace constants c_i : Tr_{k/1}(g_i) = [c_i] G   (dlog in the F_p group)
    cs = []
    for gi in gs:
        Ti = trace_point(gi)
        if Ti == Eq(0):
            cs.append(0)
        else:
            Ti_fp = E1(E0(Ti[0]), E0(Ti[1]))
            assert Ti_fp in E1, "trace of generator not in E(F_p) -- structure error"
            cs.append(dl[Ti_fp])

    half = (q - 1) // 2
    h = [0] * n
    inf = Eq(0)

    def accum(P, idx):
        if P != inf:
            yy = P[1]
            if yy != 0:                  # chi2(0) = 0, contributes nothing
                h[idx] += 1 if yy ** half == 1 else -1

    if len(gs) == 1:
        g1 = gs[0]; c1 = cs[0]; o1 = ords[0]
        P = inf
        for m1 in range(o1):
            accum(P, (m1 * c1) % n)
            P = P + g1
    elif len(gs) == 2:
        g1, g2 = gs; c1, c2 = cs; o1, o2 = ords
        base = inf
        for m1 in range(o1):
            P = base
            for m2 in range(o2):
                accum(P, (m1 * c1 + m2 * c2) % n)
                P = P + g2
            base = base + g1
    else:
        raise NotImplementedError("E(F_{p^k}) needs >2 generators (unexpected for these primes)")
    return h


def verify_histogram(ps_to_check, kmax=2):
    """Cross-check histogram_fast against the slow histogram() reference.  Must be bit-equal."""
    print("=" * 74)
    print("HISTOGRAM CROSS-CHECK: histogram_fast vs histogram (slow reference)")
    print("=" * 74)
    allok = True
    for p in ps_to_check:
        cd = curve_data(p)
        if cd is None:
            continue
        E1, G, n, dl = cd
        for k in range(1, kmax + 1):
            h_slow = histogram(p, k, E1, G, n, dl)
            h_fast = histogram_fast(p, k, E1, G, n, dl)
            ok = (h_slow == h_fast)
            allok = allok and ok
            print("  p=%d k=%d: #E(F_p^k)=%d  fast==slow: %s%s" %
                  (p, k, p ** k, ok, "" if ok else "  MISMATCH"))
    print("  CROSS-CHECK: %s" % ("PASS" if allok else "FAIL"))
    return allok


def newton_to_charpoly(ps):
    """Power sums p_1..p_4 -> elementary symmetric e_1..e_4 (in CF)."""
    e = [CF(1)]
    for kk in range(1, 5):
        s = CF(0)
        for i in range(1, kk + 1):
            s += (-1) ** (i - 1) * e[kk - i] * ps[i - 1]
        e.append(s / kk)
    return e[1:]


def eigen_from_powersums(ps):
    R = PolynomialRing(CF, 'T')
    T = R.gen()
    e = newton_to_charpoly(ps)
    f = T ** 4 - e[0] * T ** 3 + e[1] * T ** 2 - e[2] * T + e[3]
    return list(f.roots(CF)), f


def charpoly_coeffs(ps):
    """Monic char-poly coefficient vector [1, -e1, e2, -e3, e3] in CF, for consistency check."""
    e = newton_to_charpoly(ps)
    return [CF(1), -e[0], e[1], -e[2], e[3]]


# ---------------------------------------------------------------------------
# NEW: the vertical (CM-type) test functions.
# ---------------------------------------------------------------------------

def pi_hat_of(p, n):
    """Complex embedding of the Frobenius pi_p (one associate), |pi_hat| = sqrt(p).

    pi_p + conj(pi_p) = t = p + 1 - n ; pi_p * conj(pi_p) = p.
    So pi_hat = (t + i*sqrt(4p - t^2))/2.  Unit-ambiguous (mu_6 of associates); the
    ambiguity is roots of unity, so the root-of-unity test (cm_twist_order) is invariant.
    """
    t = p + 1 - n
    disc = 4 * p - t * t
    assert disc > 0, "p=%d: expected ordinary CM (disc > 0), got disc=%d" % (p, disc)
    return (CF(t) + I * CF(disc).sqrt()) / 2


def cm_twist_order(alpha, pi_hat, pi_bar, max_order=12):
    """Return the minimal m in 1..max_order with (alpha/pi_hat)^m = 1 (or alpha/pi_bar); else None.

    None means alpha is NOT a CM Grossencharacter value up to a max_order-th root of unity.
    max_order defaults to 12 (CM unit groups mu_6/mu_12); callers testing the chi_a Kummer
    twist should pass max_order = max(12, n), since chi_a is a character of Z/n and a CM-times-
    twist eigenvalue could carry an n-th root of unity that mu_12 alone would miss.
    """
    for piv in (pi_hat, pi_bar):
        z = alpha / piv
        if abs(abs(z) - 1) > TOL_MOD:
            continue
        for m in range(1, max_order + 1):
            if abs(z ** m - 1) < TOL_PAIR:
                return m
    return None


def zeta3_pair_count(eigs):
    """# of unordered pairs {i,j} with alpha_j/alpha_i = zeta_3 (expected 2 under the law).

    NON-SATURATING: this count is not pinned by the weight check (unlike sum_i alpha_i).
    Returns (count, list_of_pairs).
    """
    pairs = []
    for i in range(len(eigs)):
        for j in range(len(eigs)):
            if i == j:
                continue
            if abs(eigs[j] / eigs[i] - Z3) < TOL_PAIR:  # noqa: float — ComplexField(212) high-precision root-of-unity ID, tol 1e-50
                pairs.append((i, j))
    # unordered: keep pairs with i<j by index after matching ratio; dedupe symmetric
    seen = set()
    cnt = 0
    for (i, j) in pairs:
        key = frozenset((i, j))
        if key in seen:
            continue
        seen.add(key)
        cnt += 1
    return cnt, sorted(seen)


def find_lambda(E1, G, n, dl, p):
    """Order-3 unit lambda in (Z/n)* induced by the CM automorphism [omega]:(x,y)->(omega x,y).

    p = 1 mod 3 so a primitive cube root of 1 lives in F_p.  [omega] has order 3 on the
    group; the induced scalar lambda = dlog([omega]G, G) has order 3 in (Z/n)*.  This is
    the obstruction doc's lambda (the horizontal orbit generator).
    """
    F = GF(p)
    # primitive cube root of 1 in F_p
    g = F.multiplicative_generator()
    w = g ** ((p - 1) // 3)
    assert w != 1 and w ** 3 == 1, "p=%d: cube root of unity not found" % p
    Omega = E1([w * G[0], G[1]])          # [omega] applied to G (y unchanged since y^2=x^3+b)
    # sanity: Omega must be on E and equal [omega]G
    assert Omega in E1
    lam = dl[Omega]
    assert (lam ** 3) % n == 1, "lambda=%d not order 3 mod n=%d" % (lam, n)
    return lam


def consistency_check(V_cols, n, lam):
    """N1: charpoly(a) == charpoly(lambda*a mod n) for all a (forced by omega-descent).

    V_cols[k][a] = V_k(a).  Returns (ok, violations).
    """
    viol = []
    for a in range(n):
        b = (lam * a) % n
        ca = charpoly_coeffs([-V_cols[k][a] for k in range(4)])
        cb = charpoly_coeffs([-V_cols[k][b] for k in range(4)])
        if any(abs(x - y) > TOL_COEFF for x, y in zip(ca, cb)):
            viol.append((a, b))
    return (len(viol) == 0), viol


# ---------------------------------------------------------------------------
# FIRING CONTROLS (N2, N3).
# ---------------------------------------------------------------------------

def control_N2_zeta3_detector():
    """Plant a 4-tuple with NO zeta_3 pair; ARM R must report 0."""
    sp = CF(43).sqrt()
    planted = [sp * CF.zeta(5) ** j for j in range(4)]   # 5th roots: no zeta_3 ratio
    cnt, _ = zeta3_pair_count(planted)
    fired = (cnt == 0)
    print("  N2 FIRING (planted non-zeta_3, expect 0 pairs): pairs=%d  DETECTED=%s" % (cnt, fired))
    return fired


def control_N3_cm_detector():
    """Plant eigenvalues with |alpha| != |pi| (modulus-perturbed); ARM CM must report None.

    A modulus perturbation is the unambiguous non-CM plant: alpha/pi has |.| != 1, so the
    unit-modulus test fails immediately -- no dependence on root-of-unity arithmetic.
    """
    pihat = CF(2) + I                            # arbitrary non-real complex, |.| = sqrt(5)
    pibar = CF(2) - I
    planted = [pihat * CF(j + 2) for j in range(4)]   # moduli 2|pi|,3|pi|,4|pi|,5|pi| (all wrong)
    ids = [cm_twist_order(a, pihat, pibar) for a in planted]
    fired = all(v is None for v in ids)
    print("  N3 FIRING (planted non-CM / wrong modulus, expect all None): twist_ids=%s  DETECTED=%s"
          % (ids, fired))
    return fired


# ---------------------------------------------------------------------------
# ORCHESTRATION.
# ---------------------------------------------------------------------------

def run(p, kmax=4):
    cd = curve_data(p)
    if cd is None:
        return {"p": p, "skipped": "group order not prime"}
    E1, G, n, dl = cd
    if n % 3 != 1:
        return {"p": p, "skipped": "n != 1 mod 3 (no order-3 unit)"}
    lam = find_lambda(E1, G, n, dl, p)
    pihat = pi_hat_of(p, n)
    pibar = pihat.conjugate()
    sp = RCF(p).sqrt()
    print("\n" + "=" * 84)
    print("p = %d   n = #E(F_p) = %d   t = %d   lambda = %d (order 3)   sqrt(p) = %.4f"
          % (p, n, p + 1 - n, lam, float(sp)))
    print("pi_hat = %s   |pi_hat| = %.6f" % (pihat, float(abs(pihat))))
    print("=" * 84)

    # V_k(a) for all a via the histogram DFT (exact-int signal path).  histogram_fast is the
    # optimized (group-order + trace-constant) path; bit-identical to histogram() (slow).
    H = [histogram_fast(p, k, E1, G, n, dl) for k in range(1, kmax + 1)]
    zn = [CF.zeta(n) ** d for d in range(n)]
    V = [[sum(H[k][d] * zn[(a * d) % n] for d in range(n)) for a in range(n)]
         for k in range(kmax)]

    # N1 consistency (forced).
    ok_cons, viol = consistency_check(V, n, lam)
    print("N1 CONSISTENCY (omega-descent, forced): charpoly(a)==charpoly(lam a): %s%s"
          % ("PASS" if ok_cons else "FAIL",
             ("  [%d violations]" % len(viol)) if viol else ""))
    if not ok_cons:
        return {"p": p, "N1_consistency": "FAIL", "violations": len(viol)}

    # ARM R + ARM CM per cell.
    print("\n  %4s %12s %10s %14s   %s" % ("a", "|V_1(a)|", "/sqrt p", "z3-pairs", "CM-twist orders ord(a_i/pi)"))
    print("  " + "-" * 80)
    cell_rows = []
    law_holds = 0
    cm_holds_all = True
    cm_multisets = {}          # orbit-rep -> frozenset of twist orders
    nonzero_cells = 0
    for a in range(n):
        ps = [-V[k][a] for k in range(kmax)]
        roots, _ = eigen_from_powersums(ps)
        eigs = [r for r, mm in roots for _ in range(mm)]   # flatten multiplicities
        if len(eigs) != 4:
            print("  a=%d: WARNING recovered %d eigenvalues (expected 4); skipping cell" % (a, len(eigs)))
            continue
        v1 = abs(V[0][a]) / sp
        n_pairs, _ = zeta3_pair_count(eigs)
        # max_order = max(12, n): chi_a is a Z/n character, so a CM-times-twist eigenvalue may
        # carry an n-th root of unity that the mu_12 default would miss.
        twist = [cm_twist_order(z, pihat, pibar, max_order=max(12, n)) for z in eigs]
        # orbit representative: smallest element of <lambda> . a
        orb = sorted({(lam ** e * a) % n for e in range(3)})
        rep = orb[0]
        is_rep = (a == rep)
        if a != 0:
            nonzero_cells += 1
            if n_pairs == 2:
                law_holds += 1
            if any(t is None for t in twist):
                cm_holds_all = False
            if is_rep:
                cm_multisets[rep] = tuple(sorted(t if t is not None else -1 for t in twist))
        if is_rep or a < 6 or a > n - 4:    # print reps + a few boundary cells
            print("  %4d %12.4f %10.4f %14d   %s%s" %
                  (a, float(abs(V[0][a])), float(v1), n_pairs,
                   [t if t is not None else "None" for t in twist],
                   "   <rep>" if is_rep else ""))

    # ARM U: across-orbit variation of the CM-twist multiset.
    distinct_multisets = set(cm_multisets.values())
    uniform_across_orbits = (len(distinct_multisets) <= 1)

    print("\n  ARM R (law):  z3-pair count == 2 in %d / %d nonzero cells" % (law_holds, nonzero_cells))
    print("  ARM CM:       every eigenvalue a CM value (small root of unity): %s" % cm_holds_all)
    print("  ARM U:        CM-twist multiset constant across %d orbits: %s  (distinct multisets: %d)"
          % (len(cm_multisets), uniform_across_orbits, len(distinct_multisets)))

    # N4 weight check.
    max_w = 0
    for a in range(n):
        ps = [-V[k][a] for k in range(kmax)]
        roots, _ = eigen_from_powersums(ps)
        eigs = [r for r, mm in roots for _ in range(mm)]
        for z in eigs:
            max_w = max(max_w, float(abs(abs(z) / float(sp) - 1)))
    print("  N4 WEIGHT:    max_a max_i ||alpha_i|/sqrt p - 1| = %.3e  (weight 1: %s)"
          % (max_w, max_w < 1e-12))

    return {
        "p": int(p), "n": int(n), "t": int(p + 1 - n), "lambda": int(lam),
        "N1_consistency": "PASS",
        "ARM_R_law_holds": "%d/%d" % (law_holds, nonzero_cells),
        "ARM_CM_all_CM_values": bool(cm_holds_all),
        "ARM_U_uniform_across_orbits": bool(uniform_across_orbits),
        "ARM_U_distinct_twist_multisets": len(distinct_multisets),
        "ARM_U_orbit_count": len(cm_multisets),
        "N4_weight_max_err": float(max_w),
    }


def main():
    import sys
    print("# n1_sheaf_cm_type_probe_v1.sage -- VERTICAL (CM-type) probe of the N1 sheaf F_a")
    print("# Reused V_k/Newton machinery: n1_twisted_eigenvalues_v1.sage.  Model-scale only.\n")
    print("=" * 84)
    print("FIRING CONTROLS")
    print("=" * 84)
    n2 = control_N2_zeta3_detector()
    n3 = control_N3_cm_detector()
    if not (n2 and n3):
        print("\nA FIRING CONTROL DID NOT FIRE -- arm void, stopping.")
        return

    # Verify the optimized histogram is bit-identical to the slow reference.  k=3 at p=43
    # covers the 2-generator regime (invs [14,5642]); slow reference is still feasible there.
    verify_histogram([43], kmax=3)

    # Primes from argv (comma-separated) -- matches n1_twisted_eigenvalues_v1.sage convention.
    # Default: model primes p = 7 mod 12, p >= 19 (7 itself ramifies y^2=x^3+7), prime n = 1 mod 3.
    if len(sys.argv) > 1:
        cands = [int(t) for t in sys.argv[1].split(",") if t.strip()]
    else:
        cands = [p for p in range(19, 300) if p % 12 == 7 and is_prime(p)]
    results = []
    for p in cands:
        try:
            r = run(p)
        except Exception as ex:
            r = {"p": int(p), "error": repr(ex)}
        results.append(r)

    summary = {
        "script": "n1_sheaf_cm_type_probe_v1.sage",
        "object": "F_a = L_{chi2(y)} (x) L_{chi_a} on E:y^2=x^3+7; H^1_c dim 4, weight 1",
        "frozen_hypotheses": {
            "H_CM": "every alpha_i = pi_p or conj(pi_p) times a small root of unity (CM-i/ii)",
            "H_R": "deg gcd(L_a*(T),L_a*(zeta3 T)) = 2 per cell (the 120 deg law)",
            "H_explain": "H_R holds BECAUSE of H_CM (twist roots differ by zeta_3) = CM-iii",
        },
        "controls": {"N2_zeta3_detector_fired": n2, "N3_cm_detector_fired": n3},
        "primes_tested": cands,
        "per_prime": results,
        "scope": "model-scale verification; nothing reaches secp256k1",
        "note": "ARM CM = None means the eigenvalue is NOT a CM value up to a small root of "
                "unity -- evidence AGAINST the naive CM character as the vertical mechanism.",
    }
    txt = json.dumps(summary, indent=2, sort_keys=True, default=str)
    out = "n1_sheaf_cm_type_probe_v1.json"
    with open(out, "w") as f:
        f.write(txt + "\n")
    h = hashlib.sha256((txt + "\n").encode()).hexdigest()
    with open(out + ".sha256", "w") as f:
        f.write(h + "  " + out + "\n")
    print("\n" + "=" * 84)
    print("WROTE %s  SHA-256 %s" % (out, h))
    print("=" * 84)


if __name__ == '__main__':
    main()
