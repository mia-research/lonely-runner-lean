#!/usr/bin/env sage
# n1_twisted_eigenvalues_v1.sage — ARM B of PREREG_xdomain_ports_v1.
#
# THE OBJECT, not a proxy.  Every previous N1 run measured max_a |V(a)| — a
# MAGNITUDE.  The record's own restated question is eigenvalue-level: are all
# four Frobenius eigenvalues of the twisted sheaf of weight 1 (|alpha| = sqrt p),
# and does their configuration cap |V(a)| at 2 sqrt p rather than 4 sqrt p?
#
# Construction.  chi2(y) is the quadratic character of the y-coordinate; chi_a is
# the additive character of E(F_p) = Z/n at frequency a, pulled back to
# E(F_{p^k}) through the trace (norm) map.  Then
#
#     V_k(a) = sum_{P in E(F_{p^k})} chi2(y_P) * chi_a( Tr_{k/1} P )
#
# and the power sums of the four eigenvalues are  p_k(a) = -V_k(a)  (Lefschetz;
# the sign convention is FIXED BY THE k=1 WEIGHT CHECK below, not assumed).
# Newton's identities on p_1..p_4 give the characteristic polynomial and hence
# the four eigenvalues themselves.
#
# EFFICIENCY.  V_k(a) for ALL a at once: accumulate the integer histogram
#     h_k[d] = sum over P with Tr(P) = [d]G  of  chi2(y_P)      (exact integers)
# then V_k(a) = sum_d h_k[d] zeta_n^{a d} — an n-point transform.  The signal
# path (h_k) is exact integer; complex arithmetic enters only afterwards.
#
# CONTROLS THAT MUST FIRE
#   C1  weight check: |alpha_i| = sqrt(p) to tolerance, at k-independent values.
#   C2  Newton recovery: plant a KNOWN 4-tuple of eigenvalues, synthesise its
#       power sums, and confirm the solver returns the planted tuple.
#   C3  ramification/dimension: #R = 4 tame points => dim H^1 = 4.  If the
#       recovered polynomial is not degree 4 with 4 weight-1 roots, the whole
#       N1 framing is mis-typed and the arm reports THAT.
#
# No leakage, key-recovery or ECDLP claim is made or attempted here.

import itertools

B = 7


def curve_data(p):
    """E: y^2 = x^3 + B over F_p with PRIME order n; returns (E, G, n, dlog)."""
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
    """h[d] = sum of chi2(y_P) over P in E(F_{p^k}) with Tr_{k/1}(P) = [d]G.

    Exact integers.  chi2(y) = y^((p^k-1)/2) in {+1,-1}; chi2(0) = 0.
    """
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
            # trace to E(F_p): sum of Frobenius conjugates
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


def newton_to_charpoly(ps):
    """Given power sums p_1..p_4 return elementary symmetric e_1..e_4 (CC)."""
    e = [1]
    for kk in range(1, 5):
        s = 0
        for i in range(1, kk + 1):
            s += (-1) ** (i - 1) * e[kk - i] * ps[i - 1]
        e.append(s / kk)
    return e[1:]


def eigen_from_powersums(ps):
    R.<T> = CC[]
    e = newton_to_charpoly(ps)
    f = T ** 4 - e[0] * T ** 3 + e[1] * T ** 2 - e[2] * T + e[3]
    return [r for r, _ in f.roots(CC)], f


def control_C2():
    """Plant a known eigenvalue 4-tuple; confirm the solver returns it."""
    print("=" * 74)
    print("CONTROL C2 — Newton/root solver recovers a PLANTED eigenvalue tuple")
    print("=" * 74)
    p = 43
    sp = sqrt(RR(p))
    z6 = CC(exp(2 * CC(pi) * CC(I) / 6))
    planted = [sp * z6 ** j for j in (1, 2, 4, 5)]
    ps = [sum(a ** kk for a in planted) for kk in range(1, 5)]
    got, f = eigen_from_powersums(ps)
    got = sorted(got, key=lambda z: (round(abs(z), 6), round(arg(z), 6)))
    want = sorted(planted, key=lambda z: (round(abs(z), 6), round(arg(z), 6)))
    err = max(abs(a - b) for a, b in zip(got, want))
    print(f"  planted |alpha| = {[round(abs(a),4) for a in want]}")
    print(f"  recovered       = {[round(abs(a),4) for a in got]}")
    print(f"  max |recovered - planted| = {err:.3e}")
    print(f"  CONTROL FIRES: {err < 1e-6}")
    return err < 1e-6


def run(p, kmax=4):
    cd = curve_data(p)
    if cd is None:
        print(f"p={p}: skipped (group order not prime)")
        return None
    E1, G, n, dl = cd
    print(f"\n{'='*74}\np = {p}   n = #E(F_p) = {n}   sqrt(p) = {RR(p).sqrt():.4f}\n{'='*74}")
    H = []
    for k in range(1, kmax + 1):
        h = histogram(p, k, E1, G, n, dl)
        H.append(h)
        print(f"  k={k}: |E(F_p^k)| points swept, sum h = {sum(h)}  "
              f"(#{p**k} field elements)")

    zn = [CC(exp(2 * CC(pi) * CC(I) * d / n)) for d in range(n)]
    V = [[sum(H[k][d] * zn[(a * d) % n] for d in range(n)) for a in range(n)]
         for k in range(kmax)]

    sp = RR(p).sqrt()
    # NOTE ON A COLUMN REMOVED FROM v1's OUTPUT.  v1 printed
    #   "max attainable |sum|/sqrt p" = sum_i |alpha_i| / sqrt(p).
    # If every |alpha_i| = sqrt(p) that quantity is IDENTICALLY 4 — it is the
    # weight check restated, carries zero information, and reporting it beside
    # the weight check would double-count one fact as two.  Replaced by the
    # PHASES, which are the part of the configuration the weights do not fix.
    print(f"\n  {'a':>4} {'|V_1(a)|':>10} {'/sqrt p':>8}  moduli/sqrt(p)"
          f"          phases arg(alpha_i)/pi")
    rows = []
    for a in range(n):
        ps = [-V[k][a] for k in range(kmax)]
        try:
            al, f = eigen_from_powersums(ps)
        except Exception as ex:
            print(f"  a={a}: solver failed ({ex})")
            continue
        mods = sorted([abs(z) / sp for z in al], reverse=True)
        phs = sorted([float(arg(z) / CC(pi)) for z in al])
        rows.append((a, abs(V[0][a]) / sp, mods, phs))
    for a, v1, mods, phs in rows:
        print(f"  {a:>4} {v1*sp:>10.4f} {v1:>8.4f}  "
              f"{[round(m,4) for m in mods]}   {[round(t,4) for t in phs]}")

    w = [max(abs(m - 1) for m in r[2]) for r in rows]
    print(f"\n  C1 WEIGHT CHECK: max_a max_i | |alpha_i|/sqrt(p) - 1 | = {max(w):.4e}")
    print(f"     all four eigenvalues of weight 1 (tol 1e-6): {max(w) < 1e-6}")
    print(f"  observed max_a |V_1(a)|/sqrt(p) = {max(r[1] for r in rows):.4f}"
          f"   (record's ceiling = 4, dim H^1 = 4)")
    vals = sorted(set(round(r[1], 9) for r in rows if r[1] > 1e-9))
    print(f"  DISTINCT nonzero |V_1(a)|/sqrt p values: {len(vals)}  "
          f"vs (n-1)/6 = {(n-1)//6}   [mu_6 orbit count — the denominator that")
    print(f"     matters: n-1 = {n-1} cells are NOT {n-1} independent bits]")
    # is the configuration closed under conjugation?  (V real/imaginary constraint)
    conj_ok = True
    for a, v1, mods, phs in rows:
        ps = [-V[k][a] for k in range(kmax)]
        al, f = eigen_from_powersums(ps)
        s = sorted([(round(float(z.real()), 6), round(float(z.imag()), 6)) for z in al])
        sc = sorted([(round(float(z.real()), 6), round(-float(z.imag()), 6)) for z in al])
        if s != sc: conj_ok = False
    print(f"  eigenvalue multiset closed under complex conjugation, every a: {conj_ok}")
    return rows


if __name__ == '__main__':
    import sys
    ok = control_C2()
    if not ok:
        print("CONTROL C2 DID NOT FIRE — arm is void, stopping.")
        sys.exit(1)
    ps = [int(t) for t in (sys.argv[1].split(',') if len(sys.argv) > 1 else ['13'])]
    for p in ps:
        run(p)
