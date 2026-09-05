#!/usr/bin/env sage -python
"""verify_120deg_resultant_certificate_v1.sage -- A2: the purer Z[zeta_M] direct-gcd cross-check.

INDEPENDENT route to the g >= 2 half of the 120deg certificate, distinct from A1:
  A1 lower bound: PART 1 (verify_120deg_symbolic_factorization_v1) proves D | L and D | L(zeta3 T)
                  symbolically in Z[e1,p,omega]/(omega^2+omega+1) -- a universal polynomial identity.
  A2 (this script): build L*(T) in Q(zeta_n)[T], lift to Q(zeta_M)[T] with M = lcm(n,3) = 3n, and
                  compute gcd( L*(T), L*(zeta3 T) ) DIRECTLY in Q(zeta_M)[T] (Sage native cyclotomic
                  arithmetic). zeta_n and zeta3 are PINNED JOINTLY as powers of the single generator
                  zeta_M (zeta_n = zeta_M^3, zeta3 = zeta_M^n) -- the load-bearing joint pinning of
                  CORRECTION §5, which the standalone census cannot express (it pins them independently
                  per F_l). deg gcd >= 2 here is the SAME g >= 2, by a direct ring computation.

Conjoin A2's direct gcd (>= 2) with the census min_l g_l (<= 2) for a second, independent g = 2 route.
This is a CROSS-CHECK of A1, not required for the grade (A1 already reaches genuinely exact); it
validates the conjunction from a different algebraic code path.

EXACT cyclotomic-field arithmetic only (Sage); no floats, no finite-field inflation in the signal path.
"""
import sys, json
import audit_n1_vsign_v2_core as core
from sage.all import CyclotomicField, PolynomialRing, QQ, pari
# raise the PARI stack for large cyclotomic fields (M up to ~7700); the default 8 MB overflows.
pari.allocatemem(8 * 1024 * 1024 * 1024)   # 8 GB


def direct_gcd_certificate_prime(p, n_ells_check=3, verbose=True):
    """For prime p, build L*(T) in Q(zeta_n)[T], lift to Q(zeta_M)[T], compute the direct gcd with
    L*(zeta3 T). Return the gcd degree (>=2 is the certificate half). Uniform over a, so one check
    per prime suffices for the lower bound (PART 1 already made it a-independent); we sample a few a's
    as a sanity check that the lift is correct."""
    n = core.curve_order(int(p))
    assert core.is_prime(n), (p, n)
    eps = +1 if int(p) % 4 == 1 else -1
    M = 3 * n                                  # lcm(n,3) since n == 1 mod 3
    assert n % 3 == 1, (n, "expected n == 1 mod 3 so M = 3n")
    KM = CyclotomicField(M)
    zM = KM.gen()
    zeta_n = zM ** 3                            # joint pinning: zeta_n = zM^{M/n} = zM^3
    zeta3  = zM ** n                            # joint pinning: zeta_3 = zM^{M/3} = zM^n
    # sanity on the pinning: zeta_n has exact order n, zeta3 has exact order 3
    assert zeta_n ** n == 1, "zeta_n^n != 1"
    assert zeta3 ** 3 == 1 and zeta3 != 1, "zeta_3 not a primitive cube root"

    dl = core.dlog_table(int(p), n)
    h1 = core.hist_k1(int(p), n, dl)
    h2 = core.hist_k2(int(p), n, dl)

    R = PolynomialRing(KM, 'T'); T = R.gen()
    results = []
    # sample a few mu_6-coset reps (use the census's reps for consistency); for the lower bound the
    # result is a-independent (PART 1), so a handful is a sanity check, not the certificate.
    reps = _mu6_reps(n)
    for a in reps[:min(len(reps), n_ells_check)]:
        V1 = sum(int(h1[d]) * zeta_n ** ((a * d) % n) for d in range(n) if h1[d])
        V2 = sum(int(h2[d]) * zeta_n ** ((a * d) % n) for d in range(n) if h2[d])
        e1 = -V1; e2 = (V1 * V1 + V2) / 2; e3 = eps * int(p) * e1; e4 = KM(int(p) ** 2)
        Lstar = T**4 - e1*T**3 + e2*T**2 - e3*T + e4          # in Q(zeta_M)[T]
        Lstar_z = Lstar(zeta3 * T)                            # L*(zeta3 T), coeffs get zeta3^k factors
        g = R.gcd(Lstar, Lstar_z)                             # direct gcd in Q(zeta_M)[T]
        d_gcd = g.degree()
        results.append({"a": int(a), "gcd_deg": int(d_gcd)})
    # the certificate half: deg gcd >= 2 at every sampled a (PART 1 says it is uniform over all a)
    certified = all(r["gcd_deg"] >= 2 for r in results)
    res = {"p": int(p), "n": int(n), "M": int(M), "eps": int(eps),
           "branch": "+1" if eps == 1 else "-1", "sampled_a": results,
           "gcd_ge_2_all_sampled": bool(certified)}
    if verbose:
        print(f"  p={int(p):>5} n={n:>5} M={M:>5} eps={eps:+d} | "
              f"direct gcd(Q(zeta_M)) degs = {[r['gcd_deg'] for r in results]} | "
              f"g>=2: {'Y' if certified else 'N'}")
    return res


def _mu6_reps(n):
    """mu_6 coset reps (same rule as run_n1_120deg_v1.mu6_reps)."""
    rt = core.tonelli((-3) % n, n); inv2 = pow(2, n-2, n)
    z3 = (-1 + rt) * inv2 % n; z3sq = z3*z3 % n
    U = [1 % n, (n-1) % n, z3, (n-z3) % n, z3sq, (n-z3sq) % n]
    seen = bytearray(n); reps = []
    for m in range(1, n):
        if seen[m]: continue
        reps.append(m)
        for u in U: seen[m*u % n] = 1
    return reps


if __name__ == "__main__":
    import sys
    quick = (len(sys.argv) > 1 and sys.argv[1] == "quick")   # quick = IN_P only, for validation
    # the frozen strata (same as the conjunction runner)
    IN_P = (43, 67, 79, 127, 163, 211, 547)
    S_P  = (823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503)
    C_P  = (577, 733, 1237, 1249, 1669)
    if quick:
        S_P = (); C_P = ()
    out = {"IN": [], "S": [], "C": []}
    print("=== A2: direct gcd in Q(zeta_M), M = 3n, zeta_n and zeta_3 pinned jointly ===")
    for p in IN_P: out["IN"].append(direct_gcd_certificate_prime(p))
    for p in S_P:  out["S"].append(direct_gcd_certificate_prime(p))
    for p in C_P:  out["C"].append(direct_gcd_certificate_prime(p))
    with open("RESULT_120deg_resultant_certificate_v1.json", "w") as f:
        json.dump(out, f, indent=1, default=lambda o: int(o) if hasattr(o, "__index__") else str(o))
    def summ(rows): return "%d/%d primes g>=2 at all sampled a" % (
        sum(1 for r in rows if r["gcd_ge_2_all_sampled"]), len(rows))
    print("\n=== A2 VERDICT (direct Q(zeta_M) gcd cross-check of the g>=2 half) ===")
    print("  IN-SAMPLE :", summ(out["IN"]))
    print("  STRATUM S :", summ(out["S"]), " <-- PRIMARY")
    print("  STRATUM C :", summ(out["C"]))
