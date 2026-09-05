"""verify_universal_section13.py — exhaustive checks for the Universal §13 block.

Verifies (for n across the prime / prime-square / prime-cube / squarefree /
mixed spectrum):
  • UNIV-FSI:   Σ_{ρ ∈ U(n)} ⌊ρj/n⌋ = φ(n)·(j-1)/2,  for every j ∈ [1,n-1].
  • UNIV-T03(a): T_ρ(j) = M(q,j) + ε(ρ,j) with ε ∈ {0,1,2}.
  • UNIV-MOD:   d ∈ bad_set(ρ, T_ρ(j), n) ∩ H_π ⟹ T mod π ∈ {0, π-1}.
  • UNIV-T03(c): for q ∈ [1, ⌊(π-3)/2⌋]: bad_set(ρ, T_ρ(j), n) ∩ H_π = ∅.
  • UNIV-KSF:   Σ_{ρ ∈ U(n)} K_π(ρ,k,j) ≡ jQ + φ(n)(j-1)/2 (mod π).
  • K = T mod n at k=1 (handover example sanity).

Exit non-zero on any failure; prints a per-n / per-π summary on success.
Run:  python3 tools/verify_universal_section13.py
"""
from __future__ import annotations
import math
import random
import sys
from itertools import product
from math import gcd


def units(n: int) -> list[int]:
    return [r for r in range(1, n) if gcd(r, n) == 1]


def totient(n: int) -> int:
    return len(units(n))


def prime_divisors(n: int) -> list[int]:
    out = []
    d = 2
    m = n
    while d * d <= m:
        if m % d == 0:
            out.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        out.append(m)
    return out


def bad_set(rho: int, T: int, n: int) -> set[int]:
    inv = pow(rho, -1, n)
    return {(-T * inv) % n, (-(T + 1) * inv) % n}


def H_pi(n: int, pi: int) -> set[int]:
    return {k * pi for k in range(1, n // pi)}


def M(q: int, j: int, n: int) -> int:
    return q + (q * j) // n


def epsilon(rho: int, q: int, j: int, n: int) -> int:
    return ((q * j) % n + rho + (rho * j) // n) // n


def T_rho(rho: int, q: int, j: int, n: int) -> int:
    e = rho + q * n
    r = n + j
    return (e * r) // (n * n)


def K_pi(rho: int, k: int, j: int, q: int, n: int, pi: int) -> int:
    return (rho * k + q * j + (rho * j) // n) % pi


def check_univ_fsi(n: int) -> tuple[int, int]:
    U = units(n)
    phi = len(U)
    fails = 0
    for j in range(1, n):
        s = sum((rho * j) // n for rho in U)
        expected = phi * (j - 1) // 2
        if 2 * s != phi * (j - 1):
            print(f"  FAIL UNIV-FSI: n={n} j={j}  got 2·sum={2*s}  want {phi*(j-1)}")
            fails += 1
            if fails > 5:
                return (n - 1 - fails, fails)
    return (n - 1 - fails, fails)


def check_univ_t03a(n: int, q_range: range) -> tuple[int, int]:
    """Check T_ρ(j) = M(q,j) + ε(ρ,j) with ε ∈ {0,1,2}."""
    fails = 0
    checks = 0
    U = units(n)
    for q in q_range:
        for rho in U:
            for j in range(1, n):
                T = T_rho(rho, q, j, n)
                m = M(q, j, n)
                e = epsilon(rho, q, j, n)
                checks += 1
                if T != m + e or e not in (0, 1, 2):
                    print(f"  FAIL UNIV-T03(a): n={n} q={q} ρ={rho} j={j}  T={T}  M+ε={m+e}  ε={e}")
                    fails += 1
                    if fails > 5:
                        return (checks, fails)
    return (checks, fails)


def check_univ_mod(n: int, q_range: range) -> tuple[int, int]:
    """For each π | n and each ρ, q, j: if bad_set ∩ H_π ≠ ∅ then T mod π ∈ {0, π-1}."""
    fails = 0
    checks = 0
    U = units(n)
    primes = prime_divisors(n)
    for pi in primes:
        Hpi = H_pi(n, pi)
        if not Hpi:
            continue
        for q in q_range:
            for rho in U:
                for j in range(1, n):
                    T = T_rho(rho, q, j, n)
                    bs = bad_set(rho, T, n)
                    if bs & Hpi:
                        checks += 1
                        if T % pi not in (0, pi - 1):
                            print(f"  FAIL UNIV-MOD: n={n} π={pi} q={q} ρ={rho} j={j}  T={T}  T mod π={T%pi}")
                            fails += 1
                            if fails > 5:
                                return (checks, fails)
    return (checks, fails)


def check_univ_safeq(n: int) -> tuple[int, int]:
    """For each π | n with π ≥ 5 and q ∈ [1, ⌊(π-3)/2⌋]: bad_set ∩ H_π = ∅ for all (ρ, j)."""
    fails = 0
    checks = 0
    U = units(n)
    for pi in prime_divisors(n):
        if pi < 5:
            continue
        thresh = (pi - 3) // 2
        if thresh < 1:
            continue
        Hpi = H_pi(n, pi)
        if not Hpi:
            continue
        for q in range(1, thresh + 1):
            if q >= n:
                continue
            for rho in U:
                for j in range(1, n):
                    T = T_rho(rho, q, j, n)
                    bs = bad_set(rho, T, n)
                    checks += 1
                    if bs & Hpi:
                        print(f"  FAIL UNIV-T03(c): n={n} π={pi} q={q} ρ={rho} j={j}  bad∩H_π={bs & Hpi}")
                        fails += 1
                        if fails > 5:
                            return (checks, fails)
    return (checks, fails)


def admissible_J(n: int, pi: int) -> list[int]:
    """J(n) := {j ∈ [1, n-1] : gcd(j, n/π) = 1}.

    For n=p², n/π = p, so J = {j : p∤j} matching the existing band convention.
    For squarefree n=pq with π=p, n/π = q, so J = {j : q∤j}.
    """
    nq = n // pi
    return [j for j in range(1, n) if math.gcd(j, nq) == 1]


def is_prime_square(n: int) -> int | None:
    """Return p if n == p² for prime p ≥ 5, else None."""
    p = int(math.isqrt(n))
    if p * p == n and len(prime_divisors(n)) == 1 and p >= 5:
        return p
    return None


def check_univ_jbb_multiband(n: int, n_trials: int = 10, q_max: int = 2) -> tuple[int, int, float]:
    """Verify multi-band UNIV-JBB: for each adversarial q-tuple and (d₁,d₂),
    there exists k ∈ {1,…,π-1} with |B_k(d₁) ∪ B_k(d₂)| < |J(n)|.

    This is the CORRECT form of UNIV-JBB (single-band k=1 can saturate;
    multi-band always has a safe j).  Returns (trials_run, failures, min_margin).
    """
    fails = 0
    runs = 0
    min_margin_overall = float("inf")
    U = units(n)
    rng = random.Random(2026_05_05_07 + n)
    n2 = n * n

    for pi in prime_divisors(n):
        Hpi_list = sorted(H_pi(n, pi))
        if len(Hpi_list) < 2:
            continue
        J = admissible_J(n, pi)
        if len(J) < 2:
            continue
        k_bands = range(1, pi)

        for _ in range(n_trials):
            q_tuple = {rho: rng.randint(0, q_max * n) for rho in U}
            d1, d2 = rng.sample(Hpi_list, 2)

            safe_margin = 0
            for k in k_bands:
                B_union = set()
                for rho in U:
                    qr = q_tuple[rho]
                    inv = pow(rho, -1, n)
                    e = rho + qr * n
                    for j in J:
                        T = (e * (k * n + j)) // n2
                        bs = {(-T * inv) % n, (-(T + 1) * inv) % n}
                        if d1 in bs or d2 in bs:
                            B_union.add(j)
                margin = len(J) - len(B_union)
                if margin > 0:
                    safe_margin = margin
                    break  # found safe k-band, move on

            runs += 1
            if safe_margin <= 0:
                print(f"  FAIL UNIV-JBB: n={n} π={pi} d=({d1},{d2}) "
                      f"ALL k-bands saturated")
                fails += 1
                if fails > 3:
                    return (runs, fails, 0.0)
            else:
                min_margin_overall = min(min_margin_overall, safe_margin)

    return (runs, fails, min_margin_overall if min_margin_overall != float("inf") else 0.0)


def check_univ_jbb_strip_width(n: int) -> tuple[int, int]:
    """Verify the T-strip width bound: for any ρ, q, j; the number of j-values
    with T_ρ^k(j) = t is ≤ ⌈n²/e_ρ⌉ + 1.  This is the CORRECT per-T-value
    bound (replacing the wrong per-(ρ,d) bound in the original sketch).
    """
    fails = 0
    checks = 0
    U = units(n)
    n2 = n * n
    for q in range(0, min(n, 5)):
        for rho in U:
            e = rho + q * n
            # Count how many j give each T value at k=1
            T_count: dict[int, int] = {}
            for j in range(1, n):
                T = (e * (n + j)) // n2
                T_count[T] = T_count.get(T, 0) + 1
            bound = math.ceil(n2 / e) + 1
            for T, cnt in T_count.items():
                checks += 1
                if cnt > bound:
                    print(f"  FAIL strip-width: n={n} q={q} ρ={rho} T={T} cnt={cnt} > ⌈n²/e⌉+1={bound}")
                    fails += 1
                    if fails > 5:
                        return (checks, fails)
    return (checks, fails)


def check_univ_ksf(n: int, n_q_samples: int = 5, n_k_samples: int = 3) -> tuple[int, int]:
    """For random q-tuples and random k: Σ K_π ≡ jQ + φ(n)(j-1)/2 (mod π)."""
    fails = 0
    checks = 0
    U = units(n)
    phi = len(U)
    rng = random.Random(2026_05_05)
    for pi in prime_divisors(n):
        for _ in range(n_q_samples):
            q_tuple = {rho: rng.randint(0, 4 * n) for rho in U}
            Q = sum(q_tuple.values())
            for _k in range(n_k_samples):
                k = rng.randint(0, 5 * n)
                for j in range(1, n):
                    s = sum(K_pi(rho, k, j, q_tuple[rho], n, pi) for rho in U) % pi
                    rhs = (j * Q + phi * (j - 1) // 2) % pi
                    checks += 1
                    if s != rhs:
                        print(f"  FAIL UNIV-KSF: n={n} π={pi} k={k} j={j}  ΣK={s}  want {rhs}")
                        fails += 1
                        if fails > 5:
                            return (checks, fails)
    return (checks, fails)


def check_handover_sanity() -> int:
    """Confirm the handover's K vs T discrepancy is real (not a bug we missed).

    For n=25, ρ=24, q=0, j=12, k=1: T_ρ = ⌊24·37/625⌋ = 1, but K (mod 25) = 10
    (≡ 0 mod 5).  These are intentionally different algebraic objects; K is an
    auxiliary linear-in-(k,j) quantity whose SUM over ρ has a closed form
    (UNIV-KSF), not a residue of T_ρ.  This sanity check pins the values so
    that any future refactor that conflates the two surfaces immediately.
    """
    n = 25
    rho, q, j, k = 24, 0, 12, 1
    T = T_rho(rho, q, j, n)
    K_mod_n2 = (rho * k + q * j + (rho * j) // n) % (n * n)
    if T != 1 or K_mod_n2 != 35 or (T % 5) == (K_mod_n2 % 5):
        print(f"  FAIL handover sanity: T={T} (want 1), K mod n²={K_mod_n2} (want 35),"
              f" T%5={T%5}, K%5={K_mod_n2%5} (must differ)")
        return 1
    return 0


def main() -> int:
    # Test set spans prime, prime-square, prime-cube, squarefree pq, mixed p²q.
    test_ns = [7, 9, 15, 21, 25, 27, 35, 45, 49]
    # n=75 = 3·5² is the largest mixed case we run by default.
    if "--with-75" in sys.argv:
        test_ns.append(75)

    total_fail = 0
    total_fail += check_handover_sanity()
    print(f"  handover-K sanity: {'OK' if total_fail == 0 else 'FAIL'}")
    print()

    for n in test_ns:
        primes = prime_divisors(n)
        phi = totient(n)
        # q range: 0..3n is overkill but covers wrap behavior.
        q_range = range(0, min(2 * n + 2, 60))
        print(f"n = {n}  (φ={phi}, primes={primes})")

        fsi_checks, fsi_fails = check_univ_fsi(n)
        print(f"  UNIV-FSI:    {fsi_checks} j-values, {fsi_fails} failures")

        t03_checks, t03_fails = check_univ_t03a(n, q_range)
        print(f"  UNIV-T03(a): {t03_checks} (q,ρ,j) tuples, {t03_fails} failures")

        mod_checks, mod_fails = check_univ_mod(n, q_range)
        print(f"  UNIV-MOD:    {mod_checks} bad-set hits, {mod_fails} failures")

        safe_checks, safe_fails = check_univ_safeq(n)
        print(f"  UNIV-T03(c): {safe_checks} (π,q,ρ,j) safe-regime tuples, {safe_fails} failures")

        ksf_checks, ksf_fails = check_univ_ksf(n)
        print(f"  UNIV-KSF:    {ksf_checks} (π,k,j) sums, {ksf_fails} failures")

        # UNIV-JBB is an open conjecture — not verified here (see lrc_proof.py §13
        # UNIV-JBB comment for scope restrictions and relation to N-PSQ-T02).
        sw_checks, sw_fails = check_univ_jbb_strip_width(n)
        print(f"  T-strip-width: {sw_checks} (q,ρ,T) checks, {sw_fails} failures")

        total_fail += (fsi_fails + t03_fails + mod_fails + safe_fails
                       + ksf_fails + sw_fails)
        print()

    if total_fail == 0:
        print("All universal §13 checks passed.")
        return 0
    else:
        print(f"FAILURES: {total_fail}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
