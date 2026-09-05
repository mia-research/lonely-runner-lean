from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import gcd, lcm
import random
from typing import List, Tuple


def lcm_list(vals):
    return reduce(lcm, vals, 1)


def modinv(a: int, n: int) -> int | None:
    a %= n
    t, new_t = 0, 1
    r, new_r = n, a
    while new_r:
        q = r // new_r
        t, new_t = new_t, t - q * new_t
        r, new_r = new_r, r - q * new_r
    if r != 1:
        return None
    return t % n


def merge_closed_intervals(iv: List[Tuple[Fraction, Fraction]]) -> List[Tuple[Fraction, Fraction]]:
    if not iv:
        return []
    iv = sorted(iv)
    out: List[Tuple[Fraction, Fraction]] = [iv[0]]
    for lo, hi in iv[1:]:
        plo, phi = out[-1]
        if lo <= phi:
            if hi > phi:
                out[-1] = (plo, hi)
        else:
            out.append((lo, hi))
    return out


def intersect_interval_lists(a: List[Tuple[Fraction, Fraction]], b: List[Tuple[Fraction, Fraction]]) -> List[Tuple[Fraction, Fraction]]:
    out: List[Tuple[Fraction, Fraction]] = []
    i = j = 0
    while i < len(a) and j < len(b):
        lo = max(a[i][0], b[j][0])
        hi = min(a[i][1], b[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out


def Sf_intervals(n: int, f: int) -> List[Tuple[Fraction, Fraction]]:
    iv = []
    for m in range(f):
        lo = Fraction(m * n + 1, f * n)
        hi = Fraction(m * n + (n - 1), f * n)
        iv.append((lo, hi))
    return iv


def S_components(n: int, factors: List[int]) -> List[Tuple[Fraction, Fraction]]:
    cur = [(Fraction(0), Fraction(1))]
    for f in factors:
        cur = intersect_interval_lists(cur, Sf_intervals(n, f))
        if not cur:
            return []
    return merge_closed_intervals(cur)


def ceil_frac_mul(fr: Fraction, m: int) -> int:
    num = fr.numerator * m
    den = fr.denominator
    return -(-num // den)


def floor_frac_mul(fr: Fraction, m: int) -> int:
    num = fr.numerator * m
    den = fr.denominator
    return num // den


def component_intervals_for_M(n: int, components: List[Tuple[Fraction, Fraction]], L: int) -> List[Tuple[int, int]]:
    out = []
    for lo, hi in components:
        u = ceil_frac_mul(lo, L)
        v = floor_frac_mul(hi, L)
        if u <= v:
            out.append((u, v))
    return out


def intersect_int(a: Tuple[int, int], b: Tuple[int, int]) -> Tuple[int, int] | None:
    lo = max(a[0], b[0])
    hi = min(a[1], b[1])
    if lo <= hi:
        return (lo, hi)
    return None


def S_value(n: int, e_fix: List[int], factors: List[int], M: int) -> int:
    e_max = max(e_fix)
    E_div = [n * f for f in factors]
    L0 = lcm_list([n] + e_fix + E_div)
    L = L0 * M

    components = component_intervals_for_M(n, S_components(n, factors), L)

    I_lo = ((L + n - 1) // n, (L // e_max) - 1)
    I_hi = (((e_max - 1) * L + e_max - 1) // e_max, ((n - 1) * L) // n)

    total = 0
    for c in components:
        for band in (I_lo, I_hi):
            ij = intersect_int(c, band)
            if ij:
                total += ij[1] - ij[0] + 1
    return total


def bad_set_unit(e: int, b: int, n: int, L: int) -> set[int]:
    inv = modinv(e % n, n)
    if inv is None:
        # Outside unit-scope this would require separate branch.
        return set(range(n))
    t = (e * b) // L
    r = (e * b) % L
    s = {(-t * inv) % n}
    if r > 0:
        s.add((-(t + 1) * inv) % n)
    return s


def no_bad_on_component_bands_unit_scope(n: int, e_fix: List[int], factors: List[int], M: int) -> bool:
    e_max = max(e_fix)
    E_div = [n * f for f in factors]
    L0 = lcm_list([n] + e_fix + E_div)
    L = L0 * M

    components = component_intervals_for_M(n, S_components(n, factors), L)
    I_lo = ((L + n - 1) // n, (L // e_max) - 1)
    I_hi = (((e_max - 1) * L + e_max - 1) // e_max, ((n - 1) * L) // n)

    for c in components:
        for band in (I_lo, I_hi):
            ij = intersect_int(c, band)
            if not ij:
                continue
            lo, hi = ij
            for b in range(lo, hi + 1):
                U = set()
                for e in e_fix:
                    U |= bad_set_unit(e, b, n, L)
                U |= bad_set_unit(M, b, n, L)
                if len(U) == n:
                    return False
    return True


def admissible_Ms(n: int, L0: int, max_M: int = 120, need: int = 5) -> List[int]:
    out = []
    for M in range(1, max_M + 1):
        if gcd(M, n * L0) == 1:
            out.append(M)
        if len(out) >= need:
            break
    return out


@dataclass
class PrimeStats:
    templates: int = 0
    affine_ok: int = 0
    slope_pos: int = 0
    slope_zero: int = 0
    slope_nonint: int = 0
    witness_zero: Tuple[int, List[int], List[int], List[Tuple[int, int]]] | None = None


@dataclass
class CompositeStats:
    templates: int = 0
    local_no_bad_ok: int = 0
    local_no_bad_fail: int = 0


def run_prime_probe(seed: int = 0) -> PrimeStats:
    rng = random.Random(seed)
    stats = PrimeStats()

    # Broader than tracked pool: allow f up to 8.
    for n in (7, 11, 13):
        units = list(range(1, n))  # prime: all units
        for d in (2, 3):
            fixed_sz = n - 2 - d
            if fixed_sz <= 0:
                continue

            # sample templates rather than full explosion
            cand_fix = list(combinations(units, fixed_sz))
            rng.shuffle(cand_fix)
            cand_fix = cand_fix[:35]

            for fix in cand_fix:
                # sample many divisible-factor sets
                factor_pool = list(range(1, 9))
                cand_f = list(combinations(factor_pool, d))
                rng.shuffle(cand_f)
                cand_f = cand_f[:12]

                for fac in cand_f:
                    e_fix = list(fix)
                    E_div = [n * f for f in fac]
                    L0 = lcm_list([n] + e_fix + E_div)
                    Ms = admissible_Ms(n, L0, max_M=120, need=5)
                    if len(Ms) < 3:
                        continue

                    vals = [S_value(n, e_fix, list(fac), M) for M in Ms]
                    m1, m2 = Ms[0], Ms[1]
                    s1 = Fraction(vals[1] - vals[0], m2 - m1)
                    s0 = Fraction(vals[0], 1) - s1 * m1
                    affine = all(Fraction(v, 1) == s1 * m + s0 for v, m in zip(vals, Ms))

                    stats.templates += 1
                    if affine:
                        stats.affine_ok += 1
                    if s1.denominator != 1:
                        stats.slope_nonint += 1
                    elif s1.numerator > 0:
                        stats.slope_pos += 1
                    elif s1.numerator == 0:
                        stats.slope_zero += 1
                        if stats.witness_zero is None:
                            stats.witness_zero = (n, e_fix, list(fac), list(zip(Ms, vals)))

    return stats


def run_composite_unit_probe(seed: int = 1) -> CompositeStats:
    rng = random.Random(seed)
    stats = CompositeStats()

    for n in (8, 9, 10, 12):
        units = [u for u in range(1, n) if gcd(u, n) == 1]
        for d in (2, 3):
            fixed_sz = n - 2 - d
            if fixed_sz <= 0 or fixed_sz > len(units):
                continue

            cand_fix = list(combinations(units, fixed_sz))
            rng.shuffle(cand_fix)
            cand_fix = cand_fix[:30]

            for fix in cand_fix:
                factor_pool = list(range(1, 7))
                cand_f = list(combinations(factor_pool, d))
                rng.shuffle(cand_f)
                cand_f = cand_f[:10]

                for fac in cand_f:
                    e_fix = list(fix)
                    E_div = [n * f for f in fac]
                    L0 = lcm_list([n] + e_fix + E_div)
                    Ms = admissible_Ms(n, L0, max_M=90, need=3)
                    if not Ms:
                        continue
                    M = Ms[0]
                    ok = no_bad_on_component_bands_unit_scope(n, e_fix, list(fac), M)

                    stats.templates += 1
                    if ok:
                        stats.local_no_bad_ok += 1
                    else:
                        stats.local_no_bad_fail += 1

    return stats


def main() -> None:
    p = run_prime_probe()
    c = run_composite_unit_probe()

    print("=== Gap-2 Generalization Probe v1 ===")
    print(f"prime_templates_tested={p.templates}")
    print(f"prime_affine_exact_pass={p.affine_ok}")
    print(f"prime_slope_positive={p.slope_pos}")
    print(f"prime_slope_zero={p.slope_zero}")
    print(f"prime_slope_nonint={p.slope_nonint}")
    if p.witness_zero:
        n, fix, fac, vals = p.witness_zero
        print("prime_zero_slope_witness=")
        print(f"  n={n} e_fix={fix} factors={fac}")
        print(f"  S_samples={vals}")

    print(f"composite_unit_templates_tested={c.templates}")
    print(f"composite_unit_local_no_bad_pass={c.local_no_bad_ok}")
    print(f"composite_unit_local_no_bad_fail={c.local_no_bad_fail}")


if __name__ == "__main__":
    main()
