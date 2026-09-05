#!/usr/bin/env python3
"""
glv_seven_domain_map_v1.py

Part A of the amicable bridge: map the SEVEN Eisenstein generators pi_p + u,
u in {0} u mu6 = {0, 1, -1, omega, -omega, omega^2, -omega^2}.

Facts made exact here:
  * N(pi_p + u) for the six units are the SIX SEXTIC TWIST ORDERS; N(pi_p) = p (the field).
    In particular N(pi_p - 1) = n (base curve order / amicable) and N(pi_p + 1) = n_t
    (quadratic twist).
  * The ideals (pi_p + u) are concentric (all centered at 0), coprime in pairs, of DIFFERENT
    norms, but all theta-aligned: arg(pi_p+u) = arg(pi_p) + O(1/|pi_p|), so all seven rhombi
    share the SAME pinned / CM-stable sextant pair (match-rate -> 1 with scale; exact at secp).

This is direction (2) generalized to the whole {base, amicable, twists} family: one shared
mu6-geometry. Exact: norms integer; pinned pairs from sector_props (exact Fraction areas).
"""
from fractions import Fraction as F
from lift_sextant_rhombus_law_proof_v2 import (
    cornacchia_4p_D3, gauss_reduce, sector_props, enorm, theta_of)

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
AP, BP = 367917413016453100223835821029139468249, 303414439467246543595250775667605759171
DEG = 180.0 / 3.141592653589793

# u in {0} u mu6, in (a,b) Eisenstein coordinates (w = a + b*omega)
UNITS = {"0": (0, 0), "+1": (1, 0), "-1": (-1, 0),
         "+w": (0, 1), "-w": (0, -1), "+w2": (-1, -1), "-w2": (1, 1)}


def pinned_of(pi):
    a, b = pi
    R1, R2 = gauss_reduce((a, b), (-b, a - b))
    props = sector_props(R1, R2)
    return R1, tuple(t for t in range(6) if props[t] == F(1, 8))


def analyze(name, pi_p, verbose=True):
    pins = {}
    R1_base, pin_base = pinned_of(pi_p)
    for tag, (ua, ub) in UNITS.items():
        piu = (pi_p[0] + ua, pi_p[1] + ub)
        R1u, pinu = pinned_of(piu)
        pins[tag] = (enorm(piu), theta_of(R1u) * DEG, pinu)
    allmatch = all(pins[t][2] == pin_base for t in UNITS)
    if verbose:
        print(f"\n=== {name} ===")
        print(f"    {'u':>4} {'norm N(pi_p+u)':>50} {'theta':>7} {'pinned':>8}")
        label = {"0": "= p (field)", "-1": "= n (base/amicable)", "+1": "= n_t (quad twist)"}
        for tag in ("0", "-1", "+1", "+w", "-w", "+w2", "-w2"):
            N, th, pin = pins[tag]
            print(f"    {tag:>4} {N:>50} {th:7.2f} {str(pin):>8}  {label.get(tag,'sextic twist')}")
        print(f"    ALL SEVEN share pinned pair {pin_base}? {allmatch}")
    return allmatch


def main():
    print("=" * 74)
    print("Seven-domain map: base curve + amicable + twists = {pi_p + u}, one shared pinned pair")
    print("=" * 74)
    assert enorm((AP, BP)) == P_SECP and enorm((AP - 1, BP)) == N_SECP
    analyze("secp256k1", (AP, BP))

    import sympy
    print("\n--- all-seven pinned-match rate vs scale ---")
    for lo, hi in [(10**3, 10**4), (10**4, 10**5), (10**5, 10**6)]:
        ps = [q for q in sympy.primerange(lo, hi) if q % 3 == 1]
        ps = ps[::max(1, len(ps) // 200)]
        m = tot = 0
        for q in ps:
            pi = cornacchia_4p_D3(q)
            if pi:
                tot += 1; m += analyze("", pi, verbose=False)
        print(f"    p in [{lo:>7},{hi:<7}): all-7 pinned match {m}/{tot} = {m/tot:.3f}")


if __name__ == "__main__":
    main()
