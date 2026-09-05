#!/usr/bin/env python3
"""
scalar_mult_char_sum_v1.py — the SCALAR-multiplicative blind spot.

The closure theorem (glv_closure_theorem_v2.md, Lemma R) bounds
    |Cov(F(x([d]G)), g(d))| <= (max|T|/n) * ||F||_A * ||g||_A
with ||g||_A the ADDITIVE Wiener norm of the scalar feature g. A MULTIPLICATIVE
character psi of the scalar (e.g. the quadratic symbol (d|n)) has ||psi||_A ~ sqrt(n),
so the bound is VACUOUS for EVERY readout F -- geometric (eps/sextant/norm) included.
The hybrid sum we built last turn closed the READOUT-side blind spot (chi_k, ||F||_A~sqrt p)
against ADDITIVE scalar features. It says NOTHING about multiplicative scalar features.
This is the symmetric, broader, untested corner.

Direct object (must be built directly -- routing through Lemma R is vacuous):
    S(psi, F) = sum_{d=1..m-1}  psi(d) * F( x([d]G) )        over the whole prime-order <G>
Compare |S| to:  sqrt(m) (generic / square-root-cancellation)   vs   m (total leak).

psi (scalar multiplicative chars):  quadratic (d|m) [EXACT int]; cubic mod m if m=1 mod 3.
F  (point readouts):  chi_2,chi_3,chi_6 (mult); eps in {0,1}, sextant phase (geometric).
Controls: psi=trivial -> pure coordinate sum (~sqrt p, known); psi vs FRESH random +-1
(negative, ~sqrt m); psi vs psi (self, = m, detector fires).

EXACT: for psi,F both real (+-1, or eps in {0,1}) S is a plain INTEGER -- no float at all.
For chi_3/chi_6, S is an exact Eisenstein integer; |S|^2 via the exact norm form. Float
appears ONLY as the display ratio |S|/sqrt(m) (an analytic-size check, per this dir's
CLAUDE.md carve-out for root-of-unity character sums), never in the signal path.
"""
import math, random
from sympy import isprime
from hybrid_char_sum_v1 import (curve_points_order, find_point, padd, make_chik,
                                legendre, mul)
from int1_frame_operator_v1 import build


def orbit_xs(G, p, m):
    xs, acc = [], None
    for _ in range(m):
        acc = padd(acc, G, p)
        xs.append(acc[0] if acc is not None else None)
    return xs


def cubic_char_mod(m):
    """A nontrivial cubic multiplicative character of (Z/mZ)^*, m prime = 1 mod 3.
    psi(d) = j in {0,1,2} s.t. d is in the j-th cubic-residue coset; returns exp(2pi i j/3)
    packed as the integer j (caller maps to Eisenstein root)."""
    e = (m - 1) // 3
    g = 2
    while pow(g, e, m) == 1 or pow(g, (m - 1) // 3, m) == 1:
        # find g with g^e a primitive cube root of 1 (i.e. g a non-cubic-residue)
        if pow(g, e, m) != 1:
            break
        g += 1
    zeta = pow(g, e, m)                       # primitive cube root of unity mod m
    tbl, cur = {}, 1
    for j in range(3):
        # values with cubic symbol zeta^j:  d^e = zeta^j
        pass
    def psi(d):
        d %= m
        if d == 0:
            return None
        r = pow(d, e, m)
        # r in {1, zeta, zeta^2}; map to 0,1,2
        if r == 1:
            return 0
        if r == zeta:
            return 1
        return 2
    return psi


# exact magnitude helpers ------------------------------------------------------
def _emul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)      # (a+b w)(c+d w), w^2=-1-w


def emag2_from_expsum(counts_by_angle, L):
    """|sum_j c_j * zeta_L^j|^2 EXACTLY in Z[omega].  L in {2,3,6}. counts integer."""
    zeta = {2: (-1, 0), 3: (0, 1), 6: (1, 1)}[L]       # zeta_2=-1, zeta_3=omega, zeta_6=1+omega
    rep, cur = {}, (1, 0)
    for j in range(L):
        rep[j] = cur; cur = _emul(cur, zeta)
    a = b = 0
    for j, c in counts_by_angle.items():
        ra, rb = rep[j % L]; a += c * ra; b += c * rb
    return a * a - a * b + b * b                        # exact norm N(a+b omega)


def _label_q(d, m):
    lg = legendre(d % m, m)
    return None if lg == 0 else (0 if lg == 1 else 1)   # quadratic label in {0,1}


def combo_mag(xs, m, psi_label, ord_psi, chi_k, k):
    """|sum_d zeta^{psi(d)} * chi_k(x_d)|^2 exactly; combine to L=lcm(ord_psi,k)."""
    L = ord_psi * k // math.gcd(ord_psi, k)
    cnt = {}
    for d in range(m):
        x = xs[d]
        if x is None:
            continue
        jp = psi_label(d + 1)
        jk = chi_k(x)
        if jp is None or jk is None:
            continue
        ang = (jp * (L // ord_psi) + jk * (L // k)) % L
        cnt[ang] = cnt.get(ang, 0) + 1
    return emag2_from_expsum(cnt, L), L


def run(p):
    m = curve_points_order(p)
    if not isprime(m) or m < 300:
        return None
    G = find_point(p)
    if mul(G, m, p) is not None:                        # confirm order = m
        return None
    xs = orbit_xs(G, p, m)                              # x([d]G), d=1..m
    _, eps = build(p)
    chi = {k: make_chik(p, k) for k in (2, 3, 6) if (p - 1) % k == 0}
    rng = random.Random(p)
    rand = [rng.choice((0, 1)) for _ in range(m)]       # fresh non-d-derived +-1 label

    out = {"m4": m % 4, "m3": m % 3}
    rm = math.sqrt(m)

    # quadratic psi (EVEN iff m=1 mod4; else the x-readout sum is EXACTLY 0 by d<->-d)
    if m % 4 == 1:
        for k in (2, 3, 6):
            if k in chi:
                mag2, _ = combo_mag(xs, m, lambda d: _label_q(d, m), 2, chi[k], k)
                out[f"q x chi{k}"] = math.sqrt(mag2) / rm
        Se = sum((1 if _label_q(d + 1, m) == 0 else -1) *
                 (1 if (xs[d] is not None and eps(xs[d]) != 0) else 0)
                 for d in range(m) if _label_q(d + 1, m) is not None)
        out["q x eps"] = abs(Se) / rm
    # cubic psi (ALWAYS even: -1 is a cube mod m) -- the non-degenerate scalar-mult test
    if m % 3 == 1:
        psi_c = cubic_char_mod(m)
        for k in (2, 3, 6):
            if k in chi:
                mag2, _ = combo_mag(xs, m, lambda d: psi_c(d), 3, chi[k], k)
                out[f"cub x chi{k}"] = math.sqrt(mag2) / rm

    # controls
    if m % 4 == 1:
        Sc = sum((1 if _label_q(d + 1, m) == 0 else -1) * (1 - 2 * rand[d])
                 for d in range(m) if _label_q(d + 1, m) is not None)
        out["[ctrl] q x rand"] = abs(Sc) / rm
        Ss = sum(1 for d in range(1, m) if legendre(d, m) != 0)   # self = #units, ~ m
        out["[ctrl] q self"] = Ss / rm
    if 2 in chi:                                          # psi=triv -> pure coord sum
        mag2, _ = emag2_from_expsum(
            {j: sum(1 for d in range(m) if xs[d] is not None and chi[2](xs[d]) == j)
             for j in (0, 1)}, 2), None
        out["[ctrl] triv chi2"] = math.sqrt(mag2) / rm
    return m, out


def main():
    print("SCALAR-MULTIPLICATIVE character sum   S(psi,F) = sum_d psi(d) F(x([d]G))")
    print("Whole prime-order <G>, full enumeration.  |S|/sqrt(m):  O(1)&flat=generic; ~sqrt(m)=leak.")
    print("NOTE x([d]G)=x([-d]G) => every x-readout is EVEN in d => only the EVEN part of psi")
    print("     survives.  quadratic psi is odd for m=3 mod4 (sum EXACTLY 0, structural, shown as -).")
    print("     cubic psi is always even (-1 is a cube mod m) => the clean scalar-mult probe.")
    print()
    cols = ["q x chi2", "q x chi3", "q x chi6", "cub x chi2", "cub x chi3", "cub x chi6",
            "q x eps", "[ctrl] q x rand", "[ctrl] q self", "[ctrl] triv chi2"]
    print(f"{'p':>7} {'m':>7} {'m%12':>4} " + " ".join(f"{c:>11}" for c in cols))
    ps = [p for p in range(500, 200000) if isprime(p) and p % 3 == 1]
    got = 0
    for p in ps:
        r = run(p)
        if r is None:
            continue
        m, out = r
        if not (m % 12 == 1):            # want both quadratic (m=1 mod4) and cubic (m=1 mod3) live
            continue
        cells = " ".join(f"{out[c]:>11.3f}" if c in out else f"{'-':>11}" for c in cols)
        print(f"{p:>7} {m:>7} {m % 12:>4} {cells}")
        got += 1
        if got >= 8:
            break
    print()
    print("READ: q-self & (roughly) leak scale ~ sqrt(m); triv-chi2 = known coordinate sum;")
    print("      signal cols (q/cub x chi_k, q x eps) O(1) & flat => scalar-mult structure NOT")
    print("      visible in these readouts.  A column GROWING with p would be the gate.")


if __name__ == "__main__":
    main()
