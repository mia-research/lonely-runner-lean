#!/usr/bin/env python3
"""
odd_s3_harness_v1.py — the ODD half + the S3 (3rd-order) tensor.

Two structurally-linked probes we never ran, on full-enumeration small curves
(y^2=x^3+7 / F_p) so there is real power and a generic baseline. Everything in the
signal path is exact integer / Eisenstein-integer; float only as a displayed ratio.

  A  FULL S3 TENSOR over curve points.  Not the 2-D marginal (2nd moment is
     symmetry-pinned: Int.1 gave 1/2). The 3rd moment is the first ODD-order thing,
     and Sum z^3 = 0 over the FIELD only because the field is x->-x symmetric; curve
     points are QR-restricted (x^3+7 a QR), breaking it. So S3 = the first odd-order
     curve signature. Components S_uuu,S_uuv,S_uvv,S_vvv (exact integer). Scale /p^2:
     generic (sqrt-cancel from the p^2.5 no-cancel scale) => O(0.1) & flat.

  B  The y-coordinate UNLOCKS the odd scalar spectrum.  x([d]G)=x([-d]G) => every
     x-readout is EVEN in d => odd scalar characters give EXACTLY 0 (v5). y flips sign
     under d->-d: s_y(d) = (-1)^(y mod 2) is ODD in d. So an odd readout built from y
     un-zeros the odd characters. Test on a curve with m=3 mod4 (quadratic psi is ODD):
       - Sum_d psi(d) chi_k(x_d)          -> ~0  (odd x even, the v5 structural zero)
       - Sum_d psi(d) s_y(d)              -> the y-UNLOCKED odd probe
       - Sum_d psi(d) chi_k(x_d) s_y(d)   -> combined odd readout
     generic => O(1)*sqrt(m) & flat; a growing column = the gate.
"""
import math
from sympy import isprime
from hybrid_char_sum_v1 import (curve_points_order, find_point, padd, make_chik,
                                legendre, mul, tonelli)
from int1_frame_operator_v1 import build


def orbit_xy(G, p, m):
    xy, acc = [], None
    for _ in range(m):
        acc = padd(acc, G, p)
        xy.append(acc)                       # (x,y) or None at identity
    return xy


def _emul(z, w):
    a, b = z; c, d = w
    return (a * c - b * d, a * d + b * c - b * d)


def emag2(counts, L):
    zeta = {2: (-1, 0), 3: (0, 1), 6: (1, 1)}[L]
    rep, cur = {}, (1, 0)
    for j in range(L):
        rep[j] = cur; cur = _emul(cur, zeta)
    a = b = 0
    for j, c in counts.items():
        ra, rb = rep[j % L]; a += c * ra; b += c * rb
    return a * a - a * b + b * b


# ---------------------------------------------------------------- A: S3 tensor
def section_A():
    print("=" * 78)
    print("[A] FULL S3 tensor over curve points  (3rd-order joint (u,v); the ODD-order signature)")
    print("=" * 78)
    print(f"{'p':>7} {'Nc':>6} {'Suuu/p^2':>10} {'Suuv/p^2':>10} {'Suvv/p^2':>10} {'Svvv/p^2':>10} {'|S3|/p^2':>10}")
    ps = [p for p in range(500, 60000) if isprime(p) and p % 3 == 1]
    for p in [ps[0], ps[10], ps[40], ps[120], ps[300], ps[700], ps[-1]]:
        eis, _ = build(p)
        Suuu = Suuv = Suvv = Svvv = 0; Nc = 0
        for x in range(p):
            if pow((x * x * x + 7) % p, (p - 1) // 2, p) != 1:
                continue                                    # curve x-coords only
            u, v = eis(x); Nc += 1
            Suuu += u * u * u; Suuv += u * u * v; Suvv += u * v * v; Svvv += v * v * v
        tot = math.sqrt(Suuu**2 + Suuv**2 + Suvv**2 + Svvv**2)
        print(f"{p:>7} {Nc:>6} {Suuu/p**2:>10.4f} {Suuv/p**2:>10.4f} {Suvv/p**2:>10.4f} "
              f"{Svvv/p**2:>10.4f} {tot/p**2:>10.4f}")
    print("  generic => all /p^2 = O(0.1) & flat (sqrt-cancel from p^2.5). A component")
    print("  growing toward p^2.5/p^2 = sqrt(p) would be structure.\n")


# ---------------------------------------------------------------- B: y unlocks odd
def section_B():
    print("=" * 78)
    print("[B] y-coordinate UNLOCKS the odd scalar spectrum   (m = 3 mod 4 : quadratic psi is ODD)")
    print("=" * 78)
    print("  cols /sqrt(m):  no-y = Sum psi*chi_k(x)  (~0, structural);  y = Sum psi*s_y;")
    print("                  y*chi_k = Sum psi*chi_k(x)*s_y   (the unlocked odd readout)")
    print()
    print(f"{'p':>7} {'m':>7} {'noy chi2':>9} {'y':>8} {'y*chi2':>8} {'y*chi3':>8} {'[ctrl]rand*y':>13} {'[ctrl]self':>11}")
    ps = [p for p in range(500, 120000) if isprime(p) and p % 3 == 1]
    got = 0
    import random
    for p in ps:
        m = curve_points_order(p)
        if not isprime(m) or m % 4 != 3 or m < 500:        # want ODD quadratic char
            continue
        G = find_point(p)
        if mul(G, m, p) is not None:
            continue
        xy = orbit_xy(G, p, m)
        chi = {k: make_chik(p, k) for k in (2, 3) if (p - 1) % k == 0}
        rm = math.sqrt(m)
        rng = random.Random(p)
        rand = [rng.choice((0, 1)) for _ in range(m)]
        psi = lambda d: legendre(d % m, m)                 # +-1, ODD (m=3 mod4)
        s_y = lambda P: 1 if (P is not None and P[1] % 2 == 0) else -1   # ODD in d

        def combo(use_chi, k, use_y):
            # exact: psi in {+-1}, s_y in {+-1}, chi_k label -> root; L handles it
            if not use_chi:
                S = sum(psi(d + 1) * s_y(xy[d]) for d in range(m))
                return abs(S) / rm
            L = k
            cnt = {}
            for d in range(m):
                if xy[d] is None:
                    continue
                jk = chi[k](xy[d][0])
                if jk is None:
                    continue
                sgn = psi(d + 1) * (s_y(xy[d]) if use_y else 1)   # +-1
                # fold sign into the root-of-unity count: sign * zeta^jk
                cnt[jk] = cnt.get(jk, 0) + sgn
            return math.sqrt(emag2(cnt, L)) / rm

        noy2 = combo(True, 2, False)                       # ~0 expected (odd x even)
        y0 = combo(False, None, True)
        y2 = combo(True, 2, True)
        y3 = combo(True, 3, True) if 3 in chi else float('nan')
        # controls
        Sr = sum((1 - 2 * rand[d]) * s_y(xy[d]) for d in range(m)); cr = abs(Sr) / rm
        Ss = sum(1 for d in range(1, m) if legendre(d, m) != 0); cs = Ss / rm  # ~m -> sqrt(m)*sqrt(m)
        print(f"{p:>7} {m:>7} {noy2:>9.3f} {y0:>8.3f} {y2:>8.3f} {y3:>8.3f} {cr:>13.3f} {cs:>11.2f}")
        got += 1
        if got >= 6:
            break
    print()
    print("  READ: no-y ~ 0 (confirms odd char INVISIBLE to x);  y-cols O(1) & flat = the odd")
    print("  spectrum is UNLOCKED by y but GENERIC;  a growing y-col = odd structure (gate).")


if __name__ == "__main__":
    print("ODD + S3 HARNESS v1  (exact signal path)\n")
    section_A()
    section_B()
    print("\nDONE.")
