#!/usr/bin/env python3
"""case_63 (ii.2.b) FULL-ROUTE integer simulation (BS L607-635, both signs).

Branch hypotheses: ratio-3 A1 labeling at level h < m
  x = d1-d3 = 7^h * (t + 7*...),  y = d2-d3 = 7^h * (3t + 7*...),
  e45 = 2*d4 - d5 at level exactly h, residue s (any unit).

Route under test (the planned Lean wiring):
 0. RELABEL: pick (D1,D2,D3) in {(d1,d2,d3),(d2,d3,d1),(d3,d1,d2)} and sign
    sigma so that r(sigma*e45) = r(D2-D3)  [all 6 units occur: 3t,-t,-2t & +-].
 1. f := (D2-D3) - sigma*e45, nu(f) > h.  Sub-cases:
      nu(f) >= m+1 (incl f=0): lam1 = 1,  X-W = 0 exactly.
      nu(f) = m: constant unit mu with mu*r_m(f) == 1: X-W = 1 exactly.
      h < nu(f) < m: Lambda_{nu(f)} retarget q(lam1*f)=0: X-W in {0,1}.
 2. X=q(lam1*Y'), Y=q(lam1*X'), Z=q(lam1*(Y'-X')), W=q(lam1*sigma*e45)
    where X'=D1-D3, Y'=D2-D3. Check hZ: Z in {X-Y, X-Y+6}; hW: W in {X, X-1}.
 3. If not (3X+5Y=3 and W=X): find k per ii2b_shift; realize via Lambda_h
    j = k * r(lam1*X')^{-1}; final frame LAM = lam2*lam1.
    (A) all three A1 diff-arcs in {0,6}  -> window len 2, no carve needed
    (B) diff-arcs in {0,1,5,6} and W+3k in {0,6} -> window len 3 + carve.
 4. Exception: k0 with X+3k0=3 (then Y+k0=3, W+3k0=3, Z+2k0 in {0,6});
    DOUBLE the frame: LAM = 2*lam2*lam1 -> diff-arcs {0,6}/{0,1,5,6} + carve.
 5. CARVE check: etilde = 2*q(LAM*d4) - q(LAM*d5) not in {2,4}.
 6. WINDOW check: q(LAM*{d1,d2,d3}) fits a window of length L (2 or 3).
"""
import random

BAD = {0, 6}


def qz(m, x):
    return (x % 7 ** (m + 1)) // 7 ** m


def nu7(x):
    if x == 0:
        return None  # infinite
    n = 0
    while x % 7 == 0:
        x //= 7
        n += 1
    return n


def res(h, x):
    return (x // 7 ** h) % 7


def fits_window(vals, L):
    return any(all(any((v - (a + j)) % 7 == 0 for j in range(L)) for v in vals)
               for a in range(7))


def ii2b_shift(X, Y, Z, W):
    for k in range(7):
        if all(v % 7 in BAD for v in (X + 3 * k, Y + k, Z + 2 * k)):
            return k, 'A'
        if all(v % 7 in (0, 1, 5, 6) for v in (X + 3 * k, Y + k, Z + 2 * k)) \
                and (W + 3 * k) % 7 in BAD:
            return k, 'B'
    return None, None


def run(m, h, d1, d2, d3, d4, d5):
    e45 = 2 * d4 - d5
    t = res(h, d1 - d3)
    s = res(h, e45)
    assert t != 0 and s != 0 and res(h, d2 - d3) == 3 * t % 7
    # 0. relabel
    for (D1, D2, D3), sigma in [((d1, d2, d3), 1), ((d1, d2, d3), -1),
                                ((d2, d3, d1), 1), ((d2, d3, d1), -1),
                                ((d3, d1, d2), 1), ((d3, d1, d2), -1)]:
        Xd, Yd = D1 - D3, D2 - D3
        if res(h, Yd) == res(h, sigma * e45) != 0 and \
                res(h, Yd) == 3 * res(h, Xd) % 7 and res(h, Xd) != 0:
            break
    else:
        return "NO_RELABEL"
    g = sigma * e45
    # 1. f-retarget
    f = Yd - g
    nf = nu7(f)
    assert nf is None or nf > h, f"nu(f)={nf} <= h"
    if nf is None or nf >= m + 1:
        lam1 = 1
    elif nf == m:
        rf = res(m, f)
        lam1 = pow(rf, -1, 7)  # constant unit, mu*rf == 1 mod 7
    else:
        # Lambda_{nf} retarget: q(lam1*f) = 0
        rf = res(nf, f)
        kk = (-qz(m, f) * pow(rf, -1, 7)) % 7
        lam1 = 1 + kk * 7 ** (m - nf)
        assert qz(m, lam1 * f) == 0
    # 2. base-frame arcs
    X, Y = qz(m, lam1 * Yd), qz(m, lam1 * Xd)
    Z, W = qz(m, lam1 * (Yd - Xd)), qz(m, lam1 * g)
    if Z % 7 not in ((X - Y) % 7, (X - Y + 6) % 7):
        return "HZ_FAIL"
    if W % 7 not in (X % 7, (X - 1) % 7):
        return "HW_FAIL"
    rx1 = res(h, lam1 * Xd)
    # 3/4. table or exception
    if not ((3 * X + 5 * Y) % 7 == 3 and W == X):
        k, br = ii2b_shift(X, Y, Z, W)
        if k is None:
            return "DECIDE_FAIL"
        j = (k * pow(rx1, -1, 7)) % 7
        LAM = (1 + j * 7 ** (m - h)) * lam1
        dbl = False
    else:
        k0 = (1 + 2 * X) % 7
        j = (k0 * pow(rx1, -1, 7)) % 7
        LAM = (1 + j * 7 ** (m - h)) * lam1
        # verify the exception algebra
        assert qz(m, LAM * Yd) == 3 and qz(m, LAM * Xd) == 3
        assert qz(m, LAM * g) == 3 and qz(m, LAM * (Yd - Xd)) in BAD
        LAM *= 2
        dbl = True
        br = 'B'
    # 5/6. final checks
    arcs_diff = [qz(m, LAM * Yd), qz(m, LAM * Xd), qz(m, LAM * (Yd - Xd))]
    w_fin = qz(m, LAM * g)
    a1 = [qz(m, LAM * d) for d in (d1, d2, d3)]
    if br == 'A':
        if not all(a in BAD for a in arcs_diff):
            return "A_DIFFARC"
        if not fits_window(a1, 2):
            return "A_WINDOW"
        return "OK_A"
    # branch B
    if not all(a in (0, 1, 5, 6) for a in arcs_diff):
        return f"B_DIFFARC {arcs_diff} dbl={dbl}"
    if w_fin not in BAD:
        return f"B_WFIN {w_fin} dbl={dbl}"
    if not fits_window(a1, 3):
        return "B_WINDOW"
    et = (2 * qz(m, LAM * d4) - qz(m, LAM * d5)) % 7
    if et in (2, 4):
        return f"B_CARVE et={et} sigma={sigma} w_fin={w_fin} dbl={dbl}"
    return "OK_B" + ("_dbl" if dbl else "")


def gen(rng):
    m = rng.choice([2, 2, 3, 4])
    h = rng.randrange(1, m)
    d3 = rng.randrange(-7 ** (m + 2), 7 ** (m + 2))
    if d3 % 7 != 1:
        return None
    t = rng.randrange(1, 7)
    cx = t + 7 * rng.randrange(-7 ** (m - h + 1), 7 ** (m - h + 1))
    cy = 3 * t % 7 + 7 * rng.randrange(-7 ** (m - h + 1), 7 ** (m - h + 1))
    if cx % 7 == 0 or cy % 7 == 0:
        return None
    d1, d2 = d3 + 7 ** h * cx, d3 + 7 ** h * cy
    d4 = rng.randrange(-7 ** (m + 2), 7 ** (m + 2))
    if d4 % 7 != 2:
        return None
    s = rng.randrange(1, 7)
    ce = s + 7 * rng.randrange(-7 ** (m - h + 1), 7 ** (m - h + 1))
    if ce % 7 == 0:
        return None
    d5 = 2 * d4 - 7 ** h * ce
    if len({d1, d2, d3, d4, d5}) < 5:
        return None
    return m, h, d1, d2, d3, d4, d5


def main():
    rng = random.Random(632)
    results = {}
    n = 0
    while n < 8000:
        cfg = gen(rng)
        if cfg is None:
            continue
        n += 1
        r = run(*cfg)
        results[r] = results.get(r, 0) + 1
        if not r.startswith("OK") and results[r] <= 3:
            print(f"  [{r}] cfg={cfg}")
    print(f"\ntotal {n}: {results}")
    print("PASS" if all(k.startswith("OK") for k in results) else "FAIL")


if __name__ == "__main__":
    main()
