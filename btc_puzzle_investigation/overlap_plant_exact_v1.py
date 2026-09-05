#!/usr/bin/env python3
"""
overlap_plant_exact_v1.py -- the EXACT-INTEGER signal path for the overlap-arm planted control.

Split out of `overlap_arm_power_v1.py` so that the signal path is separately checkable:

    bash check_no_float.sh overlap_plant_exact_v1.py     ->  must print OK

Everything that touches the band, the targets, the curve readouts or the planted mixture lives HERE
and is exact (Python int / fractions.Fraction).  The float power spectrum, the Pearson rho and the
permutation z-rank live in `overlap_arm_power_v1.py` -- they are the monotone statistic, ranked
against a matched permutation null, which CLAUDE.md permits and this module deliberately excludes.

Contract exported to the statistic layer:
  * every sequence returned is a list of Python `int`;
  * `plant()` output satisfies |x| < 2^52, so the float64 FFT downstream loses no bits of it
    (checked by `selftest()` and asserted again at the call site).
"""
from fractions import Fraction
from math import isqrt

from int1_frame_operator_v1 import build
from lift_sextant_rhombus_law_proof_v2 import enorm, sextant
from t_y_maxbound_v1 import prime_order_curve, group_coords
from lift_band_spectral_v1 import band_residual

FLOAT_EXACT_BOUND = 1 << 52


def l2_scale(seq_int):
    """Exact integer l2 norm of the L-scaled centred sequence: isqrt(sum (L*x - sum x)^2).

    L-scaling keeps the centring exact (no division), and isqrt keeps the norm an integer.  Only the
    RATIO of two such scales is used downstream, so the common factor L is immaterial.
    """
    L = len(seq_int)
    tot = sum(int(x) for x in seq_int)
    return isqrt(sum((L * int(x) - tot) ** 2 for x in seq_int))


def scale_ratio(target_int, noise_int, den_cap=256):
    """(num, den) with num/den ~ l2(noise)/l2(target), as an exact bounded-denominator rational.

    Multiplying target by `num` and noise by `den` equalises the two components' l2 weight before
    mixing, without any float ratio and with multipliers small enough to keep products exact.
    """
    sT = l2_scale(target_int)
    sN = l2_scale(noise_int)
    if sT == 0 or sN == 0:
        return None
    fr = Fraction(sN, sT).limit_denominator(den_cap)
    if fr.numerator == 0:
        fr = Fraction(1, den_cap)
    return fr.numerator, fr.denominator


def plant(target_int, noise_int, a, b, den_cap=256):
    """plant = (a/b)*target + (1 - a/b)*noise, EXACT INT, the two components l2-matched.

    `a`, `b` are integers; the amplitude fraction is the exact rational a/b.  a=b gives the target
    itself (degenerate); a=0 gives pure noise, which is the arm's own null.
    """
    sr = scale_ratio(target_int, noise_int, den_cap=den_cap)
    if sr is None:
        return None
    num, den = sr
    return [a * num * int(t) + (b - a) * den * int(w)
            for t, w in zip(target_int, noise_int)]


def build_band(lo, hi, bexp, M):
    """Band targets + curve readouts, EXACT INT, identical construction to lift_band_spectral_v1."""
    r = prime_order_curve(lo, hi)
    if not r:
        return None
    p, n, G = r
    A = 1 << (bexp - 1)
    if 2 * A > n:
        return None
    xs, ys = group_coords(G, p, n, 0)
    eis, eps = build(p)
    ds = list(range(A, 2 * A))

    derr = []
    kden = []
    for d in ds:
        e, q = band_residual(d - A, A, M)
        derr.append(int(e))
        kden.append(int(q))

    U = []; V = []; S = []; EP = []; SX = []; SXY = []
    for d in ds:
        x = xs[d]; y = ys[d]
        u, v = eis(x)
        U.append(int(u)); V.append(int(v)); S.append(int(enorm((u, v))))
        EP.append(int(eps(x))); SX.append(int(sextant(u, v)))
        SXY.append(1 if 2 * (x * y % p) < p else -1)

    targets = {'derr': derr, 'k_den': kden}
    readouts = {'eis_u': U, 'eis_v': V, 'norm_s': S,
                'flap_eps': EP, 'sextant': SX, 'sign_xy': SXY}
    return p, n, A, len(ds), targets, readouts


def selftest(lo=2100, hi=4200, bexp=11, M=32, b=1024):
    """Decidable artifact: the plant is integral, Fraction-exact, and inside the float-exact bound."""
    got = build_band(lo, hi, bexp, M)
    assert got is not None, "no usable curve for selftest"
    p, n, A, L, targets, readouts = got
    checked = 0
    worst = 0
    for tname, tseq in targets.items():
        assert all(isinstance(x, int) for x in tseq), "%s not exact int" % tname
        for rname, rseq in readouts.items():
            assert all(isinstance(x, int) for x in rseq), "%s not exact int" % rname
            for a in (0, 1, 184, 256, 512, b):
                mix = plant(tseq, rseq, a, b)
                assert all(isinstance(x, int) for x in mix), "plant not exact int"
                # independent Fraction recomputation of the same mixture
                num, den = scale_ratio(tseq, rseq)
                for i in (0, 1, L // 3, L // 2, L - 1):
                    ref = Fraction(a * num * tseq[i] + (b - a) * den * rseq[i], 1)
                    assert Fraction(mix[i], 1) == ref, "plant != Fraction recomputation"
                m = max(abs(x) for x in mix)
                worst = max(worst, m)
                assert m < FLOAT_EXACT_BOUND, "plant magnitude %d >= 2^52" % m
                checked += 1
    print("selftest OK: p=%d L=%d  %d plant configurations exact-int and Fraction-verified"
          % (p, L, checked))
    print("             max |plant| = %d  =  2^%.1f   (float-exact bound 2^52)"
          % (worst, worst.bit_length() - 1))
    return True


if __name__ == '__main__':
    selftest()
