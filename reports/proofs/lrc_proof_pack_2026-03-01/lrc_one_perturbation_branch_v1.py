#!/usr/bin/env python3
from __future__ import annotations

from fractions import Fraction
import math
from decimal import Decimal, getcontext

getcontext().prec = 80


def ap_speeds(n: int, Delta: Fraction = Fraction(1, 1)):
    # runner 0 stationary; runners 1..n-1 at j*Delta
    return [Fraction(0, 1)] + [j * Delta for j in range(1, n)]


def one_perturbation_speeds(n: int, m: int, eps: Fraction, Delta: Fraction = Fraction(1, 1)):
    v = ap_speeds(n, Delta)
    v[m] += eps
    return v


def circ_dist(x: Fraction, y: Fraction) -> Fraction:
    d = (x - y) % 1
    if d > Fraction(1, 2):
        d = 1 - d
    return d


def is_single_isolated(v, i: int, t: Fraction, n: int) -> bool:
    xi = (v[i] * t) % 1
    th = Fraction(1, n)
    for j in range(len(v)):
        if j == i:
            continue
        xj = (v[j] * t) % 1
        if circ_dist(xi, xj) < th:
            return False
    return True


def ap_witness_times(n: int, Delta: Fraction = Fraction(1, 1)):
    out = []
    for r in range(1, n):
        if math.gcd(r, n) == 1:
            out.append(Fraction(r, n) / Delta)
    return out


def boundary_time(q: int, sign: int, dv: Fraction, n: int) -> Fraction:
    # |dv|*t = q +/- 1/n, q>=0, sign in {+1,-1}
    num = Fraction(q, 1) + Fraction(sign, n)
    if num <= 0:
        return Fraction(-1, 1)
    return num / abs(dv)


def event_sweep_single(v, i: int, n: int, q_max: int = 6):
    # candidate times from pair boundaries for runner i
    cand = set()
    for j in range(len(v)):
        if j == i:
            continue
        dv = v[j] - v[i]
        if dv == 0:
            continue
        for q in range(0, q_max + 1):
            for s in (-1, +1):
                t = boundary_time(q, s, dv, n)
                if t > 0:
                    cand.add(t)
    # test midpoints between sorted boundaries and boundary points themselves
    ts = sorted(cand)
    tests = set(ts)
    for a, b in zip(ts, ts[1:]):
        tests.add((a + b) / 2)
    tests = sorted(x for x in tests if x > 0)

    good = []
    for t in tests:
        if is_single_isolated(v, i, t, n):
            good.append(t)
    return good, ts


def local_shift_estimate(n: int, r: int, Delta: Fraction, eps: Fraction):
    # At AP witness t_r=r/(nDelta), perturbed runner phase shift is eps*t_r.
    t_r = Fraction(r, n) / Delta
    phase_shift = eps * t_r
    # first-order time-shift for boundary branch with neighbor distance ~Delta
    # dt ~ -(r/(nDelta^2))*eps  (for nearest-neighbor branch)
    dt = -Fraction(r, n) * eps / (Delta * Delta)
    return t_r, phase_shift, dt


def run_demo():
    n = 6
    Delta = Fraction(1, 1)
    m = 3
    eps = Fraction(1, 50)  # +0.02 perturbation

    v_ap = ap_speeds(n, Delta)
    v_eps = one_perturbation_speeds(n, m, eps, Delta)

    print(f"n={n}, AP Delta={Delta}, perturbed index m={m}, eps={float(eps):.6f}")
    print("AP witness times (phi(n) times):", [str(t) for t in ap_witness_times(n, Delta)])

    print("\nLocal branch estimates at AP witnesses:")
    for r in range(1, n):
        if math.gcd(r, n) != 1:
            continue
        t_r, dphi, dt = local_shift_estimate(n, r, Delta, eps)
        print(
            f"  r={r}: t_r={t_r}, phase_shift=eps*t_r={float(dphi):.8f}, "
            f"nearest-branch dt~{float(dt):.8f}"
        )

    # Check runner 0 (stationary frame) with boundary/event sweep.
    good, boundaries = event_sweep_single(v_eps, i=0, n=n, q_max=10)
    print("\nEvent sweep for runner 0:")
    print("  boundary_count=", len(boundaries))
    print("  isolated_hits=", len(good))
    print("  first_hits=", [str(t) for t in good[:10]])


if __name__ == "__main__":
    run_demo()
