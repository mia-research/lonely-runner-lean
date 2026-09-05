#!/usr/bin/env python3
"""pi_n_mirror_v1.py -- ITEM 1: the unrun (pi_n) mirror of the lift-geometry programme.

SYNTHESIS_curve_structure_and_new_directions_v1.md Sec 2.4 flags this "unrun and cheap":
every lift law (rhombus, sextant/angle, norm band, Cap Law, sigma, frame operator, C_T) is stated
for (pi_p) only, yet (pi_n) is another ideal of Z[omega] with prime norm.  The named check:

  "theta_n = arg(pi_n) mod 60 against theta_p = 50.55, and whether the pinned-pair <-> Frobenius-angle
   bridge ({1,4} if theta<30 else {0,3}, 0 violations / 69 primes) gives the SAME pinned pair for
   both ideals.  A forced check with a clean falsifier."
  Falsifier (its own priority table): "pinned pair differs => the two ideals are not interchangeable
   and the mirror is a different object".

NOTE (worth recording): eis_n(d) = d mod pi_n IS the GLV decomposition d -> (k1,k2).  The n-side
lift and the GLV lift are the same map.

EXACTNESS.  Norm form N(a+b*omega) = a^2 - a*b + b^2.  Sector areas are exact rationals (the six
sector boundaries are the Eisenstein unit directions = integer rays).  The theta<30 decision is made
by an EXACT integer criterion, never by a float arccos:

  theta = arg(pi), cos(theta) = t/(2*sqrt(M)) with M = N(pi), t = 2*Re(pi).
  theta mod 60 < 30  <=>  theta in [0,30) u [60,90) u [120,150)
      [0,30)   : t > 0 and t^2 > 3M
      [60,90)  : t > 0 and t^2 <= M
      [120,150): t < 0 and M <= t^2 < 3M
  otherwise theta mod 60 >= 30.
"""

from fractions import Fraction as Fr
import sys

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def nrm(v):
    a, b = v
    return a*a - a*b + b*b


def gauss(u, v):
    """Lagrange-Gauss reduction in the Eisenstein norm form (exact integers)."""
    def dot(x, y):            # the bilinear form with dot(v,v) = 2*N(v)
        return 2*x[0]*y[0] - x[0]*y[1] - x[1]*y[0] + 2*x[1]*y[1]
    if nrm(u) > nrm(v):
        u, v = v, u
    while True:
        q = dot(u, v)
        d = dot(u, u)
        m = (2*q + d) // (2*d) if d else 0     # round(q/d), exact
        v = (v[0] - m*u[0], v[1] - m*u[1])
        if nrm(v) >= nrm(u):
            return u, v
        u, v = v, u


def cornacchia_omega(M):
    """a reduced basis of an ideal of norm M: find (a,b) with a^2-ab+b^2 = M via the
       lattice {(x,y) : x + y*r = 0 mod M} for r a cube root of 1 mod M."""
    r = None
    for g in range(2, 200):
        c = pow(g, (M - 1)//3, M)
        if c != 1 and pow(c, 3, M) == 1:
            r = c
            break
    assert r is not None, "no cube root of unity mod M"
    # omega satisfies omega^2 + omega + 1 = 0; pick the root of x^2+x+1 = 0 mod M
    for cand in (r, (r*r) % M):
        if (cand*cand + cand + 1) % M == 0:
            r = cand
            break
    u, v = gauss((M, 0), (-r, 1))
    return u, v


def cross(a, b):
    return a[0]*b[1] - a[1]*b[0]


def clip(poly, d, keep):
    out = []
    L = len(poly)
    for i in range(L):
        a, b = poly[i], poly[(i + 1) % L]
        ca, cb = keep*cross(d, a), keep*cross(d, b)
        if ca >= 0:
            out.append(a)
        if (ca > 0) != (cb > 0) and ca != cb:
            t = Fr(ca, ca - cb)
            out.append((a[0] + t*(b[0] - a[0]), a[1] + t*(b[1] - a[1])))
    return out


def shoelace(poly):
    if len(poly) < 3:
        return Fr(0)
    s = Fr(0)
    for i in range(len(poly)):
        x1, y1 = poly[i]
        x2, y2 = poly[(i + 1) % len(poly)]
        s += x1*y2 - x2*y1
    return abs(s)/2


UNIT = [(1, 0), (1, 1), (0, 1), (-1, 0), (-1, -1), (0, -1)]


def sector_fractions(R1, R2):
    A = (Fr(R1[0] + R2[0], 2), Fr(R1[1] + R2[1], 2))
    B = (Fr(R1[0] - R2[0], 2), Fr(R1[1] - R2[1], 2))
    nA, nB = (-A[0], -A[1]), (-B[0], -B[1])
    V = [A, B, nA, nB] if cross(A, B) > 0 else [A, nB, nA, B]
    tot = shoelace(V)
    out = []
    for s in range(6):
        poly = clip(V, UNIT[s], +1)
        poly = clip(poly, UNIT[(s + 1) % 6], -1)
        out.append(shoelace(poly)/tot)
    return out, tot


def theta_bucket(t, M):
    """exact: True if arg(pi) mod 60 < 30, given t = 2*Re(pi) and M = N(pi)."""
    t2 = t*t
    if t > 0:
        if t2 > 3*M:
            return True         # [0,30)
        if t2 <= M:
            return True         # [60,90)
        return False            # [30,60)
    if t < 0:
        if M <= t2 < 3*M:
            return True         # [120,150)
        return False            # [90,120) or [150,180]
    return False                # t = 0 -> theta = 90 -> mod 60 = 30 -> not < 30


def pinned_from_fracs(fr):
    eighth = Fr(1, 8)
    return [i for i, f in enumerate(fr) if f == eighth]


def report(label, M, t, R1, R2):
    fr, area = sector_fractions(R1, R2)
    pin = pinned_from_fracs(fr)
    lt30 = theta_bucket(t, M)
    pred = [1, 4] if lt30 else [0, 3]
    print("  %-10s N(pi) = %s" % (label, "p" if M == p else ("n" if M == n else str(M))))
    print("     reduced basis R1=%s" % (R1,))
    print("                   R2=%s" % (R2,))
    print("     norms: N(R1)=%s  N(R2)=%s   rhombus (both == N(pi)): %s"
          % ("N(pi)" if nrm(R1) == M else nrm(R1), "N(pi)" if nrm(R2) == M else nrm(R2),
             nrm(R1) == M and nrm(R2) == M))
    print("     parallelogram area = N(pi): %s" % (area == M))
    print("     sector fractions: %s" % [str(f) for f in fr])
    print("     PINNED PAIR (exact 1/8): %s" % pin)
    print("     t = 2Re(pi) = %s%d ; t^2 vs (M, 3M): %s"
          % ("+" if t > 0 else "", t,
             "t^2>3M" if t*t > 3*M else ("t^2<=M" if t*t <= M else "M<t^2<=3M")))
    print("     theta mod 60 < 30 : %s   =>  bridge predicts pinned pair %s   MATCH: %s"
          % (lt30, pred, sorted(pin) == sorted(pred)))
    return pin, pred


if __name__ == "__main__":
    print("=" * 96)
    print("ITEM 1 -- the (pi_n) mirror.  Exact rational areas; exact integer angle criterion.")
    print("=" * 96)
    t_p = p + 1 - n                    # trace of Frobenius of E/F_p
    t_n = n + 1 - p                    # trace of Frobenius of Etilde/F_n  (= 2 - t_p)
    print("  t_p = p+1-n = %d" % t_p)
    print("  t_n = n+1-p = %d   (= 2 - t_p : %s)" % (t_n, t_n == 2 - t_p))
    print("  Hasse |t_p| <= 2*sqrt(p): %s ; |t_n| <= 2*sqrt(n): %s"
          % (t_p*t_p <= 4*p, t_n*t_n <= 4*n))
    print()
    R1p, R2p = cornacchia_omega(p)
    R1n, R2n = cornacchia_omega(n)
    pin_p, pred_p = report("(pi_p)", p, t_p, R1p, R2p)
    print()
    pin_n, pred_n = report("(pi_n)", n, t_n, R1n, R2n)
    print()
    print("  SLIPPAGE  R1_p - R1_n = %s ; R2_p - R2_n = %s"
          % ((R1p[0] - R1n[0], R1p[1] - R1n[1]), (R2p[0] - R2n[0], R2p[1] - R2n[1])))
    print()
    print("  " + "=" * 92)
    print("  VERDICT: pinned pair on (pi_p) = %s ; on (pi_n) = %s  -->  SAME: %s"
          % (pin_p, pin_n, sorted(pin_p) == sorted(pin_n)))
    print("  " + "=" * 92)

    # ---- CONTROL: validate the bridge rule itself on small j=0 primes
    print()
    print("  CONTROL -- does the bridge rule reproduce the measured pinned pair on small primes?")
    ok = bad = 0
    q = 5
    tested = 0
    while tested < 40:
        q += 1
        if q % 3 != 1:
            continue
        if any(q % d == 0 for d in range(2, int(q**0.5) + 1)):   # noqa: float
            continue
        try:
            R1q, R2q = cornacchia_omega(q)
        except AssertionError:
            continue
        a, b = R1q
        tq = 2*a - b                     # t = 2*Re(a + b*omega) = 2a - b
        if tq*tq > 4*q:
            continue
        frq, _ = sector_fractions(R1q, R2q)
        pinq = pinned_from_fracs(frq)
        predq = [1, 4] if theta_bucket(tq, q) else [0, 3]
        if not pinq:
            continue
        tested += 1
        if sorted(pinq) == sorted(predq):
            ok += 1
        else:
            bad += 1
            print("     VIOLATION at q=%d: measured %s, predicted %s (t=%d)" % (q, pinq, predq, tq))
    print("     bridge rule: %d/%d agree, %d violations" % (ok, ok + bad, bad))
