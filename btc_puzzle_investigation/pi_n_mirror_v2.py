#!/usr/bin/env python3
"""pi_n_mirror_v2.py -- ITEM 1, with the normalization the bridge rule needs.

v1 FOUND A GAP IN THE RECORD'S OWN STATEMENT.  The "pinned pair <-> Frobenius angle" bridge
({1,4} if theta<30 else {0,3}, "0 violations / 69 primes") is stated with no basis normalization.
But a reduced basis of an ideal (pi) is defined only up to the SIX Eisenstein units, and multiplying
pi by a unit rotates the fundamental parallelogram by 60 degrees, which CYCLICALLY PERMUTES the
pinned pair {0,3} -> {1,4} -> {2,5} -> {0,3}.  So "the pinned pair" is not a property of the ideal
until a generator is fixed.  With an arbitrary Cornacchia output v1 measured [2,5] for (pi_p) where
the record says [0,3], and the bridge rule scored 19/40.

THE FIX (canonical, exact).  Every ideal of Z[omega] with norm M has EXACTLY ONE generator
pi = a + b*omega with arg(pi) in [0, 60) -- in (a,b) coordinates: b >= 0 and a > b.  Normalise to it,
then build the rhombus deterministically as R1 = pi, R2 = pi*omega  (omega: (a,b) -> (-b, a-b)).
Sector fractions are then a function of the ideal alone, and theta = arg(pi) in [0,60) needs no
"mod 60" at all.

Then ITEM 1's actual question: does the pinned pair on (pi_n) equal the pinned pair on (pi_p)?
Falsifier (the record's own): "pinned pair differs => the two ideals are not interchangeable and the
mirror is a different object".
"""

from fractions import Fraction as Fr

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def nrm(v):
    a, b = v
    return a*a - a*b + b*b


def mul_omega(v):
    a, b = v
    return (-b, a - b)


def normalize(v):
    """the unique associate with arg in [0,60): b >= 0 and a > b."""
    cands = []
    w = v
    for _ in range(3):
        cands.append(w)
        cands.append((-w[0], -w[1]))
        w = mul_omega(w)
    for c in cands:
        a, b = c
        if b >= 0 and a > b:
            return c
    raise RuntimeError("no canonical associate for %s" % (v,))


def gauss(u, v):
    def dot(x, y):
        return 2*x[0]*y[0] - x[0]*y[1] - x[1]*y[0] + 2*x[1]*y[1]
    if nrm(u) > nrm(v):
        u, v = v, u
    while True:
        q, d = dot(u, v), dot(u, u)
        m = (2*q + d)//(2*d) if d else 0
        v = (v[0] - m*u[0], v[1] - m*u[1])
        if nrm(v) >= nrm(u):
            return u, v
        u, v = v, u


def pi_of(M):
    """the canonical generator of an ideal of norm M (M prime, M = 1 mod 3)."""
    r = None
    for g in range(2, 500):
        c = pow(g, (M - 1)//3, M)
        if c != 1 and pow(c, 3, M) == 1 and (c*c + c + 1) % M == 0:
            r = c
            break
    if r is None:
        return None
    u, v = gauss((M, 0), (-r, 1))
    w = u if nrm(u) == M else (v if nrm(v) == M else None)
    return normalize(w) if w else None


def cross(a, b):
    return a[0]*b[1] - a[1]*b[0]


def clip(poly, d, keep):
    out, L = [], len(poly)
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


def sector_fractions(pi):
    R1, R2 = pi, mul_omega(pi)
    A = (Fr(R1[0] + R2[0], 2), Fr(R1[1] + R2[1], 2))
    B = (Fr(R1[0] - R2[0], 2), Fr(R1[1] - R2[1], 2))
    nA, nB = (-A[0], -A[1]), (-B[0], -B[1])
    V = [A, B, nA, nB] if cross(A, B) > 0 else [A, nB, nA, B]
    tot = shoelace(V)
    return [shoelace(clip(clip(V, UNIT[s], +1), UNIT[(s + 1) % 6], -1))/tot
            for s in range(6)], tot


def pinned(fr):
    return [i for i, f in enumerate(fr) if f == Fr(1, 8)]


def theta_lt30(pi):
    """arg(pi) in [0,60) already; arg < 30 <=> exact integer test.
       pi = a + b*omega -> cartesian (a - b/2, b*sqrt3/2); arg<30 <=> y/x < tan30 = 1/sqrt3
       <=> (b*sqrt3/2) * sqrt3 < (a - b/2)  <=> 3b/2 < a - b/2 <=> 2b < a."""
    a, b = pi
    return 2*b < a


def show(label, M, pi):
    fr, area = sector_fractions(pi)
    pin = pinned(fr)
    a, b = pi
    t = 2*a - b
    pred = [1, 4] if theta_lt30(pi) else [0, 3]
    print("  %-8s pi = (%d, %d)   N(pi) = %s   area == N(pi): %s"
          % (label, a, b, "M ok" if nrm(pi) == M else "*** %d ***" % nrm(pi), area == M))
    print("           t = 2Re(pi) = 2a-b = %d   (matches curve trace: see main)" % t)
    print("           sector fractions (exact):")
    for i, f in enumerate(fr):
        mark = "   <== PINNED 1/8" if f == Fr(1, 8) else ""
        print("             c%d = %s%s" % (i, f if f.denominator < 10**6 else
                                           "%.9f" % float(f), mark))   # noqa: float
    print("           PINNED PAIR = %s | arg<30: %s -> bridge predicts %s | MATCH: %s"
          % (pin, theta_lt30(pi), pred, sorted(pin) == sorted(pred)))
    return pin, pred


if __name__ == "__main__":
    print("=" * 92)
    print("ITEM 1 -- the (pi_n) mirror, with canonical normalization arg(pi) in [0,60)")
    print("=" * 92)
    t_p, t_n = p + 1 - n, n + 1 - p
    print("  curve traces: t_p = p+1-n = %d" % t_p)
    print("                t_n = n+1-p = %d" % t_n)
    print()
    pip, pin_ = pi_of(p), pi_of(n)
    a1, b1 = show("(pi_p)", p, pip)
    print()
    a2, b2 = show("(pi_n)", n, pin_)
    print()
    print("  " + "=" * 88)
    print("  ITEM 1 VERDICT: pinned pair (pi_p) = %s ; (pi_n) = %s ;  SAME: %s"
          % (a1, a2, sorted(a1) == sorted(a2)))
    print("  " + "=" * 88)

    print()
    print("  CONTROL -- bridge rule under the canonical normalization, small j=0 primes:")
    ok = bad = 0
    viol = []
    q = 5
    while ok + bad < 60:
        q += 1
        if q % 3 != 1 or any(q % d == 0 for d in range(2, int(q**0.5) + 1)):   # noqa: float
            continue
        pq = pi_of(q)
        if pq is None:
            continue
        fr, _ = sector_fractions(pq)
        pn = pinned(fr)
        if not pn:
            continue
        pr = [1, 4] if theta_lt30(pq) else [0, 3]
        if sorted(pn) == sorted(pr):
            ok += 1
        else:
            bad += 1
            viol.append((q, pn, pr))
    print("     %d/%d agree, %d violations" % (ok, ok + bad, bad))
    for (q, pn, pr) in viol[:8]:
        print("       q=%d measured %s predicted %s" % (q, pn, pr))
