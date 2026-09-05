#!/usr/bin/env python3
"""pi_n_mirror_v3.py -- ITEM 1 REDONE. v2's "normalization defect" is RETRACTED.

WHAT v2 GOT WRONG (user-identified, and correct).
pi is not merely a generator of an ideal -- it is the FROBENIUS ENDOMORPHISM.  It obeys
    pi + conj(pi) = 2*Re(pi) = t = p + 1 - #E(F_p).
The six associates u*pi have six DIFFERENT traces, so you may NOT multiply by a unit: doing so
changes Re(pi), changes t, and the result no longer represents the curve.  v2's "canonical
normalization" arg(pi) in [0,60) did exactly that -- it forced every prime into one wedge, which is
why the pinned pair came out constant [1,4].  v2 manufactured the flatland and then blamed the rule.

Also: v2's own output string said "(matches curve trace)" next to a number that does NOT match
t_p.  A verification claim was printed without the verification being performed.

AND the record was not using an undocumented convention.  Its hardcoded
    aP = 367917413016453100223835821029139468249
    bP = 303414439467246543595250775667605759171
satisfies 2*aP - bP = 432420386565659656852420866390673177327 = t_p EXACTLY.  It is the
trace-pinned Frobenius.  The "defect" reported in RESULT_pi_n_mirror_item1_v1.md Sec 2-4 is withdrawn.

THE CORRECT CONSTRUCTION (exact, closed form).
Given M = N(pi) and trace t with disc t^2 - 4M = -3k^2:
    b = k,   a = (t + k)/2,     since 2a - b = t and a^2 - ab + b^2 = M.
The conjugate is (a - b, -b) = ((t - k)/2, -k).  Only these two are Frobenius; the other four
associates are not.

ITEM 1, properly: pinned pair of the FROBENIUS of E/F_p (trace t_p = p+1-n) versus the FROBENIUS of
Etilde/F_n (trace t_n = n+1-p).  Falsifier: pinned pairs differ => the two are not interchangeable.
"""

from fractions import Fraction as Fr

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141


def isqrt(x):
    if x < 0:
        return None
    lo, hi = 0, x
    while lo < hi:
        mid = (lo + hi + 1)//2
        if mid*mid <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo


def nrm(v):
    a, b = v
    return a*a - a*b + b*b


def frobenius(M, t):
    """the Frobenius element (a,b) = ((t+k)/2, k) with N = M and 2Re = t.  Exact; None if no j=0 CM."""
    D = 4*M - t*t
    if D <= 0 or D % 3:
        return None
    k = isqrt(D//3)
    if k is None or 3*k*k != D:
        return None
    if (t + k) % 2:
        k = -k
        if (t + k) % 2:
            return None
    a = (t + k)//2
    v = (a, k)
    if nrm(v) != M or 2*v[0] - v[1] != t:
        return None
    return v


def mul_omega(v):
    a, b = v
    return (-b, a - b)


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
            tt = Fr(ca, ca - cb)
            out.append((a[0] + tt*(b[0] - a[0]), a[1] + tt*(b[1] - a[1])))
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
    return [shoelace(clip(clip(V, UNIT[s], +1), UNIT[(s + 1) % 6], -1))/tot for s in range(6)], tot


def pinned(fr):
    return [i for i, f in enumerate(fr) if f == Fr(1, 8)]


def theta_lt30(M, t):
    """EXACT: theta = arccos(t/(2 sqrt M)) in [0,180]; theta < 30 <=> t > 0 and t^2 > 3M."""
    return t > 0 and t*t > 3*M


def show(label, M, t):
    pi = frobenius(M, t)
    if pi is None:
        print("  %-8s no Frobenius element (not j=0 CM)" % label)
        return None, None
    fr, area = sector_fractions(pi)
    pin = pinned(fr)
    pred = [1, 4] if theta_lt30(M, t) else [0, 3]
    print("  %-8s pi = (%d, %d)" % (label, pi[0], pi[1]))
    print("           N(pi) == M: %s | 2Re(pi) == t: %s | area == M: %s"
          % (nrm(pi) == M, 2*pi[0] - pi[1] == t, area == M))
    print("           sector fractions:")
    for i, f in enumerate(fr):
        print("             c%d = %-14s%s" % (i, (str(f) if f.denominator < 10**6
                                                  else "%.9f" % float(f)),          # noqa: float
                                              "  <== PINNED 1/8" if f == Fr(1, 8) else ""))
    print("           PINNED PAIR = %s | theta<30 (t>0 and t^2>3M): %s -> bridge predicts %s"
          " | MATCH: %s" % (pin, theta_lt30(M, t), pred, sorted(pin) == sorted(pred)))
    return pin, pred


if __name__ == "__main__":
    print("=" * 92)
    print("ITEM 1 REDONE -- Frobenius pinned by the trace (v2's 'defect' RETRACTED)")
    print("=" * 92)
    t_p, t_n = p + 1 - n, n + 1 - p
    print("  t_p = p+1-n = %d" % t_p)
    print("  t_n = n+1-p = %d" % t_n)
    print()
    print("  cross-check vs the record's hardcoded aP,bP in eisenstein_lift_sextant_exact_v1.py:")
    aP = 367917413016453100223835821029139468249
    bP = 303414439467246543595250775667605759171
    print("     2*aP - bP == t_p : %s   (so the record's pi IS the trace-pinned Frobenius)"
          % (2*aP - bP == t_p))
    print("     my frobenius(p, t_p) == (aP, bP) : %s" % (frobenius(p, t_p) == (aP, bP)))
    print()
    a1, b1 = show("(pi_p)", p, t_p)
    print()
    a2, b2 = show("(pi_n)", n, t_n)
    print()
    print("  " + "=" * 88)
    print("  ITEM 1 VERDICT: pinned pair (pi_p) = %s ; (pi_n) = %s ;  SAME: %s"
          % (a1, a2, (a1 is not None and a2 is not None and sorted(a1) == sorted(a2))))
    print("  " + "=" * 88)

    print()
    print("  CONTROL -- the bridge rule on real j=0 curves (trace-pinned Frobenius):")
    ok = bad = 0
    viol = []
    q = 5
    while ok + bad < 69:
        q += 1
        if q % 3 != 1 or any(q % d == 0 for d in range(2, isqrt(q) + 1)):
            continue
        # every trace t with t^2-4q = -3k^2 corresponds to a j=0 curve over F_q
        for t in range(-2*isqrt(q) - 2, 2*isqrt(q) + 3):
            if ok + bad >= 69:
                break
            pi = frobenius(q, t)
            if pi is None:
                continue
            fr, _ = sector_fractions(pi)
            pn = pinned(fr)
            if not pn:
                continue
            pr = [1, 4] if theta_lt30(q, t) else [0, 3]
            if sorted(pn) == sorted(pr):
                ok += 1
            else:
                bad += 1
                viol.append((q, t, pn, pr))
    print("     %d/%d agree, %d violations" % (ok, ok + bad, bad))
    for (q, t, pn, pr) in viol[:10]:
        print("       q=%d t=%d measured %s predicted %s" % (q, t, pn, pr))
