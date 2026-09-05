#!/usr/bin/env python3
"""tors2_involution_test_v1.py -- item 3: the 2-torsion involution test for #26.

RESULT_26_reduction_to_character_sum_v1.md reduced #26 to
    SUM_{t in P^1(F_p)} chi2( g(t)*F(t) ) = 0  exactly, for every R != O,
where E -> E/iota = P^1 is the double cover branched at {P : 2P=R}, iota(P)=R-P,
g = branch quartic (chi2(g(t)) = +1 iff the fibre SPLITS), F(t) = y_{P1}*y_{P2}.

MECHANISM UNDER TEST (the hypothesis banked in that file s4):
exact vanishing points to an ODD SYMMETRY -- an involution sigma of P^1 with
    G(sigma t) = nu * G(t),  chi2(nu) = -1,   G := g*F
so terms pair +1 / -1 and cancel.  Candidates: the E[2]-translations tau_T, which DO descend to
E/iota (tau_T commutes with iota since 2T=O), and which are NOT F_p-rational exactly when n is odd
-- the same condition under which the identity holds at all.

This script does NOT assume the candidate.  It builds the term function
    T(t) = s(t) * chi2(F(t))          s(t)=+1 split, -1 inert
directly (no symbolic g needed: split <-> rational pair, inert <-> conjugate pair) and then
BRUTE-FORCES EVERY involution in PGL_2(F_p), testing T(sigma t) = -T(t) for all t.

Outcomes are pre-committed:
  * an involution found  -> the mechanism is EXHIBITED; #26 reduces to showing it exists in general
  * none found          -> the odd-symmetry hypothesis is REFUTED in this form; the vanishing has
                           some other cause.  A refutation here is a real result, not a failure.
EXACT INTEGER ARITHMETIC ONLY.
"""
import sys
import audit_n1_vsign_v2_core as core
from jclass_e2_relation_probe_v1 import (curve_order_p, dlog_table_p, points_p,
                                         ec_add_p, ec_add_2)

INF = "INF"

def term_function(p, A, B):
    """For each R != O returns dict t -> T(t) in {+1,-1}, over t in P^1(F_p)."""
    n = curve_order_p(p, A, B)
    dl, cyc = dlog_table_p(p, A, B, n)
    if not cyc or n % 2 == 0:
        return None, n, None
    pts = points_p(p, A, B)
    half = (p - 1) // 2
    F2 = core.F2(p)
    # rational points indexed by dlog
    byd = {}
    for (x, y) in pts:
        byd[dl[(x, y)]] = (x, y)
    # all F_{p^2} points, for the conjugate pairs
    sq = {}
    for a in range(p):
        for b in range(p):
            sq[F2.sq((a, b))] = (a, b)
    A2, B2 = (A % p, 0), (B % p, 0)
    conj = {}                                    # trace-dlog -> list of (t, F)
    for a in range(p):
        for b in range(p):
            x = (a, b)
            r = F2.add(F2.add(F2.mul(F2.sq(x), x), F2.mul(A2, x)), B2)
            if r == (0, 0):
                continue
            y = sq.get(r)
            if y is None:
                continue
            for yy in (y, F2.neg(y)):
                P = (x, yy)
                if x[1] == 0 and yy[1] == 0:
                    continue                     # rational point, handled separately
                Pp = (F2.frob(x), F2.frob(yy))
                T = ec_add_2(F2, P, Pp, A2)
                if T is None:
                    continue
                if not (T[0][1] == 0 and T[1][1] == 0):
                    continue
                d = dl[(T[0][0], T[1][0])]
                tt = F2.add(x, F2.frob(x))       # x_P + x_{phi P}  in F_p
                FF = F2.mul(yy, F2.frob(yy))     # N(y_P)          in F_p
                assert tt[1] == 0 and FF[1] == 0
                conj.setdefault(d, []).append((tt[0], FF[0]))
    return (n, dl, byd, conj, half)


def build_terms(p, A, B, e, data):
    n, dl, byd, conj, half = data
    T = {}
    # split fibres: rational pairs {Q, R-Q}
    for d in range(1, n):
        d2 = (e - d) % n
        if d2 == 0:
            continue
        (x1, y1) = byd[d]; (x2, y2) = byd[d2]
        t = (x1 + x2) % p
        Fv = (y1 * y2) % p
        if Fv == 0:
            continue
        T[t] = +1 if pow(Fv, half, p) == 1 else -1
    # inert fibres: conjugate pairs
    for (t, Fv) in conj.get(e, []):
        if Fv == 0:
            continue
        s = 1 if pow(Fv, half, p) == 1 else -1
        T[t] = -s
    return T


def involutions(p):
    """all involutions in PGL_2(F_p): matrices M with M^2 scalar, M not scalar."""
    out = []
    for a in range(p):
        for b in range(p):
            for c in range(p):
                d = (-a) % p                     # trace 0  <=> involution in PGL_2
                if (a * d - b * c) % p == 0:
                    continue
                out.append((a, b, c, d))
    return out


def apply(m, t, p):
    a, b, c, d = m
    if t == INF:
        return INF if c % p == 0 else (a * pow(c, p - 2, p)) % p
    num = (a * t + b) % p; den = (c * t + d) % p
    return INF if den == 0 else num * pow(den, p - 2, p) % p


if __name__ == "__main__":
    for (p, A, B) in ((43, 0, 7), (43, 1, 1), (67, 0, 7)):
        data = term_function(p, A, B)
        if data[0] is None or len(data) == 3:
            print("p=%d (A,B)=(%d,%d): skipped (even n or non-cyclic)" % (p, A, B)); continue
        n = data[0]
        invs = involutions(p)
        print("=" * 74)
        print("p=%d (A,B)=(%d,%d) n=%d  | %d involutions in PGL_2(F_p)" % (p, A, B, n, len(invs)))
        hits_total = 0
        for e in range(1, min(n, 6)):
            T = build_terms(p, A, B, e, data)
            s = sum(T.values())
            found = []
            for m in invs:
                ok = True
                for t, v in T.items():
                    u = apply(m, t, p)
                    if u not in T or T[u] != -v:
                        ok = False; break
                if ok:
                    found.append(m)
                    if len(found) >= 3: break
            hits_total += len(found)
            print("  R=[%d]G | #t=%3d  SUM T(t)=%3d | odd involution sigma: %s"
                  % (e, len(T), s, ("FOUND %s" % (found[:2],)) if found else "NONE"))
        print("  -> %s" % ("MECHANISM EXHIBITED" if hits_total else
                           "no rational odd involution -- hypothesis refuted in this form"))
