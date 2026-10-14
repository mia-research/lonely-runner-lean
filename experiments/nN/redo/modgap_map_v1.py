"""modgap_map_v1 (2026-10-06): the map from the readings' residues mod q to the subject's gaps at the q-grid instants,
and at the displaced instants, with exact checks.  Owner's idea (2026-10-06): "are we able to find an interaction
between mod speeds, mod gaps?"  Exact (integers and Fractions); helpers in modgap_lib_v1.

Family checked: every 7-subset of [1, 14] (3,432 sets of readings), every modulus q in [1, 28] and every a in [0, 2q]
(instants a/q in [0, 2]).  Readings are differences from a subject of positive speed.

THE MAP (statements; each [P] by the one-line argument given, each checked below):
 M1 [P] position: at a/q reading d sits at x_d = (a*(d mod q) mod q)/q, since a*d/q - a*(d mod q)/q = a*floor(d/q).
 M2 [P] gaps: the right flank gap is min_d x_d, the left flank gap is min_d (1 - x_d) (both 0 if some x_d = 0); by
    Theorem 1 the subject is lonely at a/q iff both are >= 1/8 iff every r_d = a*d mod q has q <= 8 r_d <= 7q.  So the
    two flank gaps at a/q are functions of the residues d mod q and of a.
 M3 [P] D_max at modulus q: d -> d + k*q leaves every position at every a/q unchanged (k whole).
 M4 [P] a non-unit a, h = gcd(a, q) > 1: a*d mod q = h*((a/h)*d mod (q/h)), the instant (a/h)/(q/h).
 M5 [P] displaced: at t = a/q + sigma reading d sits at x_d + d*sigma (mod 1) (Theorem 5's form: vertex + deviation);
    checked at sigma = j/(64q), j in {-7, -1, 1, 5}.
 M6 [P] Theorem 10 is the case q = 8e, a = 8j+1: lonely iff every d*(8j+1) mod 8e lies in [e, 7e].
 M7 [P] cascade coordinates: at R = 8*d_min*a/q, with rho_d = d/d_min, R*rho_d mod 8 = 8*x_d; clear iff in [1, 7].

THE LANDING IN THE MAP (t* = cascade(S), the first lonely instant; [t*, t_R] its lonely component):
 P1 [P] below the landing no residue isolation exists at any modulus: a/q < t* lonely would contradict Theorem 12
    (every lonely instant is at or after every cascade step; t* is the fixed step).
 P2 [P] accounting is an interval: A_seg at a/q iff t* <= a/q <= t_R; A_tri iff t* <= a/q <= t* + min_d
    (7/8 - p_d)/(2d), p_d = frac(d t*); A_uni iff t* <= a/q <= t_uni (concave margin, modgap_lib_v1.uni_end).
    Argument for A_seg: all H means each reading's position stays in [1/8, 7/8] along the segment between a/q and t*
    (linear in time, no lap), so the segment is lonely, and by P1 a/q >= t*; conversely inside the component no
    reading crosses an edge.  A_tri: ||p_d + d u|| - d u >= 1/8 iff 1 - p_d - 2 d u >= 1/8 (the other branch is
    p_d >= 1/8).  Hence the least accounting q is the least denominator in [t*, t_X], and that rational lies on the
    Stern-Brocot path of t* (a convergent or an intermediate fraction of t*, or t* itself).
 P3 [P] the landing as a displaced residue isolation: for every residue isolation a/q in [t*, t_R],
    t* = a/q - min_d (x_d - 1/8)/d, and the readings attaining the minimum are exactly the openers (at 1/8 at t*).
    Going back from a/q every position decreases at its own speed d; the first to reach 1/8 ends the component.
 P4 [P] the opener-closer mediant: let e be an opener (e t* = J + 1/8) and f a closer (f t_R = M + 7/8).  Then
    m = (J + M + 1)/(e + f) lies in [t*, t_R]: (e+f) m = J + M + 1 = (J + 1/8) + (M + 7/8), and
    e m - (J + 1/8) = (M + 7/8) - f m = (e(M + 7/8) - f(J + 1/8))/(e + f) >= 0 since t_R >= t*.  At the modulus e + f
    the opener and the closer are negatives (e = -f mod e+f), so at every (e+f)-grid instant they stand at mirror
    positions; at m their margins (above 1/8 and below 7/8) are equal.  Hence the least denominator q_A in the
    landing component satisfies q_A <= (e + f)/gcd(J + M + 1, e + f) <= 2 d_max.
 P5 [P] finite residue characterisation (from P3 and P4): t* = min of left_end(a/q) over the residue isolations a/q
    with q <= 2 d_max (a/q in (0, 2] here; every left end is a lonely instant, so >= t*, and the landing
    component's own least-denominator rational attains t*).  Integer readings only.
 P6 [P] unit fractions: if t* < 1 and q_min = ceil(1/t_R) satisfies 1/q_min >= t*, then the least denominator in
    the landing component is q_min with a = 1 (any a/q in [t*, t_R] has q >= a/t_R >= 1/t_R).
 P7 [P] descent coordinates at modulus q: t* = (K_q + tau_q)/q, K_q = floor(q t*), tau_q = frac(q t*).  The
    multiples of q (quotients m = d/q) sit at m*tau_q; tau_q > 0 is a lonely instant of the quotients, so
    tau_q >= rho_q, their first lonely instant (cascade).  t*(S) >= t*(multiples of q) = rho_q/q, with equality iff
    S is lonely at rho_q/q (subsets: a lonely instant of S is lonely for every subset).
Every check below is a derivation check: a failure would mean the statement is wrong; failures are listed.
"""
import sys, itertools, math, collections
from fractions import Fraction as F
from math import gcd
sys.path.insert(0, '.')
from modgap_lib_v1 import (cascade, lonely, cd, frac, openers, component, tri_end, uni_end, simplest, cf,
                           stern_brocot_path, positions, residue_gap, is_iso, left_end, classify, descent_coords, E8)

N = 14; QMAX = 28
cnt = collections.Counter(); fails = collections.defaultdict(list)


def check(name, ok, info):
    cnt[(name, ok)] += 1
    if not ok and len(fails[name]) < 5:
        fails[name].append(info)


sets = list(itertools.combinations(range(1, N + 1), 7))
for S in sets:
    dmin = S[0]; dmax = S[-1]
    t = cascade(S); tR, cl = component(S, t); op = openers(S, t)
    ttri = tri_end(S, t, tR); tuni = uni_end(S, t, tR)
    best_left = None
    for q in range(1, QMAX + 1):
        for a in range(0, 2 * q + 1):
            pos = positions(S, a, q)
            # M1
            check('M1 position', all(frac(F(a * d, q)) == F(pos[d], q) == F(a * (d % q) % q, q) for d in S), (S, a, q))
            # M2
            fr = [F(pos[d], q) for d in S]
            gp = min(fr); gm = min((1 - x) if x else F(0) for x in fr)
            if gp == 0: gm = F(0)
            lon = lonely(S, F(a, q))
            check('M2 gaps', lon == (gp >= E8 and gm >= E8) == is_iso(S, a, q) == (residue_gap(S, a, q) >= E8)
                  and residue_gap(S, a, q) == min(gp, gm), (S, a, q))
            # M3
            check('M3 D_max at q', all(frac(F(a * (d + k * q), q)) == F(pos[d], q) for d in S for k in (1, 2)), (S, a, q))
            # M4
            h = gcd(a, q)
            if a and h > 1:
                check('M4 non-unit a', all(a * d % q == h * ((a // h) * d % (q // h)) for d in S), (S, a, q))
            # M5
            for j in (-7, -1, 1, 5):
                sg = F(j, 64 * q); tt = F(a, q) + sg
                if tt <= 0: continue
                check('M5 displaced', all(frac(d * tt) == frac(F(pos[d], q) + d * sg) for d in S), (S, a, q, sg))
            # M7
            if a:
                R = 8 * dmin * F(a, q)
                check('M7 cascade coordinate', all((R * F(d, dmin)) % 8 == 8 * F(pos[d], q) for d in S) and
                      (lon == all(1 <= (R * F(d, dmin)) % 8 <= 7 for d in S)), (S, a, q))
            if a == 0: continue
            s = F(a, q)
            if gcd(a, q) != 1: continue      # each instant once, in lowest terms
            iso = is_iso(S, a, q)
            # P1
            if s < t:
                check('P1 no residue isolation below t*', not iso, (S, a, q, t))
            # P2
            cls, seg, tri, uni = classify(S, a, q, t)
            check('P2 A_seg iff in [t*, t_R]', seg == (t <= s <= tR), (S, a, q, t, tR))
            check('P2 A_tri iff in [t*, t_tri]', tri == (t <= s <= ttri), (S, a, q, t, ttri))
            check('P2 A_uni iff in [t*, t_uni]', uni == (t <= s <= tuni), (S, a, q, t, tuni))
            # P3
            if iso and t <= s <= tR:
                le = left_end(S, a, q)
                arg = sorted(d for d in S if F(pos[d], q) - E8 == (le - s) * -d)
                check('P3 left end = t*, argmin = openers', le == t and arg == sorted(op), (S, a, q, le, arg, op))
            # P5 bookkeeping
            if iso and q <= 2 * dmax:
                le = left_end(S, a, q)
                best_left = le if best_left is None else min(best_left, le)
    # M6 Theorem 10
    for e in S:
        for j in range(e):
            u = 8 * j + 1
            check('M6 Theorem 10', lonely(S, F(u, 8 * e)) == all(e <= d * u % (8 * e) <= 7 * e for d in S), (S, e, j))
    # P4
    qA = simplest(t, tR)
    for e in op:
        J = e * t - E8
        for f in cl:
            M = f * tR - F(7, 8)
            m = F(int(J + M + 1), e + f)
            mm = int(J + M + 1)
            mirror = (frac(e * m) + frac(f * m) == 1) if e != f else (frac(e * m) == F(1, 2))
            ok = (t <= m <= tR and is_iso(S, m.numerator, m.denominator) and mirror
                  and qA.denominator <= m.denominator <= 2 * dmax
                  and e * m - (J + E8) == (M + F(7, 8)) - f * m)
            check('P4 mediant in component, mirror, q_A bound', ok, (S, e, f, m, t, tR))
    # P5
    check('P5 t* = min left end over residue isolations, q <= 2 d_max', best_left == t and tR <= 2, (S, best_left, t))
    # P6
    if t < 1:
        qm = math.ceil(1 / tR)
        if F(1, qm) >= t:
            check('P6 unit fraction', simplest(t, tR) == F(1, qm), (S, t, tR, qm))
    # P2 corollary: least accounting q on the Stern-Brocot path of t*
    path = {F(p, q) for p, q, kind, k in stern_brocot_path(t)}
    for name, end in (('seg', tR), ('tri', ttri), ('uni', tuni)):
        sm = simplest(t, end)
        check('P2 least-q rational on the SB path of t* (%s)' % name, sm in path or sm == t, (S, sm, t))
    # P7
    for q in range(2, N + 1):
        K, tau, rho = descent_coords(S, t, q)
        if rho is None: continue
        check('P7 tau_q >= rho_q and t* >= rho_q/q', tau > 0 and tau >= rho and t >= rho / q and t == (K + tau) / q, (S, q))
        check('P7 t* = rho_q/q iff lonely at rho_q/q', (t == rho / q) == lonely(S, rho / q), (S, q))

out = open('modgap_map_v1.out', 'w'); out.write(__doc__ + "\n")
names = sorted({k for k, _ in cnt})
for nm in names:
    p, f = cnt[(nm, True)], cnt[(nm, False)]
    out.write("%-58s [T %d/%d]%s\n" % (nm, p, p + f, '' if not f else '  FAILURES: %s' % fails[nm]))
out.write("\nsets: %d (every 7-subset of [1, %d]); moduli q <= %d; instants a/q, 0 <= a <= 2q\n" % (len(sets), N, QMAX))
out.close(); print(open('modgap_map_v1.out').read()[len(__doc__):])
