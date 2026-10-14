"""modgap_lib_v1 (2026-10-06): exact helpers for the map between the readings' residues mod q ("mod speeds") and the
subject's gaps at the q-grid instants a/q ("mod gaps").  Integers and Fractions only; no float enters any decision or
any recorded number.  Readings are positive whole-number disparities from a subject of positive speed.

Reused unchanged from the record: cascade, lonely, cd, load, full_residual (members_reach_check_v1).

Objects (exact):
  position of reading d at a/q      x_d = (a*d mod q)/q                      (depends on d mod q only)
  residue gap at a/q                g(a/q) = min_d min(r_d, q - r_d)/q,  r_d = a*d mod q
  residue isolation                 every r_d with q <= 8 r_d <= 7q   (the subject is lonely at a/q)
  displacement at t = a/q + sigma   d*sigma; position at t = x_d + d*sigma (mod 1)
  landing component                 [t*, t_R], t* = cascade(S), t_R = least exit (position 7/8) at or after t*
Per-reading classes at a/q, sigma = t* - a/q, y_d = x_d + d*sigma as a rational (no reduction mod 1):
  H  residue-held:  1/8 <= x_d <= 7/8 and 1/8 <= y_d <= 7/8
  Z  residue 0:     q | d (x_d = 0)
  N  near edge:     0 < ||x_d|| < 1/8
  W  wrapped:       1/8 <= x_d <= 7/8 and y_d outside [1/8, 7/8]
Accounting flags at a/q (does the residue map plus the displacement account for every ||d t*|| >= 1/8):
  A_seg  every reading H (the residue clears it and the displacement keeps it inside the arc it starts in)
  A_tri  every reading has ||x_d|| - |d sigma| >= 1/8 (triangle bound, per reading)
  A_uni  g(a/q) - max_d |d sigma| >= 1/8 (the residue gap and the largest displacement alone)
"""
import sys, math, itertools
from fractions import Fraction as F
from math import gcd
from functools import reduce
sys.path.insert(0, '.')
from members_reach_check_v1 import load, full_residual, cascade, lonely, cd

E8 = F(1, 8); E78 = F(7, 8)


def frac(x):
    return x - math.floor(x)


def cascade_path(S):
    """The record's cascade, with its states and setters: [(t0, None), (t1, setter1), ...]."""
    t = F(1, 8 * min(S)); path = [(t, None)]
    while True:
        bl = [d for d in S if cd(d * t) < E8]
        if not bl:
            return path
        t, d = max((F(8 * round(d * t) + 1, 8 * d), d) for d in bl)
        path.append((t, d))


def openers(S, t):
    """Readings standing exactly at 1/8 at t (d*t - 1/8 a whole number)."""
    return [d for d in S if (d * t - E8).denominator == 1]


def component(S, t):
    """For a lonely t: the right end t_R of its lonely component (least instant >= t at which a reading reaches 7/8),
    the closers (readings at 7/8 there) and their lap indices M (f*t_R = M + 7/8)."""
    best = None
    for d in S:
        x = d * t; N = math.ceil(x - E78); e = (N + E78) / d
        if best is None or e < best:
            best = e
    cl = [d for d in S if (d * best - E78).denominator == 1]
    return best, cl


def tri_end(S, t, tR):
    """A_tri holds at s in [t, tR] iff s - t <= min_d (7/8 - p_d)/(2d), p_d = frac(d t)  [derived in modgap_map_v1]."""
    return t + min((E78 - frac(d * t)) / (2 * d) for d in S)


def uni_end(S, t, tR):
    """A_uni holds at s in [t, tR] iff s in [t, t_uni].  h(s) = min_d ||p_d(s)|| - dmax (s - t) is concave on the
    component with h(t) = 1/8; t_uni is the last s with h(s) >= 1/8, computed from the linear pieces exactly."""
    dmax = max(S); P = {d: frac(d * t) for d in S}
    # h(s) >= 1/8 iff for all d: P_d + d u >= 1/8 + dmax u and 1 - P_d - d u >= 1/8 + dmax u, u = s - t >= 0
    lim = tR - t
    for d in S:
        # (P_d - 1/8) >= (dmax - d) u
        if dmax > d:
            lim = min(lim, (P[d] - E8) / (dmax - d))
        elif P[d] < E8:
            return t
        # (7/8 - P_d) >= (dmax + d) u
        lim = min(lim, (E78 - P[d]) / (dmax + d))
    return t + max(lim, F(0))


def simplest(x, y):
    """Least-denominator rational in [x, y], 0 <= x <= y (Stern-Brocot; unique)."""
    n = math.floor(x)
    if n == x:
        return F(n)
    if n + 1 <= y:
        return F(n + 1)
    return n + 1 / simplest(1 / (y - n), 1 / (x - n))


def cf(x):
    a = []; p, q = x.numerator, x.denominator
    while q:
        a.append(p // q); p, q = q, p - (p // q) * q
    return a


def convergents(x):
    """[(p_k, q_k)] for k = 0..n, and the partial quotients."""
    a = cf(x); out = []; pm2, qm2, pm1, qm1 = 0, 1, 1, 0
    for ak in a:
        p, q = ak * pm1 + pm2, ak * qm1 + qm2
        out.append((p, q)); pm2, qm2, pm1, qm1 = pm1, qm1, p, q
    return out, a


def semiconvergent_families(x):
    """Intermediate fractions (the Stern-Brocot path to x): for k >= 0, (p_{k-1} + i p_k)/(q_{k-1} + i q_k),
    0 < i < a_{k+1}.  Yields (k, p_{k-1}, q_{k-1}, p_k, q_k, a_{k+1}); members are generated on demand."""
    conv, a = convergents(x)
    prev = (1, 0)
    for k in range(len(conv) - 1):
        yield (k, prev[0], prev[1], conv[k][0], conv[k][1], a[k + 1])
        prev = conv[k]


def stern_brocot_path(x, cap=None):
    """Every convergent and intermediate fraction of x, in Stern-Brocot order (finite for rational x).  cap bounds
    the number returned per family (for families too large to list)."""
    conv, a = convergents(x)
    out = [(p, q, 'conv', k) for k, (p, q) in enumerate(conv)]
    for (k, pp, qp, pk, qk, ak1) in semiconvergent_families(x):
        n = ak1 - 1
        rng = range(1, ak1) if (cap is None or n <= cap) else itertools.chain(range(1, cap // 2 + 1), range(ak1 - cap // 2, ak1))
        for i in rng:
            out.append((pp + i * pk, qp + i * qk, 'semi', k))
    return out


def positions(S, a, q):
    return {d: a * d % q for d in S}


def residue_gap(S, a, q):
    return F(min(min(r, q - r) for r in (a * d % q for d in S)), q)


def is_iso(S, a, q):
    return all(q <= 8 * (a * d % q) <= 7 * q for d in S)


def left_end(S, a, q):
    """For a residue isolation a/q: the left end of its lonely component, a/q - min_d (x_d - 1/8)/d."""
    return F(a, q) - min((F(a * d % q, q) - E8) / d for d in S)


def classify(S, a, q, t):
    """Per-reading classes and the three accounting flags at a/q for the instant t (from the definitions)."""
    sig = t - F(a, q); cls = {}; tri = True; dmaxs = 0
    for d in S:
        r = a * d % q; x = F(r, q); y = x + d * sig; nx = F(min(r, q - r), q)
        if r == 0:
            c = 'Z'
        elif nx < E8:
            c = 'N'
        elif E8 <= y <= E78:
            c = 'H'
        else:
            c = 'W'
        cls[d] = c
        if nx - abs(d * sig) < E8:
            tri = False
        dmaxs = max(dmaxs, abs(d * sig))
    seg = all(c == 'H' for c in cls.values())
    uni = residue_gap(S, a, q) - dmaxs >= E8
    return cls, seg, tri, uni


def descent_coords(S, t, q):
    """t = (K_q + tau_q)/q with K_q = floor(q t), tau_q = frac(q t); rho_q = cascade of the quotients d/q of the
    multiples of q (None if there are none)."""
    K = math.floor(q * t); tau = q * t - K
    mult = [d // q for d in S if d % q == 0]
    rho = cascade(mult) if mult else None
    return K, tau, rho


def typ8(d):
    return 'm' if d % 8 == 0 else ('o' if d % 2 else ('t' if d % 4 == 2 else 'f'))


if __name__ == '__main__':
    # self-test on hand examples from the record (compilation section 6 worked example; IntegerDisplacementN)
    out = open('modgap_lib_v1.out', 'w'); out.write(__doc__ + "\n")
    S = (1, 2, 3, 4, 5, 7, 8)
    t = cascade(S); path = cascade_path(S); tR, cl = component(S, t)
    lines = ["self-test S = %s (speeds 1,2,3,4,5,6,8,9 for subject speed 1; any subject speed s > 0 gives the same)" % (S,),
             "  cascade path %s" % [(str(a), b) for a, b in path],
             "  t* = %s, openers %s, t_R = %s, closers %s" % (t, openers(S, t), tR, cl),
             "  simplest rational in [t*, t_R] = %s" % simplest(t, tR),
             "  convergents of t*: %s, partial quotients %s" % convergents(t),
             "  Stern-Brocot path of t*: %s" % [("%d/%d" % (p, q), kind) for p, q, kind, k in stern_brocot_path(t)]]
    s = simplest(t, tR); a, q = s.numerator, s.denominator
    cls, seg, tri, uni = classify(S, a, q, t)
    lines.append("  at %d/%d: positions %s, residue gap %s, classes %s, A_seg %s A_tri %s A_uni %s, left end %s" %
                 (a, q, positions(S, a, q), residue_gap(S, a, q), cls, seg, tri, uni, left_end(S, a, q)))
    ok = (t == F(9, 56) and tR == F(7, 40) and s == F(1, 6) and left_end(S, a, q) == t)
    lines.append("  expected t* = 9/56 (compilation section 6), simplest 1/6, left end = t*: %s" % ('PASS' if ok else 'FAIL'))
    out.write("\n".join(lines) + "\n"); out.close(); print("\n".join(lines))
