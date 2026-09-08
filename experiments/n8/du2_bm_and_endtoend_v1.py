r"""
du2_bm_and_endtoend_v1  --  two checks for the n=8 DROPPED-UNIT leaf.

PART A.  B_m two ways, and the integer-endpoint (integrality) claim.
   B_m := { x in [0,1) : floor(8m x) mod 8 in {0,7} }   [the floor form actually used]
   is shown equal, as a set of half-open intervals, to
        union_j [ j/m - 1/(8m),  j/m + 1/(8m) )   (indices mod 1)
   with exact measure 1/4, and all endpoints integral in b-coordinates (b = Lx).

PART B.  End-to-end witness check, pure integer arithmetic.
   For E = E_non u {8m1, 8m2}, L = lcm(E), N = 8L: locate b in
   S \ (B_m1 u B_m2) by EXACT interval algebra (never by search), then confirm
   for the smallest uncovered r that k = b + r*L satisfies
        e*k mod 8L  in  [L, 7L]      for every e in E
   which is the loneliness condition ||e k / N|| >= 1/8.
   The search over b is NOT used to find the witness; it is only used as a control
   that the predicted b is in fact safe.

Exact integers / Fractions only.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd

Z8 = frozenset(range(8))
UNITS = frozenset({1, 3, 5, 7})


def bad(e, t):
    return frozenset(r for r in range(8) if (e * r + t) % 8 in (0, 7))


# ---------------------------------------------------------------- PART A
def Bm_floor_form(m):
    """B_m from the floor definition, as a sorted list of disjoint [lo,hi) in [0,1).
    Breakpoints of floor(8m x) are j/(8m); on each cell the floor is constant."""
    out = []
    for j in range(8 * m):
        a, b = F(j, 8 * m), F(j + 1, 8 * m)
        # entry and exit floors (never a midpoint)
        fe = (8 * m * a).numerator // (8 * m * a).denominator
        v = 8 * m * b
        fx = v.numerator // v.denominator - (1 if v.denominator == 1 else 0)
        assert fe == fx == j, (m, j, fe, fx)
        if j % 8 in (0, 7):
            out.append((a, b))
    return merge(out)


def Bm_closed_form(m):
    """union_j [ j/m - 1/(8m), j/m + 1/(8m) ) intersected with [0,1), wrapped."""
    out = []
    for j in range(m + 1):
        lo, hi = F(j, m) - F(1, 8 * m), F(j, m) + F(1, 8 * m)
        for a, b in [(lo, hi)]:
            for aa, bb in [(a, b), (a + 1, b + 1), (a - 1, b - 1)]:
                x, y = max(aa, F(0)), min(bb, F(1))
                if x < y:
                    out.append((x, y))
    return merge(out)


def merge(iv):
    iv = sorted(iv)
    out = []
    for a, b in iv:
        if out and a <= out[-1][1]:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def meas(iv):
    return sum((b - a for a, b in iv), F(0))


def complement(iv):
    out, cur = [], F(0)
    for a, b in iv:
        if cur < a:
            out.append((cur, a))
        cur = max(cur, b)
    if cur < 1:
        out.append((cur, F(1)))
    return out


def inter(A, B):
    out = []
    i = j = 0
    while i < len(A) and j < len(B):
        lo, hi = max(A[i][0], B[j][0]), min(A[i][1], B[j][1])
        if lo < hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return out


def partA():
    print("PART A -- B_m, floor form vs closed form, m = 1..20")
    ok = True
    for m in range(1, 21):
        f, c = Bm_floor_form(m), Bm_closed_form(m)
        same = (f == c)
        mm = meas(f)
        ok &= same and mm == F(1, 4)
        print(f"  m={m:>3}  identical={same}   |B_m|={mm}   #components={len(f)}"
              f"   comp lengths {sorted({b-a for a,b in f})}")
    print(f"  ALL: floor form == closed form and |B_m| = 1/4 exactly : {ok}\n")
    return ok


# ---------------------------------------------------------------- PART B
def safe_intervals(Enon):
    """Exact S = {x : union bad(e, floor(e x)) != Z/8} with the uncovered set per cell."""
    pts = {F(0), F(1)}
    for e in Enon:
        for j in range(1, e):
            pts.add(F(j, e))
    p = sorted(pts)
    out = []
    for a, b in zip(p, p[1:]):
        cov = set()
        for e in Enon:
            v = e * a
            cov |= bad(e, v.numerator // v.denominator)
        U = Z8 - cov
        if U:
            out.append((a, b, frozenset(U)))
    return out


def lcm(vals):
    L = 1
    for v in vals:
        L = L * v // gcd(L, v)
    return L


def witness(Enon, m1, m2):
    r"""Return (E, L, b, r, U) with b an integer in S minus (B_m1 u B_m2), or None."""
    E = sorted(Enon) + [8 * m1, 8 * m2]
    L = lcm(E)
    B = merge(Bm_floor_form(m1) + Bm_floor_form(m2))
    good = complement(B)                       # [0,1) minus B, half-open, integral ends
    for a, b, U in safe_intervals(Enon):
        for lo, hi in inter([(a, b)], good):
            blo = lo * L
            assert blo.denominator == 1, (Enon, m1, m2, lo, L)   # integrality
            bb = blo.numerator
            if F(bb, L) < hi:
                return E, L, bb, min(U), U
    return None


def check(E, L, b, r):
    """Pure integer: k = b + rL is a witness iff e*k mod 8L in [L, 7L] for all e."""
    N = 8 * L
    k = b + r * L
    slack = []
    for e in E:
        v = (e * k) % N
        if not (L <= v <= 7 * L):
            return False, e, v, None
        slack.append(min(v, N - v))
    return True, None, None, min(slack)


def partB(MMAX=14):
    print(f"PART B -- end-to-end, all 18 absent pairs x all 1 <= m1 < m2 <= {MMAX}")
    pairs = [A for A in combinations(range(1, 8), 2) if set(A) & UNITS]
    ntup = 0
    fails = []
    worst_slack = None
    for A in pairs:
        Enon = sorted(set(range(1, 8)) - set(A))
        for m1 in range(1, MMAX + 1):
            for m2 in range(m1 + 1, MMAX + 1):
                W = witness(Enon, m1, m2)
                ntup += 1
                if W is None:
                    fails.append((A, m1, m2, "no safe b"))
                    continue
                E, L, b, r, U = W
                assert len(set(E)) == 7, E
                ok, e_bad, v, sl = check(E, L, b, r)
                if not ok:
                    fails.append((A, m1, m2, f"runner {e_bad} at k, e*k mod 8L = {v}"))
                    continue
                if worst_slack is None or F(sl, 8 * L) < worst_slack[0]:
                    worst_slack = (F(sl, 8 * L), E, L, b, r)
    print(f"  tuples tested: {ntup}   failures: {len(fails)}")
    for f in fails[:20]:
        print("    FAIL", f)
    q, E, L, b, r = worst_slack
    print(f"  minimum over all tuples of min_e ||e k / 8L||  =  {q} = {float(q):.6f}"
          f"   (must be >= 1/8 = 0.125)")
    print(f"     attained at E = {E}, L = {L}, b = {b}, r = {r}, k = {b + r*L}")
    return len(fails) == 0


if __name__ == "__main__":
    a = partA()
    b = partB()
    print(f"\nPART A pass: {a}\nPART B pass: {b}")
