r"""
rt_char_v1 -- the EXACT character expansion of o, and its exact verification.

o = |{ theta in [0,1) : nu_1,nu_3,nu_5,nu_7 all distinct }|,  nu_rho = a_rho XOR mu_rho,
a_rho(theta) = floor(4 frac(e_rho theta)),  mu = (0,1,2,3) for rho = 1,3,5,7.

V = {0,1,2,3} is the Klein group under XOR; its characters are
        psi_w(v) = (-1)^popcount(w AND v),    w in V.

Putting  f_w(t) := psi_w(floor(4 frac(t)))  (a +-1 step function on the circle),

        o = (1/256) * SUM_{w in V^4} K(w) eps(w) I(w),                       (Thm 1)

        K(w)   = SUM over the 24 bijections v:{1,3,5,7}->V of PROD_rho psi_{w_rho}(v_rho)
        eps(w) = PROD_rho psi_{w_rho}(mu_rho)
        I(w)   = INT_0^1 PROD_rho f_{w_rho}(e_rho theta) d theta .

K and eps are pure finite group data (independent of e).  I(w) is an integral of a step
function and is computed EXACTLY on the breakpoint grid j/(4 e_rho) -- the same grid
ob_fast_v1 uses, so requirement (i) (boundary exactness) holds structurally: the grid is
the full preimage of Z under theta -> 4 e_rho theta, hence no breakpoint lies strictly
inside a cell and entry value = exit value.  audit() re-checks by brute force.

Everything below is exact integer / Fraction arithmetic.
"""
from fractions import Fraction as F
from math import lcm, gcd
from functools import reduce
import itertools

MU = (0, 1, 2, 3)
V = (0, 1, 2, 3)


def psi(w, v):
    return -1 if bin(w & v).count("1") & 1 else 1


# ---------------------------------------------------------------- group data
def K_table():
    """K(w) for all 256 w, as a dict."""
    bij = [p for p in itertools.permutations(V)]
    K = {}
    for w in itertools.product(V, repeat=4):
        s = 0
        for v in bij:
            t = 1
            for wr, vr in zip(w, v):
                t *= psi(wr, vr)
            s += t
        K[w] = s
    return K


def eps(w):
    t = 1
    for wr, mr in zip(w, MU):
        t *= psi(wr, mr)
    return t


# --------------------------------------------------------------- exact I(w)
def grid(speeds):
    f = [4 * e for e in speeds]
    D = reduce(lcm, f)
    pts = set()
    for fi in f:
        pts.update(range(0, D, D // fi))
    p = sorted(pts)
    p.append(D)
    return D, p


def quad_table(speeds):
    """(D, widths, quads) with quads[i] = (a_1,a_3,a_5,a_7) at the ENTRY of cell i."""
    D, p = grid(speeds)
    widths = [p[i + 1] - p[i] for i in range(len(p) - 1)]
    quads = []
    for i in range(len(p) - 1):
        a = p[i]
        quads.append(tuple(((4 * e * a) // D) % 4 for e in speeds))
    return D, widths, quads


def I_all(speeds):
    """exact I(w) for all 256 w."""
    D, widths, quads = quad_table(speeds)
    out = {}
    for w in itertools.product(V, repeat=4):
        tot = 0
        for wt, q in zip(widths, quads):
            t = 1
            for wr, qr in zip(w, q):
                t *= psi(wr, qr)
            tot += t * wt
        out[w] = F(tot, D)
    return out


def o_from_chars(speeds, K=None):
    if K is None:
        K = K_table()
    I = I_all(speeds)
    s = F(0)
    for w in itertools.product(V, repeat=4):
        if K[w]:
            s += K[w] * eps(w) * I[w]
    return s / 256


def o_direct(speeds):
    D, widths, quads = quad_table(speeds)
    tot = 0
    for wt, q in zip(widths, quads):
        if len({qr ^ mr for qr, mr in zip(q, MU)}) == 4:
            tot += wt
    return F(tot, D)


def audit(speeds):
    """requirement (i), brute force: (cells, interior breakpoints, entry != exit)."""
    D, p = grid(speeds)
    n_int = n_mis = 0
    for i in range(len(p) - 1):
        a, b = p[i], p[i + 1]
        for e in speeds:
            f = 4 * e
            lo = (a * f) // D
            hi = (b * f) // D
            for k in range(lo + 1, hi + 1):
                if a * f < k * D < b * f:
                    n_int += 1
            exit_ = hi - (1 if (b * f) % D == 0 else 0)
            if lo != exit_:
                n_mis += 1
    return len(p) - 1, n_int, n_mis


# ------------------------------------------------------------------- report
def support(w):
    return tuple(i for i, x in enumerate(w) if x)


if __name__ == "__main__":
    K = K_table()
    print("=" * 78)
    print("K(w) structure  (K is independent of e)")
    print("=" * 78)
    print(f"  K(0,0,0,0) = {K[(0,0,0,0)]}        -> main term K/256 = {F(K[(0,0,0,0)],256)}")
    bysup = {}
    for w in itertools.product(V, repeat=4):
        bysup.setdefault(len(support(w)), []).append(w)
    for k in sorted(bysup):
        ws = bysup[k]
        nz = [w for w in ws if K[w] != 0]
        print(f"  |supp w| = {k}: {len(ws):3d} vectors, K != 0 for {len(nz):3d}, "
              f"sum|K| = {sum(abs(K[w]) for w in ws):4d}, max|K| = "
              f"{max(abs(K[w]) for w in ws)}")
    print(f"  SUM over all w of |K(w)|          = {sum(abs(v) for v in K.values())}")
    print(f"  SUM over w != 0 of |K(w)|         = {sum(abs(v) for w,v in K.items() if any(w))}")

    # the parity rule:  I(w) = 0 unless #{rho : w_rho in {2,3}} is even
    def parity_ok(w):
        return sum(1 for x in w if x in (2, 3)) % 2 == 0
    live = [w for w in itertools.product(V, repeat=4)
            if K[w] and any(w) and parity_ok(w)]
    print(f"\n  w with K(w) != 0, w != 0, and parity rule satisfied: {len(live)}")
    bys = {}
    for w in live:
        bys.setdefault(len(support(w)), []).append(w)
    for k in sorted(bys):
        print(f"     |supp| = {k}: {len(bys[k]):3d} vectors, sum|K| = "
              f"{sum(abs(K[w]) for w in bys[k])}")

    print()
    print("=" * 78)
    print("EXACT verification of Theorem 1 on real tuples")
    print("=" * 78)
    tests = [(1, 3, 5, 7), (1, 11, 5, 7), (17, 3, 5, 7), (1, 3, 13, 15),
             (9, 27, 5, 23), (9, 3, 5, 7), (25, 11, 13, 39), (41, 43, 13, 15),
             (33, 27, 13, 7), (9, 27, 13, 31)]
    ok = True
    for e in tests:
        oc, od = o_from_chars(e, K), o_direct(e)
        ok &= (oc == od)
        print(f"  {str(e):>18}  o = {str(od):>10} = {float(od):.6f}   "
              f"char-expansion equal: {oc == od}")
    print(f"\n  all exact matches: {ok}")

    print("\n  boundary audit (cells, interior breakpoints, entry != exit):")
    for e in tests[:5]:
        print(f"     {str(e):>18} {audit(e)}")

    # verify I(w) = 0 whenever the parity rule fails, and whenever |supp w| == 1
    print("\n  structural checks on I(w):")
    for e in tests:
        I = I_all(e)
        bad_par = [w for w in I if not parity_ok(w) and I[w] != 0]
        print(f"     {str(e):>18}  I(w) != 0 with odd-count parity broken: {len(bad_par)}")

    # the |supp| = 2 closed-form bound  |I(w)| <= g^2/(e_i e_j)
    print("\n  pair bound  |I(w)| <= gcd(e_i,e_j)^2/(e_i e_j)  on |supp w| = 2:")
    worst = F(0)
    for e in tests:
        I = I_all(e)
        bad = 0
        for w in I:
            S = support(w)
            if len(S) != 2:
                continue
            i, j = S
            g = gcd(e[i], e[j])
            bnd = F(g * g, e[i] * e[j])
            if abs(I[w]) > bnd:
                bad += 1
            if bnd:
                worst = max(worst, abs(I[w]) / bnd)
        print(f"     {str(e):>18}  violations: {bad}")
    print(f"     worst observed ratio |I| / bound = {float(worst):.6f}")
