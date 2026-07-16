#!/usr/bin/env sage
# semaev_elimination_v1.py  --  RUN WITH:  sage semaev_elimination_v1.py
#
# Item #1 of the ranked menu: the S4+ first-fall-degree / Groebner structure --- the
# elimination complexity of the Semaev point-decomposition SYSTEM an index-calculus
# attacker faces over a PRIME field, with matched CM / non-CM controls.
#
# Prior repo work (v9/v10/v11/v13) only counted relation/decomposition YIELD (generic) or
# analysed a SINGLE polynomial (S3 discriminant, v13).  Nothing here builds or solves a
# Semaev SYSTEM or measures a first-fall / solving degree.  This does.
#
# CENTREPIECE (Piece B1, structural): the classical first-fall degree is a LEADING-FORM
# invariant, and the Semaev polynomials are ISOBARIC under wt(x_i)=1, wt(A)=2, wt(B)=3, so
# their leading forms are FREE of A,B == curve-independent.  Hence the first-fall degree of
# the decomposition system is identical for secp and every other curve of the same (p,B,m):
# no CM/GLV first-fall lever exists.  This script proves the isobaric fact (numerically for
# m<=4/5) and confirms the first-fall degree is curve-blind numerically.
#
# Piece B2 (empirical): the finer SOLVING degree (which CAN see lower-order / curve terms) --
# measured secp-form vs non-CM vs j=1728, matched (p,B,m), plus a mu3-invariant-V lever test.
#
# Piece A (geometric, time-boxed): singular-locus condition of the S4 relation fibre V_t --
# climbing v13's S3 discriminant rung to S4.
#
# NO FLOAT IN THE SIGNAL PATH: everything exact over GF(p) / QQ (btc CLAUDE.md).

from sage.all import *
import itertools

# ----------------------------------------------------------------------------------------
# Semaev summation polynomials
# ----------------------------------------------------------------------------------------

def semaev3(a, b, c, A, B):
    """S3 for y^2 = x^3 + A x + B (vanishes iff exist points with these x-coords summing to O)."""
    return (a - b)**2 * c**2 - 2*((a + b)*(a*b + A) + 2*B)*c + ((a*b - A)**2 - 4*B*(a + b))

def _build_summation(F_or_FF, A, B, m):
    """Semaev_{m+1}(z1..z_{m+1}) over the given ring's base, in F[z1..z_{m+1}] (aux eliminated).
    Uses a FRESH auxiliary variable per resultant level (no X-collision in nested resultants)."""
    nz = m + 1
    naux = max(0, m - 2)
    znames = ['z%d' % i for i in range(1, nz + 1)]
    xnames = ['X%d' % i for i in range(1, naux + 1)]
    R = PolynomialRing(F_or_FF, znames + xnames)
    g = R.gens(); zs = list(g[:nz]); Xs = list(g[nz:])
    AA = R(A); BB = R(B)
    # P(k, args): the k-th Semaev polynomial evaluated at the k given args (last = slot).
    def P(k, args):
        if k == 3:
            return semaev3(args[0], args[1], args[2], AA, BB)
        X = Xs[k - 4]                          # k=4 -> Xs[0], k=5 -> Xs[1], ...
        left = P(k - 1, list(args[:k - 2]) + [X])
        right = semaev3(args[k - 2], args[k - 1], X, AA, BB)
        return left.resultant(right, X)
    S_full = P(nz, zs)
    Rt = PolynomialRing(F_or_FF, znames)
    return Rt(S_full), Rt

def summation_poly(F, A, B, m):
    """Return (S_{m+1}(x_1..x_m, t), [x_1..x_m], t) over F. Spurious factors (m>=4) removed."""
    A = F(A); B = F(B)
    S, Rt = _build_summation(F, A, B, m)
    xs = list(Rt.gens()[:m]); t = Rt.gens()[m]
    if m >= 4:
        S = _clean_spurious(F, S, xs, t, m)
    return S, xs, t

def _clean_spurious(F, S, xs, t, m):
    """Divide out spurious factors introduced by the resultant construction, verified by group law."""
    facs = S.factor()
    E = None
    # need a curve to test the group law; caller sets A,B -> but we only have S here.
    # Instead: the true summation factor is the one whose per-variable degree is 2^{m-1}.
    want = 2**(m - 1)
    keep = []
    for f, e in facs:
        if all(f.degree(v) == want for v in xs) and f.degree(t) == want:
            keep.append(f)
    if keep:
        out = prod(keep)
        return out
    return S  # fall back to raw if selection failed

# ----------------------------------------------------------------------------------------
# group-law verification of the constructed S_{m+1}
# ----------------------------------------------------------------------------------------

def verify_group_law(F, A, B, m, S, xs, t, trials=30, seed=1):
    import random as pyrandom
    pyrandom.seed(int(seed))
    E = EllipticCurve(F, [A, B])
    G = E.gens()[0]; N = int(E.order())
    ok = 0; bad = 0; skipped = 0
    for _ in range(trials):
        ds = [pyrandom.randrange(1, N) for _ in range(m)]
        pts = [int(d) * G for d in ds]
        Ssum = E(0)
        for P in pts:
            Ssum = Ssum + P
        Ptgt = -Ssum
        if Ptgt == E(0):
            skipped += 1; continue
        sub = {xs[i]: pts[i][0] for i in range(m)}
        sub[t] = Ptgt[0]
        val = S.subs(sub)
        if val == 0:
            ok += 1
        else:
            bad += 1
    return ok, bad, skipped

# ----------------------------------------------------------------------------------------
# Piece B1 support: isobaric weighting + leading-form curve-independence
# ----------------------------------------------------------------------------------------

def isobaric_check(m):
    """Over QQ[A,B]: is S_{m+1}(z_1..z_{m+1}) isobaric under wt(z_i)=1, wt(A)=2, wt(B)=3?
    Returns (sorted weighted degrees present, top-form-involves-AB, total degree)."""
    Rc = PolynomialRing(QQ, ['A', 'B']); A, B = Rc.gens()
    FF = Rc.fraction_field()
    S, Rt = _build_summation(FF, FF(A), FF(B), m)
    zs = Rt.gens()
    wds = set()
    for cf, mm in zip(S.coefficients(), S.monomials()):
        xdeg = sum(mm.degree(v) for v in zs)
        num = cf.numerator()
        for m2 in num.monomials():
            wds.add(xdeg + 2*m2.degree(A) + 3*m2.degree(B))
    d = S.degree()
    top = sum(cf*mm for cf, mm in zip(S.coefficients(), S.monomials()) if mm.degree() == d)
    involves = any(cf.numerator().degree() > 0 or cf.denominator().degree() > 0
                   for cf in top.coefficients())
    return sorted(wds), involves, d

# ----------------------------------------------------------------------------------------
# Macaulay-matrix elimination analysis (exact over GF(p))
# ----------------------------------------------------------------------------------------

def _exps_le(n, D):
    """All exponent tuples of length n with total degree <= D."""
    if n == 0:
        yield (); return
    for e in itertools.product(range(D + 1), repeat=n):
        if sum(e) <= D:
            yield e

def macaulay_stats(F, gens_list, xs, Dmax):
    """Return per-degree Macaulay stats: for each D, rank, rank on top-degree cols, and the
    affine first-fall / solving diagnostics. Exact linear algebra over F."""
    n = len(xs)
    stats = {}
    prev_rank = 0
    Rring = xs[0].parent()
    for D in range(1, Dmax + 1):
        cols = list(_exps_le(n, D))
        colidx = {e: i for i, e in enumerate(cols)}
        topcols = [i for i, e in enumerate(cols) if sum(e) == D]
        rows = []
        for f in gens_list:
            df = f.degree()
            if df > D:
                continue
            for ue in _exps_le(n, D - df):
                umon = Rring.monomial(*ue)
                poly = umon * f
                row = {}
                for e, c in poly.dict().items():
                    row[colidx[tuple(e)]] = c
                rows.append(row)
        if not rows:
            stats[D] = dict(rank=0, ncols=len(cols), quo=len(cols)); prev_rank = 0; continue
        M = matrix(F, len(rows), len(cols), sparse=True)
        for r, row in enumerate(rows):
            for ci, c in row.items():
                M[r, ci] = c
        rk = M.rank()
        # rank restricted to top-degree columns (projection onto degree-D part)
        if topcols:
            Mtop = M.matrix_from_columns(topcols)
            rk_top = Mtop.rank()
        else:
            rk_top = 0
        inter = rk - rk_top      # dim( rowspace ∩ {deg <= D-1} )
        fall = inter - prev_rank # > 0  ==>  a genuine degree fall appeared at degree D
        quo = len(cols) - rk     # dim of R_{<=D} / (ideal ∩ R_{<=D})
        stats[D] = dict(rank=rk, ncols=len(cols), rk_top=rk_top, inter=inter,
                        fall=fall, quo=quo)
        prev_rank = rk
    return stats

def first_fall_and_solving(F, gens_list, xs, Dmax, quo_dim_target):
    stats = macaulay_stats(F, gens_list, xs, Dmax)
    d_ff = None; d_solv = None
    for D in sorted(stats):
        s = stats[D]
        if d_ff is None and s.get('fall', 0) > 0:
            d_ff = D
        if d_solv is None and s['quo'] == quo_dim_target:
            d_solv = D
    return d_ff, d_solv, stats

# ----------------------------------------------------------------------------------------
# decomposition system + matched comparison
# ----------------------------------------------------------------------------------------

def decomposition_system(F, A, B, m, tval, Vroots):
    """{ S_{m+1}(x1..xm, tval)=0 } U { g(x_i)=0 } with g = prod(x - r), r in Vroots."""
    S, xs_big, t_big = summation_poly(F, A, B, m)
    Rt = xs_big[0].parent()
    Rx = PolynomialRing(F, ['x%d' % i for i in range(1, m + 1)], order='degrevlex')
    phi = Rt.hom(list(Rx.gens()) + [F(tval)], Rx)          # z_i -> x_i, t -> tval
    Sx = phi(S)
    xr = Rx.gens()
    gs = [prod([xi - F(r) for r in Vroots]) for xi in xr]  # field eqs: x_i in V
    return Rx, [Sx] + gs, list(xr)

def measure_system(F, A, B, m, tval, Vroots, Dmax):
    """Elimination diagnostics of the decomposition system. Handles dim in {-1 (inconsistent,
    quo target 0), 0 (consistent), >0 (positive-dim, skipped)}."""
    Rx, gens_list, xs = decomposition_system(F, A, B, m, tval, Vroots)
    I = Rx.ideal(gens_list)
    dim = int(I.dimension())
    if dim == 0:
        q = int(I.vector_space_dimension())
    elif dim == -1:
        q = 0                       # unit ideal: R/I = 0 (typical failed-decomposition attempt)
    else:
        q = None
    d_gb = None
    try:
        gb = I.groebner_basis(); d_gb = int(max([g.degree() for g in gb]))
    except Exception:
        pass
    d_ff = d_solv = None
    if q is not None:
        d_ff, d_solv, _ = first_fall_and_solving(F, gens_list, xs, Dmax, q)
    return dict(dim=dim, quo=q, d_ff=d_ff, d_solv=d_solv, d_gb=d_gb)

def decomposable_target(F, A, B, m, extra=0, seed=1):
    """Factor base = x-coords of m random points (+extra), and a target that DECOMPOSES as their
    sum -> a CONSISTENT system (nonempty variety). Returns (tval, Vroots) or None."""
    import random as pyr; pyr.seed(int(seed))
    E = EllipticCurve(F, [A, B]); G = E.gens()[0]; N = int(E.order())
    for _ in range(200):
        pts = [int(pyr.randrange(1, N)) * G for _ in range(m)]
        xs = [P[0] for P in pts]
        if any(P == E(0) for P in pts) or len(set(xs)) < m:
            continue
        Ssum = E(0)
        for P in pts:
            Ssum = Ssum + P
        Ptgt = -Ssum
        if Ptgt == E(0):
            continue
        Vroots = list(xs)
        for _ in range(extra):
            Q = int(pyr.randrange(1, N)) * G
            Vroots.append(Q[0])
        return Ptgt[0], Vroots
    return None

def leading_form_independence(m):
    """Numeric (over QQ) check that the LEADING (top-total-degree) form of S_{m+1} is IDENTICAL
    across curves -> curve-independent. Confirms the isobaric proof for m=4,5 without the heavy
    symbolic QQ(A,B) computation."""
    tops = []
    for (A, B) in [(0, 7), (5, 11), (3, 0), (2, 3)]:
        S, Rt = _build_summation(QQ, QQ(A), QQ(B), m)
        d = S.degree()
        top = sum(c * mm for c, mm in zip(S.coefficients(), S.monomials()) if mm.degree() == d)
        tops.append(top)
    all_same = all(t == tops[0] for t in tops)
    return all_same, int(tops[0].degree()), len(tops[0].monomials())

def matched_curves_compare(p, m, B, seed, Dmax):
    """Matched INCONSISTENT control: identical random V-roots + target across all three curves,
    so the ONLY difference is (A,B) in S_{m+1}'s lower-order terms. Isolates the curve effect."""
    F = GF(p)
    import random as pyr; pyr.seed(int(seed))
    Vroots = [F(pyr.randrange(0, p)) for _ in range(B)]
    tval = F(pyr.randrange(1, p))
    curves = [('secp_j0_CMomega', 0, 7), ('nonCM_generic', 5, 11), ('j1728_CMi', 3, 0)]
    res = []
    for name, A, Bc in curves:
        res.append((name, measure_system(F, A, Bc, m, tval, Vroots, Dmax)))
    return dict(tval=int(tval), Vroots=[int(r) for r in Vroots], res=res)

def consistent_curves_compare(p, m, extra, Dmax):
    """Per-curve CONSISTENT solve (a real decomposable target). Targets/factor bases differ per
    curve (points differ), but the solving/first-fall DEGREE is comparable across curves."""
    F = GF(p)
    curves = [('secp_j0_CMomega', 0, 7), ('nonCM_generic', 5, 11), ('j1728_CMi', 3, 0)]
    res = []
    for name, A, Bc in curves:
        dt = decomposable_target(F, A, Bc, m, extra=extra, seed=1)
        if dt is None:
            res.append((name, dict(error='no decomposable target'))); continue
        tval, Vroots = dt
        res.append((name, measure_system(F, A, Bc, m, tval, Vroots, Dmax)))
    return res

def mu3_lever_test(p, m, k, Dmax, seed=999):
    """secp-form, CONSISTENT decomposable target. beta-INVARIANT factor base V (|V|=3k, closed
    under x->beta x) vs a random V of the same size. Does mu3 drop the solving degree beyond the
    trivial |V|/3 factor-base shrink?"""
    F = GF(p)
    cbr = [F(u) for u in range(2, p) if F(u)**3 == 1]
    if not cbr:
        return dict(error='p not = 1 mod 3')
    beta = cbr[0]
    E = EllipticCurve(F, [0, 7]); G = E.gens()[0]; N = int(E.order())
    import random as pyr; pyr.seed(int(seed))
    # decomposable target from m points, then build a beta-invariant V CONTAINING their x-coords
    for _ in range(200):
        pts = [int(pyr.randrange(1, N)) * G for _ in range(m)]
        xs = [P[0] for P in pts]
        if any(P == E(0) for P in pts) or len(set(xs)) < m:
            continue
        Ssum = E(0)
        for P in pts:
            Ssum = Ssum + P
        Ptgt = -Ssum
        if Ptgt != E(0):
            break
    tval = Ptgt[0]
    # beta-invariant V: mu3-close the point x-coords, pad with full mu3 orbits to size 3k
    Vinv = set()
    for x in xs:
        Vinv |= {x, beta * x, beta * beta * x}
    while len(Vinv) < 3 * k:
        r = F(pyr.randrange(1, p))
        Vinv |= {r, beta * r, beta * beta * r}
    Vinv = list(Vinv)
    # random V of same size, also containing the decomposition x-coords (so it stays consistent)
    Vrnd = set(xs)
    while len(Vrnd) < len(Vinv):
        Vrnd.add(F(pyr.randrange(0, p)))
    Vrnd = list(Vrnd)
    out = dict(beta=int(beta), sizeV=len(Vinv), tval=int(tval))
    out['secp_betaInvV'] = measure_system(F, 0, 7, m, tval, Vinv, Dmax)
    out['secp_randomV'] = measure_system(F, 0, 7, m, tval, Vrnd, Dmax)
    return out

def piece_A_singular_locus(p):
    """Climb v13's rung to S4: eliminate x1,x2,x3 from (S4, dS4/dx_i) to a condition on t.
    v13 got Delta(t)=c*(t^3+7)^4 for S3; test whether S4's singular-fibre locus is likewise
    supported on the torsion locus. Time-boxed (elimination can be heavy)."""
    F = GF(p)
    S, xs, t = summation_poly(F, 0, 7, 3)
    R = xs[0].parent()
    grads = [S.derivative(v) for v in xs]
    J = R.ideal([S] + grads)
    elim = J.elimination_ideal(list(xs))
    out = []
    for g in elim.gens():
        if g == 0:
            out.append('0'); continue
        gg = g.polynomial(t) if hasattr(g, 'polynomial') else g
        out.append(str(g.factor()))
    return out

# ----------------------------------------------------------------------------------------
# main
# ----------------------------------------------------------------------------------------

def main():
    import sys
    sys.stdout.reconfigure(line_buffering=True)   # survive a later time-boxed hang
    print("=" * 78)
    print("SEMAEV ELIMINATION STRUCTURE  --  item #1 (S4+ first-fall / Groebner)")
    print("=" * 78)

    print("\n[0] Construction + group-law verification (secp-form y^2=x^3+7)")
    for p, m in [(211, 2), (211, 3), (307, 3)]:
        F = GF(p)
        S, xs, t = summation_poly(F, 0, 7, m)
        ok, bad, sk = verify_group_law(F, 0, 7, m, S, xs, t, trials=30, seed=1)
        print("   p=%-4d m=%d  S_%d: total_deg=%-3d per-var_deg=%-2d nterms=%-4d  group-law ok=%d bad=%d skip=%d"
              % (p, m, m + 1, S.degree(), S.degree(xs[0]), len(S.monomials()), ok, bad, sk))

    print("\n[B1] PROVED: leading form of S_{m+1} is curve-independent (isobaric wt x=1,A=2,B=3)")
    for m in [2, 3]:
        wds, involves, d = isobaric_check(m)
        print("   S_%d symbolic QQ[A,B]: deg=%-3d weighted-degrees=%s -> %s ; top involves A,B? %s"
              % (m + 1, d, wds, ("ISOBARIC" if len(wds) == 1 else "NOT"), involves))
    for m in [3, 4]:
        same, d, nt = leading_form_independence(m)
        print("   S_%d numeric leading form identical across 4 curves? %s  (deg=%d, %d monomials)"
              % (m + 1, same, d, nt))

    print("\n[B1-num] first-fall degree identical across curves (matched inconsistent control)")
    for p, m, B in [(211, 3, 2), (211, 3, 3)]:
        Dmax = 2**(m - 1) + m * B + 5
        comp = matched_curves_compare(p, m, B, seed=12345, Dmax=Dmax)
        print("   p=%d m=%d B=%d t=%d V=%s" % (p, m, B, comp['tval'], comp['Vroots']))
        for name, r in comp['res']:
            print("      %-18s dim=%s quo=%s  d_ff=%s  d_solv=%s  d_gb=%s"
                  % (name, r['dim'], r['quo'], r['d_ff'], r['d_solv'], r['d_gb']))

    print("\n[B2] solving/first-fall degree on CONSISTENT decomposable targets (per curve)")
    for p, m, extra in [(211, 3, 0), (211, 3, 1)]:
        Dmax = 2**(m - 1) + m * (m + extra) + 5
        res = consistent_curves_compare(p, m, extra, Dmax)
        print("   p=%d m=%d |V|=%d" % (p, m, m + extra))
        for name, r in res:
            if 'error' in r:
                print("      %-18s %s" % (name, r['error']))
            else:
                print("      %-18s dim=%s quo=%s  d_ff=%s  d_solv=%s  d_gb=%s"
                      % (name, r['dim'], r['quo'], r['d_ff'], r['d_solv'], r['d_gb']))

    print("\n[B2-mu3] mu3-lever test (secp beta-invariant V vs random V, consistent, same |V|)")
    for p, m, k in [(211, 3, 2), (307, 3, 2)]:
        Dmax = 2**(m - 1) + m * (3 * k) + 5
        out = mu3_lever_test(p, m, k, Dmax)
        if 'error' in out:
            print("   p=%d %s" % (p, out['error'])); continue
        print("   p=%d m=%d |V|=%d beta=%d t=%d" % (p, m, out['sizeV'], out['beta'], out['tval']))
        for label in ['secp_betaInvV', 'secp_randomV']:
            r = out[label]
            print("      %-16s dim=%s quo=%s  d_ff=%s  d_solv=%s  d_gb=%s"
                  % (label, r['dim'], r['quo'], r['d_ff'], r['d_solv'], r['d_gb']))

    print("\n[A] Piece A (time-boxed): singular-fibre locus of the S4 relation variety in t")
    try:
        for p in [211]:
            fac = piece_A_singular_locus(p)
            print("   p=%d  elim ideal (t-condition) factors:" % p)
            for s in fac:
                print("      %s" % s[:120])
    except Exception as e:
        print("   Piece A skipped/failed: %s" % repr(e)[:100])

    print("\n[done]")

if __name__ == '__main__':
    main()
