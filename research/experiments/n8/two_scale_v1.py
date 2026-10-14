"""Task AM: the two-scale decomposition D = D' u 8C of an integer disparity set (exact integers and Fractions only).

Convention.  A 7-set D of positive integers.  The subject is lonely at t iff ||d t|| >= 1/8 for all d in D.
Write s = 8 t.  A disparity d reads d*s/8 laps.  d not divisible by 8 is clear iff (d*s mod 8) in [1,7];
d = 8c is clear iff frac(c*s) in [1/8, 7/8], i.e. the multiples form the sub-instance C = {c} read at the time s.
s = a + eta (a = floor(s), eta = frac(s)); the sub-instance C is lonely at eta (1-periodic since C is integral).
LANDING of D = least positive lonely s (s* = 8 t*).  eta_C = least positive lonely point of C alone (in s).
Observation only (rule 7): every count here is [OBS]; nothing is an argument.  No floats, no random choices.
Usage: python3 two_scale_v1.py
"""
import sys
from math import gcd, floor
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
from functools import reduce
from multiprocessing import Pool


def lcm(a, b):
    return a * b // gcd(a, b)


def lcmall(S):
    return reduce(lcm, S)


def v2(n):
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def lonely_s(D, n, Lc):
    """D lonely at s = n/Lc  (t = s/8 = n/(8 Lc))."""
    M = 8 * Lc
    for d in D:
        r = (d * n) % M
        if r < Lc or r > 7 * Lc:
            return False
    return True


def landing_s(D):
    """Least positive lonely s of D as Fraction (candidates: openings (8k+1)/d, k < d, s <= 8)."""
    Lc = lcmall(D)
    cands = set()
    for d in D:
        q = Lc // d
        for k in range(d):
            cands.add((8 * k + 1) * q)
    for n in sorted(cands):
        if lonely_s(D, n, Lc):
            return F(n, Lc)
    return None


def landing_C(C):
    """Least positive lonely time for the sub-instance C alone (time s, so this is landing_s(C)/8)."""
    return landing_s(sorted(C)) / 8


def lonely_frac(D, s):
    n, Lc = s.numerator, s.denominator
    # s = n/Lc' for Lc' = denominator; reuse lonely_s with Lc = denominator
    return lonely_s(D, n, Lc)


def ceil_frac(x):
    return -((-x.numerator) // x.denominator)


def next_opening_s(d, s):
    """Next opening of runner d after s, in s coordinates: (8*ceil((d s - 1)/8) + 1)/d."""
    return F(8 * ceil_frac((d * s - 1) / 8) + 1, d)


def inway_s(d, s):
    r = (d * s) % 8
    return r < 1 or r > 7


def cascade_from(D, s0):
    """Cascade from s0 (<= landing): move to the largest next opening among runners in the way.
    Returns (landing, hops, last_opener_set)."""
    s = s0
    hops = 0
    last = None
    while True:
        ways = [d for d in D if inway_s(d, s)]
        if not ways:
            return s, hops, last
        nxt = {d: next_opening_s(d, s) for d in ways}
        m = max(nxt.values())
        last = sorted(d for d in ways if nxt[d] == m)
        s = m
        hops += 1


def split(D):
    Dp = [d for d in D if d % 8 != 0]
    C = [d // 8 for d in D if d % 8 == 0]
    return Dp, C


def odd_classes(Dp):
    return frozenset(d % 8 for d in Dp if d % 2 == 1)


def analyse(D):
    Dp, C = split(D)
    s = landing_s(D)
    a = floor(s)
    eta = s - a
    sC = landing_C(C)
    # opener types at the landing
    openers = [d for d in D if (d * s) % 8 == 1]
    otype = 'C' if any(d % 8 == 0 for d in openers) else 'Dp'
    if any(d % 8 == 0 for d in openers) and any(d % 8 != 0 for d in openers):
        otype = 'both'
    land_c, hops, last = cascade_from(D, sC)
    assert land_c == s, (D, s, land_c)
    O = odd_classes(Dp)
    dmaxp = max(Dp) if Dp else 0
    hyp_small = (sC * dmaxp <= 1)
    hyp_O = (len(O) < 4)
    expl = hyp_small and hyp_O
    met, hit = central_data(Dp, C, s)
    return dict(met=tuple(met), hit=hit, D=D, Dp=Dp, C=C, s=s, a=a, eta=eta, sC=sC, otype=otype, hops=hops, expl=expl,
                hyp_small=hyp_small, hyp_O=hyp_O, O=O,
                k=(floor(C[0] * s) if len(C) == 1 else None))


def central_cell(Dp, a):
    """Central cell of D' around the integer a (a odd, 8 not dividing any d): theta in [L, U] with
    L = max_d (1 - r_d)/d, U = min_d (7 - r_d)/d, r_d = (d a) mod 8 (in 1..7).  Returns (L, U)."""
    L = max(F(1 - ((d * a) % 8), d) for d in Dp)
    U = min(F(7 - ((d * a) % 8), d) for d in Dp)
    return L, U


def c_lonely_point(C, th):
    return all(F(1, 8) <= abs(c * th - round(c * th)) for c in C)


def c_lonely_in(C, x, y):
    """Least theta in [x, y] (closed) lonely for C (distInt(c theta) >= 1/8 for all c in C) or None; exact."""
    pts = {x, y}
    for c in C:
        m0 = floor(x * c) - 1
        m1 = floor(y * c) + 2
        for m in range(m0, m1 + 1):
            for sg in (1, -1):
                q = F(8 * m + sg, 8 * c)
                if x <= q <= y:
                    pts.add(q)
    P = sorted(pts)
    for i, q in enumerate(P):
        if c_lonely_point(C, q):
            return q
        if i + 1 < len(P):
            mid = (q + P[i + 1]) / 2
            if c_lonely_point(C, mid):
                # interior lonely -> closed set, so the left end of this stretch is lonely too
                return q
    return None


def central_data(Dp, C, s):
    """For odd a in 1,3,5,7: is the central cell of D' at a met by the C-lonely set? And is s* in a central cell?"""
    met = []
    hit = None
    for a in (1, 3, 5, 7):
        L, U = central_cell(Dp, a)
        q = c_lonely_in(C, L, U)
        if q is not None:
            met.append(a)
        if a + L <= s <= a + U:
            hit = a
    return met, hit


def pop(N):
    out = []
    for D in combinations(range(1, N + 1), 7):
        if reduce(gcd, D) != 1:
            continue
        if any(d % 8 == 0 for d in D):
            out.append(D)
    return out


def work(D):
    r = analyse(D)
    r['O'] = tuple(sorted(r['O']))
    return r


def explicit_witness_ok(r):
    """Verify the explicit statement numerically: when (O not full) and (eta_C <= 1/dmax'), some a odd and sign give a
    lonely s = a +- eta_C (the exact Lean theorem explicit_instant)."""
    D = r['D']
    Dp = r['Dp']
    sC = r['sC']
    for a in (1, 3, 5, 7):
        for sg in (1, -1):
            s = a + sg * sC
            if lonely_frac(D, s):
                return True
    return False


def main():
    print("=== TWO-SCALE DATA (exact), populations: gcd-1 7-subsets of {1..N} containing a multiple of 8 ===")
    for N in (14, 18, 22):
        P = pop(N)
        with Pool(10) as pl:
            R = pl.map(work, P, chunksize=500)
        print("\n##### N = %d : %d sets with C nonempty #####" % (N, len(R)))
        # --- split by |C| and 2-adic valuations of the multiples
        groups = defaultdict(list)
        for r in R:
            key = (len(r['C']), tuple(sorted(v2(8 * c) for c in r['C'])))
            groups[key].append(r)
        print("\n-- (2i) landing eta* versus eta_C, by (|C|, 2-adic valuations of the multiples) --")
        for key in sorted(groups):
            G = groups[key]
            n = len(G)
            same = sum(1 for r in G if r['a'] == 0 and r['eta'] == r['sC'])
            sameeta = sum(1 for r in G if r['eta'] == r['sC'])
            a0 = sum(1 for r in G if r['a'] == 0)
            adist = Counter(r['a'] for r in G)
            hops = Counter(r['hops'] for r in G)
            ot = Counter(r['otype'] for r in G)
            print("  key |C|=%d v2=%s : sets=%d ; s*=eta_C exactly (a=0, no displacement): %d ; eta*==eta_C (any a): %d ; a=0: %d"
                  % (key[0], key[1], n, same, sameeta, a0))
            print("     a distribution: %s" % sorted(adist.items()))
            print("     cascade hops from eta_C to s*: %s" % sorted(hops.items()))
            print("     opener type at s*: %s" % sorted(ot.items()))
            # displacement of eta* over eta_C inside [0,1)
            disp = Counter()
            mx = F(0)
            for r in G:
                dlt = r['eta'] - r['sC']
                assert dlt >= 0
                if dlt > mx:
                    mx = dlt
                disp['0' if dlt == 0 else '>0'] += 1
            print("     eta*-eta_C: %s ; maximum %s" % (dict(disp), mx))
        # --- explicit regime
        print("\n-- (3) explicit regime: O = odd residues of D' not all four  AND  eta_C * max(D') <= 1 --")
        ex = [r for r in R if r['expl']]
        ok = sum(1 for r in ex if explicit_witness_ok(r))
        print("  sets in the explicit regime: %d ; of these a lonely s = a +- eta_C (a in 1,3,5,7) exists: %d" % (len(ex), ok))
        rest = [r for r in R if not r['expl']]
        print("  sets outside: %d ; by (O full?, eta_C*max(D')<=1?):" % len(rest))
        cnt = Counter((not r['hyp_O'], r['hyp_small']) for r in rest)
        for k_, v in sorted(cnt.items()):
            print("     O_full=%s eta_C_small=%s : %d" % (k_[0], k_[1], v))
        # inside the explicit regime how many have landing exactly eta_C? and displacement
        exa0 = sum(1 for r in ex if r['a'] == 0 and r['eta'] == r['sC'])
        print("  explicit-regime sets whose landing is s* = eta_C itself: %d ; landing at a > 0: %d" %
              (exa0, sum(1 for r in ex if r['a'] > 0)))
        # displaced sets outside the explicit regime: landing description
        print("  outside the explicit regime: landing a distribution %s ; hops %s" %
              (sorted(Counter(r['a'] for r in rest).items()), sorted(Counter(r['hops'] for r in rest).items())))
        print("\n-- (3') central cells of D' at the units a = 1,3,5,7 (exact: theta in [max (1-r_d)/d, min (7-r_d)/d]) --")
        met_n = Counter(len(r['met']) for r in R)
        print("  number of units a whose central cell is met by the C-lonely set (theta signed): %s" % sorted(met_n.items()))
        none_met = [r for r in R if not r['met']]
        print("  sets where NO unit's central cell meets the C-lonely set: %d" % len(none_met))
        hit_n = Counter(r['hit'] for r in R)
        print("  landing s* inside a central cell of unit a (a: count): %s" % sorted(hit_n.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))
        landing_outside_but_met = sum(1 for r in R if r['hit'] is None and r['met'])
        print("  landing NOT in any central cell although some central cell is met by C: %d" % landing_outside_but_met)
        print("  landing in a central cell: %d ; not in one: %d" % (sum(1 for r in R if r['hit'] is not None), sum(1 for r in R if r['hit'] is None)))
        for r in sorted(none_met, key=lambda r: r['D'])[:6]:
            print("     no-central D=%s s*=%s O=%s" % (r['D'], r['s'], r['O']))
        # blocked_at_zero check (Lean: Fresh.TwoScale.blocked_at_zero)
        same_land = [r for r in R if r['a'] == 0 and r['eta'] == r['sC']]
        small = [r for r in R if min(r['Dp']) * r['sC'] < 1]
        print("\n-- (blocked_at_zero) sets with landing s* = eta_C exactly: %d, all with min(D')*eta_C >= 1: %s" %
              (len(same_land), all(min(r['Dp']) * r['sC'] >= 1 for r in same_land)))
        print("   sets with min(D')*eta_C < 1: %d ; of these, landing equals eta_C: %d ; landing has a = 0 : %d" %
              (len(small), sum(1 for r in small if r['a'] == 0 and r['eta'] == r['sC']), sum(1 for r in small if r['a'] == 0)))
        print("   sets with min(D')*eta_C >= 1: %d ; of these landing equals eta_C: %d" %
              (len(R) - len(small), len(same_land)))
        # --- |C| = 1 detail
        print("\n-- (2ii) |C| = 1 : lap k = floor(c s*) of the C-runner at the landing, by c --")
        one = [r for r in R if len(r['C']) == 1]
        byc = defaultdict(list)
        for r in one:
            byc[r['C'][0]].append(r)
        for c in sorted(byc):
            G = byc[c]
            kd = Counter(r['k'] for r in G)
            print("  c=%d (disparity %d): sets=%d ; lap k distribution (k: count) %s" % (c, 8 * c, len(G), sorted(kd.items())))
            print("       k == c*a + floor(c*eta) always (identity) : %s ; landing eta* is an opening of the C-runner: %d ; of a D' runner: %d ; both: %d"
                  % (all(r['k'] == c * r['a'] + floor(c * r['eta']) for r in G),
                     sum(1 for r in G if r['otype'] == 'C'), sum(1 for r in G if r['otype'] == 'Dp'),
                     sum(1 for r in G if r['otype'] == 'both')))
            # first window k=0 nonempty intersection? i.e. s* inside window 0 (<= 7/(8c))
            w0 = sum(1 for r in G if r['k'] == 0)
            print("       landing lies in the FIRST window (k=0): %d of %d" % (w0, len(G)))
        # exceptions listing: sets where the landing is displaced (hops >= 2) examples
        print("\n-- exceptions: hops>=3 or a>=3, first few (sorted order), with the blockers at eta_C --")
        exc = [r for r in R if r['hops'] >= 3 or r['a'] >= 3]
        print("  count: %d" % len(exc))
        for r in sorted(exc, key=lambda r: (-r['hops'], r['D']))[:12]:
            Dp = r['Dp']
            sC = r['sC']
            blockers = [d for d in r['D'] if inway_s(d, sC)]
            print("   D=%s C=%s eta_C=%s s*=%s (a=%d eta=%s) hops=%d blockers_at_eta_C=%s O=%s" %
                  (r['D'], r['C'], sC, r['s'], r['a'], r['eta'], r['hops'], blockers, r['O']))
        sys.stdout.flush()


def cells_s(Dp):
    """Lonely set of the integer set Dp in s in [0, 8], as a list of closed intervals ((p1, p2), T): p/T."""
    Lc = lcmall(Dp)
    T = 2 * Lc
    cand = {0, 8 * T}
    for d in Dp:
        q = Lc // d
        for m in range(0, d + 1):
            for sg in (1, -1):
                n = 2 * (8 * m + sg) * q
                if 0 <= n <= 8 * T:
                    cand.add(n)
    c = sorted(cand)

    def lon(p):
        M = 8 * T
        for d in Dp:
            r = (d * p) % M
            if r < T or r > 7 * T:
                return False
        return True
    K = len(c)
    P = [lon(x) for x in c]
    G = [lon((c[i] + c[i + 1]) // 2) for i in range(K - 1)]
    cells = []
    i = 0
    while i < K:
        if P[i]:
            j = i
            while j < K - 1 and G[j]:
                j += 1
            cells.append((c[i], c[j]))
            i = j + 1
        else:
            i += 1
    return cells, T


def first_hit(cells, T, cs):
    """Least lonely s for Dp u {8c : c in cs} given Dp's cells (c-windows [(8k+1)/(8c),(8k+7)/(8c)] for every c)
    -- implemented for len(cs)==1; returns (k, position fraction) or None, scanning windows in order."""
    c = cs[0]
    best = None
    for (x, y) in cells:
        # first window k with (8k+7)/(8c) >= x/T and (8k+1)/(8c) <= y/T ; smallest s in the intersection
        # (8k+7)*T >= 8c*x  =>  k >= ceil((8c x/T - 7)/8)
        kmin = max(0, -((-(8 * c * x - 7 * T)) // (8 * T)))
        k = kmin
        while True:
            lo_num = (8 * k + 1) * T      # window start * 8c*T
            hi_num = (8 * k + 7) * T
            if lo_num > 8 * c * y:
                break
            if hi_num >= 8 * c * x:
                # intersection nonempty: smallest point = max(x/T, (8k+1)/(8c))
                s1 = max(F(x, T), F(8 * k + 1, 8 * c))
                if best is None or s1 < best[1]:
                    best = (k, s1)
                break
            k += 1
        if best is not None and F(x, T) > best[1]:
            break
    return best


def failset_part(args):
    Dp, cmax = args
    cells, T = cells_s(Dp)
    fails = []
    for c in range(1, cmax + 1):
        h = first_hit(cells, T, [c])
        if h is None:
            fails.append(c)
    return Dp, fails, len(cells)


def fail_main():
    print("\n=== (2ii') FAIL SET OF c: D' = six non-multiples of 8 in 1..N ; for every c in 1..cmax, does D' u {8c} have a lonely s in (0,8]? ===")
    cmax = 48
    for N in (14, 18, 22):
        nm = [d for d in range(1, N + 1) if d % 8 != 0]
        P = [(Dp, cmax) for Dp in combinations(nm, 6)]
        with Pool(10) as pl:
            R = pl.map(failset_part, P, chunksize=200)
        nfail = sum(1 for r in R if r[1])
        tot = sum(len(r[1]) for r in R)
        print("N=%d : D' sets=%d ; (D', c) pairs tested=%d ; pairs with NO lonely s: %d ; D' with some failing c: %d" %
              (N, len(R), len(R) * cmax, tot, nfail))
        for r in [r for r in R if r[1]][:10]:
            print("    D'=%s failing c = %s" % (r[0], r[1]))
        # cross-check the window method against the direct landing for every D' (N=14: c<=12 ; others c<=6)
        bad = 0
        chk = 0
        for Dp in (combinations(nm, 6) if N == 14 else list(combinations(nm, 6))[::7]):
            cells, T = cells_s(Dp)
            for c in range(1, 13 if N == 14 else 7):
                h = first_hit(cells, T, [c])
                chk += 1
                if h is None or h[1] != landing_s(list(Dp) + [8 * c]):
                    bad += 1
        print("    cross-check of the window method against the cascade landing: %d pairs, mismatches %d" % (chk, bad))
        mx = max((r[2] for r in R))
        print("    max number of lonely cells of a D' in one period (0,8]: %d" % mx)
        # lap statistic: for each pair the first hit lap k as multiple of c
        sys.stdout.flush()


def tower_main():
    print("\n=== (2iii) 8-adic tower: sets containing 64 or more (multiples of 64 give depth 2) ===")
    base = [1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 13, 8, 16, 24, 32, 64, 128, 192]
    from itertools import combinations as cb
    P = [D for D in cb(sorted(base), 7) if reduce(gcd, D) == 1 and any(d % 64 == 0 for d in D)]
    print("population: 7-subsets of %s with gcd 1 and some multiple of 64: %d sets" % (sorted(base), len(P)))
    depthc = Counter()
    rows = []
    for D in P:
        d = 0
        E = list(D)
        while any(e % 8 == 0 for e in E):
            E = [e // 8 for e in E if e % 8 == 0]
            d += 1
        s = landing_s(list(D))
        # digits: t* = s/8 = a0/8 + a1/64 + ... ; a0 = floor(s), eta0 = frac(s) ; level 1: s1 = 8 eta0
        digs = []
        x = s
        for lev in range(d + 1):
            a_ = floor(x)
            digs.append(a_)
            x = 8 * (x - a_)
        C1 = [e // 8 for e in D if e % 8 == 0]
        sC = landing_C(C1)
        eta0 = s - floor(s)
        depthc[d] += 1
        rows.append((D, d, s, tuple(digs), sC, eta0 == sC, eta0))
    print("depth distribution (levels of the 8-adic tower): %s" % sorted(depthc.items()))
    print("eta_0 == landing of C alone (no displacement at the first level): %d of %d" % (sum(1 for r in rows if r[5]), len(rows)))
    dd = Counter((r[1], r[3][:2]) for r in rows)
    print("first two octal digits (a0, a1) of t* = s*/8 : (depth, digits) : count -> top 12: %s" % dd.most_common(12))
    odd0 = sum(1 for r in rows if r[3][0] % 2 == 1)
    print("a0 odd: %d of %d ; a0 even: %d" % (odd0, len(rows), len(rows) - odd0))
    for r in rows[:8]:
        print("   D=%s depth=%d s*=%s digits=%s eta_0=%s eta_C=%s" % (r[0], r[1], r[2], r[3], r[6], r[4]))
    ex = [r for r in rows if not r[5]]
    print("   displaced at the first level: %d ; first four:" % len(ex))
    for r in ex[:4]:
        print("   D=%s depth=%d s*=%s digits=%s eta_0=%s eta_C=%s" % (r[0], r[1], r[2], r[3], r[6], r[4]))
    sys.stdout.flush()


if __name__ == '__main__':
    main()
    fail_main()
    tower_main()
