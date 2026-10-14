"""Task AL: totients, exact fractions, boundaries of the lonely set (integer disparity sets, period 1).

Exact: integers and Fractions only, no floats.  Each disparity set D is a set of 7 distinct positive integers.
The subject is lonely at t iff ||d t|| >= 1/8 for all d in D.  With L = lcm(D) and T = 16 L, t = n/T and the
test is  min(r, T - r) >= 2 L  with  r = (d n) mod T.  Boundary candidates are t = (8m +- 1)/(8d).
Cells = maximal closed intervals of the lonely set in [0, 1] (degenerate = single points).
Observation only (rule 7): counts and rates are [OBS], not arguments.
Usage: python3 totient_boundaries_v1.py [N ...]   (default 14 18 22)
"""
import sys
from math import gcd, floor
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
from multiprocessing import Pool
from functools import reduce


def lcm(a, b):
    return a * b // gcd(a, b)


def lonely_int(D, n, T, L):
    L2 = 2 * L
    for d in D:
        r = (d * n) % T
        if r < L2 or T - r < L2:
            return False
    return True


def cells_of(D):
    """Return (cells, T, L): cells = list of (lo_n, hi_n) numerators over T (closed intervals, lo==hi allowed)."""
    L = reduce(lcm, D)
    T = 16 * L
    cand = {0, T}
    for d in D:
        s = L // d
        for m in range(0, d + 1):
            for sg in (1, -1):
                n = 2 * (8 * m + sg) * s
                if 0 <= n <= T:
                    cand.add(n)
    c = sorted(cand)
    K = len(c)
    P = [lonely_int(D, x, T, L) for x in c]
    G = [lonely_int(D, (c[i] + c[i + 1]) // 2, T, L) for i in range(K - 1)]
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
    return cells, T, L


def endpoint_info(D, nn, T):
    """Which runners sit at 1/8 past a lap line (opening) or 1/8 before one (entry) at t = nn/T."""
    t = F(nn, T)
    ops, ens = [], []
    for d in D:
        x = d * t
        k = floor(x)
        fr = x - k
        if fr == F(1, 8):
            ops.append((d, k))
        elif fr == F(7, 8):
            ens.append((d, k))
    return t, ops, ens


def analyse(D):
    cells, T, L = cells_of(D)
    ncell = len(cells)
    out = {}
    out['D'] = D
    out['ncell'] = ncell
    out['ndeg'] = sum(1 for a, b in cells if a == b)
    out['odd'] = sum(1 for d in D if d % 2)
    # mirror pairing: (a,b) <-> (T-b, T-a)
    cs = set(cells)
    mirror_ok = all((T - b, T - a) in cs for a, b in cells)
    central = [c for c in cells if c[0] + c[1] == T]
    out['mirror_ok'] = mirror_ok
    out['ncentral'] = len(central)
    out['half_lonely'] = lonely_int(D, T // 2, T, L)
    # half 1/2 is lonely iff all odd
    out['half_expected'] = all(d % 2 for d in D)
    out['cells'] = [(F(a, T), F(b, T)) for a, b in cells]
    # endpoint records
    eps = []
    for ci, (a, b) in enumerate(cells):
        ta, oa, ea = endpoint_info(D, a, T)
        tb, ob, eb = endpoint_info(D, b, T)
        eps.append((ci, ta, oa, ea, tb, ob, eb))
    out['eps'] = eps
    # landing
    a0, b0 = cells[0]
    tl = F(a0, T)
    dmin = min(D)
    out['landing'] = tl
    out['Rstar'] = 8 * dmin * tl
    # readings in eighths: u_z = 8 z t mod 8
    us = []
    for z in D:
        u = (8 * z * tl) % 8
        us.append((z, u))
    out['us'] = us
    # all gaps between consecutive boundary points of lonely cells
    pts = sorted({F(a, T) for a, b in cells} | {F(b, T) for a, b in cells})
    out['pts'] = pts
    return out


def run_pop(N):
    sets = [D for D in combinations(range(1, N + 1), 7) if reduce(gcd, D) == 1]
    with Pool(10) as pool:
        res = pool.map(analyse, sets, chunksize=200)
    return res


def frs(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


def summarise(N, res, special=None):
    pr = print
    pr(f"\n=== POPULATION N={N}: 7-subsets of 1..{N} with gcd 1: {len(res)} sets ===")
    # L2
    pr("\n-- L2 counts [OBS] --")
    ncell = Counter(r['ncell'] for r in res)
    pr("cells per period (count : sets):", dict(sorted(ncell.items())))
    pr("min cells:", min(ncell), " all sets have >= 1 cell:", min(ncell) >= 1, " sets with <4 cells:", sum(v for k, v in ncell.items() if k < 4))
    ndeg = Counter(r['ndeg'] for r in res)
    pr("degenerate (single-point) cells per set (count : sets):", dict(sorted(ndeg.items())))
    pr("mirror pairing t <-> 1-t holds for every set:", all(r['mirror_ok'] for r in res))
    ncen = Counter(r['ncentral'] for r in res)
    pr("central (self-mirror) cells per set (count : sets):", dict(sorted(ncen.items())))
    # parity: number of cells vs ncentral
    par = Counter((r['ncell'] - r['ncentral']) % 2 for r in res)
    pr("(cells - central) mod 2 (should be 0 as non-central cells pair up):", dict(par))
    pr("1/2 lonely iff all disparities odd, checked on every set:", all(r['half_lonely'] == r['half_expected'] for r in res))
    byodd = defaultdict(list)
    for r in res:
        byodd[r['odd']].append(r['ncell'])
    pr("by number of odd disparities: odd -> (sets, min cells, max cells, sets whose cell count is odd, sets with central cell)")
    for o in sorted(byodd):
        rs = [r for r in res if r['odd'] == o]
        cn = [r['ncell'] for r in rs]
        pr(f"   {o}: sets={len(rs)} min={min(cn)} max={max(cn)} odd-count={sum(1 for c in cn if c % 2)} central={sum(1 for r in rs if r['ncentral'])}")
    # central cell iff 1/2 lonely?
    pr("central cell present iff 1/2 lonely:", all((r['ncentral'] > 0) == r['half_lonely'] for r in res))
    ex = [r for r in res if (r['ncentral'] > 0) != r['half_lonely']]
    for r in ex[:10]:
        pr("   exception", r['D'], r['ncentral'], r['half_lonely'])
    # cell count modulus tests
    for q in (2, 3, 4, 8):
        pr(f"cell count mod {q}:", dict(sorted(Counter(r['ncell'] % q for r in res).items())))
    # minimum-count sets
    mn = min(r['ncell'] for r in res)
    pr(f"sets attaining min count {mn} (first 8):", [r['D'] for r in res if r['ncell'] == mn][:8], " total:", sum(1 for r in res if r['ncell'] == mn))

    # L1 boundaries
    pr("\n-- L1 boundaries [OBS] --")
    nleft = Counter(); kmod_left = Counter(); kmod_right = Counter()
    pnum_left = Counter(); pnum_right = Counter()
    ident_ok = True; denom_form_ok = True
    left_no_open = 0; right_no_entry = 0
    mult_left = Counter(); mult_right = Counter()
    left_also_entry = 0; right_also_open = 0
    lap_vs_x = Counter()
    gcd_stat = Counter()
    mirror_lap_ok = True
    nends = 0
    for r in res:
        D = r['D']
        for (ci, ta, oa, ea, tb, ob, eb) in r['eps']:
            nends += 2
            if not oa:
                left_no_open += 1
            if not eb:
                right_no_entry += 1
            if ea and oa:
                left_also_entry += 1
            if ob and eb:
                right_also_open += 1
            mult_left[len(oa)] += 1
            mult_right[len(eb)] += 1
            for (x, k) in oa:
                num = 8 * k + 1
                g = gcd(num, x)
                kmod_left[k % 8] += 1
                gcd_stat[('open', g if g < 10 else '>=10')] += 1
                p = num // g; q = 8 * x // g
                if p * g % 8 != 1 or ta != F(p, q) or q % (8 * x // g) != 0:
                    ident_ok = False
                pnum_left[p % 8] += 1
                if (8 * x) % q != 0:
                    denom_form_ok = False
            for (x, k) in eb:
                num = 8 * k + 7
                g = gcd(num, x)
                kmod_right[k % 8] += 1
                gcd_stat[('entry', g if g < 10 else '>=10')] += 1
                p = num // g; q = 8 * x // g
                if p * g % 8 != 7 or tb != F(p, q):
                    ident_ok = False
                pnum_right[p % 8] += 1
    pr(f"cell endpoints inspected: {nends}")
    pr("left endpoints with no opening runner (should be 0):", left_no_open, "; right endpoints with no entry runner (should be 0):", right_no_entry)
    pr("left endpoints that are also an entry point:", left_also_entry, "; right endpoints that are also an opening:", right_also_open)
    pr("opening multiplicity at left endpoints (#runners opening : count):", dict(sorted(mult_left.items())))
    pr("entry multiplicity at right endpoints:", dict(sorted(mult_right.items())))
    pr("identity p*g = +1 / -1 (mod 8) and t = p/q with q = 8x/g for every (endpoint, runner):", ident_ok, denom_form_ok)
    pr("lap index k mod 8 at left (opening, numerator 8k+1):", dict(sorted(kmod_left.items())))
    pr("lap index k mod 8 at right (entry, numerator 8k+7):", dict(sorted(kmod_right.items())))
    pr("reduced numerator p mod 8 at left openings:", dict(sorted(pnum_left.items())))
    pr("reduced numerator p mod 8 at right entries:", dict(sorted(pnum_right.items())))
    pr("g = gcd(8k+-1, x) at openings/entries:", dict(sorted(gcd_stat.items(), key=lambda kv: (kv[0][0], str(kv[0][1])))))

    # mirror: left endpoint a with opening (x,k) <-> right endpoint 1-a with entry (x, x-k-1); verify
    mir = True
    for r in res:
        cs = {(a, b) for a, b in r['cells']}
        for (ci, ta, oa, ea, tb, ob, eb) in r['eps']:
            for (x, k) in oa:
                # the mirror cell has right endpoint 1-ta, with entry (x, x-1-k)
                m = [e for e in r['eps'] if e[4] == 1 - ta]
                if not m or (x, x - 1 - k) not in m[0][6]:
                    mir = False
    pr("mirror of opening (x,k) is entry (x, x-1-k) at the mirror cell's right end, every instance:", mir)

    # L3 landing
    pr("\n-- L3 landing [OBS] --")
    Rs = [r['Rstar'] for r in res]
    pr("R* = 8 d_min t*: min", frs(min(Rs)), " max", frs(max(Rs)), " (R* >= 1 in every set:", all(R >= 1 for R in Rs), ")")
    rmax = max(res, key=lambda r: r['Rstar'])
    pr("   set with largest R*:", rmax['D'], "t* =", frs(rmax['landing']), "R* =", frs(rmax['Rstar']))
    # landing openers
    den_form = Counter(); ldenfail = 0
    opener_is_in = True
    land_first_opening_k = Counter()
    land_k_lt_x = True
    landing_open_mult = Counter()
    landing_p_mod8 = Counter(); landing_k_mod8 = Counter()
    landing_g = Counter()
    lap_distr = Counter()
    for r in res:
        e0 = r['eps'][0]
        ta, oa = e0[1], e0[2]
        landing_open_mult[len(oa)] += 1
        for (x, k) in oa:
            num = 8 * k + 1
            g = gcd(num, x)
            landing_k_mod8[k % 8] += 1
            landing_p_mod8[(num // g) % 8] += 1
            landing_g[g if g < 10 else '>=10'] += 1
            if not (0 <= k < x):
                land_k_lt_x = False
    pr("landing: number of runners opening at the landing instant (mult : sets):", dict(sorted(landing_open_mult.items())))
    pr("landing opener lap k mod 8:", dict(sorted(landing_k_mod8.items())), " (0 <= k < x for all:", land_k_lt_x, ")")
    pr("landing opener reduced numerator p mod 8:", dict(sorted(landing_p_mod8.items())))
    pr("landing opener g=gcd(8k+1,x):", dict(sorted(landing_g.items(), key=lambda kv: str(kv[0]))))
    # landing is an opening at lap 0?
    lap0 = sum(1 for r in res if any(k == 0 for (x, k) in r['eps'][0][2]))
    pr("sets whose landing has an opener at lap 0 (k=0, t = 1/(8x)):", lap0, "of", len(res))
    # denominators of landing
    dens = Counter(); denform = True; dmin_form = Counter()
    for r in res:
        D = r['D']; tl = r['landing']
        q = tl.denominator
        ok = any((8 * x) % q == 0 for x in D)
        if not ok:
            denform = False
        dens[q] += 1
    pr("landing denominator q always divides 8x for some x in D:", denform)
    pr("number of distinct landing denominators:", len(dens), "; most common (q:count):", dens.most_common(8))
    # readings of others at landing
    pr("\n-- landing: readings u_z = 8 z t* mod 8 (eighth-interval index floor(u_z); 'on' = u_z integer) --")
    onc = Counter(); eighth_hist = Counter(); ucls_multi = Counter()
    at_most_once_all = 0; at_most_once_int = 0; multi_examples = []
    onu_counts = Counter()
    for r in res:
        us = r['us']
        n_on = sum(1 for z, u in us if u.denominator == 1)
        onc[n_on] += 1
        for z, u in us:
            eighth_hist[floor(u)] += 1
        ints = [int(u) for z, u in us if u.denominator == 1]
        c = Counter(ints)
        for v in c:
            onu_counts[v] += c[v]
        if max(c.values()) == 1:
            at_most_once_int += 1
        else:
            if len(multi_examples) < 6:
                multi_examples.append((r['D'], sorted(ints)))
        c2 = Counter(floor(u) for z, u in us)
        if max(c2.values()) == 1:
            at_most_once_all += 1
    pr("number of runners exactly on an eighth at the landing instant (n : sets):", dict(sorted(onc.items())))
    pr("eighth-interval index floor(u_z) over all (set, runner):", dict(sorted(eighth_hist.items())))
    pr("exact-integer readings by value (1..7) over all sets:", dict(sorted(onu_counts.items())))
    pr("sets in which the integer readings take each value at most once:", at_most_once_int, "of", len(res))
    pr("sets in which floor(u_z) takes each value at most once (all 7 distinct eighths):", at_most_once_all, "of", len(res))
    for e in multi_examples:
        pr("   repeated integer readings e.g.", e)
    # u values: is 1 always present (the opener), and do any u have denominator pattern?
    udens = Counter()
    for r in res:
        for z, u in r['us']:
            udens[u.denominator] += 1
    pr("denominators of u_z over all (set, runner):", dict(sorted(udens.items())))
    # smallest cell / smallest gap between boundary points
    pr("\n-- extremes (exact) --")
    smallest = None; smallest_pos = None
    for r in res:
        for a, b in r['cells']:
            w = b - a
            if w > 0 and (smallest_pos is None or w < smallest_pos[0]):
                smallest_pos = (w, r['D'], a, b)
        pts = r['pts']
        for i in range(len(pts) - 1):
            g = pts[i + 1] - pts[i]
            if smallest is None or g < smallest[0]:
                smallest = (g, r['D'], pts[i], pts[i + 1])
    pr("smallest positive-width cell:", frs(smallest_pos[0]), smallest_pos[1], "[", frs(smallest_pos[2]), ",", frs(smallest_pos[3]), "]")
    pr("smallest gap between consecutive cell endpoints (any):", frs(smallest[0]), smallest[1], frs(smallest[2]), frs(smallest[3]))
    # degenerate cells examples
    degs = [(r['D'], a) for r in res for a, b in r['cells'] if a == b]
    pr("degenerate cells total:", len(degs), "; first few:", [(d, frs(a)) for d, a in degs[:6]])
    lw = max(((b - a), r['D'], a, b) for r in res for a, b in r['cells'])
    pr("widest cell:", frs(lw[0]), lw[1], frs(lw[2]), frs(lw[3]))


def summarise2(N, res):
    pr = print
    pr(f"\n=== EXTRA TESTS N={N} ===")
    # (a) lowest-terms form of every endpoint: odd numerator, 8 | denominator, cofactors
    bad_odd = 0; bad8 = 0; cof_open = True; cof_entry = True; read_ok = True
    touch_pairs = Counter(); touch_ok = True; ntouch = 0
    cofcls_open = Counter(); cofcls_entry = Counter()
    for r in res:
        D = r['D']
        for (ci, ta, oa, ea, tb, ob, eb) in r['eps']:
            for t in (ta, tb):
                if t.numerator % 2 == 0: bad_odd += 1
                if t.denominator % 8: bad8 += 1
            p, q = ta.numerator, ta.denominator
            for (x, k) in oa:
                c = 8 * x // q
                if 8 * x % q or (c - p) % 8: cof_open = False
            for (y, k) in ea:
                c = 8 * y // q
                if 8 * y % q or (c + p) % 8: cof_entry = False
            # runners on an eighth: reading = c*p mod 8
            for z in D:
                if (8 * z) % q == 0:
                    c = 8 * z // q
                    u = (8 * z * ta) % 8
                    if u != (c * p) % 8: read_ok = False
            if ci >= 0 and ta == tb:
                ntouch += 1
                gx = {gcd(8 * k + 1, x) % 8 for (x, k) in oa}
                gy = {gcd(8 * k + 7, y) % 8 for (y, k) in ea}
                for a in gx:
                    for b in gy:
                        touch_pairs[(a, b)] += 1
                        if (a + b) % 8: touch_ok = False
    pr("endpoints with even reduced numerator:", bad_odd, "; with denominator not divisible by 8:", bad8)
    pr("opener cofactor c = 8x/q is an integer with c = p (mod 8), every instance:", cof_open)
    pr("entry cofactor c = 8y/q is an integer with c = -p (mod 8), every instance:", cof_entry)
    pr("reading (eighths) of every runner with q | 8z equals c*p mod 8, every instance:", read_ok)
    pr(f"touch points (degenerate cells): {ntouch}; (g_opener mod 8, g_entry mod 8) pairs:", dict(sorted(touch_pairs.items())), "; g_open + g_entry = 0 mod 8 always:", touch_ok)
    # (b) cell count vs multiples of 8, 4, 2 in D
    pr("\n-- cell count by m8 = #{d in D : 8 | d} (m8 : sets, min cells, max cells, sets with <4 cells) --")
    for m8 in range(0, 4):
        rs = [r for r in res if sum(1 for d in r['D'] if d % 8 == 0) == m8]
        if not rs: continue
        cn = [r['ncell'] for r in rs]
        pr(f"   m8={m8}: sets={len(rs)} min={min(cn)} max={max(cn)} <4:{sum(1 for c in cn if c < 4)}  sum/len={frs(F(sum(cn), len(cn)))}")
    low = [r for r in res if r['ncell'] < 4]
    pr("sets with fewer than 4 cells:", len(low), "; all contain a multiple of 8:", all(any(d % 8 == 0 for d in r['D']) for r in low))
    for r in low[:12]:
        pr("   ", r['D'], "cells:", [(frs(a), frs(b)) for a, b in r['cells']])
    no8 = [r for r in res if not any(d % 8 == 0 for d in r['D'])]
    pr("sets with no multiple of 8:", len(no8), "; min cells among them:", min(r['ncell'] for r in no8))
    four = 0; distinct4 = 0
    for r in no8:
        T = 8
        cells = r['cells']
        idx = []
        for a in (1, 3, 5, 7):
            t = F(a, 8)
            j = [i for i, (lo, hi) in enumerate(cells) if lo <= t <= hi]
            idx.append(j[0] if j else None)
        if None not in idx and len(set(idx)) == 4:
            distinct4 += 1
    pr("sets with no multiple of 8 in which 1/8,3/8,5/8,7/8 are lonely and lie in 4 distinct cells:", distinct4, "of", len(no8))
    # exceptions among no8
    exc = [r for r in no8 if not all(any(lo <= F(a, 8) <= hi for lo, hi in r['cells']) for a in (1, 3, 5, 7))]
    pr("   no-multiple-of-8 sets where some a/8 is NOT lonely (must be 0):", len(exc))
    merged = [r for r in no8 if r['ncell'] < 4]
    pr("   no-multiple-of-8 sets with <4 cells:", len(merged))
    # cells vs m4
    pr("\n-- cells by m4 = #{d : 4 | d} (m4: sets, min, max) --")
    for m4 in range(0, 6):
        rs = [r for r in res if sum(1 for d in r['D'] if d % 4 == 0) == m4]
        if not rs: continue
        cn = [r['ncell'] for r in rs]
        pr(f"   m4={m4}: sets={len(rs)} min={min(cn)} max={max(cn)}")
    # landing cell: degenerate? coincidences at landing
    land_deg = sum(1 for r in res if r['cells'][0][0] == r['cells'][0][1])
    pr("\nlanding (first) cell is a single point:", land_deg, "of", len(res))
    coinc = 0; intrep = 0; both = 0
    for r in res:
        us = [u for z, u in r['us']]
        c = len(set(us)) < len(us)
        ints = [u for u in us if u.denominator == 1]
        ir = len(set(ints)) < len(ints)
        coinc += c; intrep += ir
        if ir and not c: both += 1
    pr("sets with two runners at the same position at the landing instant:", coinc, "; integer-reading repeats:", intrep, "; repeats without coincidence (must be 0):", both)
    # opener at landing relative to d_min
    xmin = sum(1 for r in res if any(x == min(r['D']) for (x, k) in r['eps'][0][2]))
    pr("landing has an opener x = d_min:", xmin, "of", len(res))
    Rc = Counter(r['Rstar'] for r in res)
    pr("distinct R* values:", len(Rc), "; top 6 by size:", [(frs(k), Rc[k]) for k in sorted(Rc, reverse=True)[:6]], "; most common:", [(frs(k), v) for k, v in Rc.most_common(5)])
    top = sorted(res, key=lambda r: r['Rstar'], reverse=True)[:3]
    for r in top:
        D = r['D']; e0 = r['eps'][0]
        pr("   large R*:", D, "R* =", frs(r['Rstar']), "landing", frs(r['landing']), "openers", e0[2], "cells:", [(frs(a), frs(b)) for a, b in r['cells']])
    # cell separations (gap between consecutive cells)
    best = None
    for r in res:
        c = r['cells']
        for i in range(len(c) - 1):
            g = c[i + 1][0] - c[i][1]
            if best is None or g < best[0]:
                best = (g, r['D'], c[i][1], c[i + 1][0])
    pr("smallest gap between consecutive cells:", frs(best[0]), best[1], frs(best[2]), frs(best[3]))
    # all 8-divisible fraction check: cell endpoints denominators 8x/g
    dset = Counter()
    for r in res:
        for a, b in r['cells']:
            dset[a.denominator] += 1; dset[b.denominator] += 1
    pr("distinct endpoint denominators:", len(dset), "; all divisible by 8:", all(q % 8 == 0 for q in dset), "; max:", max(dset))


def summarise3(N, res):
    """Exact extremes against closed forms (observation; the closed forms are argued in the report)."""
    pr = print
    pr(f"\n=== EXTREMES vs CLOSED FORMS N={N} ===")
    minw = min((b - a, r['D']) for r in res for a, b in r['cells'] if b > a)
    best = max((x * y, x, y) for x in range(1, N + 1) for y in range(1, N + 1) if x != y and (x + y) % 8 == 7)
    pr("smallest positive cell width:", frs(minw[0]), minw[1], "; 1/(8xy) for the largest-product pair x != y <= N with x+y = 7 (mod 8):", frs(F(1, 8 * best[0])), best[1:])
    ming = min((c[i + 1][0] - c[i][1]) for r in res for c in [r['cells']] for i in range(len(c) - 1))
    pr("smallest gap between consecutive cells:", frs(ming), "; 1/(4N) =", frs(F(1, 4 * N)))
    ok = True; n_odd = 0
    for r in res:
        if r['half_expected']:
            n_odd += 1
            dm = max(r['D'])
            c = [(a, b) for a, b in r['cells'] if a <= F(1, 2) <= b][0]
            if c != (F(1, 2) - F(3, 8 * dm), F(1, 2) + F(3, 8 * dm)):
                ok = False
    pr(f"all-odd sets: {n_odd}; central cell equals [1/2 - 3/(8 d_max), 1/2 + 3/(8 d_max)] exactly in every one:", ok)
    # every cell width is m/(8xy) with m = -(x+y) mod 8 (opener x, entry y of the same cell)
    bad = 0; tot = 0
    for r in res:
        for (ci, ta, oa, ea, tb, ob, eb) in r['eps']:
            if ta == tb: continue
            for (x, k) in oa:
                for (y, k2) in eb:
                    m = (8 * k2 + 7) * x - (8 * k + 1) * y
                    tot += 1
                    if F(m, 8 * x * y) != tb - ta or (m + x + y) % 8: bad += 1
    pr("cell width = m/(8xy), m = (8k'+7)x - (8k+1)y = -(x+y) mod 8, over all (opener, entry) pairs of non-degenerate cells:", tot, "pairs, failures:", bad)


def show_special(name, D):
    r = analyse(tuple(D))
    print(f"\n### {name}: D = {D}")
    print("cells:", len(r['cells']), " degenerate:", r['ndeg'], " central:", r['ncentral'], " mirror ok:", r['mirror_ok'])
    for (ci, ta, oa, ea, tb, ob, eb) in r['eps']:
        print(f"  cell {ci}: [{frs(ta)}, {frs(tb)}]  left openings (x,k):{oa} left entries:{ea}  right entries (x,k):{eb} right openings:{ob}")
    print("landing t* =", frs(r['landing']), " R* =", frs(r['Rstar']))
    print("readings u_z (eighths) at landing:", [(z, frs(u)) for z, u in r['us']])


if __name__ == '__main__':
    Ns = [int(a) for a in sys.argv[1:]] or [14, 18, 22]
    show_special("AP (1..7)", [1, 2, 3, 4, 5, 6, 7])
    show_special("touch-only (1,2,3,4,5,7,12)", [1, 2, 3, 4, 5, 7, 12])
    show_special("touch-only (1,4,5,6,7,11,13)", [1, 4, 5, 6, 7, 11, 13])
    for N in Ns:
        res = run_pop(N)
        summarise(N, res)
        summarise2(N, res)
        summarise3(N, res)
