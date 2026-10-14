"""Task AP: the n = 8 structures of E434 to E442 compared, exactly, at other numbers of runners n.
Own-framework data at n runners: n-1 integer disparities D (gcd 1, entries <= N); runner d is clear at t iff
distInt(d t) >= 1/n; cascade (InWay with 1/n, nextOpening (k+1/n)/d, largest next opening) from 1/(n d_min);
R = n d_min t.  Nothing here uses a published proof of the lonely runner conjecture for any n, and nothing found
at another n is a step in the n = 8 proof.  Exact integers only (t = T/(n L), L = lcm(D)); no float, no random.
Every count is [OBS].  Usage: python3 across_n_v1.py [n ...]   (default 5 6 7 8 9 10)
"""
import sys, os
from math import gcd, lcm
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
from bisect import bisect_right
from multiprocessing import Pool

POP = {5: 40, 6: 30, 7: 24, 8: 22, 9: 18, 10: 16}


def units(n):
    return [a for a in range(1, n) if gcd(a, n) == 1]


def analyse(D, n):
    """Return a dict of exact observations for the disparity tuple D (sorted, gcd 1)."""
    dmin = D[0]
    L = lcm(*D)
    M = n * L
    iv = []
    for d in D:
        s = L // d
        step = n * s
        for j in range(d + 1):
            c = j * step
            iv.append((c - s, c + s))
    iv.sort()
    cells = []
    cur = iv[0][1]
    for a, b in iv[1:]:
        if a < cur:
            if b > cur:
                cur = b
        else:
            cells.append((cur, a))
            cur = b
    out = {}
    out['ncells'] = len(cells)
    out['npoint'] = sum(1 for s, e in cells if s == e)
    out['touch_only'] = len(cells) > 0 and all(s == e for s, e in cells)
    # mirror t -> 1 - t
    out['mirror_ok'] = sorted((M - e, M - s) for s, e in cells) == cells
    out['central'] = sum(1 for s, e in cells if s + e == M)

    def lonely(T):
        for d in D:
            r = (d * T) % M
            if r < L or r > M - L:
                return False
        return True

    # cascade
    T = L // dmin
    chain = []
    while True:
        inway = [d for d in D if ((d * T) % M) < L or ((d * T) % M) > M - L]
        if not inway:
            break
        best = None
        tied = []
        for d in inway:
            j = -((L - d * T) // M)  # ceil((d T - L)/M)
            nT = (j * M + L) // d
            assert (j * M + L) % d == 0
            if best is None or nT > best[0]:
                best = (nT, d, j)
                tied = [d]
            elif nT == best[0]:
                tied.append(d)
        chain.append((T, best[1], tuple(tied)))
        T = best[0]
    out['cascade_ok'] = bool(cells) and (T == cells[0][0])
    # n-general move formula in the gate coordinate: from R0 = 1 the move goes to 1 + max over blocked e of (1-delta_e)/rho_e
    # (rho = d/dmin, rho = n z + delta with |delta| < 1 blocked); compared with the cascade's first move
    if chain:
        Tnext = chain[1][0] if len(chain) > 1 else T
        mv = None
        for d in D:
            rho = F(d, dmin)
            z = round(rho / n)
            delta = rho - n * z
            if abs(delta) < 1:
                off = (1 - delta) / rho
                if mv is None or off > mv:
                    mv = off
        out['move_formula_ok'] = (mv is not None) and (1 + mv == F(dmin * Tnext, L))
    else:
        out['move_formula_ok'] = None
    out['chainlen'] = len(chain)
    if not cells:
        out['no_cells'] = True
        return out
    Ts = cells[0][0]
    Rstar = F(dmin * Ts, L)
    out['Rstar'] = Rstar
    out['tstar_le_half'] = 2 * Ts <= M
    out['tstar'] = F(Ts, M)
    # forbidden zone of d_min: |d - n j dmin| < dmin, j >= 1
    forb = []
    for d in D:
        j = 1
        while n * j * dmin - dmin < d:
            if abs(d - n * j * dmin) < dmin:
                forb.append(d)
                break
            j += 1
    out['forb'] = bool(forb)
    out['lap0'] = (Rstar == 1)
    if chain:
        out['firstsetter_in_forb_min'] = (min(forb) in chain[0][2]) if forb else None
        out['firstsetter_is_forb'] = (chain[0][1] in forb)
    # lap-0 landing iff no forbidden  (n-general landing_lap0_iff)
    out['lap0_iff_noforb'] = ((Rstar == 1) == (not forb))
    if dmin == 1:
        out['dmin1_lap0_iff_no_mult'] = ((Rstar == 1) == (not any(d % n == 0 for d in D)))
    # landing openers
    t = F(Ts, M)
    p, q = t.numerator, t.denominator
    out['p_mod_n'] = p % n
    openers = []
    for d in D:
        if (d * Ts) % M == L:
            k = (d * Ts) // M
            c = n * d // q
            assert n * d == q * c
            openers.append((d, k, c))
    out['openers'] = openers
    out['cp_ok'] = all(c * p == n * k + 1 for d, k, c in openers)
    out['c_inv_p'] = all((c * p) % n == 1 for d, k, c in openers)
    out['c_eq_p'] = all((c - p) % n == 0 for d, k, c in openers)
    out['n_div_q'] = (q % n == 0)
    out['rank1_lap_pos'] = (Rstar > 1) and any(d == dmin for d, k, c in openers)
    if Rstar < 2:
        out['sweepdown_viol'] = any((d - dmin) in D for d, k, c in openers)
    else:
        out['sweepdown_viol_ge2'] = any((d - dmin) in D for d, k, c in openers)
    # ties: at t = p/q, runner d opens iff d = m c, m p == 1 mod n  (c = q/n)
    cq = q // n
    ok_t = True
    for d in D:
        isop = ((d * Ts) % M == L)
        pred = (d % cq == 0) and (((d // cq) * p) % n == 1)
        if isop != pred:
            ok_t = False
    out['tie_rule'] = ok_t
    # units / no multiple of n
    nomult = not any(d % n == 0 for d in D)
    out['nomult'] = nomult
    if nomult:
        us = units(n)
        out['units_lonely'] = all(lonely(a * L) for a in us)
        # cells containing unit instants
        starts = [s for s, e in cells]
        ids = set()
        for a in us:
            T0 = a * L
            i = bisect_right(starts, T0) - 1
            if i >= 0 and cells[i][0] <= T0 <= cells[i][1]:
                ids.add(i)
        out['unit_cells'] = len(ids)
        out['nonunit_lonely'] = sum(1 for a in range(1, n) if gcd(a, n) > 1 and lonely(a * L))
        out['dmax_ge_half'] = (D[-1] * 2 >= n)
    else:
        out['mult_has_units_lonely'] = [a for a in units(n) if lonely(a * L)]
    # explicit instant R = a (a unit or any in 1..n-1)
    out['lonely_iff_not_dvd_bad'] = sum(1 for a in range(1, n) if lonely(a * L) != all((d * a) % n != 0 for d in D))
    expl_unit = False
    expl_any = False
    for a in range(1, n):
        # R = a  <=> T = a * L / dmin
        T0 = a * L // dmin
        if (a * L) % dmin == 0 and lonely(T0):
            expl_any = True
            if gcd(a, n) == 1:
                expl_unit = True
    out['expl_unit'] = expl_unit
    out['expl_any'] = expl_any
    # gate lemma: no lonely R in (n-1, n+1)  <=> T in ((n-1) L/dmin, (n+1) L/dmin)
    glo = F((n - 1) * L, dmin)
    ghi = F((n + 1) * L, dmin)
    out['gate_viol'] = any(F(s) < ghi and F(e) > glo for s, e in cells)
    # touch / width identities over cells
    wid_ok = 0
    wid_bad = 0
    touch_ok = 0
    touch_bad = 0
    ep_cp = 0
    ep_cp_bad = 0
    c_self = 0
    c_notself = 0
    ent_c_eq_neg = 0
    ent_bad = 0
    conj_ok = 0
    conj_bad = 0
    for s, e in cells:
        # left openers, right entries
        lop = []
        for d in D:
            if (d * s) % M == L:
                lop.append((d, (d * s) // M))
        ren = []
        for d in D:
            if (d * e) % M == M - L:
                ren.append((d, (d * e) // M))
        assert lop and ren
        for (x, k) in lop:
            for (y, k2) in ren:
                # width = ((n k2 + n - 1) x - (n k + 1) y)/(n x y)
                m = (n * k2 + n - 1) * x - (n * k + 1) * y
                if s == e:
                    if m == 0 and (x + y) % n == 0:
                        touch_ok += 1
                    else:
                        touch_bad += 1
                else:
                    if m > 0 and (m + x + y) % n == 0:
                        wid_ok += 1
                    else:
                        wid_bad += 1
        # cofactors at both endpoints
        for T0, kind in ((s, 'o'), (e, 'e')):
            tt = F(T0, M)
            pp, qq = tt.numerator, tt.denominator
            for d in D:
                r = (d * T0) % M
                if r == L or r == M - L:
                    c = n * d // qq
                    kk = (d * T0) // M
                    if r == L:
                        ok = (c * pp == n * kk + 1) and (c * pp) % n == 1
                        ep_cp += ok
                        ep_cp_bad += (not ok)
                        if (c - pp) % n == 0:
                            c_self += 1
                        else:
                            c_notself += 1
                    else:
                        ok = (c * pp == n * kk + n - 1) and (c * pp) % n == n - 1
                        ent_c_eq_neg += ok
                        ent_bad += (not ok)
            # whole-set conjugate: N = n q - 1, N t0 = -t0 mod 1 for every d
            Nn = n * qq - 1
            good = True
            for d in D:
                if (d * Nn * T0) % M != (-(d * T0)) % M:
                    good = False
            Tn = (Nn * T0) % M
            if good and (Tn % 1 == 0) and lonely(Tn if Tn != 0 else 0):
                conj_ok += 1
            else:
                conj_bad += 1
    out['wid'] = (wid_ok, wid_bad)
    out['touch'] = (touch_ok, touch_bad)
    out['ep_op'] = (ep_cp, ep_cp_bad)
    out['ep_en'] = (ent_c_eq_neg, ent_bad)
    out['c_self'] = (c_self, c_notself)
    out['conj'] = (conj_ok, conj_bad)
    out['cell_instants'] = tuple(F(s, M) for s, e in cells) if out['touch_only'] else None
    return out


def work(args):
    n, pre = args
    N = POP[n]
    k = n - 1
    res = Counter()
    ex = defaultdict(list)
    maxR_by_dmax = {}
    for rest in combinations(range(pre[-1] + 1, N + 1), k - len(pre)):
        D = pre + rest
        if gcd(*D) != 1:
            continue
        o = analyse(D, n)
        res['sets'] += 1
        if o.get('no_cells'):
            res['NO_CELLS'] += 1
            ex['no_cells'].append(D)
            continue
        if not o['cascade_ok']:
            res['CASCADE_MISMATCH'] += 1
            ex['cascade_mismatch'].append(D)
        if o['move_formula_ok'] is not None:
            res['move_formula_sets'] += 1
            res['move_formula_bad'] += (not o['move_formula_ok'])
        res[('chainlen', o['chainlen'])] += 1
        res[('ncells', o['ncells'])] += 1
        res[('npoint', o['npoint'])] += 1
        res['touch_only'] += o['touch_only']
        if o['touch_only']:
            ex['touch_only'].append((D, o['ncells'], tuple(str(x) for x in o['cell_instants'])))
        res['mirror_bad'] += (not o['mirror_ok'])
        res[('central', o['central'])] += 1
        res[('central_parity_bad')] += ((o['ncells'] - o['central']) % 2 != 0)
        R = o['Rstar']
        res['lap0'] += (R == 1)
        res['R_1_to_nm1'] += (1 < R <= n - 1)
        res['crosser'] += (R > n - 1)
        if R > n - 1:
            ex['crosser'].append((D, str(R)))
        if R == 1:
            pass
        key = D[-1]
        prev = maxR_by_dmax.get(key)
        if prev is None or R > prev[0]:
            maxR_by_dmax[key] = (R, D)
        res['tstar_gt_half'] += (not o['tstar_le_half'])
        res['forb'] += o['forb']
        res['lap0_iff_noforb_bad'] += (not o['lap0_iff_noforb'])
        if 'dmin1_lap0_iff_no_mult' in o:
            res['dmin1_sets'] += 1
            res['dmin1_lap0_iff_no_mult_bad'] += (not o['dmin1_lap0_iff_no_mult'])
        if 'firstsetter_in_forb_min' in o:
            res['moves_sets'] += 1
            res['firstsetter_is_forb_bad'] += (not o['firstsetter_is_forb'])
            if o['firstsetter_in_forb_min'] is False:
                res['firstsetter_not_least_forb'] += 1
                ex['firstsetter_not_least'].append(D)
        res[('p_mod_n', o['p_mod_n'])] += 1
        res['cp_bad'] += (not o['cp_ok'])
        res['c_inv_p_bad'] += (not o['c_inv_p'])
        res['c_eq_p'] += o['c_eq_p']
        res['c_neq_p'] += (not o['c_eq_p'])
        res['n_div_q_bad'] += (not o['n_div_q'])
        res['rank1_lap_pos'] += o['rank1_lap_pos']
        if o['rank1_lap_pos']:
            ex['rank1'].append((D, str(R)))
        if 'sweepdown_viol' in o:
            res['sweep_lt2_sets'] += 1
            res['sweep_lt2_viol'] += o['sweepdown_viol']
        if 'sweepdown_viol_ge2' in o:
            res['sweep_ge2_sets'] += 1
            res['sweep_ge2_viol'] += o['sweepdown_viol_ge2']
        res['tie_rule_bad'] += (not o['tie_rule'])
        res['nomult'] += o['nomult']
        if o['nomult']:
            res['units_lonely_bad'] += (not o['units_lonely'])
            res[('unit_cells', o['unit_cells'])] += 1
            res[('nonunit_lonely', o['nonunit_lonely'])] += 1
            if o['unit_cells'] < len(units(n)):
                ex['fewer_unit_cells'].append((D, o['unit_cells']))
        else:
            res[('mult_units_lonely', len(o['mult_has_units_lonely']))] += 1
        res['lonely_iff_not_dvd_bad'] += o['lonely_iff_not_dvd_bad']
        res['expl_unit'] += o['expl_unit']
        res['expl_any'] += o['expl_any']
        res['gate_viol'] += o['gate_viol']
        for nm in ('wid', 'touch', 'ep_op', 'ep_en', 'conj'):
            a, b = o[nm]
            res[nm + '_ok'] += a
            res[nm + '_bad'] += b
        res['c_self'] += o['c_self'][0]
        res['c_notself'] += o['c_self'][1]
        res['landing_has_touch_cell'] += 0
    for kk in list(ex):
        ex[kk] = ex[kk][:2000]
    return res, dict(ex), maxR_by_dmax


def run(n):
    N = POP[n]
    k = n - 1
    jobs = []
    for a in range(1, N + 1):
        for b in range(a + 1, N + 1):
            jobs.append((n, (a, b)))
    res = Counter()
    ex = defaultdict(list)
    mb = {}
    with Pool(10) as pool:
        for r, e, m in pool.imap_unordered(work, jobs, chunksize=1):
            res.update(r)
            for kk, v in e.items():
                ex[kk].extend(v)
            for dm, (R, D) in m.items():
                if dm not in mb or R > mb[dm][0]:
                    mb[dm] = (R, D)
    return res, ex, mb


def ap_report(n):
    D = tuple(range(1, n))
    o = analyse(D, n)
    return o


def show(n, res, ex, mb):
    N = POP[n]
    phi = len(units(n))
    print("=" * 100)
    print(f"n = {n}  ({n-1}-subsets of 1..{N}, gcd 1):  phi(n) = {phi},  units = {units(n)},  gate (n-1, n+1) = ({n-1}, {n+1})")
    print("=" * 100)
    print(f"[OBS] sets {res['sets']};  no lonely cell: {res['NO_CELLS']};  cascade != first lonely point: {res['CASCADE_MISMATCH']}")
    print(f"[OBS] chain length (moves) distribution: {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='chainlen')}")
    print(f"[OBS] cells per period: {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='ncells')}")
    print(f"[OBS] point cells per set: {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='npoint')}")
    print(f"[OBS] mirror t<->1-t fails: {res['mirror_bad']};  central cells per set: {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='central')};  (cells-central) odd: {res['central_parity_bad']}")
    s = res['sets']
    print(f"--- (1) units and totients")
    print(f"[OBS] sets with no multiple of n: {res['nomult']};  with a multiple of n: {s - res['nomult']}")
    print(f"[OBS] no multiple of n: unit instants a/n NOT all lonely in {res['units_lonely_bad']} sets (unit_lonely general: n | d a with a unit gives n | d)")
    print(f"[OBS] no multiple of n: distinct cells containing a unit instant, (cells : sets) {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='unit_cells')}   [phi(n) = {phi}]")
    print(f"[OBS] no multiple of n: lonely NON-unit instants a/n (a in 1..n-1, gcd(a,n)>1), (count : sets) {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='nonunit_lonely')}")
    print(f"[OBS] with a multiple of n: number of unit instants still lonely (count : sets) {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='mult_units_lonely')}")
    for D, c in ex.get('fewer_unit_cells', [])[:5]:
        print(f"   fewer than phi(n) unit cells: D={D} cells={c}")
    print(f"--- (3) landing")
    print(f"[OBS] R* = 1: {res['lap0']} ({res['lap0']/s:.6f});  R* in (1, n-1]: {res['R_1_to_nm1']};  crossers R* > n-1: {res['crosser']}")
    print(f"[OBS] landing lap above 0 iff a disparity in a forbidden zone of d_min: violations {res['lap0_iff_noforb_bad']}; sets with forbidden disparity {res['forb']}")
    print(f"[OBS] d_min = 1: {res['dmin1_sets']} sets; 'R*=1 iff no d = 0 mod n' violations {res['dmin1_lap0_iff_no_mult_bad']}")
    print(f"[OBS] gate lemma: lonely instant with R in (n-1, n+1): {res['gate_viol']} sets")
    print(f"[OBS] t* > 1/2: {res['tstar_gt_half']} sets")
    mx = max(mb.values(), key=lambda v: v[0])
    print(f"[OBS] largest R* over the population: {mx[0]} = {float(mx[0]):.4f} at D = {mx[1]}")
    print(f"[OBS] max R* among sets with d_max <= N': " + ", ".join(f"N'={x}:{max(v[0] for kk,v in mb.items() if kk<=x)}" for x in sorted({N//4, N//2, 3*N//4, N}) if any(kk<=x for kk in mb)))
    for D, R in ex.get('crosser', [])[:12]:
        print(f"   crosser D={D} R*={R}")
    if res['crosser']:
        cr = ex['crosser']
        print(f"   crossers listed {len(cr)} (cap 2000); min d_min among them {min(D[0] for D,_ in cr)}; max R* {max(F(R) for _,R in cr)}")
    print(f"[OBS] sets where R*>1 and d_min is itself a landing opener (rank 1 at lap above 0): {res['rank1_lap_pos']}")
    for D, R in ex.get('rank1', [])[:6]:
        print(f"   rank-1 D={D} R*={R}")
    print(f"[OBS] sweep-down (R*<2): {res['sweep_lt2_sets']} sets, opener x with x-d_min in D: {res['sweep_lt2_viol']};  (R*>=2: {res['sweep_ge2_sets']} sets, {res['sweep_ge2_viol']})")
    print(f"[OBS] first setter in forbidden zone: violations {res['firstsetter_is_forb_bad']} of {res['moves_sets']};  first setter is NOT the least forbidden disparity: {res['firstsetter_not_least_forb']}")
    for D in ex.get('firstsetter_not_least', [])[:4]:
        print(f"   first setter not least forbidden: D={D}")
    print(f"[OBS] first move = R0 + max over blocked e of (1-delta_e)/rho_e (R0 = 1, rho = d/d_min, delta signed residue of rho mod n): mismatches {res['move_formula_bad']} of {res['move_formula_sets']} sets with a move")
    print(f"[OBS] landing numerator classes p mod n (sets): {sorted((k[1], v) for k, v in res.items() if isinstance(k, tuple) and k[0]=='p_mod_n')}")
    print(f"[OBS] landing openers: c*p = nk+1 violations {res['cp_bad']};  c*p = 1 mod n violations {res['c_inv_p_bad']};  n | q violations {res['n_div_q_bad']};  all openers c = p mod n: {res['c_eq_p']} sets, some opener c != p mod n: {res['c_neq_p']} sets")
    print(f"[OBS] tie rule (d opens at t*=p/q iff d = m c, m p = 1 mod n; c = q/n) violations: {res['tie_rule_bad']}")
    print(f"[OBS] a/n lonely iff n does not divide d*a for every d (all a in 1..n-1, every set): mismatches {res['lonely_iff_not_dvd_bad']}")
    print(f"[OBS] explicit instant R = a (a unit mod n): {res['expl_unit']};  R = a (any a in 1..n-1, a | integrality): {res['expl_any']}  of {s}")
    print(f"--- (2)/(4) boundary identities over every cell endpoint of every set")
    print(f"[OBS] width identity n | (m + x + y), m>0, (opener,entry) pairs over positive-width cells: ok {res['wid_ok']}, bad {res['wid_bad']}")
    print(f"[OBS] touch (point cells): m = 0 and n | x + y, (opener,entry) pairs: ok {res['touch_ok']}, bad {res['touch_bad']}")
    print(f"[OBS] opener cofactor c: c p = nk+1 and c p = 1 mod n: ok {res['ep_op_ok']}, bad {res['ep_op_bad']};  entry cofactor c' p = nk'+n-1 and = -1 mod n: ok {res['ep_en_ok']}, bad {res['ep_en_bad']}")
    print(f"[OBS] opener cofactor c = p mod n: {res['c_self']} openers; c != p mod n: {res['c_notself']} openers")
    print(f"[OBS] whole-set conjugate N = n q - 1 (q = denominator of the endpoint): N t0 = -t0 mod 1 for every d and N t0 lonely: ok {res['conj_ok']}, bad {res['conj_bad']}")
    print(f"--- (2) touch-only sets (every cell a single point): {res['touch_only']}")
    to = ex.get('touch_only', [])
    inst_classes = Counter(x[2] for x in to)
    print(f"   cell-instant sets among touch-only: {len(inst_classes)} distinct; unit instants a/n = {[str(F(a, n)) for a in units(n)]}")
    for D, nc, ins in sorted(to)[:60]:
        print(f"   touch-only D={D}  cells={nc}  instants={list(ins)}")


def cells_of(D, n):
    L = lcm(*D)
    iv = []
    for d in D:
        s = L // d
        step = n * s
        for j in range(d + 1):
            c = j * step
            iv.append((c - s, c + s))
    iv.sort()
    cells = []
    cur = iv[0][1]
    for a, b in iv[1:]:
        if a < cur:
            if b > cur:
                cur = b
        else:
            cells.append((cur, a))
            cur = b
    return L, cells


def cascade_R(D, n):
    """R* = n d_min t* by the integer cascade (same as analyse, no cells)."""
    dmin = D[0]
    L = lcm(*D)
    M = n * L
    T = L // dmin
    while True:
        best = None
        for d in D:
            r = (d * T) % M
            if r < L or r > M - L:
                nT = (-((L - d * T) // M) * M + L) // d
                if best is None or nT > best:
                    best = nT
        if best is None:
            return F(dmin * T, L)
        T = best


def touch_work(args):
    n, N, pre = args
    out = []
    cnt = 0
    for rest in combinations(range(pre[-1] + 1, N + 1), n - 1 - len(pre)):
        D = pre + rest
        if gcd(*D) != 1:
            continue
        cnt += 1
        L, cells = cells_of(D, n)
        if cells and all(s == e for s, e in cells):
            M = n * L
            out.append((D, len(cells), tuple(str(F(s, M)) for s, e in cells)))
    return cnt, out


def cross_work(args):
    n, N, pre = args
    cnt = 0
    out = []
    mx = F(0)
    for rest in combinations(range(pre[-1] + 1, N + 1), n - 1 - len(pre)):
        D = pre + rest
        if gcd(*D) != 1:
            continue
        cnt += 1
        R = cascade_R(D, n)
        if R > mx:
            mx = R
        if R > n - 1:
            out.append((D, R))
    return cnt, out, mx


def extra_touch(n, N):
    jobs = [(n, N, (a, b)) for a in range(1, N + 1) for b in range(a + 1, N + 1)]
    tot = 0
    allo = []
    with Pool(10) as pool:
        for c, o in pool.imap_unordered(touch_work, jobs, chunksize=1):
            tot += c
            allo.extend(o)
    print(f"[OBS] touch-only search, n = {n}, all {n-1}-subsets of 1..{N}, gcd 1: {tot} sets; touch-only sets: {len(allo)}")
    for D, nc, ins in sorted(allo):
        print(f"   touch-only D={D}  cells={nc}  all cells at unit instants a/n: {all(gcd(F(i).numerator, n) == 1 and F(i).denominator == n for i in ins)}")


def extra_cross(n, N):
    jobs = [(n, N, (a, b)) for a in range(1, N + 1) for b in range(a + 1, N + 1)]
    tot = 0
    allo = []
    mx = F(0)
    with Pool(10) as pool:
        for c, o, m in pool.imap_unordered(cross_work, jobs, chunksize=1):
            tot += c
            allo.extend(o)
            if m > mx:
                mx = m
    print(f"[OBS] crosser search (cascade only), n = {n}, all {n-1}-subsets of 1..{N}, gcd 1: {tot} sets; max R* = {mx} = {float(mx):.4f}; crossers (R* > {n-1}): {len(allo)}")
    for D, R in sorted(allo)[:10]:
        print(f"   crosser D={D} R*={R}  d_min a landing opener (R* = 1 mod n): {(R - 1) % n == 0}  d_max/d_min = {F(D[-1], D[0])}  R*-(n+1) = {R - n - 1}")
    if allo:
        print(f"   crossers with R* = 1 mod n (d_min is the landing opener): {sum(1 for D, R in allo if (R - 1) % n == 0)} of {len(allo)}")
        print(f"   min d_min among crossers {min(D[0] for D, R in allo)}; max R* {max(R for D, R in allo)}")


def ap_table():
    print("=" * 100)
    print("AP (1..n-1) for n = 3..16, exact: lonely cells per period")
    for n in range(3, 17):
        D = tuple(range(1, n))
        L, cells = cells_of(D, n)
        M = n * L
        pts = [F(s, M) for s, e in cells if s == e]
        wide = [(F(s, M), F(e, M)) for s, e in cells if s != e]
        un = [F(a, n) for a in units(n)]
        print(f"n={n:2d} phi={len(units(n)):2d}  cells={len(cells):2d} points={len(pts):2d} wide={len(wide)}  point set == unit instants a/n: {sorted(pts)==un}   n | 24: {24 % n == 0}   units self-inverse: {all((a*a) % n == 1 for a in units(n))}")
        if wide:
            print("    wide cells:", [(str(a), str(b)) for a, b in wide])


def examples():
    print("=" * 100)
    print("Exact examples of an opener cofactor c with c != p mod n (c p = 1 mod n, p^2 != 1 mod n)")
    for n, N in [(5, 14), (7, 14), (9, 14), (10, 14)]:
        found = 0
        for D in combinations(range(1, N + 1), n - 1):
            if gcd(*D) != 1:
                continue
            o = analyse(D, n)
            if not o['c_eq_p']:
                d, k, c = o['openers'][0]
                t = o['tstar']
                print(f"   n={n}: D={D} t*={t} = p/q with p={t.numerator}, q={t.denominator}; opener x={d} lap k={k} cofactor c={c}; c*p={c*t.numerator}=n*k+1={n*k+1}; p mod n={t.numerator % n}, c mod n={c % n}")
                found += 1
                if found >= 2:
                    break


def anchors():
    print("=" * 100)
    print("Anchors at n = 8 (E434 crossers, integer cascade re-run through analyse/cascade_R)")
    for D in [(6, 16, 21, 26, 29, 36, 45), (6, 16, 21, 26, 29, 37, 46), (6, 18, 23, 29, 32, 40, 50), (7, 17, 22, 29, 36, 40, 51)]:
        o = analyse(D, 8)
        print(f"   D={D}: R* (cells) = {o['Rstar']}, R* (cascade) = {cascade_R(D, 8)}, cascade_ok={o['cascade_ok']}")


EXTRA_TOUCH = {5: 80, 6: 50, 7: 40, 9: 28, 10: 24}
EXTRA_CROSS = {5: 250, 6: 80, 7: 58, 9: 40, 10: 36}


def main():
    args = sys.argv[1:]
    if args and args[0] == 'extra':
        ap_table()
        anchors()
        examples()
        print("=" * 100)
        for n in [5, 6, 7, 9, 10]:
            extra_touch(n, EXTRA_TOUCH[n])
            sys.stdout.flush()
        print("=" * 100)
        for n in [5, 6, 7, 9, 10]:
            extra_cross(n, EXTRA_CROSS[n])
            sys.stdout.flush()
        return
    ns = [int(a) for a in args] or [5, 6, 7, 8, 9, 10]
    print("across_n_v1.py: exact; populations", {n: POP[n] for n in ns})
    for n in ns:
        res, ex, mb = run(n)
        show(n, res, ex, mb)
        sys.stdout.flush()


if __name__ == '__main__':
    main()
