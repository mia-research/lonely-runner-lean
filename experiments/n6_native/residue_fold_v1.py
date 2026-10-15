#!/usr/bin/env python3
"""residue_fold_v1 -- observation only.

Residue-isolation arrangements at orders n = 3..7 and the straight-line path from the
AP (1..n-1) in speed space.  Exact Fraction arithmetic throughout.

Notation.  Arrangement d indexed by residue: d[r-1] = r (mod n), r = 1..n-1.
a_i = i (the AP runner with the same position at every p/n), m_i = (d_i - a_i)/n,
c_i = n*m_i.  Path v(s) = a + s*c, s in [0,1].

METHOD (exact component labelling).  At a lonely point (s,t), t>0, each unwrapped
reading u_i = v_i(s)*t lies in a unique block [k_i + 1/n, k_i + 1 - 1/n]; the vector
K = (k_i) is the winding label.  Points with distinct labels lie in disjoint closed
sets (blocks are separated by gaps of width 2/n), so a connected piece of the lonely
region carries one label.  For a fixed label K the lonely set is
    { (s,t) : max_i (n k_i+1)/(n v_i(s)) <= t <= min_i (n k_i+n-1)/(n v_i(s)) },
nonempty at s iff (n k_i+1) v_j(s) <= (n k_j+n-1) v_i(s) for all i != j.  Each such
condition is linear in s, so the set of s is an interval computed exactly, and over
that interval the cell is the region between two continuous graphs.  The script
cross-checks this labelling against (a) an s-grid with exact lonely t-intervals and
(b) direct reading checks at sampled points.
"""
from fractions import Fraction as F
from math import gcd, floor, factorial
from functools import reduce
import itertools, random, sys

random.seed(20261016)
BOUNDS = {3: 60, 4: 50, 5: 40, 6: 40, 7: 28}
GRID_A = 64          # s-grid for the naive overlap test and slot tracking
GRID_B = 256         # second resolution for the naive overlap test
SAMPLE_NAIVE = 150   # arrangements per order sampled for the grid tests
T_WIN = F(1)         # t-window [0, 1]

def units(n):
    return [p for p in range(1, n) if gcd(p, n) == 1]

def frac(x):
    return x - floor(x)

def lonely_direct(v, t, n):
    lo, hi = F(1, n), 1 - F(1, n)
    return all(lo <= frac(vi * t) <= hi for vi in v)

def label(v, t):
    return tuple(floor(vi * t) for vi in v)

# ---------- exact cell machinery ----------
def cone_ok(v, K, n):
    """label-K cell nonempty at speed vector v (all positive)."""
    N = len(v)
    for i in range(N):
        li = n * K[i] + 1
        for j in range(N):
            if i != j and li * v[j] > (n * K[j] + n - 1) * v[i]:
                return False
    return True

def seg_interval(A, B, K, n):
    """exact s-interval in [0,1] where label-K cell nonempty along v=A+s(B-A)."""
    lo, hi = F(0), F(1)
    N = len(A)
    D = [B[i] - A[i] for i in range(N)]
    for i in range(N):
        li = n * K[i] + 1
        for j in range(N):
            if i == j:
                continue
            uj = n * K[j] + n - 1
            al = li * A[j] - uj * A[i]
            be = li * D[j] - uj * D[i]
            if be == 0:
                if al > 0:
                    return None
            elif be > 0:
                x = F(-al, be)
                if x < hi: hi = x
            else:
                x = F(-al, be)
                if x > lo: lo = x
    if lo > hi:
        return None
    return lo, hi

def cell_t(v, K, n):
    L = max(F(n * K[i] + 1, n) / v[i] for i in range(len(v)))
    U = min(F(n * K[i] + n - 1, n) / v[i] for i in range(len(v)))
    return L, U

def speeds(a, c, s):
    return [a[i] + s * c[i] for i in range(len(a))]

def envelope_events(g0, gs, s0, s1, want_min):
    """argmin (want_min) or argmax of lines g0[i]+s*gs[i] on [s0,s1]; returns list of (s, runner)."""
    N = len(g0)
    def val(i, s): return g0[i] + s * gs[i]
    def pick(s):
        vals = [val(i, s) for i in range(N)]
        best = min(vals) if want_min else max(vals)
        cand = [i for i in range(N) if vals[i] == best]
        # tie-break by slope in the direction of travel
        return min(cand, key=lambda i: gs[i]) if want_min else max(cand, key=lambda i: gs[i])
    out = []
    s = s0
    cur = pick(s)
    out.append((s, cur))
    while True:
        nxt = None
        for j in range(N):
            if j == cur: continue
            ds = gs[j] - gs[cur]
            if (want_min and ds < 0) or ((not want_min) and ds > 0):
                x = (g0[cur] - g0[j]) / ds
                if x > s and x <= s1 and (nxt is None or x < nxt[0]):
                    nxt = (x, j)
        if nxt is None:
            break
        s = nxt[0]
        cur = pick(s)  # re-pick with slope tie-break
        out.append((s, cur))
    return out

def collisions(a, c):
    out = []
    N = len(a)
    for i in range(N):
        for j in range(i + 1, N):
            if c[i] != c[j]:
                s = F(a[j] - a[i], c[i] - c[j])
                if 0 < s <= 1:
                    out.append((s, i, j))
    return sorted(out)

# ---------- grid / interval machinery ----------
def runner_intervals(v, n, T):
    out = []
    k = 0
    while True:
        lo = (k + F(1, n)) / v
        if lo > T:
            break
        hi = (k + 1 - F(1, n)) / v
        out.append((lo, min(hi, T)))
        k += 1
    return out

def intersect(A, B):
    i = j = 0
    out = []
    while i < len(A) and j < len(B):
        lo = max(A[i][0], B[j][0]); hi = min(A[i][1], B[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return out

def lonely_intervals(v, n, T):
    res = None
    for vi in v:
        iv = runner_intervals(vi, n, T)
        res = iv if res is None else intersect(res, iv)
        if not res:
            return []
    return res

def in_intervals(iv, t):
    return any(lo <= t <= hi for lo, hi in iv)

# ---------- enumeration ----------
def arrangements(n, B):
    lists = [[x for x in range(r, B + 1, n)] for r in range(1, n)]
    ap = tuple(range(1, n))
    for d in itertools.product(*lists):
        if d == ap:
            continue
        if reduce(gcd, d) != 1:
            continue
        yield d

# ---------- per-arrangement analysis ----------
def analyse(n, d, p):
    N = n - 1
    a = list(range(1, n))
    m = [(d[i] - a[i]) // n for i in range(N)]
    c = [n * x for x in m]
    K0 = tuple((a[i] * p) // n for i in range(N))
    Kd = tuple((d[i] * p) // n for i in range(N))
    rec = {'n': n, 'd': d, 'p': p, 'm': m, 'K0': K0, 'Kd': Kd}
    fw = seg_interval(a, list(d), K0, n)
    assert fw is not None and fw[0] == 0
    rec['s_hi'] = fw[1]
    rec['fw_reach'] = (fw[1] == 1)
    vend = speeds(a, c, fw[1])
    L, U = cell_t(vend, K0, n)
    rec['end_t'] = (L, U)
    if rec['fw_reach']:
        qs = [q for q in range(1, n * 2 * max(d)) if gcd(q, n) == 1 and L <= F(q, n) <= U]
        rec['end_unit_instants'] = qs
        rec['end_at_pn'] = (L <= F(p, n) <= U)
    bw = seg_interval(a, list(d), Kd, n)
    assert bw is not None and bw[1] == 1
    rec['s_lo_back'] = bw[0]
    rec['bw_reach'] = (bw[0] == 0)
    if rec['bw_reach']:
        L0, U0 = cell_t(a, Kd, n)
        rec['back_t0'] = (L0, U0)
    rec['collisions'] = collisions(a, c)
    rec['coll_in_fw'] = [x for x in rec['collisions'] if x[0] <= fw[1]]
    # exact flank boundaries along the forward cell: entry = argmin g_i, exit = argmax h_i
    g0 = [F(a[i], n * K0[i] + 1) for i in range(N)]; gs = [F(c[i], n * K0[i] + 1) for i in range(N)]
    h0 = [F(a[i], n * K0[i] + n - 1) for i in range(N)]; hs = [F(c[i], n * K0[i] + n - 1) for i in range(N)]
    rec['entry_events'] = envelope_events(g0, gs, F(0), fw[1], True)
    rec['exit_events'] = envelope_events(h0, hs, F(0), fw[1], False)
    return rec

def slot_track(n, d, p, s_hi, grid):
    """midpoint path t(s) = (L+U)/2 of the label-K0 cell at grid s <= s_hi and at s_hi."""
    N = n - 1
    a = list(range(1, n)); c = [d[i] - a[i] for i in range(N)]
    K0 = tuple((a[i] * p) // n for i in range(N))
    ss = sorted(set([F(j, grid) for j in range(grid + 1) if F(j, grid) <= s_hi] + [s_hi]))
    rows = []
    for s in ss:
        v = speeds(a, c, s)
        L, U = cell_t(v, K0, n)
        t = (L + U) / 2
        r = [frac(v[i] * t) for i in range(N)]
        ties = any((n * x - F(1, 2)) == floor(n * x) for x in r)
        sl = tuple(round(n * x) for x in r)
        mn = min(r); mx = max(r)
        entry = tuple(i for i in range(N) if r[i] == mn)
        exitf = tuple(i for i in range(N) if r[i] == mx)
        rows.append((s, t, sl, entry, exitf, ties, len(set(sl)) < N, label(v, t) == K0))
    return rows

# ---------- main ----------
def fmt(x):
    return str(x)

def main():
    out = []
    P = out.append
    P("residue_fold_v1 -- straight-line path from the AP to residue-isolation arrangements")
    P("bounds (entries <= B): " + ", ".join(f"n={n}: B={B}" for n, B in BOUNDS.items()))
    P(f"t-window for grid tests: [0, {T_WIN}];  s-grids: {GRID_A} and {GRID_B} steps;  naive-test sample: {SAMPLE_NAIVE} arrangements per order (seeded)")
    P("")
    summaries = {}
    controls = {'gi_checked': 0, 'gi_pass': 0, 'ap_gi_pass': 0,
                'cell_pts': 0, 'cell_pts_ok': 0, 'cell_beyond': 0, 'cell_beyond_ok': 0,
                'win_t_pts': 0, 'win_t_agree': 0, 'grid_label_pts': 0, 'grid_label_agree': 0,
                'fw_t_le_pn': 0, 'fw_t_le_pn_ok': 0,
                'leg_checks': 0, 'leg_agree': 0}
    examples_wanted = {(6, (1, 2, 3, 4, 11)), (6, (1, 2, 3, 4, 35))}
    stored = {}
    for n, B in BOUNDS.items():
        N = n - 1
        U_ = units(n)
        arrs = list(arrangements(n, B))
        S = {'arr': len(arrs), 'pairs': 0, 'fw_reach': 0, 'fw_reach_at_pn': 0, 'fw_reach_unit': 0,
             'fw_reach_offgrid': 0, 'fw_reach_degenerate': 0, 'fw_die': 0, 'die_at_0': 0,
             'die_hist': {}, 'bw_reach': 0, 'bw_q': {}, 'coll_any': 0, 'coll_in_fw': 0,
             'entry_handover': 0, 'exit_handover': 0,
             'slot_const': 0, 'slot_change': 0, 'slot_share': 0, 'flank_change': 0, 'slot_ties': 0,
             'slot_tracked': 0,
             't4_tried': 0, 't4_orders_total': 0, 't4_orders_connect': 0, 't4_any_connect': 0,
             't4_maxdepth': {}, 't4b_any_connect': 0, 't4b_tried': 0,
             'per_p': {p: [0, 0] for p in U_}}
        sample = set(random.sample(range(len(arrs)), min(SAMPLE_NAIVE, len(arrs))))
        naive = {'pairs': 0, 'A': {'reach_pn': 0, 'reach_other': 0, 'die': 0, 'die_at_first': 0},
                 'B': {'reach_pn': 0, 'reach_other': 0, 'die': 0, 'die_at_first': 0},
                 'agree_exact_A': 0, 'agree_exact_B': 0}
        for idx, d in enumerate(arrs):
            a = list(range(1, n)); m = [(d[i] - a[i]) // n for i in range(N)]; c = [n * x for x in m]
            # control: global isolation at endpoints
            for p in U_:
                controls['gi_checked'] += 1
                rd = [frac(F(d[i] * p, n)) for i in range(N)]
                ok = all((n * x).denominator == 1 for x in rd) and lonely_direct(d, F(p, n), n) \
                    and len(set(rd)) == N and rd == [frac(F(a[i] * p, n)) for i in range(N)]
                controls['gi_pass'] += ok
            for p in U_:
                S['pairs'] += 1
                rec = analyse(n, d, p)
                if (n, d) in examples_wanted or (n == 3 and d == (4, 2) ):
                    stored[(n, d, p)] = rec
                S['per_p'][p][0 if rec['fw_reach'] else 1] += 1
                if rec['fw_reach']:
                    S['fw_reach'] += 1
                    L, U = rec['end_t']
                    if rec['end_at_pn']: S['fw_reach_at_pn'] += 1
                    if L == U: S['fw_reach_degenerate'] += 1
                    if rec['end_unit_instants']: S['fw_reach_unit'] += 1
                    else: S['fw_reach_offgrid'] += 1
                    if 'reach_ex' not in S: S['reach_ex'] = rec
                else:
                    S['fw_die'] += 1
                    if rec['s_hi'] == 0: S['die_at_0'] += 1
                    b = 0 if rec['s_hi'] == 0 else min(9, int(rec['s_hi'] * 10))
                    S['die_hist'][b] = S['die_hist'].get(b, 0) + 1
                    if rec['s_hi'] > 0 and 'die_ex' not in S: S['die_ex'] = rec
                if rec['bw_reach']:
                    S['bw_reach'] += 1
                    L0, U0 = rec['back_t0']
                    key = (str(L0), str(U0))
                    S['bw_q'][(p, key)] = S['bw_q'].get((p, key), 0) + 1
                    if 'bw_ex' not in S: S['bw_ex'] = rec
                if rec['collisions']: S['coll_any'] += 1
                if rec['coll_in_fw']: S['coll_in_fw'] += 1
                if len(rec['entry_events']) > 1: S['entry_handover'] += 1
                if len(rec['exit_events']) > 1: S['exit_handover'] += 1
                # control: forward cell lies in t <= p/n (window [0,1] suffices)
                controls['fw_t_le_pn'] += 1
                controls['fw_t_le_pn_ok'] += (rec['end_t'][1] <= F(p, n))
                # control: random points inside the forward cell are lonely with label K0;
                # points just beyond s_hi have an empty K0 cell
                if rec['s_hi'] > 0:
                    s = rec['s_hi'] * F(random.randint(0, 1000), 1000)
                    v = speeds(a, c, s); L, U = cell_t(v, rec['K0'], n)
                    t = L + (U - L) * F(random.randint(0, 1000), 1000)
                    controls['cell_pts'] += 1
                    controls['cell_pts_ok'] += (L <= U and lonely_direct(v, t, n) and label(v, t) == rec['K0'])
                if rec['s_hi'] < 1:
                    s = rec['s_hi'] + (1 - rec['s_hi']) * F(1, 997)
                    v = speeds(a, c, s); L, U = cell_t(v, rec['K0'], n)
                    controls['cell_beyond'] += 1
                    controls['cell_beyond_ok'] += (L > U)
                # slots along the midpoint path (task 3)
                rows = slot_track(n, d, p, rec['s_hi'], GRID_A)
                S['slot_tracked'] += 1
                sls = set(r[2] for r in rows)
                if len(sls) == 1: S['slot_const'] += 1
                else: S['slot_change'] += 1
                if any(r[6] for r in rows): S['slot_share'] += 1
                if len(set((r[3], r[4]) for r in rows)) > 1: S['flank_change'] += 1
                if any(r[5] for r in rows): S['slot_ties'] += 1
                if (n, d) in examples_wanted:
                    stored[(n, d, p, 'rows')] = rows
                # task 4: one-runner-at-a-time ramps, every order of runners with m_i > 0
                R = [i for i in range(N) if m[i] > 0]
                def vert(Sset):
                    return [a[i] + (c[i] if i in Sset else 0) for i in range(N)]
                for direction, K, tag in ((0, rec['K0'], 't4'), (1, rec['Kd'], 't4b')):
                    reached = rec['fw_reach'] if direction == 0 else rec['bw_reach']
                    if reached:
                        continue
                    S[tag + '_tried'] += 1
                    feas = {}
                    for r in range(len(R) + 1):
                        for comb in itertools.combinations(R, r):
                            feas[frozenset(comb)] = cone_ok(vert(set(comb)), K, n)
                    # leg full iff both vertices feasible (each constraint linear in s along a leg);
                    # cross-check on a sample with the exact interval routine
                    if random.random() < 0.02:
                        for r in range(len(R)):
                            for comb in itertools.combinations(R, r):
                                for i in R:
                                    if i in comb: continue
                                    A = vert(set(comb)); Bv = vert(set(comb) | {i})
                                    iv = seg_interval(A, Bv, K, n)
                                    full = iv is not None and iv[0] == 0 and iv[1] == 1
                                    controls['leg_checks'] += 1
                                    controls['leg_agree'] += (full == (feas[frozenset(comb)] and feas[frozenset(comb) | {i}]))
                    # start vertex: direction 0 starts at AP (empty set); direction 1 starts at d (full set)
                    start = frozenset() if direction == 0 else frozenset(R)
                    ways = {start: 1 if feas[start] else 0}
                    order = sorted(feas.keys(), key=len, reverse=(direction == 1))
                    maxdepth = 0
                    for Sset in order:
                        w = ways.get(Sset, 0)
                        if not w: continue
                        maxdepth = max(maxdepth, abs(len(Sset) - len(start)))
                        nbrs = [Sset | {i} for i in R if i not in Sset] if direction == 0 else [Sset - {i} for i in Sset]
                        for T in nbrs:
                            if feas[T]:
                                ways[T] = ways.get(T, 0) + w
                    end = frozenset(R) if direction == 0 else frozenset()
                    if direction == 0:
                        S['t4_orders_total'] += factorial(len(R))
                        S['t4_orders_connect'] += ways.get(end, 0)
                        S['t4_any_connect'] += (ways.get(end, 0) > 0)
                        S['t4_maxdepth'][(maxdepth, len(R))] = S['t4_maxdepth'].get((maxdepth, len(R)), 0) + 1
                    else:
                        S['t4b_any_connect'] += (ways.get(end, 0) > 0)
                # naive grid test (task 2 as specified) on the sample
                if idx in sample:
                    naive['pairs'] += 1
                    for G, key in ((GRID_A, 'A'), (GRID_B, 'B')):
                        comp = [(F(p, n), F(p, n))]
                        died = None
                        for j in range(1, G + 1):
                            s = F(j, G)
                            v = speeds(a, c, s)
                            iv = lonely_intervals(v, n, T_WIN)
                            # controls: interval routine vs direct checks
                            if G == GRID_A:
                                for _ in range(2):
                                    t = F(random.randint(1, 100003), 100003)
                                    controls['win_t_pts'] += 1
                                    controls['win_t_agree'] += (in_intervals(iv, t) == lonely_direct(v, t, n))
                                for lo, hi in iv[:3]:
                                    controls['win_t_pts'] += 2
                                    controls['win_t_agree'] += lonely_direct(v, lo, n) + lonely_direct(v, (lo + hi) / 2, n)
                                # label check: an interval with label K0 exists iff s <= s_hi
                                has = any(label(v, (lo + hi) / 2) == rec['K0'] for lo, hi in iv)
                                controls['grid_label_pts'] += 1
                                controls['grid_label_agree'] += (has == (s <= rec['s_hi']))
                            new = [x for x in iv if any(max(x[0], y[0]) <= min(x[1], y[1]) for y in comp)]
                            if not new:
                                died = s
                                break
                            comp = new
                        if died is None:
                            if any(lo <= F(p, n) <= hi for lo, hi in comp): naive[key]['reach_pn'] += 1
                            else: naive[key]['reach_other'] += 1
                            naive['agree_exact_' + key] += rec['fw_reach']
                        else:
                            naive[key]['die'] += 1
                            if died == F(1, G): naive[key]['die_at_first'] += 1
                            naive['agree_exact_' + key] += (not rec['fw_reach'])
        # AP itself: global isolation
        for p in U_:
            ap = list(range(1, n))
            controls['ap_gi_pass'] += lonely_direct(ap, F(p, n), n)
        S['naive'] = naive
        summaries[n] = S

    # ---------- report ----------
    for n, S in summaries.items():
        P("=" * 78)
        P(f"ORDER n={n}   B={BOUNDS[n]}   arrangements (primitive, AP excluded) = {S['arr']}   units p = {units(n)}   (arrangement, p) pairs = {S['pairs']}")
        P("-- Task 2 (exact label-cell method; no grid) --")
        P(f"  forward component from (s=0, t=p/n) reaches s=1           : {S['fw_reach']}")
        P(f"     of which contains (1, p/n)                              : {S['fw_reach_at_pn']}")
        P(f"     of which s=1 t-set contains some unit instant q/n       : {S['fw_reach_unit']}")
        P(f"     of which s=1 t-set contains no q/n with gcd(q,n)=1      : {S['fw_reach_offgrid']}")
        P(f"     of which s=1 t-set is a single point                    : {S['fw_reach_degenerate']}")
        P(f"  forward component dies before s=1                         : {S['fw_die']}")
        P(f"     of which dies at s=0 (component is the single point)    : {S['die_at_0']}")
        P(f"     death s histogram (bin 0 = exactly 0, bin k = [k/10,(k+1)/10)) : {dict(sorted(S['die_hist'].items()))}")
        P(f"  per p: [reach, die] = {S['per_p']}")
        P(f"  backward component from (s=1, t=p/n) reaches s=0          : {S['bw_reach']}")
        if S['bw_q']:
            P(f"     AP t-set at s=0 for those, by (p, [L,U]) : {dict(sorted(S['bw_q'].items(), key=lambda kv: -kv[1])[:12])}")
        P(f"  pairs with a speed collision on s in (0,1]                : {S['coll_any']}")
        P(f"  pairs with a collision inside the forward component       : {S['coll_in_fw']}")
        P(f"  pairs with an exact entry-flank handover in the component : {S['entry_handover']}")
        P(f"  pairs with an exact exit-flank handover in the component  : {S['exit_handover']}")
        nv = S['naive']
        P(f"-- Task 2 (naive grid overlap test, sample of {nv['pairs']} pairs, window [0,1]) --")
        for key, G in (('A', GRID_A), ('B', GRID_B)):
            x = nv[key]
            P(f"  grid {G:4d}: reach s=1 with p/n in set {x['reach_pn']}, reach s=1 elsewhere {x['reach_other']}, die {x['die']} (die at first step s=1/{G}: {x['die_at_first']});  reach/die agrees with exact method: {nv['agree_exact_' + key]}/{nv['pairs']}")
        P("-- Task 3 (slot picture along midpoint path t(s)=(L+U)/2 of the K0 cell, grid 1/64 plus s_hi) --")
        P(f"  pairs tracked {S['slot_tracked']}: slot vector constant {S['slot_const']}, changes {S['slot_change']}, two runners share a slot {S['slot_share']}, flank runner changes {S['flank_change']}, a reading at a half-slot tie {S['slot_ties']}")
        P("-- Task 4 (one m_i at a time, every order of runners with m_i>0; label kept) --")
        P(f"  forward (from (AP,p/n)) tried {S['t4_tried']} pairs where the straight line dies; orders tried {S['t4_orders_total']}; orders that reach d {S['t4_orders_connect']}; pairs with >=1 connecting order {S['t4_any_connect']}")
        md = {}
        for (dep, r), cnt in S['t4_maxdepth'].items():
            md[f"{dep}/{r}"] = md.get(f"{dep}/{r}", 0) + cnt
        P(f"  forward: deepest vertex reached (ramped runners / runners with m>0) : {dict(sorted(md.items()))}")
        P(f"  backward (from (d,p/n) toward AP) tried {S['t4b_tried']}; pairs with >=1 connecting order {S['t4b_any_connect']}")
        for k in ('reach_ex', 'die_ex', 'bw_ex'):
            if k in S:
                r = S[k]
                P(f"  sample {k}: d={r['d']} p={r['p']} m={r['m']} K0={r['K0']} s_hi={r['s_hi']} end_t={tuple(map(str, r['end_t']))} s_lo_back={r['s_lo_back']}"
                  + (f" back_t0={tuple(map(str, r['back_t0']))} Kd={r['Kd']}" if r.get('bw_reach') else ""))
    P("=" * 78)
    P("CONTROLS")
    P(f"  global isolation at endpoints: lonely at p/n, readings on slot points, distinct, equal to AP readings: {controls['gi_pass']}/{controls['gi_checked']}")
    P(f"  AP lonely at every unit p/n: {controls['ap_gi_pass']}/{sum(len(units(n)) for n in BOUNDS)}")
    P(f"  forward cell upper bound <= p/n (so window [0,1] holds the tracked component): {controls['fw_t_le_pn_ok']}/{controls['fw_t_le_pn']}")
    P(f"  random points inside forward cell lonely with label K0 (direct check): {controls['cell_pts_ok']}/{controls['cell_pts']}")
    P(f"  K0 cell empty at s = s_hi + (1-s_hi)/997: {controls['cell_beyond_ok']}/{controls['cell_beyond']}")
    P(f"  lonely-interval routine vs direct reading check (random t, interval endpoints, midpoints): {controls['win_t_agree']}/{controls['win_t_pts']}")
    P(f"  grid label check (an interval labelled K0 exists at grid s iff s <= s_hi): {controls['grid_label_agree']}/{controls['grid_label_pts']}")
    P(f"  task-4 legs: exact interval routine vs vertex test: {controls['leg_agree']}/{controls['leg_checks']}")

    # ---------- written-out examples ----------
    P("=" * 78)
    P("WORKED EXAMPLES")
    def show(n, d, p):
        rec = analyse(n, d, p)
        N = n - 1
        a = list(range(1, n))
        P("-" * 78)
        P(f"n={n}  d={d}  p={p}  a={tuple(a)}  m={tuple(rec['m'])}  path v(s)=a+s*n*m = " +
          ", ".join(f"{a[i]}+{n*rec['m'][i]}s" if rec['m'][i] else f"{a[i]}" for i in range(N)))
        P(f"  readings at s=0, t=p/n: {[str(frac(F(a[i]*p, n))) for i in range(N)]}  -> label K0 = floor(a_i p/n) = {rec['K0']}")
        P(f"  label at s=1, t=p/n: Kd = floor(d_i p/n) = {rec['Kd']}")
        P(f"  forward component s-interval [0, {rec['s_hi']}]; at s_hi the K0 cell t-set = [{rec['end_t'][0]}, {rec['end_t'][1]}]")
        P(f"  entry flank (runner index i, a_i=i+1) by exact envelope: {[(str(s), i + 1) for s, i in rec['entry_events']]}")
        P(f"  exit flank by exact envelope: {[(str(s), i + 1) for s, i in rec['exit_events']]}")
        P(f"  collisions (s, a_i, a_j): {[(str(s), i + 1, j + 1) for s, i, j in rec['collisions']]}")
        P(f"  backward component from (1,p/n): s-interval [{rec['s_lo_back']}, 1]" +
          (f"; reaches AP at t-set [{rec['back_t0'][0]}, {rec['back_t0'][1]}]" if rec['bw_reach'] else ""))
        rows = slot_track(n, d, p, rec['s_hi'], 8)
        for s, t, sl, en, ex, ti, sh, lab in rows:
            v = speeds(a, [n * x for x in rec['m']], s)
            P(f"    s={str(s):>8}  t={str(t):>14}  readings={[str(frac(v[i]*t)) for i in range(N)]}  slots={sl}  entry(a)={[i+1 for i in en]} exit(a)={[i+1 for i in ex]}")
    for (n, d) in [(6, (1, 2, 3, 4, 11)), (6, (1, 2, 3, 4, 35)), (3, (4, 2)), (4, (1, 6, 3)), (5, (6, 2, 3, 4))]:
        for p in units(n):
            show(n, d, p)
    # one forward-reaching and one backward-reaching example per order, if any
    for n, S in summaries.items():
        for k in ('reach_ex', 'die_ex', 'bw_ex'):
            if k in S:
                r = S[k]
                if (n, r['d']) not in [(6, (1, 2, 3, 4, 11)), (6, (1, 2, 3, 4, 35))]:
                    P(f"[{k} at n={n}]")
                    show(n, r['d'], r['p'])
    print("\n".join(out))

if __name__ == "__main__":
    main()
