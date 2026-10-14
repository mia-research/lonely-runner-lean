"""carving_lineage_v1.py  (task AJ; rules 1,5,6,7,13,15,16,18,21)

Carving lineage of the lonely set of an integer disparity set, exact (integers / Fractions only; no floats).

OBJECTS (as in Fresh/Carving.lean): clear(d) = {t : dist(d t, Z) >= 1/8}; window N of d = [(N+1/8)/d, (N+7/8)/d]
(opening to entry); zone N of d = ((N-1/8)/d, (N+1/8)/d) (open).  lonelySet(insert d ds) = lonelySet ds ∩ clear(d)
[L: Carving.lonelySet_insert].  A cell of ds is a maximal closed interval of lonelySet ds with left end > 0
[LonelyCells.IsCell].

WINDOW CHOICE.  All disparities are integers, so every clear(d) is invariant under t -> t+1, and no instant t in Z is
lonely (a runner of integer disparity is at distance 0).  So the lonely set is 1-periodic, no cell contains an integer,
and the landing (the least lonely instant) lies in (0,1).  Stage 0 is therefore ALL windows of the first-inserted
runner that lie in (0,1): windows N = 0..d_first-1 (the window N=d_first-1 ends at (d_first-1/8)/d_first < 1).
This is a window large enough to contain the whole-set landing cell, and it contains every final cell.
Coordinates are scaled: X = 8 L t, L = lcm(ds); all openings/entries/zone edges are then integers.

ORDERS: 'dec' = fastest first (insert d = max, ..., min); 'inc' = slowest first.

Everything printed is [OBS] (a computation) unless marked [L] (a Lean theorem exists) or [reasoned].
"""
import itertools, sys, os
from math import gcd
from functools import reduce
from fractions import Fraction as F
from collections import Counter, defaultdict
from multiprocessing import Pool

def lcm(a, b): return a * b // gcd(a, b)

# ---------------------------------------------------------------- engine
def run(order):
    """order = insertion order of integer disparities.  Returns (L, stages, kills).
    stages[s] = list of cells (u, w, parent_index_in_stage_{s-1}, clipL, clipR); stage 0 = windows of order[0].
    kills[s-1] = list of (cell_index_in_stage_{s-1}, u, w, N, a) for cells killed by the s-th insertion, N = zone index."""
    L = 1
    for d in order: L = lcm(L, d)
    d0 = order[0]; a0 = L // d0
    stages = [[((8 * N + 1) * a0, (8 * N + 7) * a0, -1, 0, 0) for N in range(d0)]]
    kills = []
    for s in range(1, len(order)):
        d = order[s]; a = L // d
        new = []; kl = []
        for ci, (u, w, _, _, _) in enumerate(stages[-1]):
            Nlo = -((-(u - 7 * a)) // (8 * a)); Nhi = (w - a) // (8 * a)
            got = False
            for N in range(max(Nlo, 0), Nhi + 1):
                lo = (8 * N + 1) * a; hi = (8 * N + 7) * a
                pu = max(u, lo); pw = min(w, hi)
                if pu <= pw:
                    got = True
                    new.append((pu, pw, ci, 1 if u < lo else 0, 1 if w > hi else 0))
            if not got:
                N = (u + a) // (8 * a)
                if not ((8 * N - 1) * a < u and w < (8 * N + 1) * a): N += 1
                assert (8 * N - 1) * a < u and w < (8 * N + 1) * a
                kl.append((ci, u, w, N, a))
        stages.append(new); kills.append(kl)
    return L, stages, kills

def carve(cells, d, L):
    a = L // d; out = []
    for (u, w) in cells:
        Nlo = -((-(u - 7 * a)) // (8 * a)); Nhi = (w - a) // (8 * a)
        for N in range(max(Nlo, 0), Nhi + 1):
            pu = max(u, (8 * N + 1) * a); pw = min(w, (8 * N + 7) * a)
            if pu <= pw: out.append((pu, pw))
    return out

def survives(cell, rs, L):
    cs = [cell]
    for d in rs:
        cs = carve(cs, d, L)
        if not cs: return False
    return True

def root_of(stages, i):
    for s in range(len(stages) - 1, 0, -1): i = stages[s][i][2]
    return i

def chain_of(stages, i):
    ch = [0] * len(stages)
    for s in range(len(stages) - 1, -1, -1):
        ch[s] = i
        if s > 0: i = stages[s][i][2]
    return ch

def sigchar(cl, cr):
    return 'U' if not cl and not cr else ('L' if cl and not cr else ('R' if cr and not cl else 'B'))

def tF(x, L): return F(x, 8 * L)

# ---------------------------------------------------------------- independent check of the engine
def lonely_X(ds, L, Xnum, den):
    """Is the instant t = Xnum/(den*8L) lonely, by the DEFINITION (every d: dist(d t, Z) >= 1/8)?  Exact integers."""
    for d in ds:
        a = L // d
        # d t = d*Xnum/(den*8L) = Xnum/(den*8a);  dist >= 1/8  <=>  (Xnum mod 8a*den) in [a*den, 7a*den]
        r = Xnum % (8 * a * den)
        if not (a * den <= r <= 7 * a * den): return False
    return True

def check_engine(ds):
    ds = list(ds)
    for order in (sorted(ds, reverse=True), sorted(ds)):
        L, st, _ = run(order)
        fin = [(u, w) for (u, w, _, _, _) in st[-1]]
        # lonely status at every half-integer lattice point of (0, 8L): points X/2
        cur = [0] * len(fin)
        for X2 in range(1, 16 * L):
            inside = any(2 * u <= X2 <= 2 * w for (u, w) in fin)
            if inside != lonely_X(ds, L, X2, 2): return False
    return True

# ---------------------------------------------------------------- per-set analysis
def left_set(u, ds, L):   # runners having an opening at u
    return tuple(d for d in ds if u % (8 * (L // d)) == (L // d))
def right_set(w, ds, L):  # runners having an entry at w
    return tuple(d for d in ds if w % (8 * (L // d)) == 7 * (L // d))

def analyse(c):
    """returns dict of counters/extrema contributions for the 7-set c (sorted ascending)."""
    m = c[-1]
    out = defaultdict(int)
    ext = {}
    def upd(key, val, ex, mx):
        cur = ext.get(key)
        if cur is None or (val > cur[0] if mx else val < cur[0]): ext[key] = (val, ex)
    # landing cell (order independent): compute once in 'inc'
    for name, o in (('dec', tuple(c[::-1])), ('inc', tuple(c))):
        L, st, kills = run(list(o))
        fin = st[-1]
        assert fin, ("no final cell", c)
        # --- window-vector form: each final cell = intersection of ONE window per runner; ancestors = prefixes
        for i, (u, w, _, _, _) in enumerate(fin):
            ch = chain_of(st, i)
            Nv = [u // (8 * (L // d)) for d in o]
            ops = [(8 * Nv[r] + 1) * (L // o[r]) for r in range(7)]
            ens = [(8 * Nv[r] + 7) * (L // o[r]) for r in range(7)]
            ok = (u == max(ops) and w == min(ens) and all(ops[r] <= u and w <= ens[r] for r in range(7)))
            for s in range(1, 7):
                uu, ww, _, cl, cr = st[s][ch[s]]
                ok = ok and uu == max(ops[:s + 1]) and ww == min(ens[:s + 1])
                ok = ok and (cl == (1 if ops[s] > max(ops[:s]) else 0)) and (cr == (1 if ens[s] < min(ens[:s]) else 0))
            out[(name, 'vector_form_ok', m, ok)] += 1
        if name == 'inc' and m <= 18:
            # count pairwise-compatible window transversals by backtracking (distinct code path)
            cnt_t = 0
            chosen = []
            def dfs(r):
                nonlocal cnt_t
                if r == 7: cnt_t += 1; return
                a = L // o[r]
                for N in range(o[r]):
                    op = (8 * N + 1) * a; en = (8 * N + 7) * a
                    if all(op <= e2 and o2 <= en for (o2, e2) in chosen):
                        chosen.append((op, en)); dfs(r + 1); chosen.pop()
            dfs(0)
            out[('inc', 'transversal_count_eq_cells', m, cnt_t == len(fin))] += 1
        # --- stage-by-stage kill law
        for s, kl in enumerate(kills):
            for (ci, u, w, N, a) in kl:
                zw = 2 * a
                ratio = F(w - u, zw)
                p = F(u - (8 * N - 1) * a, zw); q = F((8 * N + 1) * a - w, zw)
                out[(name, 'kill', s + 1, m)] += 1
                if w == u: out[(name, 'killtouch', s + 1, m)] += 1
                upd((name, 'killratio_max', s + 1, m), ratio, (c, ci, tF(u, L), tF(w, L), N), True)
                upd((name, 'killratio_min', s + 1, m), ratio, (c, ci, tF(u, L), tF(w, L), N), False)
                upd((name, 'killedge_min', s + 1, m), min(p, q), (c, tF(u, L), tF(w, L), N), False)
        # --- lineage of every final cell
        roots = set()
        for i, (u, w, _, _, _) in enumerate(fin):
            ch = chain_of(st, i)
            roots.add(ch[0])
            sig = ''.join(sigchar(st[s][ch[s]][3], st[s][ch[s]][4]) for s in range(1, 7))
            nb = sig.count('B'); nc = 6 - sig.count('U')
            out[(name, 'all_nclip', m, nc)] += 1
            out[(name, 'all_nboth', m, nb)] += 1
            if i == 0:
                out[(name, 'land_sig', m, ch[0] if name == 'dec' else 0, sig)] += 1
                out[(name, 'land_root', m, ch[0])] += 1
                out[(name, 'land_nclip', m, nc)] += 1
                out[(name, 'land_nboth', m, nb)] += 1
                out[(name, 'land_sigonly', m, sig)] += 1
                # clip ends are openings (left) / entries (right) of the inserted runner: assert
                for s in range(1, 7):
                    _, _, _, cl, cr = st[s][ch[s]]
                    uu, ww = st[s][ch[s]][0], st[s][ch[s]][1]
                    a = L // o[s]
                    if cl: assert uu % (8 * a) == a
                    if cr: assert ww % (8 * a) == 7 * a
                # ancestors' rank among cells at each stage
                for s in range(7):
                    out[(name, 'land_rank', m, s, ch[s])] += 1
                # first cell of F_s survives?
            # root index of every final cell: counted
        out[(name, 'nroots', m, len(roots), o[0])] += 0
        out[(name, 'allwin', m, len(roots) == o[0])] += 1
        if name == 'inc':
            if len(roots) < o[0]:
                out[('inc', 'nwin_missing', m, o[0] - len(roots))] += 1
        # first cell of F_s killed at which insertion?
        for s in range(0, 6):
            if not any(x[2] == 0 for x in st[s + 1]):
                out[(name, 'firstcell_dies_at', m, s + 1)] += 1
        # --- candidate P2: landing ancestor = first individually-surviving cell of F_s
        ch0 = chain_of(st, 0)
        for s in range(0, 6):
            R = o[s + 1:]
            first_ind = None
            first_pair = None
            for ci, (u, w, _, _, _) in enumerate(st[s]):
                if first_ind is None and all(survives((u, w), (r,), L) for r in R): first_ind = ci
                if first_pair is None and all(survives((u, w), pr, L) for pr in itertools.combinations(R, 2)) and \
                        all(survives((u, w), (r,), L) for r in R): first_pair = ci
                if first_ind is not None and first_pair is not None: break
            out[(name, 'P2_single', m, s, first_ind == ch0[s])] += 1
            out[(name, 'P2_pair', m, s, first_pair == ch0[s])] += 1
            if first_ind != ch0[s]:
                upd((name, 'P2_single_ex', s, m), -len(c) , (c, s, first_ind, ch0[s]), True)
    # --- order-independent facts about the landing cell
    L, st, _ = run(list(c))
    u, w = st[-1][0][0], st[-1][0][1]
    ls = left_set(u, c, L); rs = right_set(w, c, L)
    rank = {d: i + 1 for i, d in enumerate(c)}   # 1 = smallest
    out[('both', 'land_touch', m, u == w)] += 1
    for d in ls: out[('both', 'land_left_has_rank', m, rank[d])] += 1
    for d in rs: out[('both', 'land_right_has_rank', m, rank[d])] += 1
    out[('both', 'land_left_dmin', m, c[0] in ls)] += 1
    out[('both', 'land_left_ge_1_over_8dmin', m, u == (L // c[0]))] += 1       # u == 1/(8 dmin)
    out[('both', 'land_in_first_window_dmin', m, u <= 7 * (L // c[0]))] += 1
    out[('both', 'land_in_first_window_dmax', m, u <= 7 * (L // c[-1]))] += 1
    out[('both', 'land_left_has_dmax', m, c[-1] in ls)] += 1
    out[('both', 'ncells_final', m, len(st[-1]))] += 1
    return dict(out), ext

def first_window_empty(c):
    if reduce(gcd, c) != 1: return None
    L = 1
    for d in c: L = lcm(L, d)
    a0 = L // c[0]; cs = [(a0, 7 * a0)]
    for d in c[1:]:
        cs = carve(cs, d, L)
        if not cs: return c
    return None

def work(c):
    return analyse(c)

def merge(accs, parts):
    cnt, ext = accs
    for out, e in parts:
        for k, v in out.items(): cnt[k] += v
        for k, (val, ex) in e.items():
            cur = ext.get(k)
            if k[1].endswith('_max') or k[1] == 'P2_single_ex':
                if cur is None or val > cur[0]: ext[k] = (val, ex)
            else:
                if cur is None or val < cur[0]: ext[k] = (val, ex)

# ---------------------------------------------------------------- reporting
def fr(x): return str(x)

def show_named(name, c):
    print("=" * 78); print("NAMED CASE", name, c)
    for oname, o in (('dec (fastest first)', sorted(c, reverse=True)), ('inc (slowest first)', sorted(c))):
        L, st, kills = run(list(o))
        print("  --", oname, "insertion order", o, " L =", L, " (X = 8L t)")
        for s in range(len(st)):
            cells = st[s]
            txt = []
            for (u, w, par, cl, cr) in cells:
                tag = '' if s == 0 else ('[%s<-%d]' % (sigchar(cl, cr), par))
                txt.append("[%s,%s]%s" % (tF(u, L), tF(w, L), tag))
            print("   stage %d (after %d runner%s, + %d): %d cells: %s" % (s, s + 1, 's' if s else '', o[s], len(cells), ' '.join(txt)))
            if s >= 1:
                for (ci, u, w, N, a) in kills[s - 1]:
                    zw = F(2 * a, 8 * L)
                    print("      killed by %d: parent cell %d [%s,%s] in zone %d = (%s,%s); len/zonewidth = %s" % (
                        o[s], ci, tF(u, L), tF(w, L), N, F((8 * N - 1) * a, 8 * L), F((8 * N + 1) * a, 8 * L), F(w - u, 2 * a)))
        fin = st[-1]
        print("   FINAL cells and ancestry (stage-by-stage clip: U untouched, L left clipped by opening, R right clipped by entry, B both):")
        for i, (u, w, _, _, _) in enumerate(fin):
            ch = chain_of(st, i)
            sig = ''.join(sigchar(st[s][ch[s]][3], st[s][ch[s]][4]) for s in range(1, 7))
            print("     final cell %d [%s,%s]  root window of %d = #%d ; ancestors idx %s ; clip %s" % (i, tF(u, L), tF(w, L), o[0], ch[0], ch, sig))

def main():
    N_list = [14, 18, 22]
    Nmax = max(N_list)
    out_lines = []
    print(__doc__)
    # ---- named cases
    named = {'AP (1..7)': (1, 2, 3, 4, 5, 6, 7), 'touch-only (1,2,3,4,5,7,12)': (1, 2, 3, 4, 5, 7, 12),
             'touch-only (1,4,5,6,7,11,13)': (1, 4, 5, 6, 7, 11, 13)}
    for k, c in named.items(): show_named(k, c)
    # ---- independent engine check
    print("=" * 78)
    chk = [c for c in itertools.combinations(range(1, 11), 7) if reduce(gcd, c) == 1] + list(named.values())
    okc = sum(1 for c in chk if check_engine(c))
    print("ENGINE CHECK [OBS]: carved final cells = {t: all d clear by the definition} at every lattice point X/2, both orders:",
          okc, "of", len(chk), "sets (all gcd-1 7-subsets of {1..10} and the 3 named sets).")
    # ---- populations
    sets = [c for c in itertools.combinations(range(1, Nmax + 1), 7) if reduce(gcd, c) == 1]
    print("POPULATIONS: all gcd-1 7-subsets of {1..N}: " + ", ".join("N=%d: %d" % (N, sum(1 for c in sets if c[-1] <= N)) for N in N_list))
    with Pool(8) as P:
        parts = P.map(work, sets, chunksize=500)
    cnt = defaultdict(int); ext = {}
    merge((cnt, ext), parts)

    def tot(N, key_prefix, pos_m, *rest):
        """sum over m<=N of cnt[key_prefix + (m,)+rest] where m sits at index pos_m"""
        s = 0
        for k, v in cnt.items():
            if k[:pos_m] == key_prefix and k[pos_m] <= N and k[pos_m + 1:] == rest: s += v
        return s
    def agg(N, order, tag, nrest):
        """Counter over the trailing fields of keys (order, tag, m, ...rest) with m<=N"""
        C = Counter()
        for k, v in cnt.items():
            if k[0] == order and k[1] == tag and k[2] <= N and v: C[k[3:]] += v
        return C
    for N in N_list:
        npop = sum(1 for c in sets if c[-1] <= N)
        print("=" * 78); print("POPULATION N = %d  (%d sets, gcd 1, 7-subsets of {1..%d})" % (N, npop, N))
        # Q1 lineage
        for order in ('dec', 'inc'):
            print("-- order", order)
            C = agg(N, order, 'land_root', 1)
            print("  landing cell lies in lap # of the first-inserted runner (window N0):", sorted((k[0], v) for k, v in C.items()))
            C = agg(N, order, 'land_nclip', 1)
            print("  number of stages (of 6) at which the landing ancestor was clipped:", sorted((k[0], v) for k, v in C.items()))
            C = agg(N, order, 'land_nboth', 1)
            print("  number of ancestors (stages 1..6) clipped at BOTH ends on the landing chain:", sorted((k[0], v) for k, v in C.items()))
            C = agg(N, order, 'all_nboth', 1)
            print("  same for EVERY final cell (all chains):", sorted((k[0], v) for k, v in C.items()))
            C = agg(N, order, 'land_sigonly', 1)
            tops = C.most_common(12)
            print("  landing clip signatures (stage1..stage6; U/L/R/B), %d distinct; most frequent: %s" % (len(C), ', '.join('%s:%d' % (k[0], v) for k, v in tops)))
            C = agg(N, order, 'firstcell_dies_at', 1)
            print("  insertion # at which the FIRST cell of the previous stage has no descendant (counts of sets):", sorted((k[0], v) for k, v in C.items()))
            C = agg(N, order, 'allwin', 1)
            print("  every window of the first-inserted runner has a final descendant:", dict((k[0], v) for k, v in C.items()))
            # rank of landing ancestor in each stage
            for s in range(7):
                R = Counter()
                for k, v in cnt.items():
                    if k[0] == order and k[1] == 'land_rank' and k[2] <= N and k[3] == s: R[k[4]] += v
                print("  landing ancestor index (0 = first cell) at stage %d: %s" % (s, sorted(R.items())))
        for order in ('dec', 'inc'):
            C = agg(N, order, 'vector_form_ok', 1)
            print("  [window-vector form] %s: every final cell = [max openings, min entries] of ONE window per runner, every ancestor = the same expression over the first s+1 runners, and clip flag at stage s = (strict new max opening / strict new min entry): %s" % (order, dict((k[0], v) for k, v in C.items())))
            C = agg(N, order, 'land_sigonly', 1)
            F1 = Counter()
            for k, v in C.items(): F1[k[0][0]] += v
            print("  %s: first letter of the landing signature (clip at insertion 1): %s" % (order, dict(F1)))
        if N <= 18:
            C = agg(N, 'inc', 'transversal_count_eq_cells', 1)
            print("  [window-transversal count] number of pairwise-compatible window transversals (backtracking) = number of final cells: %s" % dict((k[0], v) for k, v in C.items()))
        print("-- order-independent facts about the landing cell")
        for tag in ('land_touch', 'land_left_dmin', 'land_left_ge_1_over_8dmin', 'land_in_first_window_dmin', 'land_in_first_window_dmax', 'land_left_has_dmax'):
            C = agg(N, 'both', tag, 1)
            print("  %s: %s" % (tag, dict((k[0], v) for k, v in C.items())))
        for tag in ('land_left_has_rank', 'land_right_has_rank'):
            C = agg(N, 'both', tag, 1)
            print("  %s (rank 1 = smallest disparity; a runner counted if it has an opening/entry exactly at that end): %s" % (tag, sorted((k[0], v) for k, v in C.items())))
        # Q2 kill law
        print("-- kill law  (cells of the previous stage killed by the s-th insertion; killed <=> inside ONE zone of the inserted runner [L: cell_killed_iff, cover_singleton_iff])")
        for order in ('dec', 'inc'):
            for s in range(1, 7):
                kc = sum(v for k, v in cnt.items() if k[0] == order and k[1] == 'kill' and k[2] == s and k[3] <= N)
                kt = sum(v for k, v in cnt.items() if k[0] == order and k[1] == 'killtouch' and k[2] == s and k[3] <= N)
                def ex(tag, mx):
                    best = None
                    for k, (val, e) in ext.items():
                        if k[0] == order and k[1] == tag and k[2] == s and k[3] <= N:
                            if best is None or (val > best[0] if mx else val < best[0]): best = (val, e)
                    return best
                mxr = ex('killratio_max', True); mnr = ex('killratio_min', False); mne = ex('killedge_min', False)
                if kc:
                    print("  %s insertion %d: killed %d cells (%d single-point); len/zonewidth in [%s, %s]; slack (1-len/width) min = %s;"
                          " nearest-edge offset/zonewidth min = %s" % (order, s, kc, kt, mnr[0], mxr[0], 1 - mxr[0], mne[0]))
                    print("       max-ratio example (set, parent idx, t-interval, zone N): %s" % (mxr[1],))
                else:
                    print("  %s insertion %d: killed 0 cells" % (order, s))
        # candidates
        print("-- candidate P2: the landing ancestor at stage s is the FIRST cell of F_s not killed by any single remaining runner (P2_single), or by any pair (P2_pair)")
        for order in ('dec', 'inc'):
            for kind in ('P2_single', 'P2_pair'):
                row = []
                for s in range(6):
                    t = sum(v for k, v in cnt.items() if k[0] == order and k[1] == kind and k[2] <= N and k[3] == s and k[4] is True)
                    f = sum(v for k, v in cnt.items() if k[0] == order and k[1] == kind and k[2] <= N and k[3] == s and k[4] is False)
                    row.append("s%d: holds %d / fails %d" % (s, t, f))
                print("  %s %s: %s" % (order, kind, '; '.join(row)))
    # ---- windows of d_min without isolation
    print("=" * 78)
    print("WINDOWS OF THE SLOWEST RUNNER WITHOUT ANY ISOLATION (inc order): sets for which some window N of d_min has no lonely instant")
    for N in N_list:
        C = Counter()
        for k, v in cnt.items():
            if k[0] == 'inc' and k[1] == 'nwin_missing' and k[2] <= N: C[k[3]] += v
        print("  N=%d: number of sets with k missing windows (k: sets) %s" % (N, sorted(C.items())))
    # smallest examples with the reason (minimal killing coalition)
    exs = []
    for c in sets:
        if c[-1] > 14: continue
        L, st, _ = run(list(c))
        roots = set(root_of(st, i) for i in range(len(st[-1])))
        if len(roots) < c[0]: exs.append((c, sorted(set(range(c[0])) - roots)))
    print("  all %d such sets in N<=14 (set: missing window indices of d_min):" % len(exs))
    for c, mw in exs: print("    ", c, mw)
    print("  WHY, for each: smallest coalition of the other six runners whose zones cover the window (so no lonely instant in it):")
    for c, mw in exs:
        L = 1
        for d in c: L = lcm(L, d)
        for N0 in mw:
            a0 = L // c[0]
            win = (( 8 * N0 + 1) * a0, (8 * N0 + 7) * a0)
            others = c[1:]
            for j in range(1, 7):
                found = [sub for sub in itertools.combinations(others, j) if not survives(win, sub, L)]
                if found:
                    print("     %s window %d = [%s,%s]: smallest killing coalitions have size %d: %s" % (c, N0, tF(win[0], L), tF(win[1], L), j, found[:4]))
                    break
    # extension populations for K7 (first window of d_min non-empty)
    print("=" * 78)
    print("EXTENSION [OBS]: first window of d_min contains a lonely instant, FULL populations of gcd-1 7-subsets of {1..N}:")
    for NN in (26, 30, 34, 40):
        nn = 0; bad = []
        gen = (c for c in itertools.combinations(range(1, NN + 1), 7))
        with Pool(8) as P:
            for r in P.imap_unordered(first_window_empty, gen, chunksize=4000):
                nn += 1
                if r: bad.append(r)
        print("  N=%d: %d sets (gcd 1 where gcd tested in worker), first window empty: %d %s" % (NN, nn, len(bad), bad[:3]))
    import random
    rb = 0
    rnd = random.Random(20261009)
    tot_r = 0
    for M in (60, 100, 300, 1000, 3000):
        for _ in range(100000):
            c = tuple(sorted(rnd.sample(range(1, M + 1), 7))); tot_r += 1
            if first_window_empty(c): rb += 1; print("   RANDOM COUNTEREXAMPLE", c)
    print("  random search (a SEARCH, not a population; Random(20261009)): %d sets from {1..M}, M in 60,100,300,1000,3000: first window empty: %d" % (tot_r, rb))
    # mechanism examples
    print("=" * 78)
    print("MECHANISM EXAMPLES (all gcd-1 7-subsets of {1..12}; smallest set in lexicographic order)")
    seen = set()
    for c in itertools.combinations(range(1, 13), 7):
        if reduce(gcd, c) != 1: continue
        for name, o in (('dec', c[::-1]), ('inc', c)):
            L, st, k = run(list(o))
            ch0 = chain_of(st, 0)
            for s in range(0, 6):
                R = o[s + 1:]
                fi = None
                for ci, (u, w, _, _, _) in enumerate(st[s]):
                    if all(survives((u, w), (r,), L) for r in R): fi = ci; break
                if fi != ch0[s] and (name, s) not in seen:
                    seen.add((name, s))
                    u, w = st[s][fi][0], st[s][fi][1]
                    print("  P2_single fails: %s order %s at stage %d: first individually-surviving cell #%d = [%s,%s] has no descendant (the landing ancestor is cell #%d)" % (c, name, s, fi, tF(u, L), tF(w, L), ch0[s]))
                    for j in range(2, len(R) + 1):
                        co = [sub for sub in itertools.combinations(R, j) if not survives((u, w), sub, L)]
                        if co:
                            sub = co[0]; cs = [(u, w)]; trace = []
                            for d in sub:
                                cs = carve(cs, d, L); trace.append("after %d: %s" % (d, ' '.join('[%s,%s]' % (tF(x, L), tF(y, L)) for x, y in cs) or 'EMPTY'))
                            print("      killed jointly by %s (no single runner kills it): %s" % (sub, '; '.join(trace)))
                            break
    # earliest death of the first cell in dec order
    for c in itertools.combinations(range(1, 23), 7):
        if reduce(gcd, c) != 1: continue
        o = c[::-1]
        L, st, k = run(list(o))
        dead = [s + 1 for s in range(6) if not any(x[2] == 0 for x in st[s + 1])]
        if dead and dead[0] <= 4:
            print("  dec order, first cell of the previous stage has no descendant already at insertion #%d (after %d runners): smallest-lexicographic set %s" % (dead[0], dead[0] + 1, c))
            break
    # Helly-type levels (N <= 12 only, cost)
    print("=" * 78)
    print("MINIMAL KILLING COALITION SIZE of a stage-s cell by the remaining runners (all gcd-1 7-subsets of {1..12}; 0-indexed stage s = after s+1 runners)")
    lev = {'dec': [Counter() for _ in range(6)], 'inc': [Counter() for _ in range(6)]}
    for c in itertools.combinations(range(1, 13), 7):
        if reduce(gcd, c) != 1: continue
        for name, o in (('dec', c[::-1]), ('inc', c)):
            L, st, k = run(list(o))
            for s in range(6):
                R = o[s + 1:]
                for (u, w, _, _, _) in st[s]:
                    if survives((u, w), R, L): lev[name][s]['survives'] += 1; continue
                    for j in range(1, len(R) + 1):
                        if any(not survives((u, w), sub, L) for sub in itertools.combinations(R, j)):
                            lev[name][s][j] += 1; break
    for n in lev:
        for s in range(6): print("  ", n, "stage", s, dict(lev[n][s]))

if __name__ == '__main__':
    main()
