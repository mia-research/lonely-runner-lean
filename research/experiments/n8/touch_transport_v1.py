"""TOUCH TRANSPORT v1  (Task AD).  Exact Fractions / integers only; no floats anywhere.

Question.  Along an exact affine path of speeds v_s = (1-s) v + s v' (s in [0,1]), what happens to the lonely
cells of each subject at every event, and where does the isolation go when a cell dies?

Objects (the framework's own, Fresh/Framework.lean, LonelyCells.lean).
  * subject k, disparities d_i(s) = |v_i(s) - v_k(s)|.  The paths keep the speed ORDER of v and v' equal (both sorted
    with the same labelling), so every d_i(s) is affine and positive on [0,1] (no two runners ever meet: rule 4).
  * zone of runner i, lap m:  ((8m-1)/(8 d_i), (8m+1)/(8 d_i)) (open); m = 0 zone is (0, 1/(8 d_i)).
  * lonely set = {t>0} minus the union of zones.  A CELL is a maximal closed interval of it.  Left end = an OPENING
    R(i,m) = (8m+1)/(8 d_i); right end = an ENTRY L(j,m') = (8m'-1)/(8 d_j).
  * WINDOW: t in (0,T], T a fixed integer.  Cells reaching T are clipped at T (closer label 'T').  The window is a
    device of this script, not of the framework; window events are named WINDOW and kept apart.

Event solver (exact, event driven, no sampling).  An event is a parameter s0 and instant t0 at which two zone edges of
two different runners coincide AND t0 is lonely at s0 (otherwise the structure of the lonely set does not change):
  R=L  touch (death or birth of a cell), R=R opener swap, L=L closer swap, and R/L = T (window).
  c1 d_y(s) = c2 d_x(s) is linear in s; solved over the integers.  For each event s0 the exact cell lists are computed
  at the midpoints of the phases before and after, and AT s0 itself; cells are matched through s0 by continuing their
  end labels to s0 and locating them inside the exact cells at s0.
Independent checks run inside the script (counts in the output):
  (i)  completeness: two further rational s inside every phase give the same cell signature as the midpoint;
  (ii) every before/after cell continues into an exact cell at s0 (conservation of the cell count);
  (iii) at every phase midpoint the exact cascade (IsMove / nextOpening, from 1/(8 d_min)) lands on the left end of the
        first cell of the interval computation, or, if the window holds no cell, lands beyond T.
Grades: [OBS] for the data with the population stated; [reasoned] otherwise.  Counting is tagged "count".
"""
import sys, random, itertools
from fractions import Fraction as F
from math import floor, ceil, gcd
from multiprocessing import Pool
from collections import Counter, defaultdict

E8 = F(1, 8)


def dist_int(x):
    f = x - floor(x)
    return min(f, 1 - f)


# ------------------------------------------------------------------ paths
class Path:
    """v, w: ascending Fractions of equal length 8; subject k.  d_i(s) = (A_i + B_i s)/D."""
    def __init__(self, v, w):
        assert all(v[i] < v[i + 1] and w[i] < w[i + 1] and v[i] > 0 and w[i] > 0 for i in range(7))
        self.v, self.w = v, w
        den = 1
        for x in list(v) + list(w):
            den = den * x.denominator // gcd(den, x.denominator)
        self.D = den

    def coeffs(self, k):
        A, B = {}, {}
        for i in range(8):
            if i == k:
                continue
            sg = 1 if i > k else -1
            a = sg * (self.v[i] - self.v[k]) * self.D
            b = sg * (self.w[i] - self.w[k]) * self.D - a
            assert a.denominator == 1 and b.denominator == 1 and a > 0 and a + b > 0
            A[i], B[i] = int(a), int(b)
        return A, B

    def ds(self, k, s, A=None, B=None):
        if A is None:
            A, B = self.coeffs(k)
        return [(i, (A[i] + B[i] * s) / self.D) for i in A]


# ------------------------------------------------------------------ exact cells
def cells_at(ds, T):
    """ds: list of (runner, d).  Returns cells (u, w, openers, closers); openers/closers are tuples of (runner, lap),
    or closers == ('T',) when clipped at the window."""
    zones = []
    for i, d in ds:
        m = 0
        while True:
            left = F(8 * m - 1) / (8 * d) if m > 0 else F(0)
            if left >= T:
                break
            zones.append((left, F(8 * m + 1) / (8 * d), (i, m)))
            m += 1
    zones.sort(key=lambda z: (z[0], z[1]))
    byleft = defaultdict(list)
    for l, r, lab in zones:
        byleft[l].append(lab)
    cells = []
    cur = None
    labs = None
    for l, r, lab in zones:
        if cur is None:
            cur, labs = r, [lab]
            continue
        if l < cur:
            if r > cur:
                cur, labs = r, [lab]
            elif r == cur:
                labs.append(lab)
        else:
            cells.append((cur, l, tuple(labs), tuple(byleft[l])))
            cur, labs = r, [lab]
    if cur is not None and cur <= T:
        cells.append((cur, F(T), tuple(labs), ('T',)))
    return cells


def sig(cells):
    return tuple((c[2], c[3]) for c in cells)


def val_open(lab, dmap):
    i, m = lab
    return F(8 * m + 1) / (8 * dmap[i])


def val_close(lab, dmap, T):
    if lab == 'T':
        return F(T)
    i, m = lab
    return F(8 * m - 1) / (8 * dmap[i]) if m > 0 else F(0)


# ------------------------------------------------------------------ cascade (IsMove, nextOpening)
def cascade_first(dvals, cap=400000):
    t = F(1) / (8 * min(dvals))
    steps = 0
    while True:
        way = [d for d in dvals if dist_int(d * t) < E8]
        if not way:
            return t, steps
        t2 = max((F(ceil(d * t - E8)) + E8) / d for d in way)
        t = t2
        steps += 1
        if steps > cap:
            return None, steps


# ------------------------------------------------------------------ event solver
def solve_events(path, k, T):
    A, B = path.coeffs(k)
    D = path.D
    runners = list(A)
    edges = {}
    for i in runners:
        amax = max(A[i], A[i] + B[i])
        lst = []
        m = 0
        while True:
            c = 8 * m + 1
            if c * D > 8 * T * amax + 8 * D:
                break
            lst.append(('R', c, m))
            if m > 0:
                lst.append(('L', 8 * m - 1, m))
            m += 1
        edges[i] = lst
    found = {}   # (s0, t0) -> list of coincidences

    def lonely_int(Pm, c1, Pi_x):
        # t0 = c1*Dd*den/(8*Px_den)... all in the common integer form: d_i t0 = P_i*c1/(8*P_x)
        pass

    def add(s0, t0, item):
        found.setdefault((s0, t0), []).append(item)

    # pair coincidences between distinct runners
    for xi in range(len(runners)):
        x = runners[xi]
        for yi in range(xi + 1, len(runners)):
            y = runners[yi]
            for (tx, c1, mx) in edges[x]:
                for (ty, c2, my) in edges[y]:
                    num = c2 * A[x] - c1 * A[y]
                    den = c1 * B[y] - c2 * B[x]
                    if den == 0:
                        continue
                    if den < 0:
                        num, den = -num, -den
                    if num < 0 or num > den:
                        continue
                    Px = A[x] * den + B[x] * num      # d_x(s0) = Px/(D*den)
                    # t0 = c1/(8 d_x) = c1*D*den/(8 Px) <= T
                    if c1 * D * den > 8 * T * Px:
                        continue
                    Q = 8 * Px
                    ok = True
                    for i in runners:
                        Pi = A[i] * den + B[i] * num
                        r = (Pi * c1) % Q * 1       # d_i t0 = Pi*c1/Q   (D cancels)
                        if 8 * r < Q or 8 * (Q - r) < Q:
                            ok = False
                            break
                    if not ok:
                        continue
                    s0 = F(num, den)
                    t0 = F(c1 * D * den, Q)
                    add(s0, t0, (tx + ty, x, mx, y, my))
    # window edges: edge (c, x) at t = T
    for x in runners:
        for (tx, c1, mx) in edges[x]:
            # c1/(8 d_x(s)) = T  ->  d_x = c1/(8T) ; A + B s = c1 D/(8T)
            if B[x] == 0:
                continue
            s0 = (F(c1 * D, 8 * T) - A[x]) / B[x]
            if s0 < 0 or s0 > 1:
                continue
            if not all(dist_int((A[i] + B[i] * s0) / D * T) >= E8 for i in runners):
                continue
            add(s0, F(T), (tx + 'T', x, mx, None, None))
    return found, A, B


# ------------------------------------------------------------------ analysis of one subject path
def analyse(path, k, T, label, keep_phases=False):
    found, A, B = solve_events(path, k, T)
    D = path.D
    br = sorted(set([F(0), F(1)] + [s for (s, t) in found]))
    # phases (open intervals between consecutive breakpoints)
    phases = []
    for a, b in zip(br, br[1:]):
        mid = (a + b) / 2
        phases.append((a, b, mid, cells_at(path.ds(k, mid, A, B), T)))
    out = {'label': label, 'k': k, 'n_events_s': len(br) - 2, 'phases': len(phases)}
    out['completeness_fail'] = 0
    out['cascade_fail'] = 0
    out['cascade_beyond'] = 0
    out['zero_window_phases'] = []
    out['perm_degenerate_phase_cells'] = 0
    ncells = []
    tstars = []
    for (a, b, mid, cells) in phases:
        ncells.append(len(cells))
        for fr in (F(1, 4), F(3, 4)):
            s2 = a + (b - a) * fr
            if sig(cells_at(path.ds(k, s2, A, B), T)) != sig(cells):
                out['completeness_fail'] += 1
        dm = dict(path.ds(k, mid, A, B))
        tstar, steps = cascade_first(list(dm.values()))
        tstars.append(tstar)
        if cells:
            if tstar != cells[0][0]:
                out['cascade_fail'] += 1
        else:
            if tstar is None or tstar <= T:
                out['cascade_fail'] += 1
            else:
                out['cascade_beyond'] += 1
                out['zero_window_phases'].append((a, b, tstar))
        out['perm_degenerate_phase_cells'] += sum(1 for c in cells if c[0] == c[1])
    out['min_cells'] = min(ncells)
    out['max_cells'] = max(ncells)
    # events
    events = []
    unassigned = 0
    for s0 in br:
        at_d = dict(path.ds(k, s0, A, B))
        at = cells_at(list(at_d.items()), T)
        j = br.index(s0)
        before = phases[j - 1][3] if j > 0 else None
        after = phases[j][3] if j < len(phases) else None
        nb = [[] for _ in at]
        na = [[] for _ in at]

        def place(c, d_at, side, lst):
            nonlocal unassigned
            u = val_open(c[2][0], d_at)
            w = val_close(c[3][0], d_at, T)
            for idx, (u0, w0, _, _) in enumerate(at):
                if u0 <= u and w <= w0:
                    lst[idx].append(c)
                    return
            unassigned += 1
        if before is not None:
            for c in before:
                place(c, at_d, 'b', nb)
        if after is not None:
            for c in after:
                place(c, at_d, 'a', na)
        its = []
        for idx, (u0, w0, o0, c0) in enumerate(at):
            b_, a_ = len(nb[idx]), len(na[idx])
            deg = (u0 == w0)
            if before is None and after is not None:
                cat = 'START-TOUCH' if deg and a_ >= 1 else ('START-CELL' if a_ >= 1 else 'START-OTHER')
            elif after is None:
                cat = 'END-TOUCH' if deg and b_ >= 1 else ('END-CELL' if b_ >= 1 else 'END-OTHER')
            elif b_ == 1 and a_ == 1:
                bdeg = nb[idx][0][0] == nb[idx][0][1]
                adeg = na[idx][0][0] == na[idx][0][1]
                if deg and bdeg and adeg:
                    cat = 'PERSISTENT-TOUCH' if (nb[idx][0][2:] == na[idx][0][2:]) else 'PERSISTENT-TOUCH-RELABEL'
                elif deg:
                    cat = 'PASS-THROUGH'
                else:
                    ob = nb[idx][0][2]; oa = na[idx][0][2]; cb = nb[idx][0][3]; ca = na[idx][0][3]
                    if ob != oa and cb != ca:
                        cat = 'PERSIST-BOTH-SWAP'
                    elif ob != oa:
                        cat = 'PERSIST-OPENER-SWAP'
                    elif cb != ca:
                        cat = 'PERSIST-CLOSER-SWAP'
                    else:
                        cat = 'PERSIST-SAME'
            elif b_ == 1 and a_ == 0:
                cat = 'WINDOW-EXIT' if u0 == T else 'DEATH'
            elif b_ == 0 and a_ == 1:
                cat = 'WINDOW-ENTRY' if u0 == T else 'BIRTH'
            elif b_ == 0 and a_ == 0:
                cat = 'BLIP'
            elif b_ >= 2 and a_ == 1:
                cat = 'MERGE'
            elif b_ == 1 and a_ >= 2:
                cat = 'SPLIT'
            else:
                cat = 'OTHER(%d,%d)' % (b_, a_)
            nco = len(found.get((s0, u0), [])) if deg else 0
            kinds = tuple(sorted(x[0] for x in found.get((s0, u0), []))) if deg else ()
            its.append(dict(cat=cat, u=u0, w=w0, nb=nb[idx], na=na[idx], opens=o0, closes=c0, nco=nco, kinds=kinds,
                            tstar_after=None))
        tafter = tstars[j] if j < len(phases) else None
        nbf = len(before) if before is not None else 0
        naf = len(after) if after is not None else 0
        keep = (nbf <= 2 or naf == 0)
        events.append(dict(s0=s0, tstar_after=tafter, items=its, nbefore=nbf, nafter=naf,
                           before=before if keep else None, after=after if keep else None))
    out['events'] = events
    out['unassigned'] = unassigned
    out['phases_cells'] = [(a, b, c) for (a, b, m, c) in phases] if keep_phases else None
    return out


# ------------------------------------------------------------------ populations
def rand_frac(rng, lo, hi, dens):
    """random Fraction strictly inside (lo, hi) with denominator from dens."""
    while True:
        q = rng.choice(dens)
        p = rng.randint(floor(lo * q) + 1, ceil(hi * q) - 1)
        x = F(p, q)
        if lo < x < hi:
            return x


DENS = (2, 3, 4, 5, 7, 10, 12, 16, 20)


def pop_A(seed=20261008):
    rng = random.Random(seed)
    ap = [F(j) for j in range(1, 9)]
    paths = []
    # A1: one runner moved, 8 per runner
    for j in range(8):
        for r in range(8):
            w = list(ap)
            lo = ap[j - 1] if j > 0 else F(0)
            hi = ap[j + 1] if j < 7 else F(j + 1 + 2)
            w[j] = rand_frac(rng, lo, hi, DENS)
            paths.append(('A1', 'AP->move runner %d' % (j + 1), ap, w))
    # A2: two runners moved (random distinct), 60
    cnt = 0
    while cnt < 60:
        j, l = sorted(rng.sample(range(8), 2))
        w = list(ap)
        for q in (j, l):
            lo = ap[q - 1] if q > 0 else F(0)
            hi = ap[q + 1] if q < 7 else F(10)
            w[q] = rand_frac(rng, lo, hi, DENS)
        if all(w[i] < w[i + 1] for i in range(7)):
            paths.append(('A2', 'AP->move runners %d,%d' % (j + 1, l + 1), ap, w))
            cnt += 1
    # A3: all eight perturbed, amplitudes 1/20,1/8,1/4,1/2,9/10 ; 12 each
    for amp in (F(1, 20), F(1, 8), F(1, 4), F(1, 2), F(9, 10)):
        cnt = 0
        while cnt < 12:
            w = [ap[i] + rand_frac(rng, -amp, amp, DENS) for i in range(8)]
            if all(w[i] < w[i + 1] for i in range(7)) and w[0] > 0:
                paths.append(('A3', 'AP->all eight, amp %s' % amp, ap, w))
                cnt += 1
    return paths


GRIDS = [(1, 2, 3, 4, 5, 6, 7, 16), (1, 2, 3, 4, 5, 6, 15, 16), (1, 3, 5, 7, 8, 10, 12, 14),
         (1, 2, 3, 4, 5, 6, 7, 24), (1, 3, 4, 5, 6, 7, 8, 10)]


def pop_B(seed=20261009):
    rng = random.Random(seed)
    paths = []
    for g in GRIDS:
        v = [F(x) for x in g]
        assert sorted(x % 8 for x in g) == list(range(8)), g
        cnt = 0
        top = max(g) + 2
        while cnt < 12:
            w = sorted(rand_frac(rng, F(0), F(top), (1, 2, 3, 4, 5, 6, 7, 8, 10, 12)) for _ in range(8))
            if all(w[i] < w[i + 1] for i in range(7)):
                paths.append(('B', 'grid %s->random sorted' % (g,), v, w))
                cnt += 1
    return paths


def pop_P(seed=20261010):
    """pair-law paths: AP -> AP + delta, |delta_j| <= 1/44 so rho(s) <= 1/22 on the whole path."""
    rng = random.Random(seed)
    ap = [F(j) for j in range(1, 9)]
    paths = []
    for r in range(40):
        w = [ap[i] + F(rng.randint(-100, 100), 4400) for i in range(8)]
        paths.append(('P', 'AP->AP+delta (rho<=1/22)', ap, w))
    return paths


def pop_Q(seed=20261011):
    """pair-law paths between two perturbed APs: v = AP+delta, v' = AP+delta', all |delta| <= 1/44 (rho <= 1/22 on the whole path)."""
    rng = random.Random(seed)
    ap = [F(j) for j in range(1, 9)]
    paths = []
    for r in range(40):
        v = [ap[i] + F(rng.randint(-100, 100), 4400) for i in range(8)]
        w = [ap[i] + F(rng.randint(-100, 100), 4400) for i in range(8)]
        paths.append(('Q', 'AP+delta->AP+delta2 (rho<=1/22)', v, w))
    return paths


def pop_CX():
    ap = [F(j) for j in range(1, 9)]
    rho = F(1, 10)
    w = list(ap)
    w[1] = F(2) - rho
    w[2] = F(3) + rho
    return [('CX', 'AP->cx exception (d1=1-rho,d2=2+rho, rho=1/10)', ap, w)]


# ------------------------------------------------------------------ pair law prediction (PairLaw.lean)
def pairlaw_prediction(path, s, T=1):
    """subject 0.  d_j(s) j=1..7 = v_j - v_0.  Returns list of (u_a,w_a,a) for a in 1,3,5,7 with a d_b <= b d_a."""
    d = dict(path.ds(0, s))
    res = []
    for a in (1, 3, 5, 7):
        b = 8 - a
        if a * d[b] <= b * d[a]:
            res.append((F(a * a) / (8 * d[a]), F(a * b) / (8 * d[b]), a))
    return sorted(res)


def run_one(args):
    pid, (pop, desc, v, w), T, subjects = args
    path = Path(list(v), list(w))
    res = []
    for k in subjects:
        r = analyse(path, k, T, (pid, pop, desc), keep_phases=(pop in ('P', 'Q', 'CX')))
        res.append(r)
    return res


def classify_death(r, ev, it, T):
    """returns dict describing where the survivors are."""
    others_persist = [x for x in ev['items'] if x is not it and x['cat'].startswith('PERSIST')]
    others_pass = [x for x in ev['items'] if x is not it and x['cat'] == 'PASS-THROUGH']
    births = [x for x in ev['items'] if x['cat'] in ('BIRTH',)]
    deaths = [x for x in ev['items'] if x['cat'] == 'DEATH']
    nb, na = ev['nbefore'], ev['nafter']
    t0 = it['u']
    cls = lambda t: int(round(8 * t)) % 8
    a = cls(t0)
    tm = T - t0
    surv = others_persist + others_pass + births
    mirror_in = any(x['u'] <= tm <= x['w'] for x in surv)
    class_mirror_birth = any(cls(x['u']) == (8 - a) % 8 for x in births)
    class_mirror_any = any(cls(x['u']) == (8 - a) % 8 or cls(x['w']) == (8 - a) % 8 for x in surv)
    if others_persist or others_pass:
        status = 'PERSISTS'
    elif births:
        status = 'BIRTH-SAME-EVENT'
    else:
        status = 'NONE-LEFT'
    return dict(status=status, nb=nb, na=na, n_persist=len(others_persist) + len(others_pass),
                n_birth=len(births), n_death=len(deaths), t0=t0, cls=a, mirror_in=mirror_in,
                class_mirror_birth=class_mirror_birth, class_mirror_any=class_mirror_any)


def fmt_cell(c):
    return '[%s,%s]' % (c[0], c[1])


def fmt_cells(cells):
    return '{' + ', '.join(fmt_cell(c) for c in cells) + '}' if cells else '{}'


SKIP = ('PERSIST-SAME', 'PERSISTENT-TOUCH')


def report(T, pops, results, flat, dump):
    print('=' * 100)
    print('WINDOW T = %d  (cells clipped at T; the window is a device of this script)' % T)
    print('=' * 100)
    tot = Counter()
    for r in flat:
        tot['subject-paths'] += 1
        tot['phases'] += r['phases']
        tot['breakpoints (interior event s-values)'] += r['n_events_s']
        tot['completeness_fail (extra s in a phase gives other cell signature)'] += r['completeness_fail']
        tot['cascade_fail (cascade disagrees with first cell / window-empty)'] += r['cascade_fail']
        tot['phases with no cell in window, cascade lands beyond T'] += r['cascade_beyond']
        tot['unassigned continuations (conservation failure)'] += r['unassigned']
        tot['degenerate cells at generic phases (persistent touches), count'] += r['perm_degenerate_phase_cells']
        if r['min_cells'] == 0:
            tot['subject-paths with a window-empty phase'] += 1
    print('INTEGRITY [OBS] (count over all subject-paths, all populations):')
    for k_, v_ in tot.items():
        print('  %-70s %d' % (k_, v_))
    print()

    cats = defaultdict(Counter)
    death_rows = []
    other_rows = []
    deathstat = defaultdict(Counter)
    for r in flat:
        pop = r['label'][1]
        for ev in r['events']:
            s0 = ev['s0']
            for it in ev['items']:
                c = it['cat']
                if c in SKIP:
                    continue
                if s0 == 0 or s0 == 1:
                    cats[pop]['(endpoint) ' + c] += 1
                    continue
                cats[pop][c] += 1
                if c == 'DEATH':
                    d = classify_death(r, ev, it, T)
                    d.update(label=r['label'], k=r['k'], s0=s0, it=it, ev=ev, pop=pop)
                    death_rows.append(d)
                    deathstat[pop][d['status']] += 1
                    if d['n_persist'] >= 1 and d['n_birth'] >= 1:
                        deathstat[pop]['persisting AND simultaneous birth'] += 1
                    if d['nb'] == 1:
                        deathstat[pop]['n_before==1'] += 1
                    if d['mirror_in']:
                        deathstat[pop]['mirror T-t0 inside a survivor/born cell'] += 1
                    if d['class_mirror_birth']:
                        deathstat[pop]['birth at class 8-a, same s0'] += 1
                    if d['class_mirror_any']:
                        deathstat[pop]['survivor with an end in class 8-a'] += 1
                elif c not in ('BIRTH',):
                    other_rows.append((r['label'], r['k'], s0, it, ev))
    print('EVENT ITEMS BY CATEGORY [OBS] (count; interior s0; PERSIST-SAME and PERSISTENT-TOUCH are not events):')
    for pop in sorted(cats):
        print('  %-4s ' % pop + ' '.join('%s=%d' % (c, n) for c, n in sorted(cats[pop].items())))
    print()
    print('DEATHS: where are the survivors [OBS] (count of DEATH items, interior s0; WINDOW exits are separate):')
    for pop in sorted(deathstat):
        print('  %-4s ' % pop + ', '.join('%s=%d' % (k_, v_) for k_, v_ in sorted(deathstat[pop].items())))
    print('  ALL  status:', dict(Counter(d['status'] for d in death_rows)))
    print('  deaths = %d; with one cell before (nb==1) = %d; with no cell in window after = %d; with a persisting cell on both sides = %d;'
          % (len(death_rows), sum(1 for d in death_rows if d['nb'] == 1), sum(1 for d in death_rows if d['na'] == 0),
             sum(1 for d in death_rows if d['n_persist'] >= 1)))
    print('  deaths with a BIRTH at the same s0 (different t) = %d; deaths with no persisting cell but a same-s0 birth = %d'
          % (sum(1 for d in death_rows if d['n_birth'] >= 1), sum(1 for d in death_rows if d['status'] == 'BIRTH-SAME-EVENT')))
    # opener/closer rank offsets
    off = Counter()
    offsum = Counter()
    for d in death_rows:
        it = d['it']
        o = it['nb'][0][2][0][0] - d['k']
        c = it['nb'][0][3][0][0] - d['k'] if it['nb'][0][3] != ('T',) else None
        off[(o, c)] += 1
        if c is not None:
            offsum[('opposite sides' if o * c < 0 else 'same side') + (', offsets sum to +-8' if abs(o + c) == 8 else '')] += 1
    shape = Counter()
    for r in flat:
        for ev in r['events']:
            if 0 < ev['s0'] < 1:
                nd = sum(1 for it in ev['items'] if it['cat'] == 'DEATH')
                nbth = sum(1 for it in ev['items'] if it['cat'] == 'BIRTH')
                if nd or nbth:
                    shape[(nd, nbth)] += 1
    print('  event shapes at one s0, (deaths, births) -> count [OBS], interior s0, grouped over all subject-paths:', shape.most_common(10))
    blips = [row[3]['nco'] for row in other_rows if row[3]['cat'] == 'BLIP']
    print('  BLIP items = %d; smallest number of coincident zone edges at a BLIP point = %s' % (len(blips), min(blips) if blips else None))
    print('  deaths by side of opener/closer runner relative to the subject [OBS count]:', dict(offsum))
    print('  most frequent (opener offset, closer offset) at a death [OBS count]:', off.most_common(12))
    print()

    print('NONE-LEFT / WINDOW-EMPTY: death whose cell was the last one in the window; the exact cascade (IsMove) from 1/(8 d_min)')
    print('  at the next phase gives the first cell left end t* [OBS].  class = round(8 t) mod 8.')
    n = 0
    cl = Counter()
    for d in death_rows:
        if d['na'] == 0:
            n += 1
            ts = d['ev']['tstar_after']
            cl[('t* class = 8-a' if ts is not None and int(round(8 * ts)) % 8 == (8 - d['cls']) % 8 else 'other class')] += 1
            if n <= 25:
                print('  %s rank %d s0=%s dying cell [%s,%s] (class %d)  t* after = %s (class %d) opener=%s closer=%s' %
                      (d['label'][2], d['k'], d['s0'], d['it']['u'], d['it']['nb'][0][1], d['cls'], ts,
                       int(round(8 * ts)) % 8 if ts is not None else -1, d['it']['nb'][0][2], d['it']['nb'][0][3]))
                print('       before %s   after %s' % (fmt_cells(d['ev']['before'] or []), fmt_cells(d['ev']['after'] or [])))
    print('  count NONE-LEFT deaths =', n, dict(cl))
    print()
    nz = 0
    for r in flat:
        for (a, b, tstar) in r['zero_window_phases']:
            nz += 1
    print('WINDOW-EMPTY PHASES [OBS] count =', nz, ' (every one has an exact cascade fixed point beyond T; none is a path with no cell at all)')
    print()

    print('NAMED NON-DEATH/BIRTH ITEMS [OBS]: counts and the first exact examples with the multiset of coincident edges (nco, kinds):')
    byc = defaultdict(list)
    for row in other_rows:
        byc[row[3]['cat']].append(row)
    for c, lst in sorted(byc.items()):
        print('  %s: count=%d' % (c, len(lst)))
        if c in ('BLIP', 'PASS-THROUGH', 'PERSIST-BOTH-SWAP') or c.startswith('OTHER') or c in ('MERGE', 'SPLIT'):
            kc = Counter((row[3]['nco'], row[3]['kinds']) for row in lst)
            print('     coincident-edge multisets at the point (nco,kinds) -> count:', kc.most_common(6))
        for (lab, k, s0, it, ev) in lst[:4]:
            print('     %s rank %d s0=%s at-cell [%s,%s] before=%s after=%s' %
                  (lab[2], k, s0, it['u'], it['w'], [(x[2], x[3]) for x in it['nb']], [(x[2], x[3]) for x in it['na']]))
    print()
    if T == 1:
        pairlaw(pops, results)
    if dump:
        print('FULL EVENT DUMP')
        for r in flat:
            for ev in r['events']:
                for it in ev['items']:
                    if it['cat'] not in SKIP:
                        print(r['label'][2], r['k'], ev['s0'], it['cat'], it['u'], it['w'], fmt_cells(ev['before'] or []),
                              fmt_cells(ev['after'] or []))


def apdepth(k, t0):
    """runners in the way at the AP (speeds 1..8, disparities |i-k|) at instant t0: (offset, depth below the 1/8 edge)."""
    out = []
    for i in range(8):
        if i == k:
            continue
        dd = dist_int(abs(i - k) * t0)
        if dd < E8:
            out.append((i - k, E8 - dd))
    return out


def pairlaw(pops, results):
    print('PAIR-LAW CROSS-CHECK (Fresh/PairLaw.lean: pair_law, u_le_w_iff, pair_touch, interval_isCell) [OBS], populations P and Q, subject rank 0, T = 1:')
    print('  Prediction: cells contain exactly the intervals [u_a,w_a] = [a^2/(8 d_a), a(8-a)/(8 d_{8-a})], a odd, with a d_{8-a} <= (8-a) d_a.')
    print('  PairLaw.lean states these ARE cells; it does not say they are the only cells, so extras are listed, not counted as failures.')
    nphase = pred_in = pred_out = extra_phases = extra_cells = 0
    cross_ok = cross_bad = 0
    nopair_events = Counter()
    births_extra = []
    for pid, (pop, desc, v, w) in enumerate(pops):
        if pop not in ('P', 'Q'):
            continue
        path = Path(list(v), list(w))
        r = [x for x in results[pid] if x['k'] == 0][0]
        for (a, b, cells) in r['phases_cells']:
            mid = (a + b) / 2
            pred = [(p[0], p[1]) for p in pairlaw_prediction(path, mid)]
            got = set((c[0], c[1]) for c in cells)
            nphase += 1
            if all(q in got for q in pred):
                pred_in += 1
            else:
                pred_out += 1
                print('   PREDICTED CELL MISSING', desc, mid)
            ex = got - set(pred)
            if ex:
                extra_phases += 1
                extra_cells += len(ex)
        A, B = path.coeffs(0)
        D = path.D
        crossings = {}
        for a_ in (1, 3):
            b_ = 8 - a_
            den = a_ * B[b_] - b_ * B[a_]
            num = b_ * A[a_] - a_ * A[b_]
            if den != 0:
                s0 = F(num, den)
                if 0 < s0 < 1:
                    crossings[s0] = a_
        evs = {ev['s0']: ev for ev in r['events'] if 0 < ev['s0'] < 1}
        for s0, a_ in crossings.items():
            b_ = 8 - a_
            ev = evs.get(s0)
            d = dict(path.ds(0, s0))
            ta, tb = F(a_ * a_) / (8 * d[a_]), F(b_ * b_) / (8 * d[b_])
            ok = False
            if ev is not None:
                dths = [it for it in ev['items'] if it['cat'] == 'DEATH']
                brth = [it for it in ev['items'] if it['cat'] == 'BIRTH']
                pts_d = set(it['u'] for it in dths)
                pts_b = set(it['u'] for it in brth)
                ok = (ta in pts_d and tb in pts_b) or (tb in pts_d and ta in pts_b)
            if ok:
                cross_ok += 1
            else:
                cross_bad += 1
                print('   CROSSING NOT A DEATH+BIRTH AT (t_a,t_b)', desc, s0, a_)
        for s0, ev in evs.items():
            for it in ev['items']:
                if it['cat'] in ('DEATH', 'BIRTH') and s0 not in crossings:
                    nopair_events[it['cat']] += 1
                    if it['cat'] == 'BIRTH':
                        births_extra.append((desc, s0, it['u'], apdepth(0, it['u'])))
    print('  phases checked = %d; predicted pair-law cells all present as exact cells: %d (missing %d)' % (nphase, pred_in, pred_out))
    print('  phases containing cells beyond the predicted ones = %d (extra cells = %d)' % (extra_phases, extra_cells))
    print('  pair crossings (a d_b = b d_a, a=1,3, inside (0,1)) = %d; each is one DEATH at t_a or t_b plus one BIRTH at the other: %d (not: %d)'
          % (cross_ok + cross_bad, cross_ok, cross_bad))
    print('  interior DEATH/BIRTH items NOT at a pair crossing, populations P and Q (count):', dict(nopair_events))
    for (desc, s0, t0, dp) in births_extra:
        print('    extra BIRTH at s0=%s t0=%s; runners in the way at the AP at t0 (offset, depth below 1/8): %s' % (s0, t0, dp))
    print()
    print('CX EXCEPTION PATH (PairLaw.lean section 5: displaced_cell), subject rank 0, T=1 [OBS]:')
    for pid, (pop, desc, v, w) in enumerate(pops):
        if pop != 'CX':
            continue
        r = [x for x in results[pid] if x['k'] == 0][0]
        for ev in r['events']:
            its = [it for it in ev['items'] if it['cat'] not in SKIP]
            if its:
                print('  s0=%s: ' % ev['s0'] + '; '.join('%s [%s,%s] opener=%s closer %s->%s' %
                      (it['cat'], it['u'], it['w'], it['opens'], [x[3] for x in it['nb']], [x[3] for x in it['na']]) for it in its))
                for it in its:
                    if it['cat'] == 'BIRTH':
                        print('     BIRTH t0=%s: AP runners in the way at t0 (offset, depth): %s' % (it['u'], apdepth(0, it['u'])))
        print('  phases:')
        for (a, b, cells) in r['phases_cells']:
            print('    s in (%s,%s): %s' % (a, b, fmt_cells(cells)))
    print()


def main():
    Ts = [int(x) for x in sys.argv[1:] if x.lstrip('-').isdigit()] or [1, 3]
    dump = '--dump' in sys.argv
    pops = pop_A() + pop_B() + pop_P() + pop_Q() + pop_CX()
    print('TOUCH TRANSPORT v1.  Exact Fractions only.  Windows T =', Ts)
    print('Populations (deterministic seeds; rule 14):')
    cnt = Counter(p[0] for p in pops)
    for key in ('A1', 'A2', 'A3', 'B', 'P', 'Q', 'CX'):
        print('  %-3s paths = %d  (subject-paths = %d)' % (key, cnt[key], 8 * cnt[key]))
    print('  A: AP (1..8) -> sorted rational targets; A1 one runner moved (8 per runner, seed 20261008), A2 two runners (60), '
          'A3 all eight at amplitudes 1/20,1/8,1/4,1/2,9/10 (12 each).')
    print('  B: complete-residue grids %s -> 12 random sorted rational targets each (seed 20261009).' % (GRIDS,))
    print('  P: AP -> AP+delta, |delta_j| <= 1/44 (rho <= 1/22), 40 paths (seed 20261010); Q: AP+delta -> AP+delta2, same bound, 40 paths (seed 20261011); CX: PairLaw exception path.')
    print('  Every path keeps the speed order, subjects = all eight ranks 0..7 (rank 0 slowest).')
    print()
    for T in Ts:
        tasks = [(i, p, T, range(8)) for i, p in enumerate(pops)]
        with Pool() as pool:
            results = pool.map(run_one, tasks, chunksize=2)
        flat = [r for res in results for r in res]
        report(T, pops, results, flat, dump)


if __name__ == '__main__':
    main()
