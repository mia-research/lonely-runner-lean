# v3_uniformity_lemma_v1 -- killing-cycle SHAPE extraction + per-shape product verification
# for the two V3 survivor families (Track V centerpiece, 2026-11-21).
#
# INPUTS (existing artifacts, read-only):
#   anchored family:  v3_march_census_v2_y<y>k<k>.out (the 23 base members + the period-33
#                     test member k=48; the 3 nonvacuous ones y6k15/y6k17/y6k25 carry the
#                     rejection tables), with the corrected irred certificates from
#                     v3_march_census_table_v1.out (v2's recorded irred products are loop
#                     artifacts; entry/progress are exact -- v3_march_census_findings_v1.md 5).
#   self family:      v3_march_self_m<m>.out (m = 5..10; the v3 logging fix makes ALL
#                     recorded certificates clean).
#
# METHOD.
# A. Row grammar (from the instruments v3_march_census_v2.py / v3_march_self_v1.py, copies of
#    the d0_points_only_k6_v2 search loop; rows are u_p <= c u_q, strict iff flagged).  For a
#    word z_0..z_{n-1} (reading r_i, lap l_i) the word rows are
#      z_0   : entry r_0->0  1/(8l_0-1);  progress 0->r_0  (8l_0+1)/1
#      z_i>=1: entry r_i->r_{i-1} (8l_{i-1}+1)/(8l_i-1); progress r_{i-1}->r_i (8l_i+1)/(8l_{i-1}+1)
#      z_i>=2: irred r_{i-2}->r_i (8l_i-1)/(8l_{i-2}+1)   [cand start > exit(z_{i-2})]
#    plus base rows (weak order, B-caps), region rows, family window rows (anchored:
#    apex/cover-floor/cover-entry on the hinge reading; self: strip rows).
#    VALIDATION (two independent checks):
#      (1) the candidate loop is REPLAYED on the reconstructed system (a reimplementation of
#          the instrument's M-closure): the rejection multiset (y, lap, why) per death node
#          must EQUAL the recorded one, and the recorded candidate windows [jlo, jhi] are
#          recomputed;
#      (2) every killing-cycle product is recomputed exactly (entry/progress vs the recorded
#          product; irred vs the de-contaminated value, cross-checked against the 9 table
#          corrections).
# B. Killing cycles: closed walks (failed candidate edge + least-product path), edges tagged
#    (kind, lap tuple, weight, strict).  SKELETON = (cyclic reading tuple, edge-kind tuple).
# C. SHAPES: instances of a skeleton are the same shape iff their lap slots agree slot-wise
#    under the mechanism-derived role rule -- per slot: EQUAL (abs), or EQUAL-OFFSET-FROM-BASE
#    (tied), or FREE on a slot that is window-determined by the search itself: the candidate
#    lap (slot 0 of the candidate edge), the death-frontier lap (slot 1 of the candidate
#    entry/progress edge), and -- anchored family only -- any slot whose reading is 6 (the
#    window-pinned reading; its laps are value-tied, E891's V role).  Exact greedy clique
#    cover (deterministic; may over-split, so shape counts are UPPER bounds).
# D. Per-shape verification (exact Fractions):
#    (i)   every realized instance < 1 (worst reported);
#    (ii)  the WIDENED box: free slots over their observed windows (closure across bases)
#          x base over the family range, branch-and-bound with per-factor monotone interval
#          bounds -- a rigorous superset check; binding product + cell reported;
#    (iii) the half-line in the base: per corner of the free-slot box the product is a
#          rational function of the base; Sturm sequences over Fractions decide B-A > 0 on
#          [b_min, inf) exactly; the drift law (the exact 1/b coefficient of the deficit)
#          is computed for the tied shapes.
# E. Residues: shapes realized at only one member, named precisely.
# F. Ladder-law reduction of the dominant multi-row shapes (the E840 instrument).
#
# OUTPUT: stdout (redirect to v3_uniformity_lemma_v1.out).
import sys, json, re, ast
from fractions import Fraction as F
from collections import Counter, defaultdict

EX = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8'

# ---------------------------------------------------------------- the M-closure (SysLite)

class SysLite:
    """Reimplementation of d0_points_only_k6_v2.Sys: M[p][q] = tightest (c, strict) with
    u_p <= c u_q; add() returns False iff the state becomes infeasible (a cycle with
    product < 1, or = 1 with a strict edge).  Rows are also LOGGED (v3 semantics: only
    successful adds are logged)."""
    __slots__ = ('k', 'M', 'log')

    def __init__(self, k):
        self.k = k
        self.M = [[((F(1), False) if p == q else None) for q in range(k)] for p in range(k)]
        self.log = []

    def copy(self):
        s = SysLite.__new__(SysLite)
        s.k = self.k
        s.M = [row[:] for row in self.M]
        s.log = list(self.log)
        return s

    @staticmethod
    def _better(e, f):
        if f is None: return True
        if e[0] != f[0]: return e[0] < f[0]
        return e[1] and not f[1]

    @staticmethod
    def _mul(a, b):
        return (a[0] * b[0], a[1] or b[1])

    def add(self, p, q, c, strict):
        e = (F(c), strict)
        if not self._better(e, self.M[p][q]):
            return True
        k, M = self.k, self.M
        upd = []
        for i in range(k):
            a = M[i][p]
            if a is None: continue
            ae = self._mul(a, e)
            for j in range(k):
                b = M[q][j]
                if b is None: continue
                cand = self._mul(ae, b)
                if self._better(cand, M[i][j]):
                    upd.append((i, j, cand))
        for i, j, cand in upd:
            if self._better(cand, M[i][j]):
                M[i][j] = cand
        for i in range(k):
            d = M[i][i]
            if d[0] < 1 or (d[0] == 1 and d[1]):
                return False
        self.log.append((p, q, e[0], e[1]))
        return True

    def least_prod_path(self, src, dst):
        best = {src: (F(1), [])}
        for _ in range(9):
            ch = False
            for (p, q, c, st) in self.log:
                if p in best:
                    v = best[p][0] * c
                    if q not in best or v < best[q][0]:
                        best[q] = (v, best[p][1] + [(p, q, c, st)]); ch = True
            if not ch: break
        return best.get(dst)

# ---------------------------------------------------------------- row grammar

def base_rows(nread, B):
    rows = []
    for i in range(nread - 1):
        rows.append((i + 1, i, F(1), False, 'weak', ()))
    for i in range(1, nread):
        rows.append((0, i, F(B), False, 'Bcap', ()))
    return rows

def anchored_base_rows(k, j, hy, B):
    rows = base_rows(7, B)
    rows += [
        (5, 0, F(1, 17), True,  'region6', ()),
        (6, 0, F(1, 25), False, 'region7', ()),
        (3, 0, F(1, 7),  True,  'front_lo', ()),
        (0, 3, F(5841, 833), False, 'front_hi', ()),
        (hy, 0, F(33, (8*k - 1)*7), True, 'apex', (k,)),
        (0, hy, F(8*j + 1, 7), False, 'cover_floor', (j,)),
        (hy, 0, F(7, 8*j - 1), True, 'cover_entry', (j,)),
    ]
    return rows

def self_base_rows(m, B):
    rows = base_rows(7, B)
    rows += [
        (5, 0, F(1, 17), True,  'region6', ()),
        (6, 0, F(1, 25), False, 'region7', ()),
        (6, 0, F(1, 8*m - 1), False, 'strip_entry', (m,)),
        (0, 6, F(8*m + 1), True,  'strip_exit', (m,)),
    ]
    return rows

def word_rows(word):
    rows = []
    for i, (r, l) in enumerate(word):
        if i == 0:
            rows.append((r, 0, F(1, 8*l - 1), True, 'z_entry', (l,)))
            rows.append((0, r, F(8*l + 1), True, 'z_progress', (l,)))
        else:
            rp, lp = word[i - 1]
            rows.append((r, rp, F(8*lp + 1, 8*l - 1), True, 'z_entry', (l, lp)))
            rows.append((rp, r, F(8*l + 1, 8*lp + 1), True, 'z_progress', (l, lp)))
        if i == 1:
            # z_1's irred row is against the ROOT "zone" (lap 0, pe = 8*0+1 = 1)
            rows.append((0, r, F(8*l - 1), True, 'z_irred', (l, 0)))
        elif i >= 2:
            rg, lg = word[i - 2]
            rows.append((rg, r, F(8*l - 1, 8*lg + 1), True, 'z_irred', (l, lg)))
    return rows

def build_system(rows):
    s = SysLite(7)
    for (p, q, c, st, kind, laps) in rows:
        if not s.add(p, q, c, st):
            raise RuntimeError('base row rejected: ' + str((p, q, c, st, kind)))
    return s

# ---------------------------------------------------------------- the replay

def replay_death(word, fam_rows):
    """Rebuild the death node's system, replay the candidate loop exactly as the instrument
    does, and return the rejection records with killing cycles and candidate windows.
    Path rows are annotated with their (kind, laps) via the known-row map."""
    wrows = word_rows(word)
    known = {}
    for row in fam_rows + wrows:
        p, q, c, st, kind, laps = row
        key = (p, q, c)
        if key not in known or known[key][4] == 'Bcap':
            known[key] = (p, q, c, st, kind, laps)   # prefer non-Bcap identification
    s = build_system(fam_rows + wrows)
    n = len(word)
    cv, cf = word[-1]
    ce = 8*cf + 1
    if n >= 2:
        pv, pf = word[-2]
    else:
        pv, pf = 0, 0          # a 1-zone word's prev is the ROOT "zone" (lap 0, pe = 1)
    pe = 8*pf + 1
    M = s.M
    xmin = ce / M[0][cv][0]
    xmax = ce * M[cv][0][0]
    Bmax = M[0][6][0]      # u_0 <= B u_6 caps all laps (the tightest B-cap)
    jmax = int((7 * Bmax + 1) // 8) + 1
    out = []
    def annotate(path):
        annotated = []
        for (p, q, c, st) in path:
            k = (p, q, c)
            if k in known:
                row = known[k]
                annotated.append(row)
            else:
                annotated.append((p, q, c, st, 'UNKNOWN', ()))
        return annotated
    for y2 in range(1, 7):
        uymin = 1 / M[0][y2][0]
        uymax = M[y2][0][0]
        jlo = max(1, int((xmin / uymax - 1) // 8))
        jhi = min(jmax, int((xmax / uymin + 1) // 8) + 1)
        for j2 in range(jlo, jhi + 1):
            if (0, y2, j2) in [(0, r, l) for (r, l) in word]: continue
            t = s.copy()
            ok1 = t.add(y2, cv, F(ce) / (8*j2 - 1), True)
            if not ok1:
                bp = s.least_prod_path(cv, y2)
                out.append(dict(why='entry', cand=(y2, j2), window=(jlo, jhi),
                                product=(F(ce, 8*j2 - 1) * bp[0] if bp else None),
                                candedge=(y2, cv, F(ce, 8*j2 - 1), True, 'cand_entry', (j2, cf)),
                                path=annotate(bp[1] if bp else [])))
                continue
            ok2 = t.add(cv, y2, (8*j2 + 1) / F(ce), True)
            if not ok2:
                bp = s.least_prod_path(y2, cv)
                out.append(dict(why='progress', cand=(y2, j2), window=(jlo, jhi),
                                product=(F(8*j2 + 1, ce) * bp[0] if bp else None),
                                candedge=(cv, y2, F(8*j2 + 1, ce), True, 'cand_progress', (j2, cf)),
                                path=annotate(bp[1] if bp else [])))
                continue
            if pv is not None:
                if not t.add(pv, y2, F(8*j2 - 1, pe), True):
                    # v3 logging semantics: the failed irred row is NOT in t.log (SysLite logs
                    # successful adds only), so t.log = s.log + cand entry + cand progress --
                    # exactly the log the corrected certificates were computed on.
                    bp = t.least_prod_path(y2, pv)
                    out.append(dict(why='irred', cand=(y2, j2), window=(jlo, jhi),
                                    product=(F(8*j2 - 1, pe) * bp[0] if bp else None),
                                    candedge=(pv, y2, F(8*j2 - 1, pe), True, 'cand_irred', (j2, pf)),
                                    path=annotate(bp[1] if bp else [])))
                    continue
    return out

def make_cycle(rej):
    cyc = [rej['candedge']] + [ (p, q, c, st, 'path', ()) for (p, q, c, st) in rej['path'] ]
    return cyc

# ---------------------------------------------------------------- loaders

def load_anchored():
    members = {}
    for y in (4, 5):
        for k in (13, 15, 17, 19, 21, 23, 25, 27):
            members[(y, k)] = json.load(open(f'{EX}/v3_march_census_v2_y{y}k{k}.out'))
    for k in (15, 17, 19, 21, 23, 25, 27):
        members[(6, k)] = json.load(open(f'{EX}/v3_march_census_v2_y6k{k}.out'))
    members[(6, 48)] = json.load(open(f'{EX}/v3_march_census_v2_y6k48.out'))
    return members

IRRED_CORR_RE = re.compile(
    r"k(\d+) death (\d+) irred \[(\d+), (\d+)\]: recorded \S+ -> corrected (\S+)\s+\(cycle tail (.*)\)\s*$")

def load_irred_corrections():
    out = {}
    txt = open(f'{EX}/v3_march_census_table_v1.out').read()
    for line in txt.splitlines():
        mo = IRRED_CORR_RE.search(line)
        if mo:
            k, di, y2, pv = int(mo.group(1)), int(mo.group(2)), int(mo.group(3)), int(mo.group(4))
            out[(k, di, y2, pv)] = F(mo.group(5))
    return out

def member_params(y, k):
    jtab = {13: 19, 15: 22, 17: 25, 19: 28, 21: 31, 23: 34, 25: 37, 27: 40, 48: 71}
    j = jtab[k]
    B = F(8*j + 1, 7) if y == 6 else F(49)
    if B < 25: B = F(25)
    return j, B

def build_all():
    """Replay all nonvacuous members; return (anchored_cycles, self_cycles, validation)."""
    corr = load_irred_corrections()
    anchored = load_anchored()
    val = dict(rej_ok=0, rej_bad=0, prod_ok=0, prod_bad=0, irred_corr_ok=0, irred_corr_bad=0)
    all_cycles = {}
    for (y, k), d in sorted(anchored.items()):
        if not d.get('deaths'): continue
        j, B = member_params(y, k)
        fam_rows = anchored_base_rows(k, j, y, B)
        cycles = []
        for di, (word, rejs_recorded) in enumerate(d['deaths']):
            replay = replay_death(word, fam_rows)
            # validation (1): rejection multiset
            rec = Counter((r[0], r[1], r[2]) for r in rejs_recorded)
            rep = Counter((r['cand'][0], r['cand'][1], r['why']) for r in replay)
            if rec == rep:
                val['rej_ok'] += 1
            else:
                val['rej_bad'] += 1
                if val['rej_bad'] <= 5:
                    print('REJ-MISMATCH', (y, k, di), 'recorded', sorted(rec.items()),
                          'replayed', sorted(rep.items()))
            # validation (2) + cycle construction
            recmap = {(r[0], r[1], r[2]): r for r in rejs_recorded}
            for r in replay:
                key = (r['cand'][0], r['cand'][1], r['why'])
                rr = recmap[key]
                prod_rec = F(rr[3]) if rr[3] is not None else None
                if r['why'] == 'irred':
                    # v2's recorded irred product is a loop artifact; the corrected value is
                    # the table's (keyed (k, di, y2, pv))
                    cc = corr.get((k, di, key[0], word[-2][0]))
                    ok = (cc is not None and r['product'] == cc)
                    if cc is not None:
                        if ok: val['irred_corr_ok'] += 1
                        else:
                            val['irred_corr_bad'] += 1
                            if val['irred_corr_bad'] <= 5:
                                print('IRRED-CORR-MISMATCH', (y, k, di, key),
                                      'replayed', r['product'], 'table', cc)
                else:
                    ok = (r['product'] is not None and prod_rec == r['product'])
                val['prod_ok' if ok else 'prod_bad'] += 1
                if not ok and val['prod_bad'] <= 5:
                    print('PROD-MISMATCH', (y, k, di, key), 'replayed', r['product'],
                          'recorded', prod_rec)
                cyc = [r['candedge']] + list(r['path'])
                cycles.append(dict(member=('anchored', y, k, j), base=k, why=r['why'],
                                   cand=r['cand'], window=r['window'], word=word, cycle=cyc,
                                   product=r['product'], verified=ok,
                                   readings=tuple([cyc[0][0]] + [e[1] for e in cyc]),
                                   strict=all(e[3] for e in cyc)))
        all_cycles[(y, k)] = cycles
    self_cycles = {}
    for m in range(5, 11):
        d = json.load(open(f'{EX}/v3_march_self_m{m}.out'))
        fam_rows = self_base_rows(m, F(8*m + 1))
        cycles = []
        for di, (word, rejs_recorded) in enumerate(d['deaths']):
            replay = replay_death(word, fam_rows)
            rec = Counter((r[0], r[1], r[2]) for r in rejs_recorded)
            rep = Counter((r['cand'][0], r['cand'][1], r['why']) for r in replay)
            if rec == rep:
                val['rej_ok'] += 1
            else:
                val['rej_bad'] += 1
                if val['rej_bad'] <= 5:
                    print('REJ-MISMATCH', ('self', m, di), 'recorded', sorted(rec.items()),
                          'replayed', sorted(rep.items()))
            recmap = {(r[0], r[1], r[2]): r for r in rejs_recorded}
            for r in replay:
                key = (r['cand'][0], r['cand'][1], r['why'])
                rr = recmap[key]
                prod_rec = F(rr[3]) if rr[3] is not None else None
                ok = (r['product'] is not None and prod_rec == r['product'])
                val['prod_ok' if ok else 'prod_bad'] += 1
                if not ok and val['prod_bad'] <= 5:
                    print('PROD-MISMATCH', ('self', m, di, key), 'replayed', r['product'],
                          'recorded', prod_rec)
                cyc = [r['candedge']] + list(r['path'])
                cycles.append(dict(member=('self', m, m, m), base=m, why=r['why'],
                                   cand=r['cand'], window=r['window'], word=word, cycle=cyc,
                                   product=r['product'], verified=ok,
                                   readings=tuple([cyc[0][0]] + [e[1] for e in cyc]),
                                   strict=all(e[3] for e in cyc)))
        self_cycles[m] = cycles
    return all_cycles, self_cycles, val

# ---------------------------------------------------------------- exact polynomials (Sturm)

def poly_mul(a, b):
    r = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x == 0: continue
        for j, y in enumerate(b):
            r[i+j] += x*y
    return r

def poly_add(a, b):
    n = max(len(a), len(b)); r = [F(0)]*n
    for i, x in enumerate(a): r[i] += x
    for i, x in enumerate(b): r[i] += x
    while len(r) > 1 and r[-1] == 0: r.pop()
    return r

def poly_neg(a): return [-x for x in a]

def poly_deriv(a): return [a[i]*i for i in range(1, len(a))] or [F(0)]

def poly_eval(a, x):
    r = F(0)
    for c in reversed(a): r = r*x + c
    return r

def poly_rem(a, b):
    a = list(a); db = len(b) - 1
    while len(a) >= len(b) and any(a):
        d = len(a) - 1
        if d < db: break
        f = a[d] / b[-1]
        for i in range(len(b)):
            a[d - db + i] -= f * b[i]
        while a and a[-1] == 0: a.pop()
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a

def sturm_chain(p):
    chain = [p[:], poly_deriv(p)]
    while len(chain[-1]) > 1:
        r = poly_rem(chain[-2], chain[-1])
        if not r or all(c == 0 for c in r): break
        chain.append(poly_neg(r))
    return chain

def sturm_sign_changes(chain, x):
    s = 0; last = None
    for q in chain:
        v = poly_eval(q, x)
        if v != 0:
            if last is not None and (v > 0) != (last > 0): s += 1
            last = v
    return s

def pos_on_halfline(p, lo):
    if poly_eval(p, F(lo)) <= 0: return False, 'p(lo) <= 0'
    chain = sturm_chain(p)
    big = F(10)**12
    n_roots = sturm_sign_changes(chain, F(lo)) - sturm_sign_changes(chain, big)
    return n_roots == 0, f'real roots in [lo,big)={n_roots}'

# ---------------------------------------------------------------- shapes

def skeleton_of(c):
    return (c['readings'], tuple(e[4] if e[4] != 'path' else 'path' for e in c['cycle']))

def slots_of(c):
    return tuple(x for e in c['cycle'] for x in e[5])

def slot_readings(c):
    """Per slot, the reading whose lap it is (mechanism-derived from the walk)."""
    cyc = c['cycle']
    rd = c['readings']          # rd[i] -> rd[i+1] is edge i (closed)
    out = []
    for i, e in enumerate(cyc):
        kind, laps = e[4], e[5]
        tail, head = rd[i], rd[(i + 1) % len(rd)]
        if kind in ('cand_entry', 'z_entry'):
            # entry row of the zone at the TAIL reading, frontier at the HEAD reading
            out.append((tail, head))
        elif kind in ('cand_progress', 'z_progress'):
            # progress row: frontier at the TAIL, zone at the HEAD
            out.append((head, tail))
        elif kind in ('cand_irred', 'z_irred'):
            # irred row: (i-2)-zone at the TAIL, zone at the HEAD
            out.append((head, tail))
        else:
            out.append((None, None))
    return out

def free_eligible(c):
    """Per slot: is the slot window-determined (free-eligible)?
    candidate lap = slot 0 of the candidate edge; death-frontier lap = slot 1 of the
    candidate entry/progress edge; anchored reading-6 slots."""
    is_anchored = c['member'][0] == 'anchored'
    sr = slot_readings(c)
    out = []
    for i, e in enumerate(c['cycle']):
        kind = e[4]
        for pos in range(len(e[5])):
            if i == 0 and pos == 0:
                out.append(True)                       # the candidate lap
            elif i == 0 and pos == 1 and kind in ('cand_entry', 'cand_progress'):
                out.append(True)                       # the death-frontier lap
            elif is_anchored and sr[i][pos] == 6:
                out.append(True)                       # the window-pinned reading
            else:
                out.append(False)
    return out

def approx_shape(c1, c2, free1, free2):
    s1, s2 = slots_of(c1), slots_of(c2)
    if len(s1) != len(s2): return False
    b1, b2 = c1['base'], c2['base']
    for x, y, f1, f2 in zip(s1, s2, free1, free2):
        if x == y: continue
        if x - b1 == y - b2: continue
        if f1 and f2: continue                          # both window-determined
        return False
    return True

def id_of_shape(c):
    """A per-cycle shape id: skeleton + the mixed abs/offset pattern (abs slots as values,
    window-determined slots by offset).  Used only for the Part G stability census (the
    authoritative shapes are the greedy clusters)."""
    slots = slots_of(c)
    b = c['base']
    fr = free_eligible(c)
    return (c['readings'], tuple(e[4] for e in c['cycle']),
            tuple(slots[s] if not fr[s] else None for s in range(len(slots))),
            tuple(slots[s] - b if fr[s] else None for s in range(len(slots))))

def cluster_shapes(cycles):
    shapes = []
    freeof = {}
    for c in cycles:
        freeof[id(c)] = free_eligible(c)
    for c in sorted(cycles, key=lambda c: (c['base'], skeleton_of(c), slots_of(c))):
        placed = False
        for sh in shapes:
            if skeleton_of(sh['insts'][0]) != skeleton_of(c): continue
            if all(approx_shape(c, d, freeof[id(c)], freeof[id(d)]) for d in sh['insts']):
                sh['insts'].append(c); sh['bases'].add(c['base']); placed = True
                break
        if not placed:
            shapes.append(dict(insts=[c], bases={c['base']}))
    return shapes

def resolve_roles(sh):
    insts = sh['insts']
    slots = [slots_of(c) for c in insts]
    frees = [free_eligible(c) for c in insts]
    nslot = len(slots[0])
    roles = []
    for s in range(nslot):
        vals = [sl[s] for sl in slots]
        freeable = all(f[s] for f in frees)
        if len(set(vals)) == 1:
            roles.append(('abs', vals[0]))
        elif all(v == c['base'] for v, c in zip(vals, insts)):
            roles.append(('tied0', None))
        elif len(set(v - c['base'] for v, c in zip(vals, insts))) == 1:
            roles.append(('tied', vals[0] - insts[0]['base']))
        elif freeable:
            offs = [v - c['base'] for v, c in zip(vals, insts)]
            roles.append(('free', (min(offs), max(offs))))
        else:
            roles.append(('INCONSISTENT', tuple(sorted(set(vals)))))
    return roles

# ---- symbolic product (Sturm tail) and box bounds (branch-and-bound) ----

def slot_poly(r):
    if r[0] == 'abs': return [F(r[1])]
    if r[0] in ('tied', 'tied0'): return [F(r[1] or 0), F(1)]
    return None

CONST_KINDS = {'weak': (1, 1), 'region6': (1, 17), 'region7': (1, 25),
               'front_lo': (1, 7), 'front_hi': (5841, 833)}

def edge_factor_sym(kind, sps, is_self):
    if kind in ('z_entry', 'cand_entry'):
        # entry row u_zone < ((8*frontier_lap+1)/(8*zone_lap-1)) u_frontier:
        # slots are (zone lap, frontier lap); the numerator carries the FRONTIER lap.
        return (poly_add([F(1)], poly_mul([F(8)], sps[1])),
                poly_add([F(-1)], poly_mul([F(8)], sps[0])))
    if kind in ('z_progress', 'cand_progress'):
        return (poly_add([F(1)], poly_mul([F(8)], sps[0])),
                poly_add([F(1)], poly_mul([F(8)], sps[1])))
    if kind in ('z_irred', 'cand_irred'):
        return (poly_add([F(-1)], poly_mul([F(8)], sps[0])),
                poly_add([F(1)], poly_mul([F(8)], sps[1])))
    if kind == 'apex':
        return ([F(33)], poly_mul([F(7)], poly_add(poly_mul([F(8)], sps[0]), [F(-1)])))
    if kind == 'cover_floor':
        return (poly_add([F(1)], poly_mul([F(8)], sps[0])), [F(7)])
    if kind == 'cover_entry':
        return ([F(7)], poly_add(poly_mul([F(8)], sps[0]), [F(-1)]))
    if kind == 'strip_entry':
        return ([F(1)], poly_add(poly_mul([F(8)], sps[0]), [F(-1)]))
    if kind == 'strip_exit':
        return (poly_add([F(1)], poly_mul([F(8)], sps[0])), [F(1)])
    if kind == 'Bcap':
        return (poly_add([F(1)], poly_mul([F(8)], sps[0])), [F(1)] if is_self else [F(7)])
    n, d = CONST_KINDS[kind]
    return ([F(n)], [F(d)])

def shape_polys(sh, roles, pin=None):
    inst0 = sh['insts'][0]
    is_self = inst0['member'][0] == 'self'
    A, B = [F(1)], [F(1)]
    si = 0
    for e in inst0['cycle']:
        kind = e[4]; nl = len(e[5])
        sps = []
        for s in range(si, si + nl):
            r = roles[s]
            if r[0] == 'free':
                off = pin[s] if pin is not None else r[1][0]
                sps.append([F(off), F(1)])
            else:
                sps.append(slot_poly(r))
        si += nl
        wn, wd = edge_factor_sym(kind, sps, is_self)
        A = poly_mul(A, wn); B = poly_mul(B, wd)
    return A, B

def deficit_law(A, B):
    """The exact drift law: 1 - P = (B-A)/B ~ gamma/b with gamma = lead(B-A)/lead(B)
    (gamma > 0: the product approaches 1 from below; gamma < 0: from above)."""
    D = poly_add(B, poly_neg(A))
    if all(c == 0 for c in D): return 'P == 1 identically'
    dB, dD = len(B) - 1, len(D) - 1
    if dD == dB: return f'P -> {A[-1]/B[-1]} (not -> 1)'
    gamma = D[dD] / B[dB] if dD >= 0 else F(0)
    return f'P = 1 - ({gamma})/b + O(1/b^2)'

def edge_bounds(kind, wins, is_self):
    if kind in ('z_entry', 'cand_entry'):
        return (8*wins[0][1] + 1, 8*wins[1][0] - 1)
    if kind in ('z_progress', 'cand_progress'):
        return (8*wins[0][1] + 1, 8*wins[1][0] + 1)
    if kind in ('z_irred', 'cand_irred'):
        return (8*wins[0][1] - 1, 8*wins[1][0] + 1)
    if kind == 'apex':        return (33, 7*(8*wins[0][0] - 1))
    if kind == 'cover_floor': return (8*wins[0][1] + 1, 7)
    if kind == 'cover_entry': return (7, 8*wins[0][0] - 1)
    if kind == 'strip_entry': return (1, 8*wins[0][0] - 1)
    if kind == 'strip_exit':  return (8*wins[0][1] + 1, 1)
    if kind == 'Bcap':        return (8*wins[0][1] + 1, 1 if is_self else 7)
    n, d = CONST_KINDS[kind]
    return (n, d)

def pattern_polys(sh, free_offs):
    """A, B for the shape's product with the FREE slots pinned to the offset tuple
    free_offs (base + offset); abs slots constant; tied slots base + c."""
    inst0 = sh['insts'][0]
    is_self = inst0['member'][0] == 'self'
    roles = resolve_roles(sh)
    frees = [i for i, r in enumerate(roles) if r[0] == 'free']
    pin = dict(zip(frees, free_offs))
    return shape_polys(sh, roles, pin=pin)

def killing_set(D, b_min):
    """The exact killing set K = {integer b >= b_min : D(b) >= 0} (the kill criterion is
    P <= 1 with a strict edge; D = B - A).  With lead(D) = L, every real root r obeys
    |r| <= R := 1 + max|a_i/L| (Cauchy), so the sign for b > ceil(R) is sign(L) and the
    finite range [b_min, ceil(R)+1] decides everything by exact evaluation.
    Returns dict(kind, intervals, tail, minval, argmin, tangencies, deg):
      kind 'ALL'      -- K = [b_min, inf)
          'FINITE'    -- K a finite union of bounded intervals (L < 0)
          'SEGMENTS'  -- K a union of intervals, one unbounded to +inf (L > 0)
          'ZERO'      -- D identically 0.
      intervals: the components of K as [a, b] pairs (b None = unbounded)."""
    D2 = list(D)
    while D2 and D2[-1] == 0: D2.pop()
    if not D2 or all(c == 0 for c in D2):
        return dict(kind='ZERO', intervals=[(b_min, None)], tail=None, minval=F(0),
                    argmin=None, tangencies=[], deg=0)
    L = D2[-1]
    deg = len(D2) - 1
    R = F(1) + max((abs(c / L) for c in D2[:-1] if c != 0), default=F(0))
    hi = max(int(R) + 1, b_min)
    vals = [(b, poly_eval(D2, F(b))) for b in range(b_min, hi + 1)]
    tail_kill = (L > 0)          # sign beyond hi
    # K within [b_min, hi]: b with D(b) >= 0; beyond: all (if tail_kill) or none
    live = [b for b, v in vals if v >= 0]
    tang = [b for b, v in vals if v == 0]
    mv = min(vals, key=lambda t: t[1])
    # build intervals over [b_min, inf)
    pts = sorted(set([b for b, v in vals if v >= 0] + ([hi + 1] if tail_kill else [])))
    intervals = []
    for b in pts:
        if intervals and intervals[-1][1] == b - 1:
            intervals[-1] = (intervals[-1][0], b)
        else:
            intervals.append((b, b))
    if tail_kill and intervals and intervals[-1][1] >= hi:
        intervals[-1] = (intervals[-1][0], None)
        kind = 'ALL' if intervals[0][0] == b_min and len(intervals) == 1 else 'SEGMENTS'
    else:
        kind = 'FINITE'
    if intervals and intervals[0][0] == b_min and len(intervals) == 1 and intervals[0][1] is None:
        kind = 'ALL'
    return dict(kind=kind, intervals=intervals, tail=tail_kill, minval=mv[1],
                argmin=mv[0], tangencies=tang, deg=deg)

# ---------------------------------------------------------------- report helpers

def fmt_readings(readings):
    return '->'.join(str(x) for x in readings[:-1]) + '->(closed)'

def fmt_roles(roles):
    out = []
    for r in roles:
        if r[0] == 'abs': out.append(f'abs={r[1]}')
        elif r[0] == 'tied0': out.append('tied=base')
        elif r[0] == 'tied': out.append(f'tied{r[1]:+d}')
        elif r[0] == 'free': out.append(f'free{r[1][0]:+d}..{r[1][1]:+d}')
        else: out.append('INCONSISTENT')
    return ', '.join(out)

def factorize(n):
    fs = []; d = 2
    while d*d <= n:
        while n % d == 0:
            fs.append(d); n //= d
        d += 1
    if n > 1: fs.append(n)
    return fs

# ---------------------------------------------------------------- main

def main():
    P = print

    P('== v3 uniformity lemma v1: killing-cycle shape inventory + per-shape verification ==')
    P('exact Fraction arithmetic throughout; existing census artifacts read-only.')
    P('')
    P('## A. full replay validation (rejection multisets + certificate products)')
    all_cycles, self_cycles, val = build_all()
    P(f"death nodes replayed: rejection-multiset match {val['rej_ok']}/{val['rej_ok']+val['rej_bad']}")
    P(f"certificate products: exact match {val['prod_ok']}/{val['prod_ok']+val['prod_bad']}"
      f"  (irred cross-checked vs the 9 table corrections: {val['irred_corr_ok']}/"
      f"{val['irred_corr_ok']+val['irred_corr_bad']})")
    anch_cycles = [c for cs in all_cycles.values() for c in cs]
    self_all = [c for cs in self_cycles.values() for c in cs]
    P(f'killing cycles: anchored {len(anch_cycles)}, self {len(self_all)}')
    P('')

    # ---------- Part B ----------
    P('## B. skeletons (cyclic reading tuple x edge-kind tuple)')
    for label, cycs in (('ANCHORED (nonvacuous: k=15/17/25)', anch_cycles),
                        ('SELF (m=5..10)', self_all)):
        sk = Counter(skeleton_of(c) for c in cycs)
        bylen = Counter(len(c['cycle']) for c in cycs)
        P(f'{label}: {len(cycs)} killing cycles; {len(sk)} skeletons; '
          f'cycle lengths {dict(sorted(bylen.items()))}')
    kinds_seen = Counter(e[4] for c in anch_cycles + self_all for e in c['cycle'])
    P('edge kinds in use: ' + ', '.join(f'{k}:{v}' for k, v in sorted(kinds_seen.items())))
    P('')
    P('anchored skeletons in full:')
    skc = Counter(skeleton_of(c) for c in anch_cycles)
    for (rd, kd), n in sorted(skc.items(), key=lambda t: (-t[1], t[0])):
        P(f'  {n:3d}x {fmt_readings(rd)} | {"+".join(kd)}')
    P('')
    P('self skeletons with >=100 instances:')
    sks = Counter(skeleton_of(c) for c in self_all)
    big = [(rd, kd, n) for (rd, kd), n in sks.items() if n >= 100]
    for rd, kd, n in sorted(big, key=lambda t: (-t[2], t[0])):
        P(f'  {n:5d}x {fmt_readings(rd)} | {"+".join(kd)}')
    P(f'  (plus {len(sks) - len(big)} skeletons with < 100 instances)')
    P('')

    # ---------- Part C ----------
    P('## C. shapes (exact greedy clique cover; role rule: slot equal / equal-offset-from-base')
    P('   / free on window-determined slots: candidate lap, death-frontier lap, anchored '
      'reading-6 laps)')
    def shape_table(cycs, label):
        shapes = cluster_shapes(cycs)
        sizes = sorted((len(sh['insts']) for sh in shapes), reverse=True)
        tot = sum(sizes); cum = 0; marks = {}
        for i, s in enumerate(sizes):
            cum += s
            for th, nm in ((0.5, '50%'), (0.9, '90%'), (0.99, '99%'), (1.0, '100%')):
                if cum >= tot*th and nm not in marks: marks[nm] = i + 1
        P(f'{label}: {tot} cycles -> {len(shapes)} shapes (UPPER bound; greedy may over-split)')
        P(f'  coverage: top-{marks.get("50%")} shapes reach 50% of cycles, top-{marks.get("90%")} '
          f'reach 90%, top-{marks.get("99%")} reach 99%, all {marks.get("100%")} for 100%')
        single_base = sum(1 for sh in shapes if len(sh['bases']) == 1)
        multi_base = len(shapes) - single_base
        P(f'  shapes realized at MORE than one base (the cross-member grammar): {multi_base}; '
          f'single-base: {single_base}')
        return shapes

    anch_shapes = shape_table(anch_cycles, 'ANCHORED')
    self_shapes = shape_table(self_all, 'SELF')
    P('')
    P('ANCHORED multi-base shapes (the cross-member recurring grammar):')
    for sh in sorted(anch_shapes, key=lambda sh: -len(sh['insts'])):
        if len(sh['bases']) < 2: continue
        roles = resolve_roles(sh)
        insts = sh['insts']
        worst = max(c['product'] for c in insts)
        P(f'  [{len(insts):3d}x] {fmt_readings(insts[0]["readings"])} | '
          f'{"+".join(e[4] for e in insts[0]["cycle"])} | bases {sorted(sh["bases"])}')
        P(f'        roles: {fmt_roles(roles)}; worst instance product {worst} = '
          f'{float(worst):.6f} (<1: {worst<1})')
    P('')
    P('SELF multi-base shapes with >=30 instances (the dominant grammar):')
    dom = [sh for sh in sorted(self_shapes, key=lambda sh: -len(sh['insts']))
           if len(sh['insts']) >= 30 and len(sh['bases']) >= 2]
    for sh in dom:
        roles = resolve_roles(sh)
        insts = sh['insts']
        worst = max(c['product'] for c in insts)
        bm = {}
        for c in insts:
            bm.setdefault(c['base'], []).append(c['product'])
        summ = '; '.join(f'm={b}:n={len(v)},max={max(v)}' for b, v in sorted(bm.items()))
        P(f'  [{len(insts):4d}x] {fmt_readings(insts[0]["readings"])} | '
          f'{"+".join(e[4] for e in insts[0]["cycle"])}')
        P(f'        roles: {fmt_roles(roles)}')
        P(f'        {summ}')
        P(f'        worst overall {worst} = {float(worst):.6f} (<1: {worst<1})')
    n_dom = sum(len(sh['insts']) for sh in dom)
    P(f'  -> these {len(dom)} dominant multi-base shapes cover {n_dom}/{len(self_all)} cycles '
      f'({100*n_dom/len(self_all):.2f}%)')
    P('')

    # ---------- Part D ----------
    P('## D. per-shape verification over ALL valid offset bases (exact)')
    P('A shape\'s lap slots split into ABS (constant), TIED (base + constant offset) and FREE')
    P('(window-determined: the candidate lap, the death-frontier lap, and -- anchored family')
    P('only -- the reading-6 laps).  The FREE slots are verified on the shape\'s observed')
    P('OFFSET-PATTERN set (the finite set of offset tuples realized across the family -- the')
    P('translation grammar of E891/E892), NOT an independent product box: the candidate and')
    P('frontier laps are coupled by the search semantics (a candidate below the frontier is')
    P('not a valid rejection), so per-pattern verification is the honest domain.')
    P('Per offset pattern the product is P(base) = A(base)/B(base); the kill criterion is')
    P('P <= 1 with a strict edge (every cycle here carries the strict candidate edge), and')
    P('P < 1 is the generic case.  For INTEGER bases b >= b_min this is decided exactly by')
    P('the Cauchy bound: D := B - A with lead(D) > 0 has every real root r in |r| <=')
    P('R := 1 + max|a_i/lead|, so D(b) > 0 for all b > R and the finite range [b_min,')
    P('ceil(R)] is evaluated exactly.  Sturm sequences over Fractions cross-check the real')
    P('half-line.  Families: SELF verified for ALL m >= 5; ANCHORED at its realized base-')
    P('period bases {15,17,25} (beyond the base period the regime is VACUOUS -- E892: k=48')
    P('admits no hinge word -- and that regime is the upstream-cycle lemma\'s to close).')
    P('')

    def shape_free_patterns(sh):
        """The distinct free-slot offset tuples realized by the shape's instances."""
        insts = sh['insts']
        roles = resolve_roles(sh)
        frees = [i for i, r in enumerate(roles) if r[0] == 'free']
        pats = set()
        for c in insts:
            slots = slots_of(c)
            pats.add(tuple(slots[i] - c['base'] for i in frees))
        return frees, sorted(pats)

    def symbolic_selfcheck(sh):
        """The symbolic product at each realized (base, pattern) must reproduce the
        instance's recorded product exactly (validates the symbolic layer)."""
        roles = resolve_roles(sh)
        frees = [i for i, r in enumerate(roles) if r[0] == 'free']
        bad = 0
        for c in sh['insts']:
            slots = slots_of(c)
            tau = tuple(slots[i] - c['base'] for i in frees)
            A2, B2 = pattern_polys(sh, tau)
            val = poly_eval(A2, F(c['base'])) / poly_eval(B2, F(c['base']))
            if val != c['product']:
                bad += 1
        return bad

    def verify_family(shapes, label, tail_min, realized_only, maxprint=45):
        counts = Counter()
        printed = 0
        rows = []
        for sh in shapes:
            roles = resolve_roles(sh)
            insts = sh['insts']
            worst_inst = max(c['product'] for c in insts)
            nfree = sum(1 for r in roles if r[0] == 'free')
            frees, pats = shape_free_patterns(sh)
            all_strict = all(e[3] for c in insts for e in c['cycle'])
            sc_bad = symbolic_selfcheck(sh)
            if sc_bad:
                counts['SYMBOLIC-SELFCHECK FAIL'] += 1
                rows.append((len(insts), sh, roles, worst_inst, None, [], 'SYMBOLIC-SELFCHECK FAIL',
                             nfree, all_strict, sc_bad))
                continue
            per = []
            kinds = []
            for tau in pats:
                A2, B2 = pattern_polys(sh, tau)
                D2 = poly_add(B2, poly_neg(A2))
                vd = killing_set(D2, tail_min)
                st_ok, st_why = pos_on_halfline(D2, tail_min)
                vd['sturm'] = (st_ok, st_why)
                # observed occurrence bases of this pattern, and their coverage by K
                occ = sorted(set(c['base'] for c in insts
                                 if tuple(slots_of(c)[i] - c['base'] for i in frees) == tau))
                vd['occ'] = occ
                covered = True
                for b in occ:
                    ink = any(b >= x and (y is None or b <= y) for (x, y) in vd['intervals'])
                    if not ink: covered = False
                vd['covered'] = covered
                per.append((tau, vd))
                kinds.append(vd['kind'])
            if realized_only:
                realized_ok = all(c['product'] < 1 or (c['product'] == 1 and any(e[3] for e in c['cycle']))
                                  for c in insts)
                verdict = ('PROVED (realized bases, exact)' if realized_ok
                           else 'FAIL at a realized instance')
            elif all(k in ('ALL', 'ZERO') for k in kinds):
                verdict = f'PROVED-UNIFORM: kills for EVERY integer m >= {tail_min}, every pattern'
            elif all(vd['covered'] for (_, vd) in per):
                verdict = (f'PROVED-SCOPED: every pattern kills on its exact m-set '
                           f'(all observed occurrences covered); the m-dependence of the '
                           f'pattern grammar is the named open piece')
            else:
                verdict = 'FAIL: a pattern occurrence outside its killing set'
            counts[verdict] += 1
            rows.append((len(insts), sh, roles, worst_inst, None, per, verdict,
                         nfree, all_strict, None))
        for (ni, sh, roles, worst_inst, _, per, verdict, nfree, all_strict, _) \
                in sorted(rows, key=lambda t: -t[0]):
            if ni < 2 or printed >= maxprint: continue
            printed += 1
            insts = sh['insts']
            P(f'  [{ni:4d}x] {fmt_readings(insts[0]["readings"])} | '
              f'{"+".join(e[4] for e in insts[0]["cycle"])} | free {nfree} | {verdict}')
            P(f'        roles: {fmt_roles(roles)}; worst realized {worst_inst} = '
              f'{float(worst_inst):.6f}')
            for (tau, vd) in per[:6]:
                if vd['kind'] == 'ALL':
                    msg = (f"        pattern {tau}: kills for ALL m >= {tail_min} "
                           f"(min D = {vd['minval']} at m={vd['argmin']}; deg D = {vd['deg']})")
                elif vd['kind'] == 'ZERO':
                    msg = f"        pattern {tau}: D == 0 identically (weak kill everywhere)"
                else:
                    iv = ', '.join(f'[{a},{b}]' if b is not None else f'[{a},inf)'
                                   for (a, b) in vd['intervals'])
                    msg = (f"        pattern {tau}: kills on m in {iv}; occurrences at "
                           f"m in {vd['occ']} (covered: {vd['covered']}); deg D = {vd['deg']}")
                msg += '; Sturm real-half-line: ' + ('D>0' if vd['sturm'][0] else vd['sturm'][1])
                P(msg)
            if len(per) > 6:
                kinds_rest = [vd['kind'] for (_, vd) in per[6:]]
                P(f'        ... {len(per) - 6} further patterns: {dict(Counter(kinds_rest))}')
        P(f'  -- {label} verdicts over {len(shapes)} shapes: ' +
          '; '.join(f'{k}: {v}' for k, v in sorted(counts.items())))
        P('')
        return counts

    P('#### SELF family (ALL integer m >= 5, every observed offset pattern)')
    cself = verify_family(self_shapes, 'SELF', 5, realized_only=False)
    P('#### ANCHORED family (realized base-period bases; the nonvacuous regime)')
    canch = verify_family(anch_shapes, 'ANCHORED', 13, realized_only=True)

    # ---------- Part E ----------
    P('## E. residue check: shapes realized at only one member')
    for label, shapes in (('ANCHORED', anch_shapes), ('SELF', self_shapes)):
        res = defaultdict(list)
        for sh in shapes:
            if len(sh['bases']) == 1:
                res[next(iter(sh['bases']))].append(sh)
        P(f'{label}: single-base shapes by member: ' +
          ', '.join(f'{k}:{len(v)}' for k, v in sorted(res.items())) +
          f'  (total {sum(len(v) for v in res.values())}/{len(shapes)})')
        for b, shs in sorted(res.items()):
            big = [sh for sh in shs if len(sh['insts']) >= 4]
            for sh in sorted(big, key=lambda sh: -len(sh['insts']))[:8]:
                insts = sh['insts']
                worst = max(c['product'] for c in insts)
                roles = resolve_roles(sh)
                P(f'  residue at base {b} [{len(insts)}x]: '
                  f'{fmt_readings(insts[0]["readings"])} | '
                  f'{"+".join(e[4] for e in insts[0]["cycle"])} | {fmt_roles(roles)} | '
                  f'worst {worst} = {float(worst):.6f}')
    P('')

    # ---------- Part G ----------
    P('## G. grammar stability across the family (the translation law, tabulated)')
    P('How many shapes occur per member, the cumulative union size, and the core grammar')
    P('(shapes realized at EVERY member) -- the empirical stability of the pattern grammar')
    P('that the uniformity lemma\'s hypothesis rests on.')
    for label, shapes, cycs, bases in (('SELF (m=5..10)', self_shapes, self_all, list(range(5, 11))),
                                       ('ANCHORED (k=15/17/25)', anch_shapes, anch_cycles, [15, 17, 25])):
        sk_per_m = {}; sh_per_m = {b: 0 for b in bases}
        for c in cycs:
            sk_per_m.setdefault(c['base'], set()).add(skeleton_of(c))
        core_sk = set.intersection(*[sk_per_m[b] for b in bases]) if bases else set()
        sk_cum = set(); sk_cumsizes = []
        for b in bases:
            sk_cum |= sk_per_m.get(b, set()); sk_cumsizes.append(len(sk_cum))
        for sh in shapes:
            for b in sh['bases']:
                if b in sh_per_m: sh_per_m[b] += 1
        core_sh = sum(1 for sh in shapes if all(b in sh['bases'] for b in bases))
        P(f'{label}: SKELETONS per member {dict(zip(bases, [len(sk_per_m.get(b, set())) for b in bases]))}; '
          f'cumulative skeleton union {dict(zip(bases, sk_cumsizes))}; core skeletons (all members): '
          f'{len(core_sk)}/{len(set(skeleton_of(c) for c in cycs))}')
        P(f'   shapes (clusters) per member {sh_per_m}; clusters realized at EVERY member: {core_sh}')
    P('')

    # ---------- Part F ----------
    P('## F. ladder-law reduction + exact drift law for the dominant shapes')
    P('--- SELF dominant shapes: per-pattern Sturm verdict on the real half-line m >= 5 and')
    P('    the exact drift law (the deficit 1 - P ~ gamma/m with gamma computed exactly) ---')
    shown = 0
    for sh in sorted(self_shapes, key=lambda sh: -len(sh['insts'])):
        if len(sh['insts']) < 30: continue
        frees, pats = shape_free_patterns(sh)
        if not frees or len(pats) > 24: continue
        inst0 = sh['insts'][0]
        c0 = min(sh['insts'], key=lambda c: c['base'])
        P(f'  [{len(sh["insts"]):4d}x] {fmt_readings(inst0["readings"])} | '
          f'{"+".join(e[4] for e in inst0["cycle"])}')
        P(f'    free slots {frees}; {len(pats)} offset patterns: {pats}')
        P(f'    instance at m={c0["base"]}: ' +
          ' * '.join(f'{e[2]}[{e[4]}{e[5]}]' for e in c0['cycle']) +
          f' = {c0["product"]} = {float(c0["product"]):.6f}')
        allpass = True
        gammas = []
        kinds = Counter()
        for tau in pats:
            A2, B2 = pattern_polys(sh, tau)
            D2 = poly_add(B2, poly_neg(A2))
            vd = killing_set(D2, 5)
            kinds[vd['kind']] += 1
            if vd['kind'] not in ('ALL', 'ZERO'): allpass = False
            gammas.append(deficit_law(A2, B2))
        uniq = sorted(set(str(g) for g in gammas))
        P(f'    killing-set kinds over the {len(pats)} patterns: {dict(kinds)}; '
          f'drift laws: {uniq[:3]}{" ..." if len(uniq) > 3 else ""}')
        shown += 1
        if shown >= 14: break
    P('')
    P('--- ANCHORED: every shape with >=2 instances, all distinct instances listed ---')
    for sh in sorted(anch_shapes, key=lambda sh: -len(sh['insts'])):
        if len(sh['insts']) < 2: continue
        roles = resolve_roles(sh)
        inst0 = sh['insts'][0]
        frees, pats = shape_free_patterns(sh)
        extra = ''
        if not frees:
            A, Bp = shape_polys(sh, roles)
            ok, why = pos_on_halfline(poly_add(Bp, poly_neg(A)), 13)
            dl = deficit_law(A, Bp)
            extra = f'; Sturm k>=13: {"PASS" if ok else "FAIL (" + why + ")"}; drift: {dl}'
        P(f'  [{len(sh["insts"]):3d}x] {fmt_readings(inst0["readings"])} | '
          f'{"+".join(e[4] for e in inst0["cycle"])} | roles: {fmt_roles(roles)}{extra}')
        seen = set()
        for c in sorted(sh['insts'], key=lambda c: c['base']):
            key = (c['base'], str(c['product']))
            if key in seen: continue
            seen.add(key)
            P(f'    k={c["base"]}: ' + ' * '.join(f'{e[2]}[{e[4]}{e[5]}]' for e in c['cycle'])
              + f' = {c["product"]} = {float(c["product"]):.6f}')
    P('')
    P('== end of report ==')

if __name__ == '__main__':
    main()
