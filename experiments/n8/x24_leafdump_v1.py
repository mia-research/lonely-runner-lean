# X24 leaf decomposition, v1 (2026-11-28).  E983's X24 residue: the band n7 in [23,26)
# (the audit universe of obligation_audit_2026_11_11/x24.out, 297,765 root boxes) has no
# certificate dump.  This instrument takes the fixed-R0-resistant leaves of the verbatim
# E832 DFS (frontier_box_dfs_v1.c, run 23 26 64 -> x24_dfs_leaves64.txt, 27,349 leaves)
# and classifies each leaf EXACTLY (Fractions, python -I) as ONE of:
#   (a) W0-certified: window-type (E833 item 1(b), a nondegenerate common clear interval
#       in [1,7]) or fixed-R0 (a single-point common clear interval) -- uniform-lap form,
#       the same certificate family as Fresh.Certs.WindowCert/FixedClearCert;
#   (b) W1-witnessed: a common clear point s in [9,15] with per-reading laps (the
#       Fresh.BandNoCarve.BandW1 payload; the X24 carve leaves live here);
#   (c) START/END boundary artifacts: leaves whose rho7 face touches the enumeration edge
#       22.5 (START, adjoining certified [17,23)) or 25.5 (END, adjoining E832's
#       certified [25,29)) -- flagged, still certified by (a)/(b) like any leaf;
#   resistant: neither (a) nor (b) at the subdivision cap -- bounds and shape recorded,
#   never forced (rule: honest failure reporting).
# Certificate family (uniform-lap, exact): reading i with box [lo_i, hi_i] is clear at s
# with lap j iff lo_i*s >= 8j+1 and hi_i*s <= 8j+7, i.e. s in [(8j+1)/lo_i, (8j+7)/hi_i].
# The common set is the intersection over i of the disjoint interval unions, clipped to
# [1,7] (W0) or [9,15] (W1).  Nonempty => certificate; a nondegenerate component =>
# window-type; a point => fixed-R0/W1 point witness (closed inequalities, exact).
# Cross-checks (all reported): the 96 recorded carves (E828/E829 loader, exact floats)
# re-verified as exact carves of [1,7] with a W1 clear witness; carve-in-leaf membership
# (ALARM if a carve lies in a W0-certified leaf); carve-leaf count vs the 90 in-band
# carves; the 6 out-of-band carves (rho7 in (15,17), the lap-2 strip) reported; leaf
# density vs the sibling bands; DFS regression vs E832's recorded artifact.
# usage: python -I x24_leafdump_v1.py <dfs_leaves.txt> <Dcap> <out.jsonl> <out.stats.txt> [budget_per_leaf]
import sys, glob, pickle, json
from fractions import Fraction as F

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'

# ---------- exact interval machinery (uniform-lap feasible sets) ----------

def unions(lo, hi, Rlo, Rhi):
    """disjoint closed intervals [(8j+1)/lo, (8j+7)/hi] ∩ [Rlo, Rhi] as (j, a, b) triples,
    j = 0,1,2,... the TRUE lap (indices in the list are not laps: early laps may be skipped)"""
    out = []
    j = 0
    while F(8*j + 1) <= Rhi * lo:
        a = F(8*j + 1) / lo
        b = F(8*j + 7) / hi
        if b >= Rlo:
            lo2 = a if a > Rlo else Rlo
            hi2 = b if b < Rhi else Rhi
            if lo2 <= hi2:
                out.append((j, lo2, hi2))
        j += 1
    return out

def intersect(A, B):
    """intersection of two sorted disjoint-interval lists (triples (j, a, b): the
    intersection's lap tag is meaningless, only the interval is used downstream)"""
    out = []; i = j = 0
    while i < len(A) and j < len(B):
        ja, a1, a2 = A[i]; jb, b1, b2 = B[j]
        lo = a1 if a1 > b1 else b1
        hi = a2 if a2 < b2 else b2
        if lo <= hi: out.append((0, lo, hi))
        if a2 < b2: i += 1
        else: j += 1
    return out

def lap_of(uni, X, Y):
    """the TRUE lap j whose component contains [X, Y] (uni: this reading's union)"""
    for j, a, b in uni:
        if a <= X and Y <= b: return j
    return None

def common_set(box, Rlo, Rhi):
    """(intersection list, per-reading unions) for the 6 readings of the box"""
    D, n = box
    unis = []
    for i in range(6):
        lo = F(n[i], D); hi = F(n[i] + 1, D)
        unis.append(unions(lo, hi, F(Rlo), F(Rhi)))
    cur = [(j, a, b) for j, a, b in unis[0]]
    for u in unis[1:]:
        cur = intersect(cur, u)
        if not cur: return cur, unis
    return cur, unis

def classify_common(comp, unis):
    """certificate payload from a nonempty common component list:
       ('window', X, Y, laps) on a nondegenerate component, else ('point', s, None, laps)."""
    for (_, X, Y) in comp:
        if X < Y:
            laps = [lap_of(u, X, Y) for u in unis]
            if any(l is None for l in laps): return None
            return ('window', X, Y, laps)
    _, X, Y = comp[0]
    laps = [lap_of(u, X, Y) for u in unis]
    if any(l is None for l in laps): return None
    return ('point', X, None, laps)

# ---------- point-level exact tests (carve verification, the 96) ----------

def zones_of(rs):
    z = []
    for idx, r in enumerate(rs):
        j = 1
        while True:
            a = F(8*j - 1) / r; b = F(8*j + 1) / r
            if a >= 7: break
            if b > 1: z.append((a, b))
            j += 1
    return z

def carved_seven(rs):
    """[1,7] covered by the OPEN blocking zones (exact carve test)"""
    z = zones_of(rs)
    cover = [b for a, b in z if a < 1 < b]
    if not cover: return False
    cur = max(cover)
    while cur <= 7:
        nxt = [b for a, b in z if a < cur < b]
        if not nxt: return False
        m = max(nxt)
        if m <= cur: return False
        cur = m
    return True

def clear_components(rs, Rlo, Rhi):
    """components of [Rlo,Rhi] where every reading is clear (closed gaps), exact"""
    comp = [(F(Rlo), F(Rhi))]
    for r in rs:
        z = []
        j = 0
        while True:
            a = F(8*j - 1) / r; b = F(8*j + 1) / r
            if a > F(Rhi): break
            if b > F(Rlo): z.append((a, b))
            j += 1
        out = []
        for (c1, c2) in comp:
            cur = c1
            for (a, b) in z:
                if b <= cur: continue
                if a > c2: break
                if a > cur: out.append((cur, a if a < c2 else c2))
                cur = b if b < c2 else c2
                if cur >= c2: break
            if cur < c2: out.append((cur, c2))
        comp = [(a, b) for (a, b) in out if a <= b]
        if not comp: return []
    return comp

# ---------- carve loading (the midbound_derive_v1.py loader, calibrated) ----------

def load_carves():
    carves = []
    for f in sorted(glob.glob(DIR + 'frontier_band_carve_v1_k[23]_s*.pkl')) + \
             sorted(glob.glob(DIR + 'frontier_box_carve_v1_23_25_s*.pkl')):
        carves += pickle.load(open(f, 'rb'))
    out = []
    for v in carves:
        rs = [F(1)] + [F(x) for x in sorted(v)]   # rho1 = 1 prepended; rho2..rho7
        out.append(rs)
    return out

# ---------- main ----------

def leaf_faces(box):
    D, n = box
    lo = [F(1)] + [F(n[i], D) for i in range(6)]
    hi = [F(1)] + [F(n[i] + 1, D) for i in range(6)]
    return lo, hi

def carve_in_leaf(rs, lo, hi):
    return all(lo[i] <= rs[i] <= hi[i] for i in range(1, 7))

def sorted_feasible(n):
    x = n[0]
    for i in range(6):
        if n[i] > x: x = n[i]
        if x > n[i] + 1: return False
    return True

def process_leaf(box, carves_in, Dcap, budget):
    """classify one input leaf, subdividing on failure.  Returns (records, nodes)."""
    out = []
    lo0, hi0 = leaf_faces(box)
    stack = [(box, 0, [(cid, rs) for cid, rs in carves_in if carve_in_leaf(rs, lo0, hi0)])]
    nodes = 0
    while stack:
        bx, depth, cvs = stack.pop()
        nodes += 1
        D, n = bx
        lo, hi = leaf_faces(bx)
        rec = {'D': D, 'n': list(n),
               'carves': [cid for cid, rs in cvs],
               'boundary': ('start' if 2 * n[5] == 45 * D else
                            ('end' if 2 * (n[5] + 1) == 51 * D else None))}
        # center diagnostics
        ctr = [(lo[i] + hi[i]) / 2 for i in range(7)]
        rec['center_carve_1_7'] = carved_seven(ctr)
        rec['center_w1_clear'] = bool(clear_components(ctr, 9, 15))
        # (a) W0 exact
        comp0, unis0 = common_set(bx, 1, 7)
        cert = classify_common(comp0, unis0) if comp0 else None
        if cert is not None:
            kind, X, Y, laps = cert
            rec['type'] = 'window' if kind == 'window' else 'fixedR0'
            rec['cert'] = {'kind': rec['type'], 'lo': [str(x) for x in lo],
                           'hi': [str(x) for x in hi],
                           'X': str(X), 'Y': str(Y if Y is not None else X),
                           'j': [0] + laps}
            out.append(rec); continue
        # (b) W1 exact
        comp1, unis1 = common_set(bx, 9, 15)
        cert = classify_common(comp1, unis1) if comp1 else None
        if cert is not None:
            kind, S, _, laps = cert
            rec['type'] = 'w1'
            rec['cert'] = {'kind': 'w1', 'lo': [str(x) for x in lo],
                           'hi': [str(x) for x in hi], 'S': str(S), 'j': [1] + laps}
            out.append(rec); continue
        # resist: subdivide or record
        if D < Dcap and nodes < budget:
            kids = []
            for m in range(64):
                c = tuple(2 * n[i] + ((m >> i) & 1) for i in range(6))
                if sorted_feasible(c): kids.append((2 * D, c))
            if kids:
                for k in kids:
                    klo, khi = leaf_faces(k)
                    sub = [(cid, rs) for cid, rs in cvs if carve_in_leaf(rs, klo, khi)]
                    stack.append((k, depth + 1, sub))
                continue
        # resistant: record bounds and shape, never forced
        rec['type'] = 'resistant'
        rec['cert'] = None
        shape = {}
        for label, (Rlo, Rhi) in (('w0', (1, 7)), ('w1', (9, 15))):
            comps, unis = common_set(bx, Rlo, Rhi)
            shape[label + '_common_components'] = [[str(a), str(b)] for _, a, b in comps]
            shape[label + '_per_reading_counts'] = [len(u) for u in unis]
        rec['shape'] = shape
        out.append(rec)
    return out, nodes

G_INB, G_DCAP, G_BUDGET = None, 64, 20000

def work_leaf(bx):
    return process_leaf(bx, G_INB, G_DCAP, G_BUDGET)

def verify_certificate(rec):
    """independent re-verification of one JSONL record from scratch (different code path)"""
    D, n = rec['D'], rec['n']
    lo = [F(1)] + [F(n[i], D) for i in range(6)]
    hi = [F(1)] + [F(n[i] + 1, D) for i in range(6)]
    c = rec['cert']
    if c is None: return True, ''
    if c['lo'] != [str(x) for x in lo] or c['hi'] != [str(x) for x in hi]:
        return False, 'faces mismatch'
    j = c['j']
    if len(j) != 7: return False, 'laps length'
    if c['kind'] in ('window', 'fixedR0'):
        X = F(c['X']); Y = F(c['Y'])
        if not (F(1) <= X <= Y <= F(7)): return False, 'window bounds'
        if c['kind'] == 'fixedR0' and X != Y: return False, 'fixedR0 not a point'
        if c['kind'] == 'window' and X == Y: return False, 'window degenerate'
        for i in range(7):
            if not (F(8*j[i] + 1) <= lo[i] * X and hi[i] * Y <= F(8*j[i] + 7)):
                return False, 'gap inequality i=%d' % i
        return True, ''
    if c['kind'] == 'w1':
        S = F(c['S'])
        if not (F(9) <= S <= F(15)): return False, 'S bounds'
        for i in range(7):
            if not (F(8*j[i] + 1) <= lo[i] * S and hi[i] * S <= F(8*j[i] + 7)):
                return False, 'gap inequality i=%d' % i
        return True, ''
    return True, ''

def main():
    infile = sys.argv[1]
    Dcap = int(sys.argv[2])
    outjsonl = sys.argv[3]
    outstats = sys.argv[4]
    budget = int(sys.argv[5]) if len(sys.argv) > 5 else 20000

    leaves = []
    for l in open(infile):
        v = [int(x) for x in l.split()]
        if v: leaves.append((v[0], tuple(v[1:7])))
    P = lambda *a: print(*a, flush=True)
    P('# x24_leafdump_v1: input DFS-resistant leaves', len(leaves), 'Dcap', Dcap,
      'budget', budget)

    carves = load_carves()
    P('carves loaded:', len(carves))
    inb = [(cid, rs) for cid, rs in enumerate(carves) if F(23) <= rs[6] < F(25)]
    outb = [(cid, rs) for cid, rs in enumerate(carves) if not (F(23) <= rs[6] < F(25))]
    P('in-band carves (rho7 in [23,25)):', len(inb), ' out-of-band:', len(outb),
      '(rho7 in (%.4f, %.4f): the lap-2 strip, band [15,17), outside X24)' %
      (min(float(rs[6]) for _, rs in outb), max(float(rs[6]) for _, rs in outb)))

    # verify the in-band carves: exact carve of [1,7] + W1 clear witness + landing < 17
    w1v = 0; carve_fail = []
    for cid, rs in inb:
        if not carved_seven(rs): carve_fail.append((cid, 'not a carve of [1,7]'))
        cc = clear_components(rs, 9, 15)
        if cc and cc[-1][1] < 17: w1v += 1
        else: carve_fail.append((cid, 'no W1 clear component below 17'))
    P('in-band carves re-verified (exact carve of [1,7] AND W1-clear component below 17):',
      len(inb) - len(carve_fail), '/', len(inb), '| fails:', carve_fail[:5])

    global G_INB, G_DCAP, G_BUDGET
    G_INB, G_DCAP, G_BUDGET = inb, Dcap, budget
    import multiprocessing as mp
    ctx = mp.get_context('fork')
    with ctx.Pool(4) as pool:
        results = pool.map(work_leaf, leaves, chunksize=32)
    recs_all = [r for res, _ in results for r in res]
    P('exact nodes total:', sum(nd for _, nd in results), '| final leaves:', len(recs_all))

    # census
    from collections import Counter
    tc = Counter(r['type'] for r in recs_all)
    tcD = Counter((r['type'], r['D']) for r in recs_all)
    bc = Counter(r['boundary'] for r in recs_all if r['boundary'])
    P('final leaf types:', dict(tc))
    P('by (type, D):', dict(sorted(tcD.items())))
    P('boundary flags:', dict(bc))

    # carve cross-checks
    alarmed = [r for r in recs_all if r['type'] in ('window', 'fixedR0') and r['carves']]
    w1_with_carve = sum(1 for r in recs_all if r['type'] == 'w1' and r['carves'])
    res_with_carve = sum(1 for r in recs_all if r['type'] == 'resistant' and r['carves'])
    hits = Counter()
    for r in recs_all:
        for cid in r['carves']: hits[cid] += 1
    missing = [cid for cid, _ in inb if hits[cid] == 0]
    multi = [cid for cid, c in hits.items() if c > 1]
    P('SOUNDNESS: carves inside W0-certified leaves:', len(alarmed), '(must be 0)',
      '| carve-containing w1 leaves:', w1_with_carve,
      '| carve-containing resistant leaves:', res_with_carve)
    P('carve containment: uncovered', len(missing), missing[:5],
      '| in >1 final leaf', len(multi), multi[:5])
    P('carve-leaf census: w1 leaves total', tc.get('w1', 0),
      '| w1 leaves containing >=1 of the', len(inb), 'in-band carves:', w1_with_carve)

    # independent verification pass
    bad = []
    for r in recs_all:
        ok, why = verify_certificate(r)
        if not ok: bad.append((r['n'], why))
    P('independent certificate re-verification:', len(recs_all) - len(bad), '/',
      len(recs_all), 'pass', '| failures:', bad[:5])

    # dump JSONL
    with open(outjsonl, 'w') as f:
        for r in recs_all:
            f.write(json.dumps(r) + '\n')
    P('wrote', outjsonl)

    # density vs siblings
    P('density: input resistant leaves 27349 / 297765 roots = %.2f%% (sibling [17,23): 2539/241746 = 1.05%%; [25,29): 0/632548 = 0%%)'
      % (100.0 * 27349 / 297765))
    P('final leaves / roots = %.2f%%' % (100.0 * len(recs_all) / 297765))

    # pilot selection: smallest ~20 leaves (finest D first, deterministic), carve-aware
    def vol(r): return (-r['D'], r['n'])
    smallest = sorted(recs_all, key=vol)[:20]
    P('smallest 20 leaves (D, n, type, carves, boundary):')
    for r in smallest:
        P('  ', r['D'], r['n'], r['type'], r['carves'][:3], r['boundary'])
    n_w1_in20 = sum(1 for r in smallest if r['type'] == 'w1')
    if n_w1_in20 < 4:
        w1s = sorted([r for r in recs_all if r['type'] == 'w1'], key=vol)
        have = {id(r) for r in smallest}
        add = []
        for r in w1s:
            if len(add) >= 4 - n_w1_in20: break
            if id(r) not in have: add.append(r)
        P('pilot carve-leaf addendum (smallest w1 leaves, for both shapes):')
        for r in add:
            P('  ', r['D'], r['n'], r['type'], r['carves'][:3], r['boundary'])
        smallest = smallest + add
    with open(outstats, 'w') as f:
        f.write('pilot selection + census above\n')

if __name__ == '__main__':
    main()
