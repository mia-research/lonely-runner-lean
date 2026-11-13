# leaves3739_mech_v1.py -- rule-22 closure for the five [37,39) leaves
# (E832 item 3a; E833 item 4(iii) "not understood"; E847 item 1 "outside this compression").
# Exact Fractions / integers; floats steer only.  Reads existing artifacts; writes only leaves3739_* here.
#
# Q1  rerun the E833 window-type certifier (frontier_window_cert_v1.py, same corners, same 5 sample
#     points) on the 5 D=32 boxes and on their D=64 children; record certifying types (census format).
# Q2  exact common clear window per box per depth:
#       (i)  the fixed-R0 lonely set of the box: t in [1,7] with [n_i t/D,(n_i+1)t/D] inside one closed
#            gap [8j+1,8j+7] for every reading i (E832 item 1) -- empty / point / positive;
#       (ii) per tried desc pair the certifier's [max_c X, min_c Y] = [D*na/n_ka, D*nb/(n_kb+1)].
# Q3  mechanism: (a) single-point off-grid, (b) empty at 1/32 positive at 1/64, (c) tie-plane straddler,
#     (d) a window type exists on the box but the 5-sample search misses it -- decided by an EXHAUSTIVE
#     box-level type-existence test (every desc pair, every lap vector) and a P1 plane-split side test.
# Q4  one-line datum per box (the BandNoCarve data-side discharge shape).
import sys, os, math, collections, json
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv_saved = sys.argv; sys.argv = ['x']
exec(open(os.path.join(HERE, '..', 'frontier_window_cert_v1.py')).read().split("def sorted_feasible")[0])
sys.argv = sys.argv_saved

def sorted_feasible(n):  # verbatim from frontier_window_cert_v1.py
    x = n[0]
    for i in range(6):
        if n[i] > x: x = n[i]
        if x > n[i] + 1: return False
    return True

# the 5 leaves, verbatim from frontier_box_dfs_v1_leaves_37_39.txt (D n2 n3 n4 n5 n6 n7)
BOXES = [
    ('B1', 32, (91, 123, 157, 202, 224, 1209)),
    ('B2', 32, (92, 123, 157, 202, 224, 1209)),
    ('B3', 32, (92, 123, 157, 203, 224, 1209)),
    ('B4', 32, (92, 123, 157, 203, 224, 1210)),
    ('B5', 32, (92, 123, 157, 203, 224, 1211)),
]
RN = ['rho2', 'rho3', 'rho4', 'rho5', 'rho6', 'rho7']

def dsc(a):
    return '1' if a[1] is None else '%d/%s' % (a[0], RN[a[1]])

def certify_key(D, n):  # verbatim from frontier_type_census_v1.py (E847 census)
    V = corners(D, n); tried = set()
    for u in [tuple(F(2 * n[i] + 1, 2 * D) for i in range(6)), V[0], V[63], V[21], V[42]]:
        for X, Y, xv, yv in windows(u):
            ineqs = wtype(u, X, Y, xv); k = tuple(ineqs)
            if k in tried: continue
            tried.add(k)
            if holds(ineqs, V): return (X, Y, tuple(ineqs[3 + 2 * i][0][0] for i in range(6)))
    return None

def certify_diag(D, n):
    """the E833 search with per-tried-type diagnostics"""
    V = corners(D, n); seen = set(); out = []
    for si, u in enumerate([tuple(F(2 * n[i] + 1, 2 * D) for i in range(6)), V[0], V[63], V[21], V[42]]):
        for X, Y, xv, yv in windows(u):
            ineqs = wtype(u, X, Y, xv); k = tuple(ineqs)
            if k in seen: continue
            seen.add(k)
            out.append({'sample': si, 'X': X, 'Y': Y, 'laps': tuple(ineqs[3 + 2 * i][0][0] for i in range(6)),
                        'ineqs': ineqs, 'ok': holds(ineqs, V)})
    return out

def worst_viol(ineqs, V):
    """max over corners of A*rt - B*rs over failing ineqs; None if all hold"""
    best = None
    for ii, ((A, s), (B, t)) in enumerate(ineqs):
        for u in V:
            rs = u[s] if s is not None else F(1); rt = u[t] if t is not None else F(1)
            v = A * rt - B * rs
            if v > 0 and (best is None or v > best[0]):
                best = (v, ii, (A, s), (B, t), u)
    return best

def common_window(D, n, X, Y):
    """closed-form [max_c X, min_c Y] over the 64 corners for a desc pair"""
    mx = F(1) if X[1] is None else F(X[0] * D, n[X[1]])
    mn = F(7) if Y[1] is None else F(Y[0] * D, n[Y[1]] + 1)
    return mx, mn

def lonely_set(D, n):
    """t in [1,7] that is a lonely instant for EVERY arrangement of the box:
    intersection over readings of union_j [(8j+1)D/n_i, (8j+7)D/(n_i+1)] (E832 item 1)."""
    cur = [(F(1), F(7))]
    hist = []
    for i in range(6):
        ivs = []
        j = 0
        while True:
            lo = F((8 * j + 1) * D, n[i]); hi = F((8 * j + 7) * D, n[i] + 1)
            if lo > 7: break
            if hi >= 1: ivs.append((max(lo, F(1)), min(hi, F(7))))
            j += 1
        nxt = []
        for a, b in cur:
            for lo, hi in ivs:
                c, d = (a if a > lo else lo), (b if b < hi else hi)
                if c <= d: nxt.append((c, d))
        nxt.sort()
        m = []
        for c, d in nxt:
            if m and c <= m[-1][1]:
                if d > m[-1][1]: m[-1] = (m[-1][0], d)
            else: m.append((c, d))
        hist.append((i, cur, m, ivs))
        cur = m
        if not cur: return [], hist
    return cur, hist

def exhaustive_types(D, n):
    """EXHAUSTIVE over the E833 type space (all desc pairs, all lap vectors), at box level.
    Each certificate inequality involves at most 2 independent box coordinates, so 'holds at all
    64 corners' <=> one integer worst-case inequality (worst corner = independent extremes)."""
    xdescs = [(1, None)]; ydescs = [(7, None)]
    for k in range(6):
        j = 0
        while True:
            num = 8 * j + 1
            if num * D > 7 * n[k]: break
            if num * D >= n[k] + 1: xdescs.append((num, k))
            j += 1
        j = 1
        while True:
            num = 8 * j - 1
            if num * D > 7 * n[k]: break
            if num * D >= n[k] + 1: ydescs.append((num, k))
            j += 1
    out = []
    for na, ka in xdescs:
        for nb, kb in ydescs:
            if ka is not None and na * D < n[ka] + 1: continue          # 1 <= X
            if kb is not None and nb * D > 7 * n[kb]: continue          # Y <= 7
            if ka is None and kb is None: pass                          # X <= Y
            elif ka is None:
                if (n[kb] + 1) > nb * D: continue
            elif kb is None:
                if na * D > 7 * n[ka]: continue
            elif ka == kb:
                if na > nb: continue                                    # na*rho_t <= nb*rho_t, same coordinate
            else:
                if na * (n[kb] + 1) > nb * n[ka]: continue
            laps = []; ok = True
            for i in range(6):
                # X-side: (8j+1)/rho_i <= X at every corner
                if ka is None: jx = (n[i] - D) // (8 * D)
                elif ka == i: jx = (na - 1) // 8                             # (8j+1)*rho_t <= na*rho_t, same coord
                else: jx = (na * n[i] - (n[ka] + 1)) // (8 * (n[ka] + 1))
                # Y-side: Y <= (8j+7)/rho_i at every corner
                if kb is None: jy = -((7 * D - 7 * (n[i] + 1)) // (8 * D))
                elif kb == i: jy = -((7 - nb) // 8)                          # nb*rho_t <= (8j+7)*rho_t, same coord
                else: jy = -((7 * n[kb] - nb * (n[i] + 1)) // (8 * n[kb]))
                jlo = jy if jy > 0 else 0
                if jlo > jx: ok = False; break
                laps.append(8 * jx + 1)                                  # largest valid lap (certifier convention)
            if ok: out.append(((na, ka), (nb, kb), tuple(laps)))
    return out

def children(D, n):
    out = []
    for m in range(64):
        c = tuple(2 * n[i] + ((m >> i) & 1) for i in range(6))
        if sorted_feasible(c): out.append((2 * D, c))
    return out

def dyadic_hit(iv, bits=20):
    """does the closed interval contain a grid point r/2^bits (the C certifier's grid)?"""
    lo, hi = iv; M = 1 << bits
    r_lo = math.ceil(lo * M); r_hi = math.floor(hi * M)
    return r_lo <= r_hi, r_lo, r_hi

def kill_diag(hist):
    """when the sweep empties: which reading kills the last surviving t-range, by how much (exact)"""
    i_kill = None
    for step in range(6):
        i, prev, cur, ivs = hist[step]
        if not cur and i_kill is None: i_kill = step
    if i_kill is None: return None
    i, prev, cur, ivs = hist[i_kill]
    rows = []
    for a, b in prev:
        cands = []
        for lo, hi in ivs:
            if hi < a: cands.append((a - hi, 'late', lo, hi))
            elif lo > b: cands.append((lo - b, 'early', lo, hi))
        if cands:
            d = min(cands)
            rows.append((a, b, d[0], d[1], d[2], d[3]))
    rows.sort(key=lambda r: r[2])
    return i, rows[0], rows

def side_vertices(D, n, plane, want_positive):
    """vertices of the box cut by plane (a linear form on (rho2..rho7)): corners on the side
    plus intersections of box edges with the plane (the cut polytope's vertex set)."""
    V = corners(D, n); pos = []; neg = []; zero = []
    for u in V:
        h = plane(u)
        if h > 0: pos.append(u)
        elif h < 0: neg.append(u)
        else: zero.append(u)
    cross = []
    # edges: pairs of corners differing in one bit -- reconstruct from n directly
    for i in range(6):
        for m0 in range(64):
            if (m0 >> i) & 1: continue
            m1 = m0 | (1 << i)
            c0 = tuple(F(n[k] + ((m0 >> k) & 1), D) for k in range(6))
            c1 = tuple(F(n[k] + ((m1 >> k) & 1), D) for k in range(6))
            h0, h1 = plane(c0), plane(c1)
            if (h0 > 0) == (h1 > 0) or h0 == 0 or h1 == 0: continue
            s = h0 / (h0 - h1)                      # h = 0 at c0 + s*(c1-c0), s in (0,1)
            w = tuple(c0[k] + s * (c1[k] - c0[k]) for k in range(6))
            cross.append(w)
    side = pos + zero + cross
    other = neg + zero + cross
    if want_positive: return side, other
    return other, side

def side_types(V):
    """exhaustive window types valid on the vertex set V (a convex polytope: linear ineqs hold on it
    iff they hold on its vertices).  Ratios rho_i/rho_k precomputed per vertex pair."""
    if not V: return []
    rmin = {}; rmax = {}
    for i in range(6):
        for k in range(6):
            vals = [u[i] / u[k] for u in V]
            rmin[(i, k)] = min(vals); rmax[(i, k)] = max(vals)
    cmin = [min(u[i] for u in V) for i in range(6)]
    cmax = [max(u[i] for u in V) for i in range(6)]
    xdescs = [(1, None)]; ydescs = [(7, None)]
    for k in range(6):
        j = 0
        while True:
            num = 8 * j + 1
            if num > 7 * cmax[k]: break
            if num >= cmin[k]: xdescs.append((num, k))
            j += 1
        j = 1
        while True:
            num = 8 * j - 1
            if num > 7 * cmax[k]: break
            if num >= cmin[k]: ydescs.append((num, k))
            j += 1
    out = []
    for na, ka in xdescs:
        for nb, kb in ydescs:
            if ka is not None and na < cmax[ka]: continue                # 1 <= X
            if kb is not None and nb > 7 * cmin[kb]: continue            # Y <= 7
            if ka is None and kb is None: pass                           # X <= Y
            elif ka is None:
                if cmax[kb] > nb: continue
            elif kb is None:
                if na > 7 * cmin[ka]: continue
            else:
                if na * rmax[(kb, ka)] > nb: continue
            laps = []; ok = True
            for i in range(6):
                if ka is None: top = cmin[i]                             # (8j+1) <= rho_i
                elif ka == i: top = F(na)
                else: top = na * rmin[(i, ka)]                           # (8j+1) <= na*rho_i/rho_ka
                jx = math.floor((top - 1) / 8)
                if kb is None: bot = 7 * cmax[i]                         # 7*rho_i <= 8j+7
                elif kb == i: bot = F(nb)
                else: bot = nb * rmax[(i, kb)]                           # nb*rho_i/rho_kb <= 8j+7
                jy = math.ceil((bot - 7) / 8)
                jlo = jy if jy > 0 else 0
                if jlo > jx: ok = False; break
                laps.append(8 * jx + 1)
            if ok: out.append(((na, ka), (nb, kb), tuple(laps)))
    return out

P1 = lambda c: 7 * c[3] - 9 * c[2]

def bind_edges(D, n, t0):
    """which gap edges of which readings sit exactly at t0 (a lonely touch point)"""
    out = []
    for i in range(6):
        j = 0
        while True:
            lo = F((8 * j + 1) * D, n[i]); hi = F((8 * j + 7) * D, n[i] + 1)
            if lo > 7 and hi > 7: break
            if lo == t0: out.append('%s entry gap[%d,%d] (lower corner)' % (RN[i], 8 * j + 1, 8 * j + 7))
            if hi == t0: out.append('%s exit gap[%d,%d] (upper corner)' % (RN[i], 8 * j + 1, 8 * j + 7))
            j += 1
    return out

O = open(os.path.join(HERE, 'leaves3739_mech_v1.out'), 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s); O.write(s + '\n')

P('== leaves3739_mech_v1: rule-22 closure, the five [37,39) leaves (E832 3a / E833 4(iii) / E847 1) ==')
P('[0] inputs: the 5 boxes of frontier_box_dfs_v1_leaves_37_39.txt at D=32 (n2..n7):')
for lab, D, n in BOXES:
    P('   ', lab, 'D=%d' % D, n, '| rho2..rho7 in', ['[%s,%s]' % (F(n[i], D), F(n[i] + 1, D)) for i in range(6)],
      '| centre rho7/rho5 =', F(2 * n[5] + 1, 2 * n[3] + 1))

# ---- [1] Q1a: the E833 window-type certifier at D=32 (reproduce frontier_close_win32_37_39.out, with diagnostics)
P('')
P('[1] E833 window-type certifier at D=32 (search = centre + corners V0,V63,V21,V42):')
for lab, D, n in BOXES:
    tr = certify_diag(D, n)
    nok = sum(1 for t in tr if t['ok'])
    P('   ', lab, '| window types tried at the 5 sample points:', len(tr), '| certified:', nok)
    fails = []
    for t in tr:
        w = worst_viol(t['ineqs'], corners(D, n))
        mx, mn = common_window(D, n, t['X'], t['Y'])
        fails.append((w[0] if w else F(0), t, w, mx, mn))
    fails.sort(key=lambda f: f[0])
    v, t, w, mx, mn = fails[0]
    P('      closest tried type: X =', dsc(t['X']), ', Y =', dsc(t['Y']), ', laps(8j+1) =', t['laps'],
      '| [max X, min Y] = [%s, %s] width %s' % (mx, mn, mn - mx))
    if w:
        v0, ii, (A, s), (B, tt), u = w
        P('      worst violation: ineq #%d: %s*%s <= %s*%s fails by %s at corner rho=(%s) [sample %d]'
          % (ii, A, RN[tt] if tt is not None else '1', B, RN[s] if s is not None else '1', v,
             ','.join(str(x) for x in u), t['sample']))
    P('      all tried types (X, Y, laps 8j+1, holds?):',
      [('(%s,%s)' % (dsc(t['X']), dsc(t['Y'])), list(t['laps']), t['ok']) for t in tr])

# ---- [2] Q2i: exact fixed-R0 lonely set of each D=32 box
P('')
P('[2] exact common lonely set per D=32 box (t in [1,7] lonely for EVERY arrangement; E832 item 1 semantics):')
parent_ls = {}
for lab, D, n in BOXES:
    ls, hist = lonely_set(D, n); parent_ls[lab] = ls
    if not ls:
        kd = kill_diag(hist)
        i, r0, rows = kd
        a, b, delta, kind, lo, hi = r0
        P('   ', lab, '| EMPTY.  last surviving t-range [%s, %s] (width %s) killed by reading %s:' % (a, b, b - a, RN[i]),
          'gap window [%s, %s] is %s by exact %s (t-units)' % (lo, hi, 'closed before a' if kind == 'late' else 'opened after b', delta))
        P('       all killing gaps for that range:', ['(gap [%s,%s] %s by %s)' % (lo, hi, 'late' if k == 'late' else 'early', d) for d, k, lo, hi in [(x[2], x[3], x[4], x[5]) for x in rows]][:6])
    else:
        tot = sum(b - a for a, b in ls)
        dy = [dyadic_hit(iv) for iv in ls]
        P('   ', lab, '| NONEMPTY:', ['[%s, %s] (width %s)' % (a, b, b - a) for a, b in ls],
          '| total width', tot, '| dyadic r/2^20 hit:', [d[0] for d in dy])

# ---- [3] tie planes on the 64 corners of each D=32 box
P('')
P('[3] tie planes, min/max over the 64 corners (straddle iff min < 0 < max):')
PLANES = [('h1: rho7-7rho5', lambda c: c[5] - 7 * c[3]),
          ('h2: 3rho6-5rho4', lambda c: 3 * c[4] - 5 * c[2]),
          ('h3: 25rho7-89rho5', lambda c: 25 * c[5] - 89 * c[3]),
          ('P1: 7rho5-9rho4', lambda c: 7 * c[3] - 9 * c[2]),
          ('P2: rho7-7rho6', lambda c: c[5] - 7 * c[4]),
          ('w1: 23rho7-137rho5', lambda c: 23 * c[5] - 137 * c[3])]
for lab, D, n in BOXES:
    V = corners(D, n)
    row = []
    for nm, f in PLANES:
        vals = [f(u) for u in V]; mn, mx = min(vals), max(vals)
        row.append('%s [%s .. %s]%s' % (nm.split(':')[0], mn, mx, ' STRADDLE' if (mn < 0 < mx) else (' touch0' if 0 in (mn, mx) else '')))
    P('   ', lab, '|', ' | '.join(row))

# ---- [4] Q3d: exhaustive box-level window-type existence at D=32
P('')
P('[4] EXHAUSTIVE window-type existence on the whole D=32 box (all desc pairs x all lap vectors,')
P('    one integer worst-case inequality per condition; superset of the E833 5-sample search):')
parent_types = {}
for lab, D, n in BOXES:
    ts = exhaustive_types(D, n); parent_types[lab] = ts
    P('   ', lab, '| window types valid on the whole box:', len(ts))
    for a, b, laps in ts[:8]:
        mx, mn = common_window(D, n, a, b)
        P('       type: X =', dsc(a), ', Y =', dsc(b), ', laps(8j+1) =', laps, '| [max X, min Y] = [%s, %s] width %s' % (mx, mn, mn - mx))

# ---- [5] Q1b: the D=64 children: certifying types (census format) + exact lonely sets
P('')
P('[5] D=64 children (the fixed-R0 certifier of E832 ref64 closed all of them; here: window types):')
cnt = collections.Counter(); per_parent = {}; child_rows = []
for lab, D, n in BOXES:
    kids = children(D, n)
    tc = 0; rows = []
    for D2, c in kids:
        key = certify_key(D2, c)
        ls, _ = lonely_set(D2, c)
        pos_iv = [iv for iv in ls if iv[0] < iv[1]]
        pts = [iv[0] for iv in ls if iv[0] == iv[1]]
        if ls:
            wmax = max(b - a for a, b in pos_iv) if pos_iv else F(0)
            dy = any(dyadic_hit(iv)[0] for iv in pos_iv) if pos_iv else all(math.ceil(t * (1 << 20)) == math.floor(t * (1 << 20)) for t in pts)
        else:
            wmax = F(0); dy = False
        cls = 'EMPTY' if not ls else ('POINTONLY' if not pos_iv else ('HASPOINT' if pts else 'POS'))
        if key is not None: cnt[key] += 1; tc += 1
        rows.append((c, key, ls, wmax, cls, dy, pts))
    per_parent[lab] = (kids, rows)
    P('   ', lab, '| children kept (sorted_feasible):', len(kids), '| window-type certified:', tc,
      '| fixed-R0 only:', len(kids) - tc)
    child_rows.append((lab, rows))
cc = collections.Counter(r[4] for _, rows in child_rows for r in rows)
P('    child lonely-set classes:', dict(cc),
  '| children with a positive-width window:', cc['POS'] + cc['HASPOINT'],
  '| all positive-window children contain a dyadic r/2^20 point:',
  all(r[5] for _, rows in child_rows for r in rows if r[4] in ('POS', 'HASPOINT')))
wmin = min(r[3] for _, rows in child_rows for r in rows if r[4] in ('POS', 'HASPOINT'))
P('    min positive-window width over children:', wmin, '(C grid spacing 1/2^20 =', F(1, 1 << 20), ')')

# ---- [5b] the isolated lonely points among the children (touch points of gap edges)
P('')
P('[5b] isolated lonely points (degenerate intervals) among the D=64 children:')
pt_pairs = collections.Counter(); npt = 0; pt_only_dy = []
for lab, rows in child_rows:
    for c, key, ls, wmax, cls, dy, pts in rows:
        for t0 in pts:
            npt += 1
            be = bind_edges(64, c, t0)
            isdy = math.ceil(t0 * (1 << 20)) == math.floor(t0 * (1 << 20))
            pt_only_dy.append((lab, c, t0, isdy, be))
            sig = tuple(sorted(be))
            pt_pairs[sig] += 1
P('    degenerate intervals total:', npt, '| children with >= 1:', sum(1 for _, rows in child_rows for r in rows if r[6]),
  '| POINTONLY children (fixed R0 = a single point):', cc['POINTONLY'])
P('    first 8 points (parent, child n, t0, on C grid r/2^20?, binding edges):')
for lab, c, t0, isdy, be in pt_only_dy[:8]:
    P('     ', lab, c, '| t0 =', t0, '| on grid:', isdy, '|', ' = '.join(be) if be else 'clamp 1/7')
P('    binding-edge signatures (count):')
for sig, k in pt_pairs.most_common(8):
    P('     ', k, 'x', ' = '.join(sig))

# ---- [5c] the P1 plane-split side test at D=32
P('')
P('[5c] P1 plane-split side test (P1 = 7rho5 - 9rho4, the E834-item-9 seam-cycle plane):')
P('     exhaustive window types on each side vertex set (corners on the side + box-edge x plane points):')
side_info = {}
for lab, D, n in BOXES:
    Sp, Sn = side_vertices(D, n, P1, True)
    tp = side_types(Sp); tn = side_types(Sn)
    side_info[lab] = (len(Sp), len(Sn), tp, tn)
    P('   ', lab, '| side vertices: P1>=0:', len(Sp), ' P1<0:', len(Sn),
      '| types on P1>=0 side:', len(tp), '| types on P1<0 side:', len(tn))
    for nm, ts in (('P1>=0', tp), ('P1<0', tn)):
        for a, b, laps in ts[:3]:
            P('       %s type: X = %s, Y = %s, laps(8j+1) = %s' % (nm, dsc(a), dsc(b), list(laps)))

# ---- [5d] per-child record (all D=64 children; census-format type + exact lonely windows)
P('')
P('[5d] per-child record (all D=64 children; certifying window type in census format + exact lonely windows):')
for lab, rows in child_rows:
    for c, key, ls, wmax, cls, dy, pts in rows:
        P('   ', lab, '| D=64 n =', c, '| type:',
          ('X=%s Y=%s laps(8j+1)=%s' % (dsc(key[0]), dsc(key[1]), list(key[2]))) if key else 'NONE (fixed R0 only)',
          '| lonely windows:', ['[%s, %s]' % (a, b) for a, b in ls])

# ---- [6] census of the children's types (E847 format) + overlap with the 17 types
P('')
P('[6] census of certifying window types over the D=64 children (E847 frontier_type_census_v1 format):')
P('    certified children:', sum(cnt.values()), '| distinct types:', len(cnt),
  '| boxes per type: largest', max(cnt.values()) if cnt else 0,
  ', median', sorted(cnt.values())[len(cnt) // 2] if cnt else 0,
  ', types used by one box', sum(1 for v in cnt.values() if v == 1))
def keystr(key):
    X, Y, laps = key
    return ('1' if X[1] is None else '%d/%s' % (X[0], RN[X[1]]),
            '7' if Y[1] is None else '%d/%s' % (Y[0], RN[Y[1]]), tuple(laps))
dump = [d for d in json.load(open(os.path.join(HERE, '..', 'frontier_type_dump_v1.json'))) if d.get('kind') == 'window']
dump_keys = {(d['X'], d['Y'], tuple(d['laps'])) for d in dump}
mine = {keystr(k) for k in cnt}
overlap = mine & dump_keys
P('    overlap with the 17 window types of E847 (frontier_type_dump_v1.json):', len(overlap), 'of', len(mine))
for x in sorted(overlap): P('      shared type: X =', x[0], ', Y =', x[1], ', laps(8j+1) =', list(x[2]))
P('    children types (all):')
for k, v in cnt.most_common():
    ks = keystr(k)
    P('      X =', ks[0], ', Y =', ks[1], ', laps(8j+1) =', list(ks[2]), '-> laps j =', [(x - 1) // 8 for x in ks[2]], '| children', v)

# ---- [6b] child x P1-sign x type cross-tab
P('')
P('[6b] children x P1 sign x certifying type:')
xt = collections.Counter()
for lab, rows in child_rows:
    for c, key, ls, wmax, cls, dy, pts in rows:
        V = [tuple(F(2 * c[i] + ((m >> i) & 1), 64) for i in range(6)) for m in range(64)]
        hs = [P1(u) for u in V]
        sg = 'straddle' if (min(hs) < 0 < max(hs)) else ('P1>=0' if min(hs) >= 0 else 'P1<0')
        xt[(sg, keystr(key) if key else None)] += 1
for (sg, ks), k in sorted(xt.items(), key=lambda x: str(x[0])):
    P('     ', sg, '| type:', ('X=%s Y=%s laps=%s' % (ks[0], ks[1], list(ks[2]))) if ks else 'NONE', '| children', k)

# ---- [7] soundness cross-checks
P('')
P('[7] cross-checks:')
bad = 0; checked = 0
for lab, rows in child_rows:
    for c, key, ls, wmax, cls, dy, pts in rows:
        checked += 1
        ex = exhaustive_types(64, c)
        if key is not None and len(ex) == 0: bad += 1; P('      MISMATCH', lab, c)
P('    (a) ALL certifier-certified children => exhaustive box-level test finds >= 1 type: checked', checked, ', mismatches', bad)
ok2 = True
for lab, D, n in BOXES:
    V = corners(D, n)
    for (na, ka), (nb, kb), laps in parent_types[lab][:20]:
        ineqs = [((1, None), (na, ka)), ((nb, kb), (7, None)), ((na, ka), (nb, kb))]
        for i in range(6):
            j = (laps[i] - 1) // 8
            ineqs.append(((8 * j + 1, i), (na, ka))); ineqs.append(((nb, kb), (8 * j + 7, i)))
        if not holds(ineqs, V): ok2 = False; P('      MISMATCH exhaustive type fails corner test', lab, (na, ka), (nb, kb))
P('    (b) every exhaustive box-level type passes the certifier holds() corner test on its box:', ok2)

# ---- [8] Q4: the one-line datum per box (data-side discharge shape for BandNoCarve)
P('')
P('[8] one-line datum per box:')
for lab, D, n in BOXES:
    ls = parent_ls[lab]
    kids, rows = per_parent[lab]
    if ls:
        P('   ', lab, '| D=32 fixed-R0 datum: R0 in', ['[%s, %s]' % (a, b) for a, b in ls],
          '| e.g. R0 =', (ls[0][0] + ls[0][1]) / 2)
    else:
        P('   ', lab, '| NO fixed-R0 datum exists at D=32 (common lonely set empty, exact).')
        ex = parent_types[lab]
        P('       no single window type at D=32 either (exhaustive:', len(ex), 'types).')
        Sp_n, Sn_n, tp, tn = side_info[lab]
        P('       P1-split discharge (2 types, 1 plane):',
          'P1>=0: X=%s Y=%s laps=%s' % (dsc(tp[0][0]), dsc(tp[0][1]), list(tp[0][2])) if tp else 'NONE',
          '|',
          'P1<0: X=%s Y=%s laps=%s' % (dsc(tn[0][0]), dsc(tn[0][1]), list(tn[0][2])) if tn else 'NONE')
        r0 = rows[0]
        P('       D=64 fallback datum (first child): child n =', r0[0],
          '| R0 window', ['[%s, %s]' % (a, b) for a, b in r0[2]],
          '| type:', ('X=%s Y=%s laps=%s' % (dsc(r0[1][0]), dsc(r0[1][1]), list(r0[1][2]))) if r0[1] else 'NONE')

P('')
P('[9] verdict inputs: per parent box: lonely-set empty?', {lab: (len(parent_ls[lab]) == 0) for lab, _, _ in BOXES},
  '| exhaustive types on box:', {lab: len(parent_types[lab]) for lab, _, _ in BOXES},
  '| P1-side types (+,-):', {lab: (len(side_info[lab][2]), len(side_info[lab][3])) for lab, _, _ in BOXES})
O.close()
