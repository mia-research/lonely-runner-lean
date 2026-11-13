# leaves3739_split_v1.py -- rule-22 Q4: the data-side discharge shape for the five [37,39) leaves at D=32.
# Recursive plane-split (E833 item 1(c) shape, planes chained): each leaf polytope (box x halfspaces) is
# tested for window types (exhaustive over desc pairs x lap vectors on its vertex set); a leaf with no
# type is split by the next candidate plane.  Planes = the binding planes of the D=64 children's
# certifying types (na*rho_b = nb*rho_a for X = na/rho_a, Y = nb/rho_b) plus P1.
# Vertex enumeration is COMPLETE: every vertex has 6 active constraints among the 6 box facets and the
# plane halfspaces (k planes + 6-k facets, all subsets, exact Fraction Gaussian elimination).
# Exact Fractions; floats steer only.  Companion to leaves3739_mech_v1.py.
import sys, os, math, itertools
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.argv_saved = sys.argv; sys.argv = ['x']
exec(open(os.path.join(HERE, '..', 'frontier_window_cert_v1.py')).read().split("def sorted_feasible")[0])
sys.argv = sys.argv_saved

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

# planes as sparse coefficient vectors over (rho2..rho7) = indices 0..5
PLANES = [
    ('P1', [(3, 7), (2, -9)]),      # 7rho5 - 9rho4   (E834 item 9; binding plane of type 9/rho5 -> 7/rho4)
    ('w1', [(5, 23), (3, -137)]),   # 23rho7 - 137rho5 (binding plane of type 137/rho7 -> 23/rho5)
    ('w2', [(5, 5), (4, -27)]),     # 5rho7 - 27rho6   (binding plane of type 25/rho6 -> 135/rho7)
    ('w3', [(5, 17), (1, -167)]),   # 17rho7 - 167rho3 (binding plane of type 17/rho3 -> 167/rho7)
    ('w4', [(5, 23), (1, -225)]),   # 23rho7 - 225rho3 (binding plane of type 225/rho7 -> 23/rho3)
]
def pl_val(pi, v):
    return sum(F(co) * v[idx] for idx, co in PLANES[pi][1])

def side_types(V):
    """exhaustive window types valid on the vertex set V (linear ineqs hold on conv(V) iff on V)"""
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
            if ka is not None and na < cmax[ka]: continue
            if kb is not None and nb > 7 * cmin[kb]: continue
            if ka is None and kb is None: pass
            elif ka is None:
                if cmax[kb] > nb: continue
            elif kb is None:
                if na > 7 * cmin[ka]: continue
            else:
                if na * rmax[(kb, ka)] > nb: continue
            laps = []; ok = True
            for i in range(6):
                if ka is None: top = cmin[i]
                elif ka == i: top = F(na)
                else: top = na * rmin[(i, ka)]
                jx = math.floor((top - 1) / 8)
                if kb is None: bot = 7 * cmax[i]
                elif kb == i: bot = F(nb)
                else: bot = nb * rmax[(i, kb)]
                jy = math.ceil((bot - 7) / 8)
                jlo = jy if jy > 0 else 0
                if jlo > jx: ok = False; break
                laps.append(8 * jx + 1)
            if ok: out.append(((na, ka), (nb, kb), tuple(laps)))
    return out

def exhaustive_types(D, n):
    """box-level integer worst-case test (leaves3739_mech_v1.py); for validation"""
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
            if ka is not None and na * D < n[ka] + 1: continue
            if kb is not None and nb * D > 7 * n[kb]: continue
            if ka is None and kb is None: pass
            elif ka is None:
                if (n[kb] + 1) > nb * D: continue
            elif kb is None:
                if na * D > 7 * n[ka]: continue
            elif ka == kb:
                if na > nb: continue
            else:
                if na * (n[kb] + 1) > nb * n[ka]: continue
            laps = []; ok = True
            for i in range(6):
                if ka is None: jx = (n[i] - D) // (8 * D)
                elif ka == i: jx = (na - 1) // 8
                else: jx = (na * n[i] - (n[ka] + 1)) // (8 * (n[ka] + 1))
                if kb is None: jy = -((7 * D - 7 * (n[i] + 1)) // (8 * D))
                elif kb == i: jy = -((7 - nb) // 8)
                else: jy = -((7 * n[kb] - nb * (n[i] + 1)) // (8 * n[kb]))
                jlo = jy if jy > 0 else 0
                if jlo > jx: ok = False; break
                laps.append(8 * jx + 1)
            if ok: out.append(((na, ka), (nb, kb), tuple(laps)))
    return out

def gauss(rows, k):
    """exact Gauss-Jordan solve of k x k; None if singular; [] for k = 0"""
    if k == 0: return []
    M = [(list(r), F(b)) for r, b in rows]
    for c in range(k):
        p = None
        for r in range(c, k):
            if M[r][0][c] != 0: p = r; break
        if p is None: return None
        M[c], M[p] = M[p], M[c]
        piv = M[c][0][c]
        M[c] = ([a / piv for a in M[c][0]], M[c][1] / piv)
        for r in range(k):
            if r != c and M[r][0][c] != 0:
                f = M[r][0][c]
                M[r] = ([a - f * b for a, b in zip(M[r][0], M[c][0])], M[r][1] - f * M[c][1])
    for c in range(k):
        if M[c][0][c] != 1 or any(M[c][0][d] != 0 for d in range(k) if d != c): return None
    return [M[c][1] for c in range(k)]

def region_vertices(D, n, cons):
    """complete vertex set of box x halfspaces, cons = [(plane_index, want_nonneg), ...]"""
    lo = [F(n[i], D) for i in range(6)]; hi = [F(n[i] + 1, D) for i in range(6)]
    verts = []
    K = len(cons)
    for assign in itertools.product([0, 1, 2], repeat=6):     # 0 = at lo, 1 = at hi, 2 = free
        free = [i for i in range(6) if assign[i] == 2]
        k = len(free)
        if k > K: continue
        for planes in itertools.combinations(range(K), k):
            rows = []
            bad = False
            for pj in planes:
                pi, wp = cons[pj]
                row = [F(0)] * k; r = F(0)
                for idx, co in PLANES[pi][1]:
                    if assign[idx] == 2: row[free.index(idx)] = F(co)
                    else: r -= F(co) * (lo[idx] if assign[idx] == 0 else hi[idx])
                rows.append((row, r))
            sol = gauss(rows, k) if k > 0 else []
            if sol is None: continue
            v = [None] * 6
            for i in range(6):
                if assign[i] == 0: v[i] = lo[i]
                elif assign[i] == 1: v[i] = hi[i]
                else: v[i] = sol[free.index(i)]
            if any(v[i] < lo[i] or v[i] > hi[i] for i in free): continue
            okf = True
            for pi, wp in cons:
                val = pl_val(pi, v)
                if wp and val < 0: okf = False; break
                if not wp and val > 0: okf = False; break
            if okf: verts.append(tuple(v))
    seen = set(); out = []
    for u in verts:
        if u not in seen: seen.add(u); out.append(u)
    return out

def sorted_feasible(n):  # verbatim from frontier_window_cert_v1.py
    x = n[0]
    for i in range(6):
        if n[i] > x: x = n[i]
        if x > n[i] + 1: return False
    return True

def certify_key(D, n):  # verbatim from frontier_type_census_v1.py (E847 census)
    V = corners(D, n); tried = set()
    for u in [tuple(F(2 * n[i] + 1, 2 * D) for i in range(6)), V[0], V[63], V[21], V[42]]:
        for X, Y, xv, yv in windows(u):
            ineqs = wtype(u, X, Y, xv); k = tuple(ineqs)
            if k in tried: continue
            tried.add(k)
            if holds(ineqs, V): return (X, Y, tuple(ineqs[3 + 2 * i][0][0] for i in range(6)))
    return None

def children(D, n):
    out = []
    for m in range(64):
        c = tuple(2 * n[i] + ((m >> i) & 1) for i in range(6))
        if sorted_feasible(c): out.append((2 * D, c))
    return out

O = open(os.path.join(HERE, 'leaves3739_split_v1.out'), 'w')
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s); O.write(s + '\n')

P('== leaves3739_split_v1: recursive plane-split discharge of the five [37,39) leaves at D=32 ==')

P('[a] validation: side_types on the uncut box (64 corners) vs the box-level integer test:')
ok = True
for lab, D, n in BOXES:
    V = corners(D, n)
    a = sorted(side_types(V)); b = sorted(exhaustive_types(D, n))
    P('   ', lab, '| side_types:', len(a), '| exhaustive_types:', len(b), '| identical:', a == b)
    if a != b: ok = False
P('    all identical:', ok)
# vertex-set sanity: the uncut box region (no cons) must give exactly the 64 corners
for lab, D, n in BOXES:
    V = region_vertices(D, n, [])
    P('   ', lab, '| region_vertices(no cons):', len(V), '| == 64 corners:', sorted(V) == sorted(corners(D, n)))

P('')
P('[b] recursive split (planes in order P1, w1, w2, w3, w4; a leaf with >= 1 window type closes):')
total_lines = 0
discharge = {}
for lab, D, n in BOXES:
    P('   ', lab)
    leaves = [([], 'box')]
    used_planes = 0
    nlines = 0
    tree = []
    while leaves:
        cons, label = leaves.pop(0)
        V = region_vertices(D, n, cons)
        if not V:
            tree.append((label, 'EMPTY', 0)); continue
        ts = side_types(V)
        if ts:
            na, ka = ts[0][0]; nb, kb = ts[0][1]
            mx = F(1) if ka is None else na / min(u[ka] for u in V)   # max X over the leaf
            mn = F(7) if kb is None else nb / max(u[kb] for u in V)   # min Y over the leaf
            tree.append((label, 'CLOSED', len(ts), dsc(ts[0][0]), dsc(ts[0][1]), list(ts[0][2]),
                         '[max X, min Y] = [%s, %s]' % (mx, mn)))
            nlines += 1
        else:
            if used_planes >= len(PLANES):
                tree.append((label, 'OPEN (no planes left)', 0)); continue
            nm, _ = PLANES[used_planes]; used_planes += 1
            leaves.insert(0, (cons + [(used_planes - 1, True)], label + ' & %s>=0' % nm))
            leaves.insert(1, (cons + [(used_planes - 1, False)], label + ' & %s<0' % nm))
            tree.append((label, 'split by ' + nm, 0))
    total_lines += nlines
    discharge[lab] = (used_planes, nlines, tree)
    for t in tree:
        P('      ', t[0], '->', t[1], ('types %d' % t[2]) if len(t) == 3 else ('type X=%s Y=%s laps=%s %s' % (t[3], t[4], t[5], t[6]) if len(t) == 7 else ''))
    P('       planes used:', used_planes, '| SideWindowCert lines:', nlines)
P('    TOTAL: SideWindowCert lines to discharge all 5 boxes at D=32:', total_lines)

P('')
P('[c] the discharge types per box (first type per closed leaf, census format):')
for lab, D, n in BOXES:
    for t in discharge[lab][2]:
        if t[1] == 'CLOSED':
            P('   ', lab, '|', t[0], '| X =', t[3], ', Y =', t[4], ', laps(8j+1) =', t[5], ',', t[6])

P('')
P('[d] direct verification of each discharge line: the leaf type re-tested with holds() on the leaf vertices:')
VOK = True
from fractions import Fraction as FF
def build_ineqs(t):
    (na, ka), (nb, kb), laps = t
    ineqs = [((1, None), (na, ka)), ((nb, kb), (7, None)), ((na, ka), (nb, kb))]
    for i in range(6):
        j = (laps[i] - 1) // 8
        ineqs.append(((8 * j + 1, i), (na, ka))); ineqs.append(((nb, kb), (8 * j + 7, i)))
    return ineqs
for lab, D, n in BOXES:
    leaves = [([], 'box')]; used = 0
    while leaves:
        cons, label = leaves.pop(0)
        V = region_vertices(D, n, cons)
        if not V: continue
        ts = side_types(V)
        if ts:
            if not holds(build_ineqs(ts[0]), V): VOK = False; P('      MISMATCH', lab, label)
            continue
        if used >= len(PLANES): continue
        nm, _ = PLANES[used]; used += 1
        leaves.insert(0, (cons + [(used - 1, True)], label + ' & %s>=0' % nm))
        leaves.insert(1, (cons + [(used - 1, False)], label + ' & %s<0' % nm))
P('    all discharge lines pass the certifier holds() test on their leaf vertex sets:', VOK)

# ---- [e] reduction validation on ALL 320 D=64 children:
#      (i) side_types(64 corners) == exhaustive_types (two independent implementations);
#      (ii) the record certifier's certifying type (certify_key, verbatim census) has its desc pair
#          among side_types' valid desc pairs (a type holding on the box via holds() must be found).
P('')
P('[e] reduction validation on all 320 D=64 children:')
mismatch = 0; nofind = 0; nonempty = 0; tot = 0
for lab, D, n in BOXES:
    for D2, c in children(D, n):
        tot += 1
        V = corners(D2, c)
        a = sorted(side_types(V)); b = sorted(exhaustive_types(D2, c))
        if a != b: mismatch += 1; P('      MISMATCH side_types vs exhaustive on', lab, c)
        if a: nonempty += 1
        ck = certify_key(D2, c)
        if ck is not None:
            keys = {(t[0], t[1]) for t in a}
            if (ck[0], ck[1]) not in keys: nofind += 1; P('      certifier type desc pair not found by side_types on', lab, c, ck[0], ck[1])
P('    children tested:', tot, '| side_types == exhaustive_types mismatches:', mismatch,
  '| children with >= 1 exhaustive type:', nonempty,
  '| certifier desc pair missing from side_types:', nofind)
O.close()
