# usage: win_stats_v1.py GROUP   GROUP in J1 | taxo | lat1 | lat3 | lat5 | lat7   (reads win_rec_*.pkl)
import sys, pickle, glob
from collections import Counter, defaultdict
from fractions import Fraction as F
g = sys.argv[1]
rec = []
for fn in sorted(glob.glob('win_rec_%s_*_v1.pkl' % g)): rec += pickle.load(open(fn, 'rb'))
fl = lambda x: '%.6f' % float(x)
def fs(x): return str(x) if x.denominator < 10**6 else '%s(~%s)' % (x, fl(x))
def arr(rh): return '[' + ', '.join(fs(r) for r in rh) + ']'
def wstr(ws): return '[' + ', '.join('[%s,%s]' % (fs(a), fs(b)) for a, b in ws) + ']'
def inw(t, ws): return any(a <= t <= b for a, b in ws)
def idx(t, ws):
    for i, (a, b) in enumerate(ws):
        if a <= t <= b: return i
    return None
def per(ws, lo, hi): return [w for w in ws if w[0] >= lo and w[1] <= hi]
def block(rows, name):
    n = len(rows); print('=' * 8, name, 'members', n)
    if not n: return
    cA = Counter(); cB = Counter(); cC = Counter(); cAB = Counter(); cAll = Counter(); cAll15 = Counter(); cross = Counter()
    firstph = Counter(); odd_pat = Counter(); inst = Counter(); inst_even = Counter()
    pairs = Counter(); rules = Counter(); ex = {}
    mn_windows = None; mn_w = None; mn_deg = 0; degcount = 0; latest = None; first_narrow = None
    pair_defs = [('S1S2@0', (1, 7), (3, 5), 0), ('S1S2@8', (1, 7), (3, 5), 8), ('S1S2@16', (1, 7), (3, 5), 16)]
    mid = Counter()
    for lab, rh, ws in rows:
        A = per(ws, 1, 7); B = per(ws, 9, 15); C = per(ws, 17, 23)
        assert len(A) + len(B) + len(C) == len(ws)
        cA[len(A)] += 1; cB[len(B)] += 1; cC[len(C)] += 1; cAB[(len(A), len(B))] += 1
        cAll[len(ws)] += 1; cAll15[len(A) + len(B)] += 1
        cross[(len(A) > 0, len(B) > 0)] += 1
        f = ws[0]; firstph['A' if f[0] <= 7 else 'B' if f[0] <= 15 else 'C'] += 1
        if latest is None or f[0] > latest[0][0]: latest = (f, lab, rh, ws)
        for a, b in ws:
            if a == b: degcount += 1
        pos = [(b - a, lab, rh, ws, (a, b)) for a, b in ws if b > a]
        for p in pos:
            if mn_w is None or p[0] < mn_w[0]: mn_w = p
        if mn_windows is None or len(ws) < mn_windows[0]: mn_windows = (len(ws), lab, rh, ws)
        if first_narrow is None or (f[1] - f[0]) < first_narrow[0]: first_narrow = (f[1] - f[0], lab, rh, ws)
        S = tuple(t for t in range(1, 24) if inw(t, ws))
        odd = tuple(t for t in S if t % 2 == 1)
        odd_pat[tuple(t for t in odd if t <= 15)] += 1
        for t in S:
            inst[t] += 1
        mid[(inw(4, ws), inw(12, ws), inw(20, ws))] += 1
        # pair structure per period
        for nm, s1, s2, o in pair_defs:
            p1 = [t + o for t in s1 if inw(t + o, ws)]; p2 = [t + o for t in s2 if inw(t + o, ws)]
            both = bool(p1) and bool(p2)
            same = any(idx(a, ws) is not None and idx(a, ws) == idx(b, ws) for a in p1 for b in p2)
            pairs[(nm, 'S1 present', bool(p1))] += 1; pairs[(nm, 'S2 present', bool(p2))] += 1
            pairs[(nm, 'both present (any windows)', both)] += 1; pairs[(nm, 'one window holds one of S1 and one of S2', same)] += 1
            pairs[(nm, 'S1 and S2 members: 1&7 both in windows', len(p1) == 2)] += 1
            pairs[(nm, '3&5 both in windows', len(p2) == 2)] += 1
        # rules
        r1 = any(t in odd for t in range(1, 16, 2)); r2 = any(inw(t, ws) for t in range(1, 16))
        r3 = any(inw(t, ws) for t in range(1, 8)); r4 = any(inw(t, ws) for t in range(9, 16))
        r5 = any(t in odd for t in (1, 3, 5, 7)); r6 = any(t in odd for t in (9, 11, 13, 15))
        r7 = any(inw(t, ws) for t in range(1, 24))
        r8 = r5 and r6
        for nm, v in (('R1 odd integer instant in 1..15 in a window', r1), ('R2 any integer in 1..15 in a window', r2),
                      ('R3 any integer in 1..7', r3), ('R4 any integer in 9..15', r4),
                      ('R5 odd in {1,3,5,7}', r5), ('R6 odd in {9,11,13,15}', r6), ('R5&R6', r8), ('R7 any integer 1..23', r7)):
            rules[(nm, v)] += 1
            if not v and nm not in ex: ex[nm] = (lab, rh, ws)
    print('windows in [1,7] count -> members:', dict(sorted(cA.items())))
    print('windows in [9,15]:', dict(sorted(cB.items())))
    print('windows in [17,23]:', dict(sorted(cC.items())))
    print('(nA,nB) joint:', dict(sorted(cAB.items())))
    print('windows in [1,15] total:', dict(sorted(cAll15.items())))
    print('windows in [1,23] total:', dict(sorted(cAll.items())))
    print('members with nA=0 (first window in [9,15]):', cA[0], '; members with no window in [1,15]:', cAll15[0], '; no window in [1,23]:', cAll[0])
    print('(A nonempty, B nonempty) crosstab:', dict(cross))
    print('first window lies in:', dict(firstph))
    print('windows containing (4,12,20):', dict(mid))
    print('instants t in 1..23: members whose some window contains t:', {t: inst[t] for t in range(1, 24)})
    print('odd-instant patterns within 1..15 (top 12):', odd_pat.most_common(12), 'distinct', len(odd_pat))
    for k in sorted(pairs): print('pair', k, pairs[k])
    for k in sorted(rules): print('rule', k, rules[k])
    for nm, v in ex.items(): print('COUNTEREXAMPLE to', nm, ':', v[0], arr(v[1]), 'windows', wstr(v[2]))
    print('degenerate (single-point) windows total:', degcount)
    print('FEWEST windows in [1,23]:', mn_windows[0], mn_windows[1], arr(mn_windows[2]), wstr(mn_windows[3]))
    print('NARROWEST positive-width window: width', mn_w[0], '(~%s)' % fl(mn_w[0]), mn_w[1], arr(mn_w[2]), 'window', wstr([mn_w[4]]), 'all', wstr(mn_w[3]))
    print('NARROWEST first window:', first_narrow[0], '(~%s)' % fl(first_narrow[0]), first_narrow[1], arr(first_narrow[2]), wstr(first_narrow[3]))
    print('LATEST first window:', latest[0][0], '(~%s)' % fl(latest[0][0]), latest[1], arr(latest[2]), wstr(latest[3]))
if g.startswith('lat'):
    m = int(g[3:])
    rows = [(a[0], a[1], a[2]) for a in rec]
    block(rows, g + ' windows in [1,23]')
    wm = Counter(); oddc = Counter(); first = Counter(); cen = Counter(); chk = 0; cenfirst = Counter()
    for lab, rh, ws, wmm in rec:
        wm[len(wmm)] += 1; first[wmm[0]] += 1
        c = inw(F(4 * m), wmm); cen[(len(wmm) % 2 == 1, c)] += 1
        # window containing 4m is its own mirror image: lo+hi == 8m
        cw = [w for w in wmm if w[0] <= 4 * m <= w[1]]
        if c: chk += (cw[0][0] + cw[0][1] == 8 * m)
    print('LATTICE m=%d: windows in [1,%d] count -> members:' % (m, 8 * m - 1), dict(sorted(wm.items())))
    print('(count odd, window contains 4m):', dict(cen), '; windows containing 4m that are self-mirror (lo+hi=8m):', chk, 'of', sum(1 for c in cen.elements() if c[1]))
    print('first window distinct values:', len(first), 'earliest', min(first), 'latest', max(first))
    print('first-window lo values (top 10):', [(wstr([k]), v) for k, v in first.most_common(10)])
else:
    block(rec_ := [(a[0], a[1], a[2]) for a in rec], g + ' all')
    if g == 'taxo':
        fam = defaultdict(list)
        for r in rec_: fam[r[0][1]].append(r)
        for k in sorted(fam): block(fam[k], 'taxo family ' + k)
    if g == 'J1':
        # split by gate crossing
        A = [r for r in rec_ if r[2][0][0] <= 7]; B = [r for r in rec_ if r[2][0][0] > 7]
        block(A, 'J1 first window in [1,7]'); block(B, 'J1 first window in [9,15] (gate-crossing)')
