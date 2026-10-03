import pickle, glob
from collections import Counter
from fractions import Fraction as F
exec(open('win_lib_v1.py').read())
def load(g):
    r = []
    for fn in sorted(glob.glob('win_rec_%s_*_v1.pkl' % g)): r += pickle.load(open(fn, 'rb'))
    return r
fl = lambda x: '%.6f' % float(x)
def fs(x): return str(x) if x.denominator < 10**6 else '%s(~%s)' % (x, fl(x))
def arr(rh): return '[' + ', '.join(fs(r) for r in rh) + ']'
def wstr(ws): return '[' + ', '.join('[%s,%s]' % (fs(a), fs(b)) for a, b in ws) + ']'
per = lambda ws, lo, hi: [w for w in ws if w[0] >= lo and w[1] <= hi]
J1 = load('J1'); TX = load('taxo')
print('### (a) widths and integer content, all datasets')
for nm, rec in (('J1', J1), ('taxo', TX), ('lat1', load('lat1')), ('lat3', load('lat3')), ('lat5', load('lat5')), ('lat7', load('lat7'))):
    mx = None; ge1 = 0; two_int = 0; deg = 0; allw = 0
    for r in rec:
        for a, b in r[2]:
            allw += 1
            if b == a: deg += 1
            if b - a >= 1: ge1 += 1
            if int(b // 1) - int(-((-a) // 1)) >= 1: two_int += 1     # contains >= 2 integers
            if mx is None or b - a > mx[0]: mx = (b - a, r[0], r[1], (a, b))
    print(nm, 'windows', allw, 'degenerate', deg, 'width>=1:', ge1, 'containing >=2 integers:', two_int, 'widest', fs(mx[0]), mx[1], 'window', wstr([mx[3]]), 'arrangement', arr(mx[2]))
print('### (b) taxo restricted to rho_7 <= 9 vs > 9; exceptions to nB>=2 / nC>=2')
cnt = Counter(); exc = []
for lab, rh, ws in TX:
    A = per(ws, 1, 7); B = per(ws, 9, 15); C = per(ws, 17, 23)
    s = 'le9' if rh[-1] <= 9 else 'gt9'
    cnt[(s, 'members')] += 1
    cnt[(s, 'nB<2')] += len(B) < 2; cnt[(s, 'nC<2')] += len(C) < 2; cnt[(s, 'nB=0')] += len(B) == 0; cnt[(s, 'nA=0')] += len(A) == 0
    cnt[(s, 'first window in [9,15]')] += ws[0][0] > 7
    if len(B) < 2 or len(C) < 2: exc.append((rh[-1], lab, rh, ws, len(A), len(B), len(C)))
for k in sorted(cnt): print(k, cnt[k])
exc.sort(key=lambda t: t[0])
print('taxo members with nB<2 or nC<2:', len(exc), '; smallest rho_7 among them:', fs(exc[0][0]), '; largest', fs(exc[-1][0]))
for e in exc[:3]: print('EXC', e[1], arr(e[2]), '(nA,nB,nC)=', e[4:], 'windows', wstr(e[3]))
print('### (c) J1 members with all readings 2..7 non-integer, and boundary members')
nonint = [r for r in J1 if all(x.denominator != 1 for x in r[1][1:])]
print('J1 members with no integer reading among rho_2..rho_7:', len(nonint), 'of', len(J1))
for nm, rec in (('J1 no-integer-reading', nonint), ('J1 with an integer reading', [r for r in J1 if r not in nonint])):
    c = Counter(); degs = 0
    for lab, rh, ws in rec:
        B = per(ws, 9, 15); C = per(ws, 17, 23); A = per(ws, 1, 7)
        c[('min nB', len(B))] += 0
        degs += sum(1 for a, b in ws if a == b)
    nB = Counter(len(per(ws, 9, 15)) for _, _, ws in rec); nC = Counter(len(per(ws, 17, 23)) for _, _, ws in rec); tot = Counter(len(ws) for _, _, ws in rec)
    print(nm, 'members', len(rec), 'degenerate windows', degs, 'min nB', min(nB), 'min nC', min(nC), 'min total in [1,23]', min(tot), 'first window in B:', sum(1 for _, _, ws in rec if ws[0][0] > 7))
print('### (d) degenerate windows in J1: location')
loc = Counter(); noninteger_loc = 0
for lab, rh, ws in J1:
    for a, b in ws:
        if a == b: loc[a if a.denominator == 1 else 'nonint'] += 1
print(dict(loc))
print('### (e) J1: members whose first window starts exactly at 9, at 1; (nB) examples with nB=2')
print('R*=1:', sum(1 for _, _, ws in J1 if ws[0][0] == 1), 'R*=9:', sum(1 for _, _, ws in J1 if ws[0][0] == 9))
ex2 = [r for r in J1 if len(per(r[2], 9, 15)) == 2]
print('J1 members with exactly 2 windows in [9,15]:', len(ex2))
for lab, rh, ws in ex2[:3]: print(lab, arr(rh), 'nA', len(per(ws, 1, 7)), 'windows', wstr(ws))
print('### (f) lat1: odd instants 1..15 in windows  <=>  no reading divisible by 8')
L1 = load('lat1'); ok = 0; viol = 0; n_yes = 0
for lab, rh, ws, wm in L1:
    odd_all = all(any(a <= t <= b for a, b in ws) for t in range(1, 24, 2)); odd_none = not any(any(a <= t <= b for a, b in ws) for t in range(1, 24, 2))
    no8 = not any(c % 8 == 0 for c in lab[1])
    if odd_all != no8 or (odd_all == odd_none): viol += 1
    n_yes += odd_all
print('lat1 members', len(L1), 'all-odd-instants (1..23) members', n_yes, 'violations of (all-odd <=> no reading in {8,16}; else none):', viol)
print('### (g) lat3 members with no window in [9,15] (symmetric centre 12)')
L3 = load('lat3'); z = [r for r in L3 if len(per(r[2], 9, 15)) == 0]
print(len(z), 'members; c-vectors (readings c/3) first 12:', [r[0][1] for r in z[:12]])
print('their window counts in [1,23]:', Counter(len(r[2]) for r in z))
r = z[0]; print('EXAMPLE', r[0], arr(r[1]), 'windows', wstr(r[2]))
print('do they all contain 4 and 20 (windows):', Counter((any(a <= 4 <= b for a, b in r[2]), any(a <= 20 <= b for a, b in r[2])) for r in z))
print('### (h) gate-crossing J1: relation between first window and its successors')
gap = []
for lab, rh, ws in J1:
    if ws[0][0] > 7:
        gap.append((ws[1][0] - ws[0][1], lab))
print('gap from first to second window: min', fs(min(gap)[0]), min(gap)[1], 'max', fs(max(gap)[0]))
