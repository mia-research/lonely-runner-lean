"""v3: as v2 on pin_ident_v1's population exactly (crossers whose attaining readings are all class X with identified facing
ends), and for every rigid pin: are the two window ends that give x_P and x_A zone edges of the pin reading j itself, of the
type the pass formula needs (upper end at a window END b with 8 r_j b = 8m - 1; lower end at a window START a with
8 r_j a = 8m + 1), and is the pin the number inequality (8k+1)/(8m'-1) < (8k'-1)/(8m+1) (below; mirrored above)?
v2: E951, rule 22 on pin_form_v1's 26 rigid pins outside the standard sign form (P end (8a+1)/(8b-1), A end (8a'-1)/(8b'+1) on
the below side; mirrored above).  Exact Fractions.  For each rigid pin: the provenance of x_P and x_A, i.e. which window,
which end of a pass interval ((8k-1)/(8a) lower, (8k+1)/(8b) upper), or a clip at the neighbours (lo, hi) or at an
inherited A end; and the window ends a, b as zone edges of which frozen reading (8 r_j t = 8m +- 1).
Population: as pin_ident_v1 (rigid pins of the 2,607)."""
import sys
from fractions import Fraction as Fr
from collections import Counter
src = open('pin_ident_v1.py').read()
exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
def zedge(t, six):
    out = []
    for j, s in enumerate(six):
        u = 8 * s * t
        if u.denominator == 1 and u % 8 in (1, 7): out.append((j, int(u)))
    return out or [('none', t)]
def prov_passes(a, b, lo0, hi0, tagL, tagH, jj):
    out = []
    for l, h, k in passes(a, b, lo0, hi0):
        lt = ('win', jj, 'lower', k) if l == Fr(8 * k - 1) / (8 * a) else tagL
        ht = ('win', jj, 'upper', k) if h == Fr(8 * k + 1) / (8 * b) else tagH
        out.append((l, h, lt, ht))
    return out
def sform(q):
    s = pm8(q)
    if '/' not in s or s.startswith('not'): return s
    a, b = map(int, s.split('/')); return ('+' if a % 8 == 1 else '-') + ('+' if b % 8 == 1 else '-')
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    bad = False
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        if f is None or f[0] == 0 or ident(f[1], rs)[0] is None or ident(f[2], rs)[0] is None: bad = True
    if bad: continue
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        d, xP, xA, side = f; IP, IA = idents(xP, rs), idents(xA, rs)
        if not (len(IP) == 1 and len(IA) == 1 and IP[0][0] == IA[0][0]): continue
        sP, sA = sform(IP[0][1]), sform(IA[0][1])
        std = (side == 'below' and sP == '+-' and sA == '-+') or (side == 'above' and sP == '-+' and sA == '+-')
        k = k1 - 1; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = prov_passes(a, b, lo, hi, 'clip lo', 'clip hi', n)
        A = [(lo, hi, 'clip lo', 'clip hi')]
        for jj in range(n):
            nA = []
            for l, h, lt, ht in A: nA.extend(prov_passes(ws[jj][0], ws[jj][1], l, h, lt, ht, jj))
            A = nA
        pP = next((lt if l == xP else ht) for l, h, lt, ht in P if xP in (l, h))
        pA = next((lt if l == xA else ht) for l, h, lt, ht in A if xA in (l, h))
        def wend(pv):
            if pv[0] != 'win': return pv
            jj = pv[1]; t = ws[jj][0] if pv[2] == 'lower' else ws[jj][1]
            return pv + (tuple(zedge(t, six)),)
        key = ('standard' if std else 'NON-STANDARD', side, 'P', sP, pP[:3] if pP[0] == 'win' else pP, 'A', sA, pA[:3] if pA[0] == 'win' else pA)
        c[('form', 'standard' if std else 'NON-STANDARD', side, 'P from', pP[0] + ('' if pP[0] != 'win' else ':' + pP[2]), 'A from', pA[0] + ('' if pA[0] != 'win' else ':' + pA[2]))] += 1
        j = IP[0][0]
        def check(pv):
            if pv[0] != 'win': return ('not a window end', pv[0])
            jj = pv[1]; t = ws[jj][0] if pv[2] == 'lower' else ws[jj][1]; u = 8 * rs[j - 1] * t
            if u.denominator != 1: return ('window end not a zone edge of the pin reading',)
            want = 1 if pv[2] == 'lower' else 7
            return ('zone edge of the pin reading', 'type right', int(u) % 8 == want), int(u), pv[3]
        cP, cA = check(pP), check(pA)
        c[('v3 pin', side, 'P end', cP[0], 'A end', cA[0])] += 1
        if cP[0][0] == 'zone edge of the pin reading' and cA[0][0] == 'zone edge of the pin reading':
            mP, kP = cP[1], cP[2]; mA, kA = cA[1], cA[2]
            vP = Fr(8 * kP + 1, mP) if pP[2] == 'upper' else Fr(8 * kP - 1, mP)
            vA = Fr(8 * kA + 1, mA) if pA[2] == 'upper' else Fr(8 * kA - 1, mA)
            c[('v3 pin', side, 'q_P = formula', vP == IP[0][1], 'q_A = formula', vA == IA[0][1], 'gap sign right', (vP < vA) if side == 'below' else (vP > vA))] += 1
        if False: print('NS', idx, 'k', k1, side, 'qP', IP[0][1], sP, wend(pP), 'qA', IA[0][1], sA, wend(pA), 'n', n, flush=True)
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
