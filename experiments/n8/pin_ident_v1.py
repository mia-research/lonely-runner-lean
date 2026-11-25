"""E951: the same-reading pins of cert_cycle_v2 (1,992 crossers), checked for identification artefacts.  Exact Fractions.
attain_pin_v2.ident returns the FIRST reading j with x / r_j of small terms (num, den < 2000).  If two frozen readings stand
in a small rational ratio at the member (E341: one max-slack point per cell, so coincidences occur), a facing end has more
than one identification and a 'pin' may be an artefact.  For each attaining reading of the 2,607 (all-X, identified):
every identification of x_P and of x_A is listed; a pin is RIGID if x_P and x_A have exactly one identification each and
it is the same reading.  Recorded for rigid pins: the reading's role, q_P, q_A, q_A / q_P, the side, and both written
as (8a+-1)/(8b+-1) where possible; the window index of W_k (n) and of the earlier window whose pass set gives x_A."""
import sys
from fractions import Fraction as Fr
from collections import Counter
src = open('attain_lp_cert_v4.py').read()
exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
def idents(x, rs):
    out = []
    for j in range(7):
        q = x / rs[j]
        if q.numerator < 2000 and q.denominator < 2000: out.append((j + 1, q))
    return out
def pm8(q):
    a, b = q.numerator, q.denominator
    for g in range(1, 50):
        A_, B_ = a * g, b * g
        if A_ % 8 in (1, 7) and B_ % 8 in (1, 7): return f'{A_}/{B_}'
    return 'not (8a+-1)/(8b+-1) below x50'
def which_window(six, lo, hi, ws, n, xA):
    for jj in range(n):
        for l, h, m in passes(ws[jj][0], ws[jj][1], lo, hi):
            if xA in (l, h): return jj
    return None
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    fs = []
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        if f is None or f[0] == 0: fs = None; break
        d, xP, xA, side = f
        if ident(xP, rs)[0] is None or ident(xA, rs)[0] is None: fs = None; break
        fs.append((k1, f))
    if fs is None: continue
    rigid_any = False; art_any = False
    for k1, (d, xP, xA, side) in fs:
        IP, IA = idents(xP, rs), idents(xA, rs)
        c[('identifications per facing end', 'P', len(IP), 'A', len(IA))] += 1
        jP, qP = IP[0]; jA, qA = IA[0]
        if jP != jA: continue
        rigid = len(IP) == 1 and len(IA) == 1
        common = set(j for j, q in IP) & set(j for j, q in IA)
        if rigid: rigid_any = True
        else:
            alt_diff = any(j1 != j2 for j1, _ in IP for j2, _ in IA)
            c[('first-ident pin, NOT rigid', 'readings common to both lists', len(common), 'some pair of identifications differs', alt_diff)] += 1
            art_any = True; continue
        role = 'c' if jP in closers else ('o' if jP == o else ('1' if jP == 1 else 'x'))
        k = k1 - 1; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        jj = which_window(six, lo, hi, ws, n, xA)
        c[('rigid pin', 'role', role, 'side', side)] += 1
        c[('rigid pin', 'q_A/q_P', str(qA / qP), 'q_P', pm8(qP), 'q_A', pm8(qA))] += 1
        c[('rigid pin', 'W_k index n', n, 'x_A from window', jj)] += 1
    c[('crosser', 'has a rigid pin', rigid_any, 'has a non-rigid first-ident pin', art_any)] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
