"""v2: as v1, plus for each changed pin reading the new facing ends classified against the member's: for P and A separately,
unchanged, a neighbour (r_{k-1} or r_{k+1}, q = 1), the same reading with another q, or another reading; and whether the
closest pair moved to another interval of P or A (interval count of P and A at member and point).
E951, rule 22 on pin_cascade_v1's exception: cell points (same seven-path) where a member's rigid pin is not kept
(facing ends change, facing None, or gap 0).  Exact Fractions; the float LP only proposes points (as pin_cascade_v1).
At each such point: (a) what the pin reading's facing ends are now (identifications, side, gap) or why facing is None;
(b) whether the six-reading windows of that reading changed: the list of six-windows up to W_k and the index n of W_k,
compared with the member's (windows() of the six; ends compared as identifications of the window ends); (c) whether some
member-attaining reading is BLOCKED at the point (rigid pin, or a ratio cycle < 1 with cell_exact(point), cert_cycle_v2)."""
import sys
from fractions import Fraction as Fr
from collections import Counter
src = open('pin_cascade_v1.py').read(); exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
src4 = open('attain_lp_cert_v4.py').read(); exec('def cell_exact' + src4.split('def cell_exact')[1].split('def solve_exact')[0])
src2 = open('cert_cycle_v2.py').read(); exec('def to_edges' + src2.split('def to_edges')[1].split('step, off = int')[0])
def wsig(rs_, k, T_):
    six = rs_[:k] + rs_[k + 1:]; ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T_ <= y)
    out = []
    for x, y, z in ws[:n + 1]:
        def wid(t):
            for j, s in enumerate(six):
                u = 8 * s * t
                if u.denominator == 1 and u % 8 in (1, 7): return (j, int(u))
            return 'x'
        out.append((wid(x), wid(y)))
    return n, tuple(out)
def blocked_at(p, Tp, k1, closers):
    f = facing(p, Tp, k1 - 1)
    if f is None or f[0] == 0: return 'no facing pair'
    d, xP, xA, side = f; IP, IA = idents(xP, p), idents(xA, p)
    if not IP or not IA: return 'not identified'
    if len(IP) == 1 and len(IA) == 1 and IP[0][0] == IA[0][0]: return 'rigid pin'
    A_, b_, tag_ = cell_exact(p); Ec = to_edges(A_, b_, tag_, Counter(), 'x')
    for jP, qP in IP:
        for jA, qA in IA:
            v = [Fr(0)] * 6; rhs = Fr(0); sgn = 1 if side == 'below' else -1
            for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
                if j_ == 1: rhs -= s_ * q_
                else: v[j_ - 2] += s_ * q_
            w = [-rhs] + v
            if any(x > 0 for x in w) and not any(x < 0 for x in w): continue
            E1 = dict(Ec)
            for key, val in to_edges([v], [rhs], [('escape', k1, side)], Counter(), 'x').items():
                if key not in E1 or val[0] < E1[key][0]: E1[key] = val
            if not any(x[0] < 1 for x in cycles(E1)): return 'free'
    return 'cycle'
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    info = {}; skip = False
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        if f is None or f[0] == 0 or ident(f[1], rs)[0] is None or ident(f[2], rs)[0] is None: skip = True; break
        IP, IA = idents(f[1], rs), idents(f[2], rs)
        info[k1] = (IP, IA, f[3], len(IP) == 1 and len(IA) == 1 and IP[0][0] == IA[0][0])
    if skip or not any(v[3] for v in info.values()): continue
    A, bb = cell(rs); bb = bb - 1e-9 * np.linalg.norm(A, axis=1)
    bounds = [(1.0, 10 * float(rs[q])) for q in range(1, 7)]
    _, sig0 = path_sig(rs)
    for obj in ([0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, -1], [1, 0, 0, 0, -1, 0]):
        res = linprog(np.array(obj, float), A_ub=A, b_ub=bb, bounds=bounds, method='highs')
        if res.status != 0: continue
        v = [Fr(1)] + [Fr(float(x)) for x in res.x]
        for lam in (Fr(1, 2), Fr(1, 10), Fr(1, 100)):
            p = [rs[q] + lam * (v[q] - rs[q]) for q in range(7)]
            if p == rs or sorted(p) != p or path_sig(p)[1] != sig0: continue
            Tp, _ = cascade(p, E); changed = []
            for k1, (IP, IA, side, rp) in info.items():
                if not rp: continue
                f = facing(p, Tp, k1 - 1)
                ok = f is not None and f[0] != 0 and any(f[1] == q * p[j - 1] for j, q in IP) and any(f[2] == q * p[j - 1] for j, q in IA)
                if not ok: changed.append(k1)
            if changed:
                for k1 in changed:
                    n0, s0 = wsig(rs, k1 - 1, T); n1, s1 = wsig(p, k1 - 1, Tp)
                    c[('changed pin reading', 'W_k index same', n0 == n1, 'window ends same', s0 == s1)] += 1
                    c[('changed pin reading', 'now', blocked_at(p, Tp, k1, closers))] += 1
                    IP, IA, side, rp = info[k1]; f = facing(p, Tp, k1 - 1)
                    if f is None:
                        c[('changed pin reading', 'facing None at point')] += 1; continue
                    if f[0] == 0: c[('changed pin reading', 'gap 0 at point')] += 1; continue
                    def cl(x, I):
                        if any(x == q * p[j - 1] for j, q in I): return 'unchanged'
                        if x in (p[k1 - 2], p[k1] if k1 < 7 else None): return 'neighbour'
                        J = idents(x, p)
                        if not J: return 'unidentified'
                        if any(j == I[0][0] for j, q in J): return 'same reading, other q'
                        return 'other reading'
                    c[('changed pin reading', 'windows same' if s0 == s1 else 'windows changed', 'P', cl(f[1], IP), 'A', cl(f[2], IA), 'side same', f[3] == side)] += 1
                bl = [blocked_at(p, Tp, k1, closers) for k1 in info]
                c[('point with a changed pin', 'some member-attaining reading blocked', any(b in ('rigid pin', 'cycle') for b in bl))] += 1
                if not any(b in ('rigid pin', 'cycle') for b in bl): print('UNBLOCKED POINT', idx, lam, bl, flush=True)
            break
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
