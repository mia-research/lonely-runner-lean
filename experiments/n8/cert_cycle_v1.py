"""E951: E950 item 1 (the certificates' rows as a rule), 2026-11-25.  Exact Fractions throughout; no floats.
Claim tested, not assumed: every row of the closed path cell (attain_lp_cert_v4.cell_exact), every order row, every lower
bound (r_q >= r_1 = 1) and every escape row is homogeneous in (r_1..r_7) with exactly one positive and one negative
coefficient: a r_i <= b r_j, a ratio bound r_i / r_j <= b / a.  Rows are classified and counted; none is assumed.
If so, the closed system is infeasible iff the ratio graph (node = reading, edge i->j weight b/a, tightest per ordered
pair) has a simple cycle with product < 1 (multiply the bounds round the cycle: r_i <= w r_i with w < 1 and r_i >= 1).
Every simple cycle of the 7-node graph is enumerated exactly; the verdict is compared with E949's 2,607 certificates.
Recorded per crosser: the shortest product-<1 cycle, its edges' kinds (cell state R and kind, order, lower bound, escape)
and the readings' roles; whether the cell alone has a cycle < 1 (it must not: the member satisfies it); cycles = 1."""
import sys, itertools
from fractions import Fraction as Fr
from collections import Counter
src = open('attain_lp_cert_v4.py').read()
exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
def to_edges(A, b, tags, c, label):
    E_ = {}
    for u in range(len(A)):
        w = [-b[u]] + list(A[u]); pos = [(i, x) for i, x in enumerate(w) if x > 0]; neg = [(i, -x) for i, x in enumerate(w) if x < 0]
        if len(pos) == 1 and len(neg) == 1:
            (i, a), (j, bb) = pos[0], neg[0]; r = bb / a
            if (i, j) not in E_ or r < E_[(i, j)][0]: E_[(i, j)] = (r, tags[u])
            c[('row class', label, 'ratio bound')] += 1
        elif not pos: c[('row class', label, 'no positive coefficient (holds for positive speeds)')] += 1
        else: c[('row class', label, 'other', len(pos), len(neg))] += 1
    return E_
def cycles(E_):
    out = []
    for n in range(1, 8):
        for nodes in itertools.combinations(range(7), n):
            first = nodes[0]
            for perm in itertools.permutations(nodes[1:]):
                cyc = (first,) + perm; p = Fr(1); es = []; ok = True
                for a_, b_ in zip(cyc, cyc[1:] + (first,)):
                    if a_ == b_: ok = False; break
                    e = E_.get((a_, b_))
                    if e is None: ok = False; break
                    p *= e[0]; es.append((a_, b_, e[1]))
                if ok: out.append((p, cyc, es))
    return out
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    A, b, tag = cell_exact(rs); ok = True; esc = []; o = rs.index(path[-1]) + 1
    tag = [(R, kd, qs) for R, kd, qs in tag]
    for k1 in att:
        k = k1 - 1; f = facing(rs, T, k)
        if f is None or f[0] == 0: ok = False; break
        d, xP, xA, side = f; jP, qP = ident(xP, rs); jA, qA = ident(xA, rs)
        if jP is None or jA is None: ok = False; break
        v = [Fr(0)] * 6; rhs = Fr(0); sgn = 1 if side == 'below' else -1
        for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
            if j_ == 1: rhs -= s_ * q_
            else: v[j_ - 2] += s_ * q_
        esc.append((v, rhs, ('escape', k1, side)))
    if not ok: c[('skipped: facing ends not identified',)] += 1; continue
    Ec = to_edges(A, b, tag, c, 'cell/order/lower')
    Ee = to_edges([e[0] for e in esc], [e[1] for e in esc], [e[2] for e in esc], c, 'escape')
    cc_ = cycles(Ec); bad_cell = [x for x in cc_ if x[0] < 1]
    c[('cell alone: cycles with product < 1', len(bad_cell))] += 1
    c[('cell alone: cycles with product = 1 (pins)', sum(1 for x in cc_ if x[0] == 1))] += 1
    Eall = dict(Ec)
    for key, val in Ee.items():
        if key not in Eall or val[0] < Eall[key][0]: Eall[key] = val
    ca = [x for x in cycles(Eall) if x[0] < 1]
    c[('cell + escapes: some cycle < 1 (closure infeasible, exact)', bool(ca))] += 1
    if not ca: print('NO CYCLE', idx, att, flush=True); continue
    ca.sort(key=lambda x: (len(x[1]), x[0])); p, cyc, es = ca[0]
    def role(q1):
        ks = set(e[2][1] for e in es if e[2][0] == 'escape')
        return 'k' if q1 in ks else ('c' if q1 in closers else ('o' if q1 == o else ('1' if q1 == 1 else 'x')))
    def st(R):
        return 'R=1' if R == 1 else ('R=9' if R == 9 else ('ph1' if R < 9 else 'ph2'))
    kinds = []
    for a_, b_, tg in es:
        if tg[0] == 'escape': kinds.append('esc')
        elif tg[0] is None: kinds.append(tg[1])
        else: kinds.append(st(tg[0]) + ':' + tg[1])
    c[('shortest cycle < 1: length', len(cyc))] += 1
    c[('shortest cycle < 1: escape edges', sum(1 for k_ in kinds if k_ == 'esc'))] += 1
    c[('shortest cycle < 1: edge kinds', tuple(sorted(kinds)))] += 1
    c[('shortest cycle < 1: node roles', ''.join(sorted(role(q + 1) for q in cyc)))] += 1
    cellR = set(tg[0] for a_, b_, tg in es if tg[0] not in ('escape', None))
    c[('shortest cycle < 1: distinct cell states used', len(cellR))] += 1
    c[('shortest cycle < 1: reading 1 a node', 0 in cyc)] += 1
    c[('cycles < 1 in all: count bucket', min(len(ca), 50))] += 0
for kk, v in sorted(c.items(), key=str):
    if v: print(v, '|', kk)
