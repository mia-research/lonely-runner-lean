"""The B = 10 box (S in [9, 10]) reported 14 climbs into (7, 9).  Check them directly: take the witness point of every
terminal cell (exact rationals, strictly inside: tau > 0), realise it as integer speeds with positive values
(the runner at speed L of (L, L + L s_1, ..., L + L s_7), L the common denominator), and run the plain exact cascade on
that runner.  A real late event has u* = d_min t* > 7/8.  Exact; no floating point in any decision."""
from gmpy2 import mpq
from math import lcm, floor
from fractions import Fraction as F
import climb_cells_v3 as v3
from arrangement_lib import readings, nd

found = []
orig = v3.Search.children
def children(self, st):
    rows, wit, N, p, lab, word = st
    n0 = len(self.terms)
    kids = orig(self, st)
    if len(self.terms) > n0:
        # recompute the witness of each new terminal cell (the exit rows) exactly
        W = [k for k in self.runners if lab[k][0] == 'way']
        for q in W:
            Mq = lab[q][1]; r2 = list(rows)
            for k in W:
                if k != q: r2.append(v3.le({k: -mpq(8 * Mq + 1), q: mpq(8 * lab[k][1] + 1)}))
            rx = r2 + [v3.le({q: mpq(self.E)}, mpq(8 * Mq + 1), strict=True)]
            r = v3.lp_max(rx, v3.CT, wit[1])
            if r is not None and r[0] > 0: found.append((word + [(q, Mq)], r[1]))
    return kids
v3.Search.children = children
S = v3.Search(10, 9)
for root in S.roots(): S.dfs(root)
print(f"terminal cells: {len(S.terms)}; witnesses recovered: {len(found)}")
def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
ok = 0
for word, x in found:
    s = [F(1)] + [F(int(v.numerator), int(v.denominator)) for v in x[:6]]
    L = lcm(*[v.denominator for v in s])
    ds = sorted({int(v * L) for v in s})
    V = [L] + [L + d for d in ds]                      # positive speeds; the subject is the runner at speed L
    dd = readings(V, 0); t = cascade(dd); u = min(dd) * t
    late = u > F(7, 8)
    ok += late
    print(f"  S = {s[-1]} ({float(s[-1]):.4f})  word length {len(word)}  realised u* = {u} ({float(u):.4f})  late: {late}  speeds {V}")
print(f"late events confirmed by the plain cascade: {ok} of {len(found)}")
