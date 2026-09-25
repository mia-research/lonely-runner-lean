"""Order 8: every cascade climb from R = 1 into (7, 9), followed EXACTLY, as cells of reading space.
Exact rational arithmetic throughout (gmpy2.mpq); no floating point.

Coordinates.  Readings s_1 = 1 (d_min) <= s_2 <= ... <= s_7 = S <= B (d_j / d_min; scale invariance).
R = 8 d_min t; the bound is R = 1.  At R a runner of reading s reads s R; it is IN THE WAY iff s R lies in
(8M - 1, 8M + 1) for some M >= 1, and CLEAR otherwise.  Loneliness needs only that: where a clear runner sits
beyond 1/8 does not matter.  So each runner, at each step, carries one coarse label:
    gap M  (M >= 0):  8M + 1 <= s R <= 8M + 7        (clear, between laps M and M + 1)
    way M  (M >= 1):  8M - 1 <  s R <  8M + 1        (in the subject's slot at lap M)
The lap number is kept only to follow the cascade.

The cascade, exactly (MANUSCRIPT_v21 s6.1, s6.13): at R with in-the-way set W (non-empty), the move goes to the
LATEST opening, R' = (8 M_q + 1)/s_q for the setter q in W with (8 M_q + 1) s_k >= (8 M_k + 1) s_q for all k in W.
Writing R = N / s_p (N = 8M + 1, p the last setter; R_0 = 1 = 1 / s_1), every label and every setter choice is a
linear inequality in (s_2, ..., s_7).  Strict inequalities carry the margin tau; a cell is realisable iff max tau > 0.
Nothing is relaxed: every real climb lies in exactly the cell of its own label sequence, and every cell with
tau > 0 contains real climbs.

The LP (7 unknowns: s_2..s_7, tau; many rows a.x <= b) is solved through its dual, min b.y s.t. A^T y = c, y >= 0,
by the primal simplex with Bland's rule; the basis is 7 x 7 and starts from the explicit bound rows.

Output: number of LPs, cells explored, climbs that exit into (7, 9) (terminal cells), the exact range of S over
them, and climbs that stop in band 0 (early events)."""
import sys, time
from gmpy2 import mpq
from multiprocessing import Pool
from collections import Counter

NV = 7            # x = (s_2, ..., s_7, tau)
TAU = 6
Z = mpq(0); ONE = mpq(1)

# ------------------------------------------------------------------ exact LP: max c.x  s.t.  A x <= b
def solve7(M, rhs):
    """solve M z = rhs, M 7x7, exact; returns None if singular"""
    n = len(M); A = [list(M[i]) + [rhs[i]] for i in range(n)]
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c] != 0), None)
        if piv is None: return None
        A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]
        A[c] = [v / pv for v in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]; A[r] = [a - f * b for a, b in zip(A[r], A[c])]
    return [A[i][n] for i in range(n)]

def lp_max(rows, c, init):
    """rows: list of (a[7], b).  c: objective.  init: 7 row indices whose a's are +/- unit vectors matching sign of c
    (a dual-feasible basis).  Returns (value, x) or None if the primal is infeasible."""
    basis = list(init)
    while True:
        AB = [rows[i][0] for i in basis]
        # y_B from A_B^T y_B = c
        ABt = [[AB[j][i] for j in range(NV)] for i in range(NV)]
        yB = solve7(ABt, c)
        if yB is None: raise RuntimeError('singular basis')
        # primal point x from A_B x = b_B
        x = solve7(AB, [rows[i][1] for i in basis])
        # pricing: reduced cost of row j is b_j - a_j.x ; negative => enters (Bland: smallest index)
        bset = set(basis); enter = -1
        for j, (a, b) in enumerate(rows):
            if j in bset: continue
            if b - sum(ai * xi for ai, xi in zip(a, x)) < 0: enter = j; break
        if enter < 0:
            return sum(ci * xi for ci, xi in zip(c, x)), x
        d = solve7(ABt, rows[enter][0])        # A_B^T d = a_enter
        leave = -1; best = None
        for i in range(NV):
            if d[i] > 0:
                r = yB[i] / d[i]
                if best is None or r < best or (r == best and basis[i] < basis[leave]):
                    best = r; leave = i
        if leave < 0:
            return None                          # dual unbounded => primal infeasible
        basis[leave] = enter

# ------------------------------------------------------------------ rows
def unit(i, sgn):
    a = [Z] * NV; a[i] = mpq(sgn); return a

def base_rows(B):
    """the bound rows first (indices 0..13): s_j <= B, -s_j <= -1, tau <= 1, -tau <= 1; then the order chain."""
    R = []
    for i in range(6): R.append((unit(i, 1), mpq(B)))
    for i in range(6): R.append((unit(i, -1), mpq(-1)))
    R.append((unit(TAU, 1), ONE)); R.append((unit(TAU, -1), ONE))
    for i in range(5):
        a = [Z] * NV; a[i] = ONE; a[i + 1] = -ONE; R.append((a, Z))        # s_{i+2} <= s_{i+3}
    return R

def lin(coef, const=Z, tau=Z):
    """coef: {reading index 1..7: value}; reading 1 is the constant 1.  Returns (a, shift) with sum = a.x + shift."""
    a = [Z] * NV; sh = const
    for k, v in coef.items():
        if k == 1: sh += v
        else: a[k - 2] += v
    a[TAU] = tau
    return a, sh

def le(coef, rhs=Z, strict=False):
    """sum coef_k s_k (+ tau if strict) <= rhs"""
    a, sh = lin(coef, tau=ONE if strict else Z)
    return (a, rhs - sh)

def reading_rows(k, N, p, label):
    """runner k's reading N s_k / s_p lies in the label's interval; returns rows."""
    kind, M = label
    def cf(x, y):     # x * N s_k  - y * s_p  as coef dict
        d = {}
        d[k] = d.get(k, Z) + x * N
        d[p] = d.get(p, Z) - y
        return d
    if kind == 'gap':
        lo, hi = mpq(8 * M + 1), mpq(8 * M + 7)
        return [le(cf(-1, -lo)), le(cf(1, hi))]              # lo s_p <= N s_k <= hi s_p
    lo, hi = mpq(8 * M - 1), mpq(8 * M + 1)
    return [le(cf(-1, -lo), strict=True), le(cf(1, hi), strict=True)]

def order(label):
    kind, M = label
    return 2 * M if kind == 'gap' else 2 * M - 1

def from_order(o):
    return ('gap', o // 2) if o % 2 == 0 else ('way', (o + 1) // 2)

# ------------------------------------------------------------------ the search
class Search:
    def __init__(self, B, Slo):
        self.B = mpq(B); self.rows0 = base_rows(B)
        a = [Z] * NV; a[5] = -ONE; self.rows0.append((a, -mpq(Slo)))       # s_7 >= Slo
        self.nlp = 0; self.cells = 0; self.terms = []; self.early = 0
        self.maxo = 2 * ((7 * int(B) + 1) // 8) + 2

    def init_for(self, c):
        idx = []
        for i in range(NV):
            if i == TAU: idx.append(12 if c[i] >= 0 else 13)
            else: idx.append(i if c[i] >= 0 else 6 + i)
        return idx

    def tau(self, rows):
        self.nlp += 1
        c = [Z] * NV; c[TAU] = ONE
        r = lp_max(rows, c, self.init_for(c))
        return None if r is None else r[0]

    def srange(self, rows):
        # tau = 0: the closure.  Rows 12, 13 are tau's own bounds (part of the starting basis): keep them.
        closed = [(a, b) if i in (12, 13) else (a[:TAU] + [Z], b) for i, (a, b) in enumerate(rows)]
        c = [Z] * NV; c[5] = ONE
        hi = lp_max(closed, c, self.init_for(c)); c[5] = -ONE
        lo = lp_max(closed, c, self.init_for(c))
        return (-lo[0] if lo else None), (hi[0] if hi else None)

    def labels(self, rows, N, p, prev, k_list, i, cur, out):
        """assign labels to runners k_list[i:], each >= prev[k], contiguous feasible ranges."""
        if i == len(k_list):
            out.append((dict(cur), rows)); return
        k = k_list[i]; o = order(prev[k]); seen = False
        while o <= self.maxo:
            lab = from_order(o)
            r2 = rows + reading_rows(k, N, p, lab)
            t = self.tau(r2)
            if t is not None and t > 0:
                seen = True; cur[k] = lab
                self.labels(r2, N, p, prev, k_list, i + 1, cur, out)
                del cur[k]
            elif seen:
                break
            o += 1

    def step(self, rows, N, p, lab, word):
        """state: R = N / s_p with labels lab (runners 2..7).  Branch on the setter, then on the new labels."""
        self.cells += 1
        W = [k for k in range(2, 8) if lab[k][0] == 'way']
        if not W:
            self.early += 1; return                                    # lonely in band 0: an early event
        for q in W:
            Mq = lab[q][1]
            r2 = list(rows)
            for k in W:
                if k != q:                                             # q's opening is the latest
                    r2.append(le({k: -mpq(8 * Mq + 1), q: mpq(8 * lab[k][1] + 1)}))
            # exit into (7, 9): 7 s_q < 8 Mq + 1
            rx = r2 + [le({q: mpq(7)}, mpq(8 * Mq + 1), strict=True)]
            t = self.tau(rx)
            if t is not None and t > 0:
                lo, hi = self.srange(rx)
                self.terms.append((word + [(q, Mq)], t, lo, hi))
            # stay in band 0: 8 Mq + 1 <= 7 s_q
            rs = r2 + [le({q: -mpq(7)}, -mpq(8 * Mq + 1))]
            t = self.tau(rs)
            if t is None or t <= 0: continue
            Nn = mpq(8 * Mq + 1)
            prev = {}
            for k in range(2, 8):
                if k == q: continue
                if k in W: prev[k] = ('gap', lab[k][1])                # it has left its zone by R'
                else: prev[k] = lab[k]
            others = [k for k in range(2, 8) if k != q]
            outs = []
            self.labels(rs, Nn, q, prev, others, 0, {}, outs)
            for newlab, rr in outs:
                newlab[q] = ('gap', Mq)                                # the setter reads exactly 8 Mq + 1
                self.step(rr, Nn, q, newlab, word + [(q, Mq)])

def run(args):
    B, Slo, fixed = args                      # fixed: {runner: label at R = 1} for runners 7 and 6
    S = Search(B, Slo)
    # R_0 = 1 = 1 / s_1 : reading of k is s_k
    rows = list(S.rows0)
    for k, lab in fixed.items(): rows += reading_rows(k, ONE, 1, lab)
    t = S.tau(rows)
    if t is None or t <= 0: return S.nlp, S.cells, S.terms, S.early
    prev = {k: ('gap', 0) for k in range(2, 8)}
    prev.update(fixed)
    others = [k for k in range(2, 8) if k not in fixed]
    outs = []
    S.labels(rows, ONE, 1, prev, others, 0, dict(fixed), outs)
    for lab, rr in outs:
        lab.update(fixed)
        S.step(rr, ONE, 1, lab, [])
    return S.nlp, S.cells, S.terms, S.early

if __name__ == '__main__':
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    Slo = mpq(sys.argv[2]) if len(sys.argv) > 2 else mpq(1)
    t0 = time.time()
    # split the work on runner 7's (the far runner's) label at R = 1
    maxo = 2 * ((7 * B + 1) // 8) + 2
    # split the work on the labels of runners 7 and 6 at R = 1 (labels only rise with the reading, 6 <= 7)
    jobs = [(B, Slo, {7: from_order(o7), 6: from_order(o6)}) for o7 in range(0, 2 * B + 2) for o6 in range(0, o7 + 1)]
    with Pool() as p:
        res = p.map(run, jobs, chunksize=1)
    nlp = sum(r[0] for r in res); cells = sum(r[1] for r in res); early = sum(r[3] for r in res)
    terms = [t for r in res for t in r[2]]
    print(f"climb cells: readings in [1, {B}], S >= {Slo}; exact; {time.time() - t0:.0f}s")
    print(f"  LPs {nlp}; cells explored {cells}; climbs ending in band 0 (early events) {early}")
    print(f"  climbs exiting into (7, 9) (terminal cells): {len(terms)}")
    if terms:
        lo = min(t[2] for t in terms); hi = max(t[3] for t in terms)
        print(f"  far reading S over every terminal cell: [{lo}, {hi}] = [{float(lo):.5f}, {float(hi):.5f}]  (floats printed beside exact values)")
        words = Counter(tuple(t[0]) for t in terms)
        print(f"  distinct setter words among terminal cells: {len(words)}; lengths {sorted(set(len(w) for w in words))}")
        first = Counter(t[0][0] for t in terms)
        print(f"  first setter (reading index, lap): {dict(first)}")
        with open(f"climb_cells_B{B}_S{str(Slo).replace('/', '_')}_words.txt", "w") as f:
            for w, tt, l, h in terms:
                f.write(f"{w}\t{tt}\t{l}\t{h}\n")
