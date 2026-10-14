"""Exact ratio-zone engine (agent_caseB_A).

Every constraint that occurs in this problem has the form   s_a <= q * s_b   or
s_a < q * s_b  with q a positive rational (band ordering, band bounds on s6/s0,
and every cluster/lap inequality of a block).  In log coordinates these are
difference constraints, so a finite conjunction of them is a 'zone' and is handled
exactly by a 7x7 bound matrix closed under Floyd-Warshall (multiplicative weights).

Bound entries: (q, strict) with q a Fraction or None (= +infinity).
  B[a][b] = (q, st)  means  s_a <= q s_b   (s_a < q s_b if st).
All arithmetic is Fraction; no floating point anywhere.
"""
from fractions import Fraction as F

N = 7
INF = None


def tighter(x, y):
    """True if bound x is strictly tighter than bound y."""
    if y[0] is None:
        return x[0] is not None
    if x[0] is None:
        return False
    return x[0] < y[0] or (x[0] == y[0] and x[1] and not y[1])


def compose(x, y):
    if x[0] is None or y[0] is None:
        return (None, False)
    return (x[0] * y[0], x[1] or y[1])


class Zone:
    __slots__ = ('B',)

    def __init__(self, B=None):
        if B is None:
            B = [[(F(1), False) if a == b else (None, False) for b in range(N)] for a in range(N)]
        self.B = B

    def copy(self):
        return Zone([row[:] for row in self.B])

    def add(self, a, b, q, strict):
        """impose s_a <= q s_b (strict if strict). Returns self (not closed)."""
        q = F(q)
        if tighter((q, strict), self.B[a][b]):
            self.B[a][b] = (q, strict)
        return self

    def close(self):
        B = self.B
        for k in range(N):
            Bk = B[k]
            for i in range(N):
                bik = B[i][k]
                if bik[0] is None:
                    continue
                Bi = B[i]
                for j in range(N):
                    c = compose(bik, Bk[j])
                    if c[0] is not None and tighter(c, Bi[j]):
                        Bi[j] = c
        return self

    def empty(self):
        for a in range(N):
            q, st = self.B[a][a]
            if q < 1 or (q == 1 and st):
                return True
        return False

    def implies(self, a, b, q, strict):
        """(closed zone) does the zone imply s_a <= q s_b (strict if strict)?"""
        cur = self.B[a][b]
        if cur[0] is None:
            return False
        q = F(q)
        if cur[0] < q:
            return True
        if cur[0] == q:
            return cur[1] or not strict
        return False

    def point(self):
        """a rational point (s0=1,...,s6) inside the (closed, non-empty) zone,
        chosen by sequential midpoint fixing.  Returns None if empty."""
        z = self.copy().close()
        if z.empty():
            return None
        vals = [F(1)] + [None] * (N - 1)
        # fix s0 = 1
        for i in range(1, N):
            # bounds on s_i relative to s0 (already fixed variables folded in by closure)
            hi = z.B[i][0]          # s_i <= hi * s0
            lo = z.B[0][i]          # s0 <= lo * s_i  -> s_i >= 1/lo
            lo_v = (F(0), False) if lo[0] is None else (1 / lo[0], lo[1])
            if hi[0] is None:
                v = lo_v[0] + 1
            elif lo_v[0] < hi[0]:
                v = (lo_v[0] + hi[0]) / 2
            else:
                v = hi[0]
            vals[i] = v
            z.add(i, 0, v, False).add(0, i, 1 / v, False).close()
            if z.empty():
                raise RuntimeError("point(): zone became empty while fixing (should not happen)")
        return vals

    def constraints(self):
        """non-trivial finite entries as a list (a,b,q,strict)."""
        out = []
        for a in range(N):
            for b in range(N):
                if a != b and self.B[a][b][0] is not None:
                    out.append((a, b, self.B[a][b][0], self.B[a][b][1]))
        return out


def band_zone():
    z = Zone()
    for i in range(N - 1):
        z.add(i, i + 1, 1, True)      # s_i < s_{i+1}
    z.add(0, 6, F(1, 7), True)        # s0 < s6/7  i.e. s6 > 7 s0
    z.add(6, 0, 9, False)             # s6 <= 9 s0
    return z.close()


def contains(vals, c):
    a, b, q, st = c
    return vals[a] < q * vals[b] if st else vals[a] <= q * vals[b]


# ------------------------------------------------------------- block types

def block_ok_vals(vals, e, K):
    m = 8 * K + 1
    for sd in vals:
        x = m * sd / vals[e]
        r = x - 8 * (x.numerator // (8 * x.denominator))
        if r < 1 or r > 7:
            return False
    return True


def type_of(vals, e, K):
    m = 8 * K + 1
    return tuple((m * sd / vals[e]).__floor__() // 8 for sd in vals)


def type_constraints(e, K, laps):
    """cluster form of block (e,K) with the given lap vector.
    Reading d in lap k:  (8k+1) s_e <= (8K+1) s_d <= (8k+7) s_e.
    Only the extreme member of each cluster (maximal run of equal laps) needs a bound;
    ordering supplies the rest.  Returns list of (a,b,q,strict) meaning s_a <= q s_b."""
    m = 8 * K + 1
    cons = []
    n = len(laps)
    d = 0
    while d < n:
        k = laps[d]
        lo = d
        while d + 1 < n and laps[d + 1] == k:
            d += 1
        hi = d
        # lower bound on the smallest member:  s_e * (8k+1)/m <= s_lo   <=>  s_e <= m/(8k+1) s_lo
        if lo != e:
            cons.append((e, lo, F(m, 8 * k + 1), False))
        # upper bound on the largest member:   s_hi <= (8k+7)/m s_e
        if hi != e:
            cons.append((hi, e, F(8 * k + 7, m), False))
        d += 1
    return cons


def range_ok(vals, e, K):
    R = F(8 * K + 1) / vals[e]
    return (1 <= R <= 7) or (9 <= R <= 15)


def all_types_at(vals):
    """every (e,K,laps) whose block works at this point with R in range."""
    out = []
    for e in range(N):
        K = 0
        while True:
            R = F(8 * K + 1) / vals[e]
            if R > 15:
                break
            if ((1 <= R <= 7) or (9 <= R <= 15)) and block_ok_vals(vals, e, K):
                out.append((e, K, type_of(vals, e, K)))
            K += 1
    return out
