"""mixed_lemma_check_v1 (2026-10-06): M(2,2) and M(1,3), exact arithmetic only.

||x|| = distance from x to the nearest integer.  c's at threshold 1/8, odd u's at threshold 1/4.
M(2,2): distinct c1,c2 >= 1, distinct odd u1,u2: exists tau with ||c_i tau|| >= 1/8, ||u_j tau|| >= 1/4.
M(1,3): c >= 1, distinct odd u1<u2<u3: exists tau with ||c tau|| >= 1/8, ||u_j tau|| >= 1/4.

RESULT.  M(2,2): proof by hand below, case split A / C / DE1-DE4; one counting step (Lemma Q), tagged.
         M(1,3): no complete proof.  Cases a, b, e, c, f below are proved; the rest (class R) is open.
         No counterexample to either statement up to 40 (this script), and none in a scratch C search
         (distinct values, M(1,3) to 200, M(2,2) to 150; not a project artifact).

NOTATION.  For odd u let b = u if u = 1 mod 4, b = -u if u = 3 mod 4; so b = 1 (mod 4), ||u x|| = ||b x||.
"Quarter points" are the multiples of 1/4.

LEMMA ROT (identity).  K integer: b*K/4 = K/4 (mod 1) because b = 1 mod 4; if 4 | c then c*K/4 is an
  integer.  So tau -> tau + K/4 leaves ||c tau|| unchanged for 4 | c and moves every b*tau by +K/4.
  Hence: if v is a quarter point with ||b_j tau0 - v|| >= 1/4 for all j, then tau = tau0 + K/4 with
  K = -4v makes ||u_j tau|| = ||b_j tau0 - v|| >= 1/4.
LEMMA FIT2 (inequality).  If ||p - q|| <= 1/4 there is a quarter point v with ||p - v||, ||q - v|| >= 1/4.
  Lift so q = p + D, 0 <= D <= 1/4.  The closed interval [p + D + 1/4, p + 3/4] has length 1/2 - D >= 1/4,
  so it contains a multiple v of 1/4; then v - p and v - q both lie in [1/4, 3/4].
LEMMA CELL2.  If p, q lie in one closed quarter cell [w, w + 1/4] (w a quarter point), then v = w + 1/2 and
  v' = w + 3/4 both have distance >= 1/4 from p and q (v - x in [1/4,1/2], v' - x in [1/2,3/4]).
LEMMA C2.  Let 4 | c1, c2 not = 0 mod 4.  If v, v + 1/4 are both at distance >= 1/4 from b1*tau0, b2*tau0 and
  ||c1 tau0|| >= 1/8, one of K = -4v, -4v - 1 gives tau = tau0 + K/4 satisfying all four conditions.
  u's and c1 by ROT.  c2 odd: with b' = +-c2 = 1 mod 4, ||c2 tau|| = ||b' tau0 - v''|| for v'' in {v, v+1/4};
  a point cannot be within 1/8 of two points 1/4 apart.  c2 = 2 mod 4: c2*K/4 = K/2 (mod 1), so the two
  choices give c2 tau = x and x + 1/2, and ||x|| < 1/8, ||x + 1/2|| < 1/8 cannot both hold.

LEMMA Q.  For positive integers A1, A2, D there is s with ||s|| <= 1/4, ||A1 s/D|| >= 1/8, ||A2 s/D|| >= 1/8.
  Grid (1/L)Z, L = 32*A1*A2, one period s in [0, D).  W = {||s|| <= 1/4}: D disjoint closed windows,
  L/2 + 1 grid points each, D(L/2 + 1) in all.  N_i = {||A_i s/D|| < 1/8}: A_i open intervals of length
  D/(4A_i) per period with endpoints on the grid, so LD/(4A_i) - 1 grid points each, LD/4 - A_i in all.
  LD/2 - A1 - A2 < D(L/2 + 1), so a grid point of W lies outside N_1 and N_2.
  [PROVISIONAL: counting tool; supports: existence of s in Lemma Q, hence case C of M(2,2)]
  The script takes the least such s in [0, D) (a left endpoint of a constraint interval) and checks it.

PROOF OF M(2,2).  d = |b1 - b2| (a multiple of 4, nonzero), g = gcd(u1,u2), d = 4 g d' with d' >= 1.
 A  (4 divides neither c): tau = 1/4.  ||c/4|| is 1/4 (c odd) or 1/2 (c = 2 mod 4); ||u/4|| = 1/4.
 C  (4 divides both): Lemma Q with A_i = c_i, D = d gives s; tau0 = s/d has ||c_i tau0|| >= 1/8 and
    ||b1 tau0 - b2 tau0|| = ||s|| <= 1/4.  FIT2 gives v, ROT gives tau = tau0 + K/4 (c's unchanged).
 DE (4 divides exactly one; call it c1 = 4|c1, c2 the other).  It suffices to find tau0 with
    ||c1 tau0|| >= 1/8 and b1 tau0, b2 tau0 in one closed quarter cell (CELL2, then C2).
  DE1  d does not divide c1.  q = d/gcd(c1,d) >= 2; the values c1 k/d mod 1 (k integer) are the multiples
       of 1/q, and floor(q/2)/q has distance >= 1/3 from the integers.  tau0 = k/d for such k; then
       (b1 - b2) tau0 is an integer, so b1 tau0 = b2 tau0 (one point, in a closed cell).
  DE2  c1 = t d, d' >= 2.  xi = 1/(8t), tau0 = (k + xi)/d: c1 tau0 = t k + 1/8; b1 tau0 - b2 tau0 = +-xi.
       Let P be the lower of the two points (the other is P + xi).  4P mod 1 runs, as k varies, over a coset
       of (1/d')Z (4P = beta (k + xi)/d' with beta = b/g coprime to d').  The target [0, 1 - 4 xi] has
       length >= 1/2 >= 1/d', so some k puts 4P mod 1 there, and then P, P + xi lie in one closed cell.
  DE3  c1 = t d, d' = 1, b1 b2 > 0.  Then |u1 - u2| = 4g; q = min(u)/g.  tau0 = sign(b) xi/(4g) gives
       4 b_j tau0 = (u_j/g) xi, i.e. the points q xi/4 and (q + 4) xi/4; one closed cell iff {q xi} <= 1 - 4 xi;
       c1 tau0 = +-t xi.  If q + 4 <= 8t: xi = 1/(8t) (q xi + 4 xi <= 1, t xi = 1/8).  Else q >= 5 and q does
       not divide t (q | t would give 8t >= 8q > q + 4); r = ||t/q|| >= 1/q; n = 1 if r >= 1/8, else
       n = ceil(1/(8r)) (then nr in [1/8, 1/4), and n <= q/8 + 1 <= q/4 since r < 1/8 forces q >= 9);
       xi = n/q <= 1/4, {q xi} = 0, ||t xi|| = nr >= 1/8.
  DE4  c1 = t d, d' = 1, b1 b2 < 0.  Then {u1,u2} = {g, 3g} and c1 = 4 g t.  Put tau = y/g with
       y = n + 1/2 + z, n integer, 0 <= z <= 1/12: ||y|| >= 5/12, ||3y|| >= 1/4 (3y in 3n + [5/4, 7/4]),
       c1 tau = 4ty = 4tz (mod 1), c2 tau = c2 y / g.
   DE4a  g does not divide c2.  z = 1/(32t) (4tz = 1/8).  h = gcd(c2,g), g' = g/h >= 3, gcd(c2/h, g') = 1, so
         as n varies c2 tau runs over a coset of (1/g')Z; its point nearest 1/2 is within 1/(2g') <= 1/6 of 1/2,
         so has distance >= 1/3 from the integers.
   DE4b  e = c2/g integer, e not = 0 mod 4; take n = 0.
     e odd: c2 tau = 1/2 + ez (mod 1), need ||ez|| <= 3/8.  e <= 12t: z = 1/(32t), ez <= 3/8.
            e > 12t: on [z_lo, z_hi] = [1/(32t), min(7/(32t), 1/12)] c1 is clear and e(z_hi - z_lo) >= 1/4
            (t = 1: 13*5/96; t = 2: 25*13/192; t >= 3: 12t*3/(16t)); take z_lo if ||e z_lo|| <= 3/8, else
            z = (floor(e z_lo) + 5/8)/e <= z_lo + 1/(4e) <= z_hi.
     e = 2 mod 4: c2 tau = ez (mod 1).  3 does not divide t: z = 1/12 (||t/3|| = 1/3; e/12 is an odd
            multiple of 1/6, distance >= 1/6).  t = 3s: if e >= 4s, on [1/(96s), 7/(96s)] c1 is clear; take
            z_lo if ||e z_lo|| >= 1/8, else z = (N + 1/8)/e with N the integer within 1/8 of e z_lo
            (step < 1/(4e) <= 6/(96s)).  If e < 4s, on [1/(8e), min(7/(8e), 1/12)] e is clear; take z_lo if
            ||12 s z_lo|| >= 1/8, else z = (N + 1/8)/(12s) (step < 1/(48s) <= min(3/(4e), 1/12 - 1/(8e))).
  These cases are exhaustive (d' >= 2, or d' = 1 with b1 b2 > 0 or < 0).  M(2,2) holds.  QED (with the tag on Q).

M(1,3), PROVED CASES (c = 4m where 4 | c; tau0 below, then ROT with the least K in {0,1,2,3} making all u's
good; c is unchanged by ROT).
 a  4 does not divide c: tau = 1/4.
 b  u3 <= 2c: tau = 1/2 + 1/(8c): c tau = 1/8 (mod 1); u tau = 1/2 + u/(8c), 0 < u/(8c) <= 1/4.
 e  the points b_j/(8c) lie in one closed aligned half circle [n/4, (n+2)/4]: tau0 = 1/(8c) (c tau0 = 1/8).
 c  some pair has g = gcd(u_i,u_j) not dividing m: tau0 = k/(4g) with ||m k/g|| >= 1/8 (multiples of 1/q,
    q = g/gcd(g,m) >= 3).  b_i tau0 = b_j tau0 = a quarter point w (4g | b_i - b_j); the other three quarter
    points are at distance >= 1/4 from w, and the third point blocks (distance < 1/4) at most two of them.
 f  some pair (i,j) and third l with, on the lattice k/d (d = |b_i - b_j|, k in Z/d),
    #{k: ||(b_l - b_i)k/d|| <= 1/4} > #{k: ||c k/d|| < 1/8}; counts are g(2 floor(M/4)+1) and
    g(2 ceil(M/8)-1) with g = gcd(.,d), M = d/g.  Such k gives b_i tau0 = b_j tau0 and FIT2 for the two points.
    [PROVISIONAL: counting tool; supports: existence of k in case f of M(1,3)]
 R  everything else: no proof.  Listed below with the tau found by the exhaustive search.
 Exact reduction used in the analysis (not needed for the proved cases): for 4 | c, M(1,3) holds iff some y
 with ||y|| >= 1/8 and some quarter point v have ||(b_j/c) y - v|| >= 1/4 for j = 1,2,3; for c = 4 this is a
 statement about y in [1/8, 7/8] alone.

Exhaustive decision (part a): a non-empty closed clear set of period 1 contains a left endpoint
(8j+1)/(8c) or (4j+1)/(4u), 0 <= j < c (resp. u); all are tested (plus 1/4, 1/2 first), integer arithmetic.
"""
import itertools, math, sys
from fractions import Fraction as F
from math import gcd

N = int(sys.argv[1]) if len(sys.argv) > 1 else 40

# ---------- exact distance tests ----------
def dist(x):
    x = x - math.floor(x)
    return min(x, 1 - x)

def far8i(k, p, q):
    r = (k * p) % q
    return 8 * r >= q and 8 * r <= 7 * q

def far4i(k, p, q):
    r = (k * p) % q
    return 4 * r >= q and 4 * r <= 3 * q

def good(C, U, t):
    return all(dist(c * t) >= F(1, 8) for c in C) and all(dist(u * t) >= F(1, 4) for u in U)

def solvable(C, U):
    cands = [(1, 4), (1, 2)]
    cands += [(8 * j + 1, 8 * c) for c in C for j in range(c)]
    cands += [(4 * j + 1, 4 * u) for u in U for j in range(u)]
    for p, q in cands:
        if all(far8i(c, p, q) for c in C) and all(far4i(u, p, q) for u in U):
            return F(p, q)
    return None

def b_of(u):
    return u if u % 4 == 1 else -u

def rotate(tau0, U):
    """least K in 0..3 with all u good at tau0 + K/4 (ROT); None if no K."""
    for K in range(4):
        t = tau0 + F(K, 4)
        if all(dist(u * t) >= F(1, 4) for u in U):
            return t
    return None

# ---------- Lemma Q: least s in [0,D) with ||s||<=1/4, ||A_i s/D||>=1/8 ----------
def lemma_q(A1, A2, D):
    cands = set()
    for k in range(0, D + 1):
        cands.add(F(4 * k - 1, 4))
    for A in (A1, A2):
        for m in range(0, A + 1):
            cands.add(F((8 * m + 1) * D, 8 * A))
    for s in sorted(x for x in cands if 0 <= x < D + 1):
        if dist(s) <= F(1, 4) and dist(F(A1) * s / D) >= F(1, 8) and dist(F(A2) * s / D) >= F(1, 8):
            return s
    return None

# ---------- M(2,2) construction ----------
STEP_FAIL = []   # intermediate claims of DE1-DE3 that do not hold (should stay empty)

def in_cell(P, w):
    x = (P - w) % 1
    return x <= F(1, 4)

def c2_finish(tau0, w, cz, co, U):
    """Lemma C2: v in {w+1/2, w+3/4}, K = -4v; return the first tau that passes all checks.
    Records a step failure if tau0 does not have c1 clear and both b_j tau0 in [w, w+1/4]."""
    if not (dist(cz * tau0) >= F(1, 8) and all(in_cell(b_of(u) * tau0, w) for u in U)):
        STEP_FAIL.append((cz, co, U, tau0))
    for v in (w + F(1, 2), w + F(3, 4)):
        K = (-4 * v) % 4
        t = tau0 + K / 4
        if good((cz, co), U, t):
            return t
    return None

def cell_w(P):
    """w = floor(4P)/4 for the lower point P (mod 1)."""
    x = P - math.floor(P)
    return F(math.floor(4 * x), 4)

def construct22(C, U):
    c1, c2 = C
    u1, u2 = U
    if c1 % 4 and c2 % 4:
        return 'A', F(1, 4)
    b1, b2 = b_of(u1), b_of(u2)
    d = abs(b1 - b2)
    if c1 % 4 == 0 and c2 % 4 == 0:
        s = lemma_q(c1, c2, d)
        if s is None:
            return 'C', None
        if not (dist(s) <= F(1, 4) and dist(F(c1) * s / d) >= F(1, 8) and dist(F(c2) * s / d) >= F(1, 8)):
            STEP_FAIL.append((C, U, s))
        return 'C', rotate(s / d, U)
    cz, co = (c1, c2) if c1 % 4 == 0 else (c2, c1)
    if cz % d:
        k = next(k for k in range(d) if dist(F(cz * k, d)) >= F(1, 8))
        tau0 = F(k, d)
        return 'DE1', c2_finish(tau0, cell_w(b1 * tau0), cz, co, U)
    t = cz // d
    g = gcd(u1, u2)
    dp = d // (4 * g)
    if dp >= 2:
        xi = F(1, 8 * t)
        lo = b2 if b1 - b2 > 0 else b1
        for k in range(dp):
            tau0 = (k + xi) / d
            x = 4 * lo * tau0
            x = x - math.floor(x)
            if x <= 1 - 4 * xi:
                return 'DE2', c2_finish(tau0, cell_w(lo * tau0), cz, co, U)
        return 'DE2', None
    if b1 * b2 > 0:
        q = min(u1, u2) // g
        sb = 1 if b1 > 0 else -1
        if q + 4 <= 8 * t:
            xi = F(1, 8 * t)
        else:
            n = next((n for n in range(1, q // 4 + 1) if dist(F(t * n, q)) >= F(1, 8)), None)
            if n is None:
                return 'DE3', None
            xi = F(n, q)
        tau0 = sb * xi / (4 * g)
        lo = b1 if abs(b1) < abs(b2) else b2
        return 'DE3', c2_finish(tau0, cell_w(lo * tau0), cz, co, U)
    # DE4: {u1,u2} = {g,3g}, cz = 4 g t
    assert sorted((u1, u2)) == [g, 3 * g] and cz == 4 * g * t
    if co % g:
        z = F(1, 32 * t)
        h = gcd(co, g)
        gp, cop = g // h, co // h
        best = max(range(gp), key=lambda n: (dist(cop * (n + F(1, 2) + z) / gp), -n))
        y = best + F(1, 2) + z
        return 'DE4a', y / g
    e = co // g
    if e % 2:
        if e <= 12 * t:
            z = F(1, 32 * t)
        else:
            zlo = F(1, 32 * t)
            if dist(e * zlo) <= F(3, 8):
                z = zlo
            else:
                z = (math.floor(e * zlo) + F(5, 8)) / e
        return 'DE4b-odd', (F(1, 2) + z) / g
    if t % 3:
        z = F(1, 12)
    else:
        s = t // 3
        if e >= 4 * s:
            zlo = F(1, 96 * s)
            if dist(e * zlo) >= F(1, 8):
                z = zlo
            else:
                Nn = round(e * zlo)
                z = (Nn + F(1, 8)) / e
        else:
            zlo = F(1, 8 * e)
            if dist(12 * s * zlo) >= F(1, 8):
                z = zlo
            else:
                Nn = round(12 * s * zlo)
                z = (Nn + F(1, 8)) / (12 * s)
    return 'DE4b-even', (F(1, 2) + z) / g

# ---------- M(1,3) construction (partial) ----------
def fits(pts):
    for n in range(4):
        lo = F(n, 4)
        if all(((p - lo) % 1) <= F(1, 2) for p in pts):
            return True
    return False

def cnt_close(D, d):
    g = gcd(D, d); M = d // g
    return g * (2 * (M // 4) + 1)

def cnt_near(c, d):
    g = gcd(c, d); M = d // g
    return g * (2 * (-(-M // 8)) - 1)

def construct13(c, U):
    if c % 4:
        return 'a', F(1, 4)
    if U[2] <= 2 * c:
        return 'b', F(1, 2) + F(1, 8 * c)
    B = [b_of(u) for u in U]
    m = c // 4
    tau0 = F(1, 8 * c)
    if fits([b * tau0 for b in B]):
        return 'e', rotate(tau0, U)
    for i, j in ((0, 1), (0, 2), (1, 2)):
        g = gcd(U[i], U[j])
        if m % g:
            k = next(k for k in range(g) if dist(F(m * k, g)) >= F(1, 8))
            return 'c', rotate(F(k, 4 * g), U)
    for i, j, l in ((0, 1, 2), (0, 2, 1), (1, 2, 0)):
        d = abs(B[i] - B[j]); D = abs(B[l] - B[i])
        if cnt_close(D, d) > cnt_near(c, d):
            k = next((k for k in range(d) if dist(F(D * k, d)) <= F(1, 4) and dist(F(c * k, d)) >= F(1, 8)), None)
            if k is None:
                return 'f', None
            return 'f', rotate(F(k, d), U)
    return 'R', None

# ---------- main ----------
if __name__ == '__main__':
    out = open('mixed_lemma_check_v1.out', 'w')
    def w(s=""):
        out.write(s + "\n"); print(s)
    w(__doc__)
    odds = [u for u in range(1, N + 1) if u % 2]

    # (a) exhaustive exact test
    w("== (a) exhaustive exact test, distinct values in [1, %d] ==" % N)
    fail22 = []; tot22 = 0
    for C in itertools.combinations(range(1, N + 1), 2):
        for U in itertools.combinations(odds, 2):
            tot22 += 1
            if solvable(C, U) is None: fail22.append((C, U))
    w("M(2,2): cases %d, with no tau %d %s" % (tot22, len(fail22), fail22[:20]))
    fail13 = []; tot13 = 0
    for c in range(1, N + 1):
        for U in itertools.combinations(odds, 3):
            tot13 += 1
            if solvable((c,), U) is None: fail13.append((c, U))
    w("M(1,3): cases %d, with no tau %d %s" % (tot13, len(fail13), fail13[:20]))

    # firing control and agreement with mixed_threshold_v1 at 24
    w("-- control: the same decision procedure on statements with failures, values in [1, 24] --")
    o24 = [u for u in range(1, 25) if u % 2]
    f14 = [(c, U) for c in range(1, 25) for U in itertools.combinations(o24, 4) if solvable((c,), U) is None]
    f23 = [(C, U) for C in itertools.combinations(range(1, 25), 2) for U in itertools.combinations(o24, 3)
           if solvable(C, U) is None]
    w("M(1,4): no tau in %d cases, first %s" % (len(f14), f14[:3]))
    w("M(2,3): no tau in %d cases, first %s" % (len(f23), f23[:3]))
    n22 = sum(1 for C in itertools.combinations(range(1, 25), 2) for U in itertools.combinations(o24, 2))
    n13 = sum(1 for c in range(1, 25) for U in itertools.combinations(o24, 3))
    w("case counts at 24: M(2,2) %d, M(1,3) %d (mixed_threshold_v1.out records 18216 and 5280)" % (n22, n13))

    # (b) constructed tau, checked exactly
    w("")
    w("== (b) M(2,2): the tau the proof constructs, checked on every case ==")
    cls = {}; bad = []
    for C in itertools.combinations(range(1, N + 1), 2):
        for U in itertools.combinations(odds, 2):
            k, t = construct22(C, U)
            cls[k] = cls.get(k, 0) + 1
            if t is None or not good(C, U, t): bad.append((k, C, U, t))
    for k in sorted(cls): w("  case %-10s %6d cases" % (k, cls[k]))
    w("  constructed tau fails in %d cases %s" % (len(bad), bad[:20]))
    w("  intermediate claims (Lemma Q output; DE1-DE3: c1 clear at tau0 and both points in one closed")
    w("  quarter cell) that fail: %d %s" % (len(STEP_FAIL), STEP_FAIL[:10]))

    w("")
    w("== (b) M(1,3): the tau of the proved cases, checked; class R has no proof ==")
    cls = {}; bad = []; rem = []
    for c in range(1, N + 1):
        for U in itertools.combinations(odds, 3):
            k, t = construct13(c, U)
            cls[k] = cls.get(k, 0) + 1
            if k == 'R':
                rem.append((c, U, solvable((c,), U)))
            elif t is None or not good((c,), U, t):
                bad.append((k, c, U, t))
    for k in sorted(cls): w("  case %-3s %6d cases" % (k, cls[k]))
    w("  constructed tau fails in %d cases %s" % (len(bad), bad[:20]))
    w("  class R (not covered by a proof; tau from the exhaustive search, checked exactly):")
    for c, U, t in rem:
        w("    c=%d U=%s B=%s tau=%s ok=%s" % (c, U, [b_of(u) for u in U], t, t is not None and good((c,), U, t)))
    out.close()
