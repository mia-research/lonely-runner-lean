"""m13_proof_v1 (2026-10-06): M(1,3) for every c >= 1 and every triple of distinct odd u's; exact arithmetic only.

FRAME (rule 1, RULES_n8_v4).  The displacement step of the quarter- and eighth-level descents (E402, E404): the
isolation is taken at the grid shifts j/4 or k/8, displaced by tau; the still reading c must be clear at 1/8 at tau
and three silenced readings, divided down to odd numbers, clear at 1/4 at tau.

STATEMENT M(1,3).  c >= 1, u1 < u2 < u3 distinct odd positive integers: there is a real tau with ||c tau|| >= 1/8
and ||u_j tau|| >= 1/4 (j = 1, 2, 3).  ||x|| is the distance from x to the nearest integer.

RESULT.  A written proof by the case split a / S / T / Phi / P below, exhaustive over every c >= 1 and every triple.
  Tagged steps: QP (used in S, T, Phi and P) and the choice of j in P, both [PROVISIONAL: counting tool].  No covering
  or complement step; the split is by integer divisibility and size conditions.  Order four (three numbers clear at
  1/4 at once) is not used.  No floating point.  Old case b, e, c and f of mixed_lemma_check_v1 are not used.
  mixed_lemma_check_v1's class R lies inside part Phi (REMARK; checked 170 of 170 on c <= 48, odd u <= 79).

NOTATION (as in mixed_lemma_check_v1).  b = u if u = 1 (mod 4), b = -u otherwise; so b = 1 (mod 4) and ||u x|| =
  ||b x||.  Sort the three b's: b_lo < b_mid < b_hi.  For 4 | c write c = 4m and a = (b - 1)/4 (distinct integers,
  a_lo < a_mid < a_hi).  G = gcd(a_mid - a_lo, a_hi - a_mid), x = (a_mid - a_lo)/G, N = (a_hi - a_lo)/G; then
  1 <= x < N, gcd(x, N) = 1, b_mid - b_lo = 4Gx, b_hi - b_lo = 4GN.  H_w = [w, w + 1/2] (mod 1) for a quarter point w
  (a multiple of 1/4) is an aligned closed half circle.

LEMMA ROT (identity; mixed_lemma_check_v1).  For 4 | c and K an integer, tau -> tau + K/4 leaves c tau (mod 1)
  unchanged (cK/4 = mK) and moves every b tau by K/4 (mod 1) (bK/4 = K/4 + K(b - 1)/4).

THE REDUCTION (re-derived).  For 4 | c, M(1,3) holds iff some tau0 has ||c tau0|| >= 1/8 and b_lo tau0, b_mid tau0,
  b_hi tau0 all in one H_w.  If tau works, each b_j tau lies in [1/4, 3/4] = H_{1/4}.  Conversely, given tau0 and w,
  put K = (1 - 4w) mod 4 and tau = tau0 + K/4.  By ROT, c tau = c tau0 (mod 1) and b_j tau = b_j tau0 + K/4 lies in
  H_{w + K/4} = H_{1/4} (mod 1), so ||u_j tau|| = ||b_j tau|| >= 1/4.  With y = c tau0 the points are (b_j/c) y and
  w = v + 1/4 for the quarter point v of mixed_lemma_check_v1's form: ||(b_j/c) y - v|| >= 1/4 for j = 1, 2, 3.
  The equivalence holds pointwise (for each tau0: some K gives a solution iff the points lie in one H_w); it is
  checked below on every class-R case at every real tau0 (see CHECK 2).

LEMMA QP.  For a real p, the quarter point w = floor(4p)/4 satisfies w <= p < w + 1/4.  Hence
  (i)  every point of the closed arc [p, p + 1/4] lies in H_w;
  (ii) p and p + 1/3 both lie in H_w when 4p - floor(4p) <= 2/3 (then p - w <= 1/6).
  [PROVISIONAL: counting tool; supports: the half circle H_w in parts S, T, Phi and P]
  QP is the floor function.  It carries the tag because E404 tags FIT2, whose content (an interval of length 1/4
  against the quarter points) is the same.

PROOF.  In parts S, T, Phi, P: tau0 as stated; p = b_lo tau0; w from QP; K and tau as in THE REDUCTION.
 a    4 does not divide c.  tau = 1/4: ||c/4|| is 1/4 (c odd) or 1/2 (c = 2 mod 4); ||u/4|| = 1/4 (u odd).
 S    4 | c and b_hi - b_lo <= 2c.  tau0 = 1/(8c), so c tau0 = 1/8.  The reals b_j/(8c) lie in
      [p, p + (b_hi - b_lo)/(8c)], inside [p, p + 1/4]; QP(i).
 T    4 | c, b_hi - b_lo > 2c, and G does not divide m.  h = gcd(G, m), q = G/h >= 2, m'' = m/h (a unit mod q).
      k = floor(q/2) * m''^(-1) mod q, tau0 = k/(4G).  c tau0 = m'' k/q = floor(q/2)/q (mod 1), and
      floor(q/2)/q lies in [1/3, 1/2] for q >= 2, so ||c tau0|| >= 1/3.  (b_j - b_lo) tau0 = (a_j - a_lo) k/G is an
      integer: the three points coincide at p; QP(i).
      Otherwise G | m.  Put n = m/G.  b_hi - b_lo = 4GN > 2c = 8Gn gives N > 2n >= 2.
 Phi  N = 3 and n = 1 (so G = m and x is 1 or 2).  w0 = x/3, tau0 = (w0 + k)/c with k below; c tau0 = w0 + k, so
      ||c tau0|| = 1/3.  b_j - b_lo = 4G M_j = c M_j with M_j = 0, x, 3 for lo, mid, hi, so (b_j - b_lo) tau0 =
      M_j (w0 + k): hi coincides with lo (3 w0 = x), and mid is at p + x w0 = p + x^2/3 = p + 1/3 (mod 1).
      Choice of k: h = gcd(b_lo, m), b' = b_lo/h, m' = m/h (b' a unit mod m'), k = -floor(b' w0) * b'^(-1) mod m'
      (k = 0 if m' = 1).  Then 4p = b'(w0 + k)/m' = {b' w0}/m' (mod 1), because b'w0 + b'k = {b'w0} + (floor(b'w0) +
      b'k) and the bracket is 0 mod m'.  {b' w0} is 0, 1/3 or 2/3, so 4p - floor(4p) <= 2/3; QP(ii).
 P    N > 2n and (N, n) is not (3, 1); then N >= 4 (N = 3 > 2n forces n = 1).  tau0 = k/(4GN), k below.
      (b_hi - b_lo) tau0 = k: hi coincides with lo.  (b_mid - b_lo) tau0 = xk/N.  c tau0 = 4Gn k/(4GN) = nk/N.
      xbar = x^(-1) mod N; nu = n xbar mod N, nu* its representative in (-N/2, N/2], r = |nu*|/N = ||nu/N||.
      nu is not 0 mod N (xbar is a unit and N > n >= 1 so N does not divide n), so r >= 1/N.
      j = 1 if r >= 1/8.  Otherwise j = ceil(1/(8r)); then jr lies in [1/8, 1/8 + r), inside [1/8, 1/4); and
      r < 1/8 with r >= 1/N forces N >= 9, so j < N/8 + 1 <= N/4.
      [PROVISIONAL: counting tool; supports: the choice of j in part P (multiples of r against the arc [1/8, 1/4),
      the step E404 tags in DE3)]
      k = xbar j mod N.  Then xk = j (mod N), so mid is at p + j/N with 1 <= j <= N/4; and nk = nu j (mod N), so
      ||c tau0|| = ||nu* j/N|| = jr >= 1/8 (jr <= 1/4 < 1/2).  The three points lie in [p, p + 1/4]; QP(i).
 Exhaustive: 4 does not divide c (a); else b_hi - b_lo <= 2c (S); else G does not divide m (T); else G | m with
 N > 2n, and either (N, n) = (3, 1) (Phi) or not (P).  M(1,3) holds for every c >= 1 and every triple.  QED, with
 the two tags.

REMARK (mixed_lemma_check_v1's class R lies in Phi; not used in the proof).  Class R needs 4 | c, not e and not f.
  S implies e (e tests the fit at tau0 = 1/(8c), which S proves), so class R is not in S.  For a pair with difference
  A = G M (M one of x, N - x, N), the case-f inequality of mixed_lemma_check_v1, with its counts (gcd(d, D) = 4G,
  gcd(c, d) = 4 gcd(A, m)), reads phi1(M) > phi2(M'), phi1(M) = (2 floor(M/4) + 1)/M, phi2(M') = (2 ceil(M'/8) - 1)/M',
  M' = A/gcd(A, m).  phi1 >= 1/3, with equality only at M = 3; phi2(M') <= 1/3 for M' >= 3, with equality only at
  M' = 3, 9.  So "not f" at a pair forces M' in {1, 2, 3, 9}; M' in {3, 9} forces M = 3; M' = 2 forces M = 2 or 3
  (mod 4) and v2(A) = v2(m) + 1.  If no pair had M' = 1, at least two pairs would have M' = 2 (at most one M is 3;
  x = N - x = 1 gives two pairs with M = 1, which need M' = 1); their M's have equal 2-adic valuation, so both are odd,
  and the third M (even, since one of x, N - x, N is even) fits neither M' = 2 nor M = 3.  So some A divides m, hence
  G | m.  The extreme pair then has M' = N/gcd(N, n) >= 3 (N > 2n because R is not in S), so M' is 3 or 9, N = 3,
  M' = 3, and n = 1: part Phi.
  [PROVISIONAL: counting tool; supports: the remark only (it reads the residue counts of case f)]

CHECKS (this script; integer and Fraction arithmetic).
 1. Range A (required): every c in [1, 48] and every triple of distinct odd u in [1, 79].  Each part's tau is
    constructed as named above, its intermediate claims are tested, and the final tau is tested twice (Fraction
    distance and integer residues).  Reported: cases per part, failing tau, failing intermediate claims.
    Cross-table against mixed_lemma_check_v1.construct13 (imported unchanged), and the remark's inclusions.
 2. The reduction on class R: for each class-R case and every tau0 in [0, 1), "some K in 0..3 makes tau0 + K/4 a
    solution" agrees with "||c tau0|| >= 1/8 and the three b_j tau0 lie in one H_w".  Both predicates are constant
    between consecutive points of E = {8c tau0 in Z} u {4u_j tau0 in Z}: ||c tau|| crosses 1/8 only where 8c tau is an
    integer, ||u(tau + K/4)|| crosses 1/4 only where 4u tau is an integer, and b_j tau meets a quarter point only
    where 4u_j tau is an integer.  So testing every point of E and every midpoint between neighbours in E tests every
    real tau0.
 3. Range B: every c in [1, CB] and every triple of distinct odd u in [1, UB] (defaults 128, 159).
 4. Large values, Phi: m in [1, 100], x in {1, 2}, b_lo = 1 + 4t for t in [-400, 400]; u's = |b_lo|, |b_lo + xc|,
    |b_lo + 3c| (Phi's b-sets).  Large values, window: c = 4m for m in [1, 16], odd u in [999001, 999099], all
    triples, and triples with u1 odd in [1, 39] and u2 < u3 in that window.
 5. Firing control: the opposite rotation tau0 + (K + 2)/4 is tested on Range A; the checker must reject it in the
    cases where some point lies strictly inside H_w.
"""
import itertools, math, os, sys, time, collections
from fractions import Fraction as F
from math import gcd, floor

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
_argv = sys.argv
sys.argv = [_argv[0], '40']
from mixed_lemma_check_v1 import construct13, fits as old_fits, cnt_close, cnt_near
sys.argv = _argv

CB = int(sys.argv[1]) if len(sys.argv) > 1 else 128
UB = int(sys.argv[2]) if len(sys.argv) > 2 else 159


def b_of(u):
    return u if u % 4 == 1 else -u


def dist(x):
    x = x - math.floor(x)
    return min(x, 1 - x)


def good_frac(c, U, t):
    return dist(c * t) >= F(1, 8) and all(dist(u * t) >= F(1, 4) for u in U)


def good_int(c, U, t):
    p, q = t.numerator, t.denominator
    r = (c * p) % q
    if not (8 * r >= q and 8 * r <= 7 * q):
        return False
    for u in U:
        r = (u * p) % q
        if not (4 * r >= q and 4 * r <= 3 * q):
            return False
    return True


def in_H(x, w):
    """x in [w, w + 1/2] mod 1."""
    return (x - w) % 1 <= F(1, 2)


def frac(x):
    return x - math.floor(x)


def construct(c, U):
    """Return (part, tau0, tau, claims) where claims is the list of (name, bool) intermediate claims."""
    if c % 4:
        return 'a', None, F(1, 4), []
    m = c // 4
    B = sorted(b_of(u) for u in U)
    blo, bmid, bhi = B
    A = [(b - 1) // 4 for b in B]
    G = gcd(A[1] - A[0], A[2] - A[1])
    x = (A[1] - A[0]) // G
    N = (A[2] - A[0]) // G
    cl = []
    if bhi - blo <= 2 * c:
        part = 'S'
        tau0 = F(1, 8 * c)
        cl.append(('S: c tau0 = 1/8', frac(c * tau0) == F(1, 8)))
        cl.append(('S: span <= 1/4', F(bhi - blo, 8 * c) <= F(1, 4)))
    elif m % G:
        part = 'T'
        h = gcd(G, m); q = G // h; mm = m // h
        k = ((q // 2) * pow(mm, -1, q)) % q
        tau0 = F(k, 4 * G)
        cl.append(('T: q >= 2', q >= 2))
        cl.append(('T: c tau0 = floor(q/2)/q', frac(c * tau0) == F(q // 2, q)))
        cl.append(('T: ||c tau0|| >= 1/3', dist(c * tau0) >= F(1, 3)))
        cl.append(('T: points coincide', all(((b - blo) * tau0).denominator == 1 for b in B)))
    else:
        n = m // G
        cl.append(('G|m: N > 2n', N > 2 * n))
        if (N, n) == (3, 1):
            part = 'Phi'
            w0 = F(x, 3)
            h = gcd(abs(blo), m); bp = blo // h; mp = m // h
            k = (-math.floor(bp * w0) * pow(bp, -1, mp)) % mp if mp > 1 else 0
            tau0 = (w0 + k) / c
            p = blo * tau0
            cl.append(('Phi: x in {1,2}', x in (1, 2)))
            cl.append(('Phi: ||c tau0|| = 1/3', dist(c * tau0) == F(1, 3)))
            cl.append(('Phi: hi coincides with lo', ((bhi - blo) * tau0).denominator == 1))
            cl.append(('Phi: mid = lo + 1/3', frac((bmid - blo) * tau0) == F(1, 3)))
            cl.append(('Phi: {4p} = {b w0}/m\'', frac(4 * p) == frac(bp * w0) / mp))
            cl.append(('Phi: {4p} <= 2/3', frac(4 * p) <= F(2, 3)))
        else:
            part = 'P'
            xb = pow(x, -1, N)
            nu = (n * xb) % N
            nus = nu if 2 * nu <= N else nu - N
            r = F(abs(nus), N)
            if r >= F(1, 8):
                j = 1
            else:
                j = -(-N // (8 * abs(nus)))   # ceil(1/(8r)) = ceil(N/(8|nu*|))
            k = (xb * j) % N
            tau0 = F(k, 4 * G * N)
            cl.append(('P: N >= 4', N >= 4))
            cl.append(('P: nu != 0', nu != 0))
            cl.append(('P: 1 <= j <= N/4', 1 <= j and 4 * j <= N))
            cl.append(('P: j r in [1/8, 1/4] when j > 1', j == 1 or (F(1, 8) <= j * r <= F(1, 4))))
            cl.append(('P: hi coincides with lo', ((bhi - blo) * tau0).denominator == 1))
            cl.append(('P: mid = lo + j/N', frac((bmid - blo) * tau0) == F(j, N)))
            cl.append(('P: ||c tau0|| >= 1/8', dist(c * tau0) >= F(1, 8)))
    p = blo * tau0
    w = F(math.floor(4 * p), 4)
    cl.append(('QP: w <= p < w + 1/4', w <= p < w + F(1, 4)))
    cl.append(('all points in H_w', all(in_H(b * tau0, w) for b in B)))
    cl.append(('||c tau0|| >= 1/8', dist(c * tau0) >= F(1, 8)))
    K = int((1 - 4 * w) % 4)
    tau = tau0 + F(K, 4)
    return part, (tau0, w, K), tau, cl


def run(cases, tally, fails, clfails, label, control=None):
    n = 0
    for c, U in cases:
        n += 1
        part, info, tau, cl = construct(c, U)
        tally[part] += 1
        g1 = good_frac(c, U, tau); g2 = good_int(c, U, tau)
        if not (g1 and g2):
            fails.append((label, part, c, U, tau, g1, g2))
        for name, ok in cl:
            if not ok:
                clfails[name] += 1
                if clfails[name] <= 3:
                    fails.append((label, 'claim', name, c, U))
        if control is not None and info is not None:
            tau0, w, K = info
            B = [b_of(u) for u in U]
            interior = any(F(0) < (b * tau0 - w) % 1 < F(1, 2) for b in B)
            opp = tau0 + F((K + 2) % 4, 4)
            rej = not good_frac(c, U, opp)
            control['tested'] += 1
            control['interior'] += interior
            control['rejected'] += rej
            control['interior_and_rejected'] += interior and rej
    return n


def reduction_check(c, U):
    """Exact check of the reduction at every real tau0 in [0,1) (breakpoints and midpoints)."""
    B = [b_of(u) for u in U]
    L = 2 * math.lcm(8 * c, *[4 * u for u in U])
    E = set(t * (L // (8 * c)) for t in range(8 * c))
    for u in U:
        E |= set(t * (L // (4 * u)) for t in range(4 * u))
    E = sorted(E)
    pts = list(E) + [(E[i] + E[i + 1]) // 2 for i in range(len(E) - 1)] + [((E[-1] + L + E[0]) // 2) % L]
    q4 = L // 4; q2 = L // 2
    mism = 0; nonempty = 0
    for t in pts:
        lhs = False
        for K in range(4):
            tt = t + K * q4
            r = (c * tt) % L
            if not (8 * r >= L and 8 * r <= 7 * L):
                continue
            if all(L <= 4 * ((u * tt) % L) <= 3 * L for u in U):
                lhs = True
                break
        r = (c * t) % L
        rhs = (8 * r >= L and 8 * r <= 7 * L) and any(
            all(((b * t - nn * q4) % L) <= q2 for b in B) for nn in range(4))
        if lhs != rhs:
            mism += 1
        nonempty += lhs
    return len(pts), mism, nonempty


if __name__ == '__main__':
    out = open(os.path.join(HERE, 'm13_proof_v1.out'), 'w')

    def W(s=""):
        out.write(s + "\n"); out.flush(); print(s)
    W(__doc__)
    TOT = collections.Counter()

    def report(fails, clf):
        nf = sum(1 for f in fails if f[1] != 'claim')
        W("  constructed tau fails (Fraction or integer test): %d %s" % (nf, [f for f in fails if f[1] != 'claim'][:10]))
        W("  intermediate claims failing: %d %s" % (sum(clf.values()), dict(clf)))
        TOT['tau fails'] += nf
        TOT['claim fails'] += sum(clf.values())
    T0 = time.time()

    # ---------- CHECK 1: Range A ----------
    CA, UA = 48, 79
    oddsA = [u for u in range(1, UA + 1) if u % 2]
    casesA = [(c, U) for c in range(1, CA + 1) for U in itertools.combinations(oddsA, 3)]
    tally = collections.Counter(); fails = []; clf = collections.Counter()
    ctrl = collections.Counter()
    nA = run(casesA, tally, fails, clf, 'A', control=ctrl)
    W("== CHECK 1: Range A, c in [1, %d], distinct odd u in [1, %d]: %d cases ==" % (CA, UA, nA))
    for k in ('a', 'S', 'T', 'Phi', 'P'):
        W("  part %-4s %7d cases" % (k, tally[k]))
    report(fails, clf)
    # cross-table against the old classifier, and the remark
    xt = collections.Counter(); oldR = []; rem_viol = collections.Counter()
    for c, U in casesA:
        old, _ = construct13(c, U)
        new = construct(c, U)[0]
        xt[(old, new)] += 1
        if old == 'R':
            oldR.append((c, U, new))
        if c % 4 == 0:
            m = c // 4
            B = sorted(b_of(u) for u in U)
            A = [(b - 1) // 4 for b in B]
            G = gcd(A[1] - A[0], A[2] - A[1]); N = (A[2] - A[0]) // G
            notf = all(cnt_close(abs(B[l] - B[i]), abs(B[i] - B[j])) <= cnt_near(c, abs(B[i] - B[j]))
                       for i, j, l in ((0, 1, 2), (0, 2, 1), (1, 2, 0)))
            S = B[2] - B[0] <= 2 * c
            if S and not old_fits([F(b, 8 * c) for b in B]):
                rem_viol['S but no fit at 1/(8c)'] += 1
            if notf and m % G:
                rem_viol['not f but G does not divide m'] += 1
            if notf and not S and new != 'Phi':
                rem_viol['not f, not S, but not Phi'] += 1
            rem_viol['(tested 4|c cases)'] += 1
            rem_viol['(not f)'] += notf
    W("  cross-table, old construct13 label -> new part (counts):")
    for old in ('a', 'b', 'e', 'c', 'f', 'R'):
        row = ["%s %d" % (new, xt[(old, new)]) for new in ('a', 'S', 'T', 'Phi', 'P') if xt[(old, new)]]
        W("    old %-2s : %s" % (old, ", ".join(row)))
    W("  old class R: %d cases, in part Phi: %d" % (len(oldR), sum(1 for r in oldR if r[2] == 'Phi')))
    W("  remark, on the %d cases of Range A with 4 | c (%d of them not f): S without the fit at 1/(8c) %d;"
      % (rem_viol['(tested 4|c cases)'], rem_viol['(not f)'], rem_viol['S but no fit at 1/(8c)']))
    W("    not f with G not dividing m %d; not f and not S outside Phi %d" % (
        rem_viol['not f but G does not divide m'], rem_viol['not f, not S, but not Phi']))
    W("  CHECK 5 (firing control, Range A, parts S/T/Phi/P): opposite rotation tau0 + (K+2)/4 tested %d; some point"
      % ctrl['tested'])
    W("    strictly inside H_w %d; rejected by the checker %d; inside and rejected %d" % (
        ctrl['interior'], ctrl['rejected'], ctrl['interior_and_rejected']))
    W("  [%.1fs]" % (time.time() - T0))

    # ---------- CHECK 2: the reduction on class R ----------
    W("")
    W("== CHECK 2: the reduction, pointwise at every real tau0 in [0,1), on old class R of Range A ==")
    tp = 0; tm = 0; ne = 0
    for c, U, _ in oldR:
        a1, a2, a3 = reduction_check(c, U)
        tp += a1; tm += a2; ne += (a3 > 0)
    W("  class-R cases %d; points tested %d; points where the two sides disagree %d; cases with a solution %d" % (
        len(oldR), tp, tm, ne))
    W("  [%.1fs]" % (time.time() - T0))

    # ---------- CHECK 3: Range B ----------
    W("")
    oddsB = [u for u in range(1, UB + 1) if u % 2]
    tally = collections.Counter(); fails = []; clf = collections.Counter()
    gen = ((c, U) for c in range(1, CB + 1) for U in itertools.combinations(oddsB, 3))
    nB = run(gen, tally, fails, clf, 'B')
    W("== CHECK 3: Range B, c in [1, %d], distinct odd u in [1, %d]: %d cases ==" % (CB, UB, nB))
    for k in ('a', 'S', 'T', 'Phi', 'P'):
        W("  part %-4s %8d cases" % (k, tally[k]))
    report(fails, clf)
    W("  [%.1fs]" % (time.time() - T0))

    # ---------- CHECK 4: large values ----------
    W("")
    tally = collections.Counter(); fails = []; clf = collections.Counter()
    def phi_cases():
        for m in range(1, 101):
            c = 4 * m
            for x in (1, 2):
                for t in range(-400, 401):
                    blo = 1 + 4 * t
                    U = tuple(sorted(abs(b) for b in (blo, blo + x * c, blo + 3 * c)))
                    yield c, U
    nP = run(phi_cases(), tally, fails, clf, 'Phi-family')
    W("== CHECK 4a: Phi b-sets {b, b + xc, b + 3c}, m in [1, 100], x in {1, 2}, b = 1 + 4t, t in [-400, 400]: %d cases =="
      % nP)
    for k in ('a', 'S', 'T', 'Phi', 'P'):
        if tally[k]: W("  part %-4s %8d cases" % (k, tally[k]))
    report(fails, clf)
    tally = collections.Counter(); fails = []; clf = collections.Counter()
    win = [u for u in range(999001, 999100) if u % 2]
    small = [u for u in range(1, 40) if u % 2]
    def win_cases():
        for m in range(1, 17):
            c = 4 * m
            for U in itertools.combinations(win, 3):
                yield c, U
            for u1 in small:
                for u2, u3 in itertools.combinations(win, 2):
                    yield c, (u1, u2, u3)
    nW = run(win_cases(), tally, fails, clf, 'window')
    W("== CHECK 4b: c = 4m, m in [1, 16]; odd u in [999001, 999099] (all triples) and u1 odd in [1, 39] with two"
      " from the window: %d cases ==" % nW)
    for k in ('a', 'S', 'T', 'Phi', 'P'):
        if tally[k]: W("  part %-4s %8d cases" % (k, tally[k]))
    report(fails, clf)
    W("  [%.1fs]" % (time.time() - T0))
    W("")
    W("TOTAL constructed and checked: %d cases (Range A %d, Range B %d, Phi family %d, window %d)." % (
        nA + nB + nP + nW, nA, nB, nP, nW))
    W("TOTAL failing constructed tau: %d; failing intermediate claims: %d." % (TOT['tau fails'], TOT['claim fails']))
    out.close()
