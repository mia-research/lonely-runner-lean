#!/usr/bin/env python3
"""
newtypes_membership_v1.py -- exact-Fraction membership tests for the 21 disjuncts of
Fresh.ArrangementTypesOct26.NewTypes (LonelyRunnerFresh/Fresh/ArrangementTypesOct26.lean 110-131).

No floating point.  Every comparison is on fractions.Fraction.  No Lean file is read or written here.

Inputs
  S  : 7 distinct positive whole-number readings (disparities of the subject from the other seven runners).
  T  : the 8-point arrangement {0} u {d : d in S}  (subject at 0, i.e. the lowest speed; translation is
       immaterial to every class tested, B is a free real in each v-class).
  "literal" mode  = exactly the arrangement the brief specifies (subject at the bottom).
  "sign-free" mode (supplementary) = exists a choice of signs eps_i with arrangement {0} u {eps_i d_i};
       the readings alone do not fix which side of the subject each runner is on.

Result of a test is (status, message) with status True (member), False (not member), 'N' (the
necessary part passes; membership is not decided).  On False the message is the first defining conjunct
(in the order the Lean definition lists them) that fails for the furthest-progressing candidate witness.
"""
import sys, itertools, math
from fractions import Fraction as F
from math import gcd

# ----------------------------------------------------------------------------------------------
# helpers
# ----------------------------------------------------------------------------------------------
def fl(x):            # floor of a Fraction
    return x.numerator // x.denominator
def ce(x):
    return -((-x.numerator) // x.denominator)
def mod8(x):
    return x - 8 * fl(x / 8)
def modn(x, n):
    return x - n * fl(x / n)
def lcm_den(*xs):
    L = 1
    for x in xs:
        L = L * x.denominator // gcd(L, x.denominator)
    return L
def rnd(x):           # nearest integer (distInt is insensitive to the half-integer tie rule)
    return fl(x + F(1, 2))
def distint(x):
    r = x - fl(x)
    return min(r, 1 - r)

class Prog:
    def __init__(s):
        s.r = -1
        s.m = 'no candidate decomposition of the required shape exists'
    def f(s, r, m):
        if r > s.r:
            s.r = r
            s.m = m

def ap_step(lst):
    """lst sorted ascending, len>=2 -> common difference or None; len==1 -> 'any'."""
    if len(lst) == 1:
        return 'any'
    d = lst[1] - lst[0]
    for i in range(1, len(lst) - 1):
        if lst[i + 1] - lst[i] != d:
            return None
    return d

def mirror(T):
    return [-t for t in reversed(T)]

def orients(T, pos=None):
    yield T, pos
    yield mirror(T), (None if pos is None else 7 - pos)

def compositions(n, k):
    """positive compositions of n into k parts."""
    if k == 1:
        yield (n,)
        return
    for a in range(1, n - k + 2):
        for rest in compositions(n - a, k - 1):
            yield (a,) + rest

def blocks_of(T, sizes):
    out = []
    i = 0
    for s in sizes:
        out.append(T[i:i + s])
        i += s
    return out

def block_structure(T, sizes):
    """T sorted ascending (8 points).  Split contiguously into blocks of the given sizes; every block of size>=2
    must be an AP, all with one common step z.  Returns (z, gaps) with gaps in units of z, or None."""
    bl = blocks_of(T, sizes)
    z = None
    for b in bl:
        st = ap_step(b)
        if st is None:
            return None
        if st != 'any':
            if z is None:
                z = st
            elif z != st:
                return None
    if z is None:
        return None
    gaps = [(bl[i + 1][0] - bl[i][-1]) / z for i in range(len(bl) - 1)]
    return z, gaps

def band4(g, h, j):
    """exists m>=1, integers a,b,e with 8a+1<=G g, 8b+1<=G h, 8e+1<=G j, G(g+h+j)<=8(a+b+e)+4, G=8m+1.
    Equivalent (maximal a,b,e): sum of ((G x - 1) mod 8) <= 1.  Periodic in m with period lcm(den)."""
    P = lcm_den(g, h, j)
    for m in range(1, P + 1):
        G = 8 * m + 1
        if sum(mod8(G * x - 1) for x in (g, h, j)) <= 1:
            return m
    return None

def band3rev(g, h):
    """exists m>=1, ints a,b: (8m-1)g<=8a-1, (8m-1)h<=8b-1, 8(a+b)-3<=(8m-1)(g+h).
    Minimal a,b: delta_x=(-1-Fx) mod 8; condition delta_g+delta_h<=1."""
    P = lcm_den(g, h)
    for m in range(1, P + 1):
        Fm = 8 * m - 1
        if mod8(-1 - Fm * g) + mod8(-1 - Fm * h) <= 1:
            return m
    return None

def m_candidates(g):
    """integers m>=1 with 1 < (8m+1) g and (8m-1) g < 1."""
    out = []
    if g <= 0:
        return out
    hi = int(1 / g / 8) + 3
    for m in range(1, hi + 1):
        G = 8 * m + 1
        if G * g > 1 and (G - 2) * g < 1:
            out.append(m)
    return out

# ----------------------------------------------------------------------------------------------
# 01 APCoreOpeningClass  (v,k ; reads disparitySet only)
# ----------------------------------------------------------------------------------------------
def t_apcore(S):
    """exists r in 1..6, u,x>0, w>=0, C finite : C in [x,x+w]; 8 r u <= x(7-r); w(1/(8u)+1/x)<=3/4;
    every reading is j u (1<=j<=r) or lies in C.
    Reduction: C = readings that are not j*u (enlarging C only widens [x,x+w]); x = min C, w = max C - min C is
    optimal (both inequalities are monotone in x up and w down).  u is either d/j for a reading d (some reading
    is j u) or free (no reading is j u), in which case 8ru<=x(7-r) is taken with equality (monotone in u).
    EXACT."""
    S = sorted(F(d) for d in S)
    P = Prog()
    for r in range(1, 7):
        cands = set()
        for d in S:
            for j in range(1, r + 1):
                cands.add(d / j)
        for u in cands:
            A = [d for d in S if (d / u).denominator == 1 and 1 <= d / u <= r]
            L = [d for d in S if d not in A]
            if not L:
                return True, 'r=%d u=%s, all readings j*u, C empty' % (r, u)
            x, w = L[0], L[-1] - L[0]
            if not (8 * r * u <= x * (7 - r)):
                P.f(0, 'conjunct 8*r*u <= x*(7-r) fails at best candidate (r=%d,u=%s,x=%s)' % (r, u, x)); continue
            if not (w * (1 / (8 * u) + 1 / x) <= F(3, 4)):
                P.f(1, 'conjunct w*(1/(8u)+1/x) <= 3/4 fails at best candidate (r=%d,u=%s,x=%s,w=%s)' % (r, u, x, w)); continue
            return True, 'r=%d u=%s x=%s w=%s' % (r, u, x, w)
        # no reading of the form j*u : all readings in C
        x, w = S[0], S[-1] - S[0]
        u = x * (7 - r) / (8 * r)
        if w * (1 / (8 * u) + 1 / x) <= F(3, 4):
            return True, 'r=%d, C = all seven readings, u=%s' % (r, u)
        P.f(1, 'conjunct w*(1/(8u)+1/x) <= 3/4 fails when all readings are in C (r=%d)' % r)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 02 SplitAPReadingsClass
# ----------------------------------------------------------------------------------------------
def t_splitap(S):
    """exists r in 1..5, s>0, a>0 with every reading in s*splitTrain r a; splitTrain r a = {1..r} u {a, a+1, .., a+6-r}.
    Seven distinct readings force |splitTrain|=7 and D = s*splitTrain.  s is a reading (q=1).  Remaining readings/s
    must be exactly an AP of step 1 (a = its minimum).  EXACT."""
    S = sorted(F(d) for d in S)
    P = Prog()
    for r in range(1, 6):
        for s in S:
            Q = sorted(d / s for d in S)
            if not all(F(i) in Q for i in range(1, r + 1)):
                P.f(0, 'conjunct "readings contain s*{1..r}" fails (no s,r with 1..r among readings/s)'); continue
            R = [q for q in Q if not (q.denominator == 1 and 1 <= q <= r)]
            ok = all(R[i + 1] - R[i] == 1 for i in range(len(R) - 1))
            if not ok:
                P.f(1, 'conjunct "remaining readings/s form an AP of step 1" fails'); continue
            return True, 'r=%d s=%s a=%s' % (r, s, R[0])
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 03 SignedAPReadingsClass
# ----------------------------------------------------------------------------------------------
def runs(lst):
    return all(lst[i + 1] - lst[i] == 1 for i in range(len(lst) - 1))

def t_signed(S):
    """exists r in 1..5, s>0, B non-integer: every reading in s*|splitTrain r B|.  Seven distinct readings force the
    seven |q| to be distinct, and 1..r among them.  Rest R (= |B+j|, j=0..6-r) is non-integer and is
    (i) one AP of step 1 (all B+j same sign), or (ii) split N u P, N = {alpha+i}, P = {(1-alpha)+i}, alpha in (0,1)
    (B+j negative for the first |N| indices).  EXACT."""
    S = sorted(F(d) for d in S)
    P = Prog()
    for r in range(1, 6):
        for s in S:
            Q = sorted(d / s for d in S)
            if not all(F(i) in Q for i in range(1, r + 1)):
                P.f(0, 'conjunct "readings contain s*|q| for q=1..r" fails'); continue
            R = [q for q in Q if not (q.denominator == 1 and 1 <= q <= r)]
            if any(q.denominator == 1 for q in R):
                P.f(1, 'conjunct "B non-integer" fails (remaining |B+j| contains an integer)'); continue
            if runs(R):
                return True, 'r=%d s=%s B=%s (single sign)' % (r, s, R[0])
            m = len(R)
            for mask in range(1, 2 ** m - 1):
                N = [R[i] for i in range(m) if mask >> i & 1]
                Pp = [R[i] for i in range(m) if not mask >> i & 1]
                if runs(N) and runs(Pp) and 0 < N[0] < 1 and 0 < Pp[0] < 1 and N[0] + Pp[0] == 1:
                    return True, 'r=%d s=%s alpha=%s (B straddles 0)' % (r, s, N[0])
            P.f(2, 'conjunct "remaining |B+j| = one AP of step 1, or two AP runs with minima alpha, 1-alpha" fails')
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 04 GeneralTwoAPBlockClass   (v only)
# ----------------------------------------------------------------------------------------------
def t_general2ap(T):
    """v = B + s*speeds c A p (sigma i), 1<=p<=7, s!=0, speeds injective: two AP blocks of the SAME step
    (p and 8-p elements, any real offset A, interleaving allowed; a singleton imposes no step).
    Test: partition of the 8 points into two nonempty sets, each an AP with one common step.  EXACT."""
    T = sorted(T)
    P = Prog()
    n = 8
    for mask in range(1, 2 ** n - 1):
        if mask & 1 == 0:
            continue                    # block containing the smallest point is listed first
        X = [T[i] for i in range(n) if mask >> i & 1]
        Y = [T[i] for i in range(n) if not mask >> i & 1]
        sx, sy = ap_step(X), ap_step(Y)
        if sx is None or sy is None:
            P.f(0, 'conjunct "both blocks are APs" fails for every split')
            continue
        if sx != 'any' and sy != 'any' and sx != sy:
            P.f(1, 'conjunct "common step" fails (both blocks are APs of different steps)')
            continue
        return True, 'blocks %s | %s' % ([str(x) for x in X], [str(y) for y in Y])
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 05 PairTrainOpeningClass
# ----------------------------------------------------------------------------------------------
def t_pair(S):
    """exists s,a,x,w,C,p,q (p,q naturals): D = {s,a} u C exactly; C in [x,x+w]; pairLeft+1/x<=pairRight;
    w(pairLeft+1/x)<=3/4, pairLeft=max((p+1/8)/s,(q+1/8)/a), pairRight=min((p+7/8)/s,(q+7/8)/a).
    s,a are readings (possibly equal), C = D \\ {s,a}, x = min C, w = max C - min C (monotone-optimal).
    Readings are integers, so t -> t+1 shifts (p,q) by (s,a) and leaves window length unchanged while raising
    pairLeft; the smallest pairLeft is in the first period, p in [0,s), q in [0,a).  EXACT."""
    S = sorted(F(d) for d in S)
    P = Prog()
    for s in S:
        for a in S:
            C = [d for d in S if d != s and d != a]
            x, w = C[0], C[-1] - C[0]
            for p in range(0, int(s)):
                for q in range(0, int(a)):
                    L = max((p + F(1, 8)) / s, (q + F(1, 8)) / a)
                    R = min((p + F(7, 8)) / s, (q + F(7, 8)) / a)
                    if not (L + 1 / x <= R):
                        P.f(0, 'conjunct pairLeft + 1/x <= pairRight fails (best window too short or empty)'); continue
                    if not (w * (L + 1 / x) <= F(3, 4)):
                        P.f(1, 'conjunct w*(pairLeft+1/x) <= 3/4 fails'); continue
                    return True, 's=%s a=%s p=%d q=%d x=%s w=%s' % (s, a, p, q, x, w)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 06 TwoSlowTrainClass
# ----------------------------------------------------------------------------------------------
def t_twoslow(S):
    """exists s,a,x,w,f:Fin 5->R,n,m naturals: D = {s,a} u range f (iff).  Seven distinct readings force s!=a and
    f a bijection onto the other five readings F.  Conditions on x: x<=sN<=7x; (8m+1)x<=aN<=(8m+7)x; x<=f_i<=x+w;
    wN<=6x, N=8n+1.  With w=maxF-x these give an interval for x:
       max(sN/7, aN/(8m+7), maxF*N/(N+6)) <= x <= min(sN, aN/(8m+1), minF).   EXACT (n,m bounded by the interval)."""
    S = sorted(F(d) for d in S)
    P = Prog()
    for s in S:
        for a in S:
            if s == a:
                continue
            Fv = [d for d in S if d != s and d != a]
            mn, mx = Fv[0], Fv[-1]
            nmax = int(6 * mn / (mx - mn) / 8) + 2
            for n in range(0, nmax + 1):
                N = 8 * n + 1
                if not (maxF_ok(mx, mn, N)):
                    P.f(0, 'conjunct w(8n+1)<=6x with x<=min F and w>=max F - x fails for every n (train too wide)'); continue
                mbound = int(7 * a / s) + 3
                for m in range(0, mbound + 1):
                    lo = max(s * N / 7, a * N / (8 * m + 7), mx * N / (N + 6))
                    hi = min(s * N, a * N / (8 * m + 1), mn)
                    if lo <= hi:
                        return True, 's=%s a=%s n=%d m=%d x in [%s,%s]' % (s, a, n, m, lo, hi)
                P.f(1, 'conjunct "x<=sN<=7x and (8m+1)x<=aN<=(8m+7)x for some x in the train interval" fails')
    return False, P.m

def maxF_ok(mx, mn, N):
    return mx * N / (N + 6) <= mn

# ----------------------------------------------------------------------------------------------
# two-block classes (07, 08a-d, 09a-b, 10, 11, 12)
# ----------------------------------------------------------------------------------------------
def two_block_options(T):
    """yield (nL, nU, p, u, v, G) for each contiguous split T=Lo|Up with both blocks APs of >=2 points.
    Orientation s>0: block1 = Lo (p=nL,u=stepLo,v=stepUp); s<0: block1 = Up (p=nU,u=stepUp,v=stepLo).
    G = min(Up) - max(Lo) is the gap A-(p-1)u of the Lean parametrisation in either orientation."""
    T = sorted(T)
    for nL in range(2, 7):
        Lo, Up = T[:nL], T[nL:]
        sL, sU = ap_step(Lo), ap_step(Up)
        if sL is None or sU is None:
            continue
        G = Up[0] - Lo[-1]
        yield nL, 8 - nL, nL, sL, sU, G
        yield nL, 8 - nL, 8 - nL, sU, sL, G

def run_two_block(T, conds, pre):
    """conds: list of (label, fn(p,u,v,G)->bool); pre: label, fn(p)->bool."""
    P = Prog()
    any_split = False
    for nL, nU, p, u, v, G in two_block_options(T):
        any_split = True
        if not pre[1](p):
            P.f(0, 'conjunct %s fails (block sizes %d|%d)' % (pre[0], nL, nU)); continue
        ok = True
        for i, (lab, fn) in enumerate(conds):
            if not fn(p, u, v, G):
                P.f(1 + i, 'conjunct %s fails (p=%d,u=%s,v=%s,G=%s)' % (lab, p, u, v, G)); ok = False; break
        if ok:
            return True, 'lower block %d pts, upper %d pts, p=%d u=%s v=%s gap G=%s' % (nL, nU, p, u, v, G)
    if not any_split:
        return False, 'no contiguous split into two APs each of >=2 points (first conjunct "V = B+s*speeds(sigma i)" fails)'
    return False, P.m

def t_unequal(T):
    conds = [
        ('0<A-(p-1)u', lambda p, u, v, G: G > 0),
        ('8(p-1)u <= G(8-p)', lambda p, u, v, G: 8 * (p - 1) * u <= G * (8 - p)),
        ('8(7-p)v <= G p', lambda p, u, v, G: 8 * (7 - p) * v <= G * p),
        ('(7-p)v(1/(8u)+1/G) <= 3/4', lambda p, u, v, G: (7 - p) * v * (1 / (8 * u) + 1 / G) <= F(3, 4)),
        ('(p-1)u(1/(8v)+1/G) <= 3/4', lambda p, u, v, G: (p - 1) * u * (1 / (8 * v) + 1 / G) <= F(3, 4)),
    ]
    return run_two_block(T, conds, ('2<=p<=6', lambda p: 2 <= p <= 6))

def t_mixed4_two(T):
    conds = [('b=2 (v=2u)', lambda p, u, v, G: v == 2 * u),
             ('51/4 <= A-3 (G >= 51u/4)', lambda p, u, v, G: G >= F(51, 4) * u)]
    return run_two_block(T, conds, ('p=4', lambda p: p == 4))

def t_mixed4_param(T):
    conds = [('2<=b (v>=2u)', lambda p, u, v, G: v >= 2 * u),
             ('0<A-3 and 9b^2<=(A-3)(8-3b) (9v^2 <= G(8u-3v))', lambda p, u, v, G: G > 0 and 9 * v * v <= G * (8 * u - 3 * v))]
    return run_two_block(T, conds, ('p=4', lambda p: p == 4))

def t_mixed4_lower(T):
    conds = [('8/7<=b<=2', lambda p, u, v, G: F(8, 7) * u <= v <= 2 * u),
             ('9b<=A-3 (9v<=G)', lambda p, u, v, G: 9 * v <= G)]
    return run_two_block(T, conds, ('p=4', lambda p: p == 4))

def t_uniform4(T):
    conds = [('21 max(1,b) <= A-3 (21 max(u,v) <= G)', lambda p, u, v, G: 21 * max(u, v) <= G)]
    return run_two_block(T, conds, ('p=4', lambda p: p == 4))

def t_middle5(T):
    conds = [('6/7<=b (v>=6u/7)', lambda p, u, v, G: 7 * v >= 6 * u),
             ('32b<=3(A-2) (32v<=3G)', lambda p, u, v, G: 32 * v <= 3 * G)]
    return run_two_block(T, conds, ('p=3', lambda p: p == 3))

def t_full35(T):
    conds = [('0<b and (32/3)max(1,b)<=A-2 ((32/3)max(u,v)<=G)', lambda p, u, v, G: F(32, 3) * max(u, v) <= G)]
    return run_two_block(T, conds, ('p=3', lambda p: p == 3))

def t_sep21(T):
    conds = [('21 max(1,b) <= A-(p-1) (21 max(u,v) <= G)', lambda p, u, v, G: 21 * max(u, v) <= G)]
    return run_two_block(T, conds, ('2<=p<=6', lambda p: 2 <= p <= 6))

def t_two69(T):
    conds = [('9 max(1,b) <= A-1 (9 max(u,v) <= G)', lambda p, u, v, G: 9 * max(u, v) <= G)]
    return run_two_block(T, conds, ('p=2 (speeds c A 1 b 2)', lambda p: p == 2))

def t_two6thin(T):
    conds = [('4<=3(A-1) (4u<=3G)', lambda p, u, v, G: 4 * u <= 3 * G),
             ('40b<=(A-1)(6-5b) (40uv <= G(6u-5v))', lambda p, u, v, G: 40 * u * v <= G * (6 * u - 5 * v))]
    return run_two_block(T, conds, ('p=2 (speeds c A 1 b 2)', lambda p: p == 2))

# ----------------------------------------------------------------------------------------------
# 13 DoubleCoveredClass   (v only)  -- NECESSARY ONLY, plus one exact leaf
# ----------------------------------------------------------------------------------------------
def four_block_splits(T):
    for sizes in compositions(8, 4):
        bs = block_structure(T, sizes)
        if bs is not None:
            yield sizes, bs[0], bs[1]

LAST = {}

def t_doublecovered(T):
    """DoubleCovered = MiddleCovered v DoubleSingleton; MiddleCovered = ShortOpeningCovered v MiddlePacket, and
    ShortOpeningCovered descends (ChartsCovered, APAnchorCovered, PacketFrameCovered, FiveReturnCovered,
    SingletonReturnCovered, FourReturnCovered, InnerCovered, ReturnCovered, PacketCovered) to FourBlockCovered =
    FourBlockClass v LongTailClass.  EVERY leaf has V = B+z*speeds c g h j p q r (sigma i) (FourBlockNeighbour.speeds:
    four unit-step AP blocks, gaps g,h,j>0), 1<=m, and 8a+1<=(8m+1)g, 8b+1<=(8m+1)h, 8e+1<=(8m+1)j,
    (8m+1)(g+h+j)<=8(a+b+e)+4.  Most leaves add an opening/chart certificate (opening, PacketBands, RemainingBands,
    EndpointData, FrameBands...) with free integers (rho, unitLap, window, L, role, u) that is NOT decided here.
    Test:  member  if the pure-inequality leaf FourBlockClass holds (exact: g+h+j<=3, p=1->1<=g, p+q+r=7->1<=j, bands);
           'N'     if only the necessary part holds (some 4-block split of T with the four band inequalities);
           False   otherwise (a necessary conjunct fails => not a member, exact)."""
    P = Prog()
    T = sorted(T)
    nec = None
    for TT, _ in orients(T):
        for sizes, z, gaps in four_block_splits(TT):
            g, h, j = gaps
            if g <= 0 or h <= 0 or j <= 0:
                P.f(0, 'conjunct 0<g,0<h,0<j fails'); continue
            m = band4(g, h, j)
            if m is None:
                P.f(1, 'conjunct bands 8a+1<=(8m+1)g, 8b+1<=(8m+1)h, 8e+1<=(8m+1)j, (8m+1)(g+h+j)<=8(a+b+e)+4 fails for every m>=1')
                continue
            if nec is None:
                nec = 'sizes %s gaps(g,h,j)=%s,%s,%s m=%d' % (sizes, g, h, j, m)
            p, q, r, s_ = sizes
            if g + h + j <= 3 and (p != 1 or g >= 1) and (s_ != 1 or j >= 1):
                LAST['13'] = (TT, sizes, z, g, h, j, m)
                return True, 'FourBlockClass leaf: sizes %s gaps %s,%s,%s m=%d' % (sizes, g, h, j, m)
            P.f(2, 'FourBlockClass leaf conjunct (g+h+j<=3, p=1->1<=g, last block singleton->1<=j) fails')
    if nec is not None:
        return 'N', 'necessary part holds (%s); leaf FourBlockClass fails; certificate leaves undecided' % nec
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 14 ThreeBlockReverseMiddlePartitionsClass   (v only)  EXACT
# ----------------------------------------------------------------------------------------------
def t_3block_rev(T):
    P = Prog()
    T = sorted(T)
    for TT, _ in orients(T):
        for p in range(2, 7):
            for q in range(1, 7 - p + 1):
                if p + q > 6:
                    continue
                sizes = (p, q, 8 - p - q)
                bs = block_structure(TT, sizes)
                if bs is None:
                    P.f(0, 'conjunct "V = B+z*speeds c g h p q": no split into 3 unit-step AP blocks with common step'); continue
                z, (g, h) = bs
                if not (g > 0 and h > 0 and g + h <= 2):
                    P.f(1, 'conjunct 0<g, 0<h, g+h<=2 fails (g=%s,h=%s)' % (g, h)); continue
                m = band3rev(g, h)
                if m is None:
                    P.f(2, 'conjunct (8m-1)g<=8a-1, (8m-1)h<=8b-1, 8(a+b)-3<=(8m-1)(g+h) fails for every m>=1'); continue
                LAST['14'] = (TT, sizes, z, g, h, m)
                return True, 'sizes %s g=%s h=%s m=%d' % (sizes, g, h, m)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 15 ThreeGapPacketClass (v,k ; only |V i - V k| enters)
# ----------------------------------------------------------------------------------------------
TYPES = [(D, e, f, l) for D in range(4) for e in (0, 1) for f in (0, 1) for l in (0, 1) if (D, e, f, l) != (0, 0, 0, 0)]

def _vals(u, G1, G2, G3):
    out = set()
    for D, e, f, l in TYPES:
        out.add(D * u + e * G1 + f * G2 + l * G3)
    return out

def bandN(xs):
    """bands for a list of used gap variables (unused gaps are free reals and can be given zero slack)."""
    if not xs:
        return 1
    P = lcm_den(*xs)
    for m in range(1, P + 1):
        G = 8 * m + 1
        if sum(mod8(G * x - 1) for x in xs) <= 1:
            return m
    return None

def t_threegap(S):
    """exists u,g,h,j>0, m>=1, a,b,c: bands (same four inequalities as FourBlock) and for each reading
    d = u(D + e g + f h + l j), D<=3, e,f,l in {0,1}, not all zero.  Unknown vector X=(u, ug, uh, uj); each reading
    gives one linear equation in X.  Depth-first assignment of types (the used variables g,h,j form a prefix, which
    removes the g,h,j symmetry of the class), incremental Gaussian elimination, prune on inconsistency.
    Full rank on the used variables: X unique on them -> check positivity and the bands for the used gaps (a gap that
    no reading uses is a free positive real and takes zero band slack).  EXACT on that branch.
    Rank deficient on the used variables (free parameters): bands are linear in X for fixed integers but the integers
    are unbounded; such branches are only recorded and make the answer 'N' (necessary), never a False."""
    S = sorted(F(d) for d in S)
    P = Prog()
    under = []
    found = []

    def solve(rows, ncol):
        X = [F(0)] * 4
        for pv, rv, rhs in reversed(rows):
            X[pv] = rhs - sum(rv[c] * X[c] for c in range(4) if c != pv)
        return X

    def lin_solve(M, rhs, ncol):
        """Gaussian elimination over Fractions; returns (rank, solution or None)."""
        A = [list(r) + [b] for r, b in zip(M, rhs)]
        piv = []
        r = 0
        for c in range(ncol):
            p = None
            for i in range(r, len(A)):
                if A[i][c] != 0:
                    p = i; break
            if p is None:
                continue
            A[r], A[p] = A[p], A[r]
            pv = A[r][c]
            A[r] = [x / pv for x in A[r]]
            for i in range(len(A)):
                if i != r and A[i][c] != 0:
                    f = A[i][c]
                    A[i] = [A[i][k] - f * A[r][k] for k in range(ncol + 1)]
            piv.append(c); r += 1
        if r < ncol:
            return r, None
        return r, [A[i][ncol] for i in range(ncol)]

    def finish(assign, used_now):
        """Readings assigned types `assign` (consistent).  Variables whose columns coincide over all seven readings
        enter only through their sum Y; grouped system unknowns (u, Y_1..Y_q)."""
        groups = {}
        for k in range(1, 1 + used_now):
            groups.setdefault(tuple(t[k] for t in assign), []).append(k)
        gl = list(groups.items())
        q = len(gl)
        M = [[F(t[0])] + [F(col[i]) for col, _ in gl] for i, t in enumerate(assign)]
        rank, sol = lin_solve(M, S, 1 + q)
        if sol is None:
            under.append(rank); return
        u = sol[0]
        if not (u > 0 and all(y > 0 for y in sol[1:])):
            P.f(0, 'conjunct 0<u, 0<g, 0<h, 0<j fails on every consistent full-rank type assignment'); return
        ys = [(y / u, len(vs)) for y, (_, vs) in zip(sol[1:], gl)]
        P_ = lcm_den(*[y for y, _ in ys]) if ys else 1
        for m in range(1, P_ + 1):
            G = 8 * m + 1
            if all(G * y >= t for y, t in ys) and sum(mod8(G * y - t) for y, t in ys) <= 1:
                LAST['15'] = (S, u, [(y, t, vs) for (y, t), (_, vs) in zip(ys, gl)], m, used_now)
                found.append('u=%s groups(sum of gap(s) in the group, size)=%s m=%d' % (u, [(str(y), t) for y, t in ys], m))
                return
        P.f(2, 'conjunct bands (8a+1<=(8m+1)g, ..., (8m+1)(g+h+j)<=8(a+b+c)+4) fails for every m>=1 on the unique solution (u,gap groups)=%s' % ([str(u)] + [(str(y), t) for y, t in ys]))

    def dfs(i, rows, nused, assign=()):
        if found:
            return
        if i == len(S):
            finish(list(assign), nused); return
        d = S[i]
        for t in TYPES:
            eu = (t[1], t[2], t[3])
            newset = set(range(nused)) | {k for k in range(3) if eu[k]}
            used_now = len(newset)
            if newset != set(range(used_now)):
                continue
            row = [F(t[0]), F(t[1]), F(t[2]), F(t[3])]
            rhs = d
            for pv, rv, r0 in rows:
                c = row[pv]
                if c:
                    row = [row[k] - c * rv[k] for k in range(4)]
                    rhs = rhs - c * r0
            nz = [k for k in range(4) if row[k] != 0]
            if not nz:
                if rhs != 0:
                    continue
                dfs(i + 1, rows, used_now, assign + (t,))
                continue
            pv = nz[0]
            pivval = row[pv]
            row = [x / pivval for x in row]
            rhs = rhs / pivval
            nrows = rows + [(pv, row, rhs)]
            if len(nrows) == 4:
                X = solve(nrows, 3)
                if X[0] > 0 and X[1] > 0 and X[2] > 0 and X[3] > 0:
                    vs = _vals(*X)
                    if all(S[k] in vs for k in range(i + 1, len(S))):
                        g, h, j = X[1] / X[0], X[2] / X[0], X[3] / X[0]
                        m = bandN([g, h, j])
                        if m is not None:
                            LAST['15'] = (S, X[0], [(g, 1, [1]), (h, 1, [2]), (j, 1, [3])], m, 3)
                            found.append('u=%s g=%s h=%s j=%s m=%d' % (X[0], g, h, j, m))
                            return
                        P.f(2, 'conjunct bands (8a+1<=(8m+1)g, ..., (8m+1)(g+h+j)<=8(a+b+c)+4) fails for every m>=1 on the unique solution (u,g,h,j)=%s' % ([str(X[0]), str(g), str(h), str(j)]))
                    else:
                        P.f(1, 'conjunct "each reading = u(D+e g+f h+l j)" fails for the remaining readings on the unique solution')
                else:
                    P.f(0, 'conjunct 0<u, 0<g, 0<h, 0<j fails on every consistent full-rank type assignment')
                continue
            dfs(i + 1, nrows, used_now, assign + (t,))

    dfs(0, [], 0)
    if found:
        return True, found[0]
    if under:
        return 'N', 'reading equations consistent with free parameters (rank-deficient on the used gaps); positivity/bands undecided (%d branches)' % len(under)
    if P.r < 0:
        return False, 'conjunct "each reading = u(D+e g+f h+l j)": no consistent type assignment exists for the seven readings'
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 16 FourPairNativeClass (v,k)
# ----------------------------------------------------------------------------------------------
def t_fourpair_native(T, pos):
    """V = B+z*FourAPPairs.speeds c g h j (sigma i); base = pairs (1,2),(g+2,g+3),(g+h+3,g+h+4),(g+h+j+4,g+h+j+5).
    Sorted T' (orientation z>0): T'1-T'0=T'3-T'2=T'5-T'4=T'7-T'6=z; g=(T'2-T'1)/z, h=(T'4-T'3)/z, j=(T'6-T'5)/z.
    subject: base index 1 (case 1: 1<(8m+1)g, (8m-1)g<1, 8a<=(8m+1)(g+h)<=8a+5) or base index 6 (case 2: same with j,
    h+j); both: 8b<=(8m+1)(g+h+j)<=8b+4.  EXACT (m confined to (1/g,1/g+2) resp. j)."""
    P = Prog()
    for TT, pp in orients(sorted(T), pos):
        d01, d23, d45, d67 = TT[1] - TT[0], TT[3] - TT[2], TT[5] - TT[4], TT[7] - TT[6]
        if not (d01 == d23 == d45 == d67):
            P.f(0, 'conjunct "V = B+z*speeds c g h j (sigma i)": the four consecutive pairs do not have one common step'); continue
        z = d01
        g, h, j = (TT[2] - TT[1]) / z, (TT[4] - TT[3]) / z, (TT[6] - TT[5]) / z
        if not (g > 0 and h > 0 and j > 0):
            P.f(1, 'conjunct 0<g,0<h,0<j fails'); continue
        if pp not in (1, 6):
            P.f(2, 'conjunct "sigma k = 1 or sigma k = 6" fails: subject sits at sorted index %s of 0..7' % pp); continue
        if pp == 1:
            ms = m_candidates(g); xs = lambda G: G * (g + h)
        else:
            ms = m_candidates(j); xs = lambda G: G * (h + j)
        if not ms:
            P.f(3, 'conjunct 1<(8m+1)x and (8m-1)x<1 (x=g resp. j) has no integer m>=1'); continue
        for m in ms:
            G = 8 * m + 1
            if modn(xs(G), 8) > 5:
                P.f(4, 'conjunct 8a<=(8m+1)(g+h)<=8a+5 (resp. h+j) fails for the admissible m'); continue
            if modn(G * (g + h + j), 8) > 4:
                P.f(5, 'conjunct 8b<=(8m+1)(g+h+j)<=8b+4 fails for the admissible m'); continue
            return True, 'case sigma k=%d, z=%s, g=%s h=%s j=%s m=%d' % (pp, z, g, h, j, m)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 17 FourBlockInternalClass (v,k)
# ----------------------------------------------------------------------------------------------
def t_fourblock_internal(T, pos):
    P = Prog()
    T = sorted(T)
    for sizes in compositions(8, 4):
        bs = block_structure(T, sizes)
        if bs is None:
            P.f(0, 'conjunct "V = B+z*speeds c g h j p q r (sigma i)": no split into 4 contiguous unit-step AP blocks with common step'); continue
        z, (g, h, j) = bs
        if not (g > 0 and h > 0 and j > 0):
            P.f(1, 'conjunct 0<g,0<h,0<j fails'); continue
        m = band4(g, h, j)
        if m is None:
            P.f(2, 'conjunct bands (8a+1<=(8m+1)g, 8b+1<=(8m+1)h, 8e+1<=(8m+1)j, (8m+1)(g+h+j)<=8(a+b+e)+4) fails for every m>=1'); continue
        if not (1 <= pos <= 6):
            P.f(3, 'conjunct 1 <= sigma k <= 6 fails: subject sits at sorted index %s (an end runner)' % pos); continue
        LAST['17'] = (T, sizes, z, g, h, j, m, pos)
        return True, 'sizes %s z=%s gaps %s,%s,%s m=%d' % (sizes, z, g, h, j, m)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 18 PartitionNativeBypassClass (v,k)
# ----------------------------------------------------------------------------------------------
def t_partition_bypass(T, pos):
    P = Prog()
    for TT, pp in orients(sorted(T), pos):
        for p in range(1, 7):
            for q in range(2, 7):
                r3 = 8 - p - q
                if r3 < 1:
                    continue
                bs = block_structure(TT, (p, q, r3))
                if bs is None:
                    P.f(0, 'conjunct "V = B+z*speeds c g h p q (sigma i)": no split into 3 contiguous unit-step AP blocks with common step'); continue
                z, (g, h) = bs
                if not (g > 0 and h > 0):
                    P.f(1, 'conjunct 0<g, 0<h fails'); continue
                cases = []
                if 2 <= p and p + q <= 7:
                    cases.append(('A', p - 1, g))
                if 1 <= p and p + q <= 6:
                    cases.append(('B', p + q, h))
                if not cases:
                    P.f(2, 'conjunct "(2<=p, p+q<=7) or (1<=p, p+q<=6)" fails'); continue
                for lab, idx, x in cases:
                    if pp != idx:
                        P.f(3, 'conjunct sigma k = %s fails (case %s needs sorted index %d, subject is at %s)' % (lab, lab, idx, pp)); continue
                    ms = m_candidates(x)
                    if not ms:
                        P.f(4, 'conjunct 1<(8m+1)x and (8m-1)x<1 (x=%s) has no integer m>=1' % x); continue
                    for m in ms:
                        G = 8 * m + 1
                        if modn(G * (g + h), 8) > 3:
                            P.f(5, 'conjunct 8n<=(8m+1)(g+h)<=8n+3 fails for the admissible m'); continue
                        return True, 'sizes %s case %s z=%s g=%s h=%s m=%d' % ((p, q, r3), lab, z, g, h, m)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 19 FourPairStepIndependentClass (v,k)
# ----------------------------------------------------------------------------------------------
def t_fourpair_stepindep(T, pos):
    """base b = [1, 2, g+2, g+3, 3+(8+sg)/G, 4+(7-ka)/G, 8-rho/G, 9-rho/G], G=8m+1, subject = base index 1.
    Increasing in the index for all admissible parameters, so sorted T' (z>0) matches b with z=T'1-T'0.
      g=(T'2-T'1)/z ; T'3-T'2=z ; sg=G((T'4-T'3)/z+g)-8 in [0,1] ; ka=G(1-(T'5-T'4)/z)-1-sg in (0,1];
      rho=G(4-(T'6-T'5)/z)-7+ka in [0,1] ; T'7-T'6=z ; 1<Gg, (G-2)g<1.   EXACT."""
    P = Prog()
    for TT, pp in orients(sorted(T), pos):
        z = TT[1] - TT[0]
        if not (TT[3] - TT[2] == z and TT[7] - TT[6] == z):
            P.f(0, 'conjunct "V = B+z*speeds c g m ka sg rho (tau i)": unit steps T1-T0, T3-T2, T7-T6 are not equal'); continue
        g = (TT[2] - TT[1]) / z
        if g <= 0:
            P.f(1, 'conjunct 0<g fails'); continue
        if pp != 1:
            P.f(2, 'conjunct tau k = 1 fails: subject sits at sorted index %s (needs the second runner of the base)' % pp); continue
        ms = m_candidates(g)
        if not ms:
            P.f(3, 'conjunct 1<(8m+1)g and (8m-1)g<1 has no integer m>=1'); continue
        for m in ms:
            G = 8 * m + 1
            sg = G * ((TT[4] - TT[3]) / z + g) - 8
            if not (0 <= sg <= 1):
                P.f(4, 'conjunct 0<=sigma<=1 fails (sigma=%s)' % sg); continue
            ka = G * (1 - (TT[5] - TT[4]) / z) - 1 - sg
            if not (0 < ka <= 1):
                P.f(5, 'conjunct 0<kappa<=1 fails (kappa=%s)' % ka); continue
            rho = G * (4 - (TT[6] - TT[5]) / z) - 7 + ka
            if not (0 <= rho <= 1):
                P.f(6, 'conjunct 0<=rho<=1 fails (rho=%s)' % rho); continue
            return True, 'z=%s g=%s m=%d sigma=%s kappa=%s rho=%s' % (z, g, m, sg, ka, rho)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# 20 TwoMoverSubjectClass (v only)
# ----------------------------------------------------------------------------------------------
def t_twomover(T):
    """v = B+s*twoMover c (c+x) y 0 7 (sigma i): six runners at c+1..c+6 (a 6-term unit AP), runner 0 at c+x, runner 7 at y.
    x<1/6; 2(1-x)(6-x) <= (1-6x)|y-(c+x)|; (0<=x) or (1-x<=|y-(c+x)| and 4(6-x)<=3|y-(c+x)|).
    In units of the AP step delta: P0 lies outside the AP at distance rho*delta from an end element (rho=1-x>5/6),
    W=|P7-P0|/delta.  Test over the 28 six-subsets that are APs, both labellings of the other two points, both ends.
    Positivity of the base is free (B,c are free reals).  EXACT."""
    P = Prog()
    T = sorted(T)
    for idx in itertools.combinations(range(8), 6):
        sub = [T[i] for i in idx]
        dlt = ap_step(sub)
        if dlt is None:
            continue
        rest = [T[i] for i in range(8) if i not in idx]
        for P0, P7 in (rest, rest[::-1]):
            for end in ('lo', 'hi'):
                if end == 'lo':
                    if not P0 < sub[0]:
                        continue
                    rho = (sub[0] - P0) / dlt
                else:
                    if not P0 > sub[-1]:
                        continue
                    rho = (P0 - sub[-1]) / dlt
                x = 1 - rho
                W = abs(P7 - P0) / dlt
                if not x < F(1, 6):
                    P.f(0, 'conjunct x<1/6 fails (x=%s)' % x); continue
                if not 2 * (1 - x) * (6 - x) <= (1 - 6 * x) * W:
                    P.f(1, 'conjunct 2(1-x)(6-x) <= (1-6x)|y-(c+x)| fails (x=%s, W=%s)' % (x, W)); continue
                if not (x >= 0 or (1 - x <= W and 4 * (6 - x) <= 3 * W)):
                    P.f(2, 'conjunct "0<=x or (1-x<=|y-(c+x)| and 4(6-x)<=3|y-(c+x)|)" fails (x=%s, W=%s)' % (x, W)); continue
                return True, 'AP %s step %s, x=%s, W=%s' % ([str(a) for a in sub], dlt, x, W)
    return False, P.m if P.r >= 0 else 'conjunct "v = B+s*twoMover(...)": no six points of T form a unit AP with the other two outside-ish'

# ----------------------------------------------------------------------------------------------
# 21 CanonicalReturnClass (v,k ; readings only)
# ----------------------------------------------------------------------------------------------
def t_canonical(S, qmax=1):
    """exists u != k, Q>0, N integer: N-1/8 < d_u Q < N+1/8 (u in the way at Q); IsMove(D,Q,P) with P = (N+1/8)/d_u
    (u's next opening is the largest next opening among readings in the way at Q); and for every i with advance>0
    (advance = max(0, label(d_i P) - label(d_i Q)), label x = ceil(x-7/8)):  d_u(label(d_i P)+1/8) <= d_i(N+1/8).
    All readings are integers, so every predicate is periodic of period 1 in Q (P shifts by 1, labels by d_i, N by d_u):
    Q in (0,1] suffices.  Within (0,1] every predicate is constant between the points Q = (j+1/8)/d and (j+7/8)/d;
    those points and the midpoints of consecutive points are tested.  EXACT."""
    S = [F(d) for d in S]
    pts = set()
    for d in S:
        for j in range(0, int(d) + 1):
            for off in (F(1, 8), F(7, 8)):
                q = (j + off) / d
                if 0 < q <= qmax:
                    pts.add(q)
    pts.add(F(qmax))
    pts = sorted(pts)
    cand = list(pts)
    prev = F(0)
    for q in pts:
        cand.append((prev + q) / 2)
        prev = q
    cand = sorted(set(cand))
    P = Prog()
    for Q in cand:
        inway = [d for d in S if distint(d * Q) < F(1, 8)]
        if not inway:
            P.f(-1, 'no reading is in the way at the tested Q (not applicable)')
            continue
        nxt = {d: (ce(d * Q - F(1, 8)) + F(1, 8)) / d for d in S}
        for u in inway:
            N = rnd(u * Q)
            Pp = (N + F(1, 8)) / u
            if nxt[u] != Pp:
                P.f(0, 'internal: nextOpening mismatch'); continue
            if not all(nxt[d] <= Pp for d in inway):
                P.f(0, 'conjunct IsMove(D,Q,opening): another reading in the way has a later next opening'); continue
            ok = True
            for d in S:
                adv = max(0, ce(d * Pp - F(7, 8)) - ce(d * Q - F(7, 8)))
                if adv > 0:
                    if not (u * (ce(d * Pp - F(7, 8)) + F(1, 8)) <= d * (N + F(1, 8))):
                        P.f(1, 'conjunct d_u(label(d_i P)+1/8) <= d_i(N+1/8) fails for a reading with advance>0'); ok = False; break
            if ok:
                LAST['21'] = (S, Q, u, N, Pp)
                return True, 'Q=%s u=%s N=%d P=%s' % (Q, u, N, Pp)
    return False, P.m

# ----------------------------------------------------------------------------------------------
# registry
# NOTE on class 21 (CanonicalReturnClass): it holds iff the subject is isolated at some instant.
#   (=>) Lean canonical_isolation.  (<=) Let P be the first lonely instant (the lonely set is closed and excludes (0,eps));
#   just before P some reader u was in the way and at P stands at d_u P = N+1/8 exactly, so P = (N+1/8)/d_u is u's opening.
#   Take Q = P - eps.  Readers in the way at Q have next opening <= P (else they would be in the way at P), u attains P, and no
#   label ceil(d P - 7/8) changes between Q and P.  So every conjunct holds.  Hence 'member' is a restatement of 'subject isolated'.
# ----------------------------------------------------------------------------------------------
# kind: 'S' readings, 'T' arrangement, 'K' arrangement with subject position
CLASSES = [
    ('01 APCoreOpening',            'S', t_apcore,   'exact'),
    ('02 SplitAPReadings',          'S', t_splitap,  'exact'),
    ('03 SignedAPReadings',         'S', t_signed,   'exact'),
    ('04 GeneralTwoAPBlock',        'T', t_general2ap, 'exact'),
    ('05 PairTrainOpening',         'S', t_pair,     'exact'),
    ('06 TwoSlowTrain',             'S', t_twoslow,  'exact'),
    ('07 UnequalTwoAPBlock',        'T', t_unequal,  'exact'),
    ('08a MixedFourTwo',            'T', t_mixed4_two, 'exact'),
    ('08b MixedFourParam',          'T', t_mixed4_param, 'exact'),
    ('08c MixedFourLower',          'T', t_mixed4_lower, 'exact'),
    ('08d UniformFour',             'T', t_uniform4, 'exact'),
    ('09a MiddleFiveAll',           'T', t_middle5,  'exact'),
    ('09b FullThreeFive',           'T', t_full35,   'exact'),
    ('10 SeparatedTwoAP21',         'T', t_sep21,    'exact'),
    ('11 TwoSixNine',               'T', t_two69,    'exact'),
    ('12 TwoSixThin',               'T', t_two6thin, 'exact'),
    ('13 DoubleCovered',            'T', t_doublecovered, 'necessary (exact leaf FourBlockClass)'),
    ('14 ThreeBlockReverseMiddle',  'T', t_3block_rev, 'exact'),
    ('15 ThreeGapPacket',           'S', t_threegap, 'exact on rank-4 branch; rank<4 branches necessary'),
    ('16 FourPairNative',           'K', t_fourpair_native, 'exact'),
    ('17 FourBlockInternal',        'K', t_fourblock_internal, 'exact'),
    ('18 PartitionNativeBypass',    'K', t_partition_bypass, 'exact'),
    ('19 FourPairStepIndependent',  'K', t_fourpair_stepindep, 'exact'),
    ('20 TwoMoverSubject',          'T', t_twomover, 'exact'),
    ('21 CanonicalReturn',          'S', t_canonical, 'exact'),
]

def run_class(cls, S, mode):
    """mode 'lit' (subject at the bottom) or 'sf' (any sign pattern)."""
    name, kind, fn, _ = cls
    if kind == 'S':
        return fn(S)
    if mode == 'lit':
        T = [F(0)] + sorted(F(d) for d in S)
        return fn(T, 0) if kind == 'K' else fn(T)
    best = (False, None)
    seen = set()
    last = None
    allf = None
    for signs in itertools.product((1, -1), repeat=7):
        if signs[0] == -1:
            continue                       # mirror image of a pattern with signs[0]=+1 (all classes mirror-invariant)
        pts = [F(0)] + [F(sg * d) for sg, d in zip(signs, S)]
        T = sorted(pts)
        pos = T.index(0)
        key = (tuple(T), pos if kind == 'K' else None)
        if key in seen:
            continue
        seen.add(key)
        res = fn(T, pos) if kind == 'K' else fn(T)
        if res[0] is True:
            return True, 'signs %s: %s' % (signs, res[1])
        if res[0] == 'N' and best[0] is False:
            best = ('N', 'signs %s: %s' % (signs, res[1]))
        last = res
    if best[0] == 'N':
        return best
    return False, 'no sign pattern (%d tried) is a member' % len(seen)

# ----------------------------------------------------------------------------------------------
# generators for positive controls (written from the Lean speeds formulas, independent of the tests)
# ----------------------------------------------------------------------------------------------
def sp_unequal(c, A, u, v, p):
    return [c + u * i if i < p else c + A + v * (i - p) for i in range(8)]

def sp_fourblock(c, g, h, j, p, q, r):
    out = []
    for i in range(8):
        x = c + 1 + i
        if p <= i: x += g - 1
        if p + q <= i: x += h - 1
        if p + q + r <= i: x += j - 1
        out.append(x)
    return out

def sp_3block(c, g, h, p, q):
    out = []
    for i in range(8):
        if i < p: out.append(c + 1 + i)
        elif i < p + q: out.append(c + g + i)
        else: out.append(c + g + h + i - 1)
    return out

def sp_fourpair(c, g, h, j):
    out = []
    for i in range(8):
        if i < 2: x = 1 + i
        elif i < 4: x = g + i
        elif i < 6: x = g + h + i - 1
        else: x = g + h + j + i - 2
        out.append(c + x)
    return out

def sp_stepindep(c, g, m, ka, sg, rho):
    G = 8 * m + 1
    out = []
    for i in range(8):
        if i < 2: x = 1 + i
        elif i < 4: x = g + i
        elif i == 4: x = 3 + (8 + sg) / G
        elif i == 5: x = 2 + 2 + (7 - ka) / G
        else: x = i + 2 - rho / G
        out.append(c + x)
    return out

def sp_twomover(c, x, y):
    return [c + x] + [c + i for i in range(1, 7)] + [y]

def aff(base, B, z):
    return sorted(B + z * b for b in base)

def to_S_from_T(T, pos):
    return sorted(abs(t - T[pos]) for i, t in enumerate(T) if i != pos)

# ----------------------------------------------------------------------------------------------
# controls
# ----------------------------------------------------------------------------------------------
def controls():
    C = {}
    # S-kind controls are reading sets; T-kind are 8-point sets; K-kind are (T,pos)
    C['01 APCoreOpening'] = ([1, 2, 3, 40, 41, 42, 43], None)
    C['02 SplitAPReadings'] = ([2, 4, 7, 9, 11, 13, 15], None)          # s=2, r=2, a=7/2
    C['03 SignedAPReadings'] = ([1, 3, 4, 5, 7, 8, 11], None)           # s=4, r=2, B=-5/4
    C['04 GeneralTwoAPBlock'] = ([F(x) for x in (0, 1, 2, 3, 10, 11, 12, 13)], None)
    C['05 PairTrainOpening'] = ([1, 2, 20, 21, 22, 23, 24], None)
    C['06 TwoSlowTrain'] = ([1, 5, 28, 29, 30, 31, 32], None)
    C['07 UnequalTwoAPBlock'] = ([F(x) for x in (0, 1, 41, 42, 43, 44, 45, 46)], None)
    C['08a MixedFourTwo'] = ([F(x) for x in (0, 1, 2, 3, 16, 18, 20, 22)], None)
    C['08b MixedFourParam'] = ([F(x) for x in (0, 1, 2, 3, 21, 23, 25, 27)], None)
    C['08c MixedFourLower'] = ([F(x) for x in (0, 2, 4, 6, 33, 36, 39, 42)], None)
    C['08d UniformFour'] = ([F(x) for x in (0, 1, 2, 3, 66, 69, 72, 75)], None)
    C['09a MiddleFiveAll'] = ([F(x) for x in (0, 1, 2, 13, 14, 15, 16, 17)], None)
    C['09b FullThreeFive'] = ([F(x) for x in (0, 1, 2, 56, 61, 66, 71, 76)], None)
    C['10 SeparatedTwoAP21'] = ([F(x) for x in (0, 1, 22, 23, 24, 25, 26, 27)], None)
    C['11 TwoSixNine'] = ([F(x) for x in (0, 1, 10, 11, 12, 13, 14, 15)], None)
    C['12 TwoSixThin'] = ([F(x) for x in (0, 2, 14, 15, 16, 17, 18, 19)], None)
    # 13: FourBlockClass leaf; sizes (2,2,2,2), gaps g=h=j=1/9 (m=1: eps=0), step 9 : speeds c g h j 2 2 2
    b = sp_fourblock(F(0), F(1, 9), F(1, 9), F(1, 9), 2, 2, 2)
    C['13 DoubleCovered'] = (aff(b, F(0), F(9)), None)
    # 14: sizes (2,1,5): g,h with g+h<=2, m=1: (8m-1)=7 : choose g=h=1/7*... delta=(-1-7x) mod 8 ; x=1/7 -> mod8(-2)=6 no ;
    # search below fills it
    C['14 ThreeBlockReverseMiddle'] = (None, None)
    # 15 ThreeGapPacket: u=9, g=h=j=1/9 : readings 9D + {0..3}
    C['15 ThreeGapPacket'] = ([1, 2, 3, 9, 10, 18, 27], None)
    # 16: z=15, g=2/15,h=3/15,j=1/15, m=1, subject base index 1
    bb = sp_fourpair(F(0), F(2, 15), F(3, 15), F(1, 15))
    C['16 FourPairNative'] = ((aff(bb, F(0), F(15))), 1)
    # 17: four blocks (2,2,2,2) gaps 1/9, z=9; subject interior (index 3)
    b17 = sp_fourblock(F(0), F(1, 9), F(1, 9), F(1, 9), 2, 2, 2)
    C['17 FourBlockInternal'] = (aff(b17, F(0), F(9)), 3)
    # 18: sizes (2,3,3) case A, subject base index p-1=1, z=15, g=2/15,h=3/15, m=1
    b18 = sp_3block(F(0), F(2, 15), F(3, 15), 2, 3)
    C['18 PartitionNativeBypass'] = (aff(b18, F(0), F(15)), 1)
    # 19: m=1, G=9, g in (1/9,1/7): g=2/15 ; sg=1/2 ; ka=1/2 ; rho=1/2 ; z=30 so everything is integral-ish
    b19 = sp_stepindep(F(0), F(2, 15), 1, F(1, 2), F(1, 2), F(1, 2))
    C['19 FourPairStepIndependent'] = (aff(b19, F(0), F(1)), 1)
    b20 = sp_twomover(F(0), F(0), F(20))
    C['20 TwoMoverSubject'] = (sorted(b20), None)
    C['21 CanonicalReturn'] = (None, None)
    return C

# ----------------------------------------------------------------------------------------------
SURVIVORS = [
    (1, 4, 28, 30, 31, 32, 38), (1, 6, 29, 30, 31, 32, 35), (1, 7, 8, 15, 22, 23, 30),
    (1, 8, 33, 35, 36, 37, 41), (1, 8, 33, 35, 36, 37, 42), (1, 13, 14, 15, 16, 29, 36),
    (1, 13, 14, 15, 16, 29, 42), (1, 13, 16, 28, 29, 30, 33), (1, 16, 27, 29, 30, 31, 35),
    (1, 28, 29, 30, 32, 35, 39), (2, 10, 12, 14, 16, 26, 37), (2, 10, 12, 14, 16, 26, 39),
    (2, 10, 12, 14, 16, 26, 41), (2, 10, 12, 14, 16, 26, 43), (2, 12, 14, 16, 18, 30, 39),
    (2, 12, 14, 16, 18, 30, 43), (3, 15, 18, 21, 24, 33, 38), (3, 15, 18, 21, 24, 33, 43),
    (3, 15, 18, 21, 24, 39, 44),
]

STRUCT_MARKS = ('no contiguous', 'V = B+', 'no candidate', 'both blocks are APs', 'no split', 'the four consecutive pairs',
                'unit steps', 'no consistent type', 'no six points', 'no sign pattern')

def is_structural(msg):
    return any(k in msg for k in STRUCT_MARKS)

def eval_control(cls, ctrl):
    name, kind, fn, _ = cls
    data, pos = ctrl
    if kind == 'K':
        return fn(data, pos)
    return fn(data)

def find_negatives(cls, data, pos):
    """structural negative: first perturbation (move the last point/reading) the test rejects at the structural conjunct;
       near-miss negative: first shift of an upper suffix (all points from index i up) that keeps the structure and
       is rejected by a numeric/arithmetical conjunct."""
    name, kind, fn, _ = cls
    structural = near = None
    def ev(d2):
        return fn(d2, pos) if kind == 'K' else fn(d2)
    if kind == 'S':
        for delta in list(range(1, 40)) + list(range(-1, -40, -1)):
            d2 = list(data)
            d2[-1] = d2[-1] + delta
            if len(set(d2)) != 7 or min(d2) <= 0:
                continue
            d2 = sorted(d2)
            r = ev(d2)
            if r[0] is False:
                if is_structural(r[1]) and structural is None:
                    structural = (d2, r)
                if not is_structural(r[1]) and near is None:
                    near = (d2, r)
            if structural and near:
                break
        return structural, near
    for delta in [F(x, 2) for x in range(1, 80)] + [F(-x, 2) for x in range(1, 80)]:
        for idx in range(7, 0, -1):
            d2 = list(data)
            for i in range(idx, 8):
                d2[i] = d2[i] + delta
            if len(set(d2)) != 8 or sorted(d2) != d2:
                continue
            r = ev(d2)
            if r[0] is False:
                if is_structural(r[1]) and structural is None:
                    structural = (d2, r)
                if not is_structural(r[1]) and near is None:
                    near = (d2, r)
        if structural and near:
            break
    return structural, near

def verify_witnesses(cls_name, T_used, S):
    """independent re-derivation of a found witness from the Lean formulas (separate code path)."""
    w = LAST.get(cls_name[:2])
    if cls_name.startswith('13') and w:
        TT, sizes, z, g, h, j, m = w
        base = sp_fourblock(F(0), g, h, j, *sizes[:3])
        rec = sorted(TT[0] + z * (b - min(base)) for b in base)
        G = 8 * m + 1
        a, b_, e = [fl((G * x - 1) / 8) for x in (g, h, j)]
        ok = (rec == sorted(TT) and 8 * a + 1 <= G * g and 8 * b_ + 1 <= G * h and 8 * e + 1 <= G * j
              and G * (g + h + j) <= 8 * (a + b_ + e) + 4 and g + h + j <= 3)
        return 'independent check (rebuild speeds + explicit a,b,e): %s' % ('OK' if ok else 'FAILED')
    if cls_name.startswith('14') and w:
        TT, sizes, z, g, h, m = w
        base = sp_3block(F(0), g, h, sizes[0], sizes[1])
        rec = sorted(TT[0] + z * (b - min(base)) for b in base)
        Fm = 8 * m - 1
        a, b_ = ce((Fm * g + 1) / 8), ce((Fm * h + 1) / 8)
        ok = (rec == sorted(TT) and Fm * g <= 8 * a - 1 and Fm * h <= 8 * b_ - 1 and 8 * (a + b_) - 3 <= Fm * (g + h) and g + h <= 2)
        return 'independent check (rebuild speeds + explicit a,b): %s' % ('OK' if ok else 'FAILED')
    if cls_name.startswith('17') and w:
        TT, sizes, z, g, h, j, m, pos = w
        base = sp_fourblock(F(0), g, h, j, *sizes[:3])
        rec = sorted(TT[0] + z * (b - min(base)) for b in base)
        G = 8 * m + 1
        a, b_, e = [fl((G * x - 1) / 8) for x in (g, h, j)]
        ok = (rec == sorted(TT) and 1 <= pos <= 6 and 8 * a + 1 <= G * g and 8 * b_ + 1 <= G * h and 8 * e + 1 <= G * j
              and G * (g + h + j) <= 8 * (a + b_ + e) + 4)
        return 'independent check (rebuild speeds + explicit a,b,e): %s' % ('OK' if ok else 'FAILED')
    if cls_name.startswith('15') and w:
        S_, u, groups, m, used_now = w
        # expand: for groups of size t split the sum evenly on the lattice (8b+1+e)/G, then verify every reading directly
        G = 8 * m + 1
        gaps = {}
        for y, t, vs in groups:
            s = fl((G * y - t) / 8)               # sum of the b_i
            rem = G * y - t - 8 * s               # total slack
            parts = [F(8 * 0 + 1) / G] * t        # b_i = 0 baseline then add s to the first part
            vals = []
            for idx in range(t):
                bi = s if idx == 0 else 0
                ei = rem if idx == 0 else 0
                vals.append((8 * bi + 1 + ei) / G)
            for v_, k in zip(vals, vs):
                gaps[k] = v_
        for k in (1, 2, 3):
            gaps.setdefault(k, F(1) / G)          # unused gap: free, a=0, zero slack
        g1, g2, g3 = gaps[1], gaps[2], gaps[3]
        a1, a2, a3 = [fl((G * x - 1) / 8) for x in (g1, g2, g3)]
        bands = (g1 > 0 and g2 > 0 and g3 > 0 and 8 * a1 + 1 <= G * g1 and 8 * a2 + 1 <= G * g2 and 8 * a3 + 1 <= G * g3
                 and G * (g1 + g2 + g3) <= 8 * (a1 + a2 + a3) + 4 and u > 0)
        vals = {u * (D + e * g1 + f * g2 + l * g3) for D, e, f, l in TYPES}
        ok = bands and all(d in vals for d in S_)
        return 'independent check (explicit g,h,j; every reading in u(D+eg+fh+lj); explicit a,b,c): %s' % ('OK' if ok else 'FAILED')
    if cls_name.startswith('21') and w:
        S_, Q, u, N, Pp = w
        S_ = [F(d) for d in S_]
        c1 = N - F(1, 8) < u * Q < N + F(1, 8) and Pp == (N + F(1, 8)) / u and Q > 0
        inway = [d for d in S_ if distint(d * Q) < F(1, 8)]
        c2 = u in inway and all((ce(d * Q - F(1, 8)) + F(1, 8)) / d <= Pp for d in inway)
        c3 = True
        for d in S_:
            adv = max(0, ce(d * Pp - F(7, 8)) - ce(d * Q - F(7, 8)))
            if adv > 0 and not (u * (ce(d * Pp - F(7, 8)) + F(1, 8)) <= d * (N + F(1, 8))):
                c3 = False
        lonely = all(distint(d * Pp) >= F(1, 8) for d in S_)
        return 'independent check of the Lean conjuncts: %s ; subject isolated at P=%s: %s' % ('OK' if (c1 and c2 and c3) else 'FAILED', Pp, lonely)
    return None

def run_class_verified(cls, S, mode):
    LAST.clear()
    r = run_class(cls, S, mode)
    if r[0] is True:
        extra = verify_witnesses(cls[0], None, S)
        if extra:
            r = (True, r[1] + '   | ' + extra)
    return r

def worker(args):
    kind, payload = args
    S = payload
    out = {}
    for cls in CLASSES:
        out[(cls[0], 'lit')] = run_class_verified(cls, S, 'lit')
        out[(cls[0], 'sf')] = run_class_verified(cls, S, 'sf') if cls[1] != 'S' else out[(cls[0], 'lit')]
    return S, out

import random

def rnd_frac(rng, lo, hi, den=12):
    return F(rng.randint(lo * den, hi * den), den)

def affine_shuffle(rng, base):
    """B + z*base with random sign/scale/shift; the permutation sigma is absorbed by sorting."""
    z = rnd_frac(rng, 1, 5, 4) * rng.choice((1, -1))
    B = rnd_frac(rng, -20, 20, 3)
    return z, B, sorted(B + z * b for b in base)

def sample(rng, gen, accept, tries=200000):
    for _ in range(tries):
        w = gen()
        if accept(*w):
            return w
    return None

def selftest(seed=7, n=40):
    """Completeness check.  Parameters are drawn from the Lean constraints (rejection sampling with the Lean
    inequalities written out again here), the arrangement/readings are built by the Lean speeds formulas, passed
    through a random affine map B+z*(.) with random sign and shuffled labels, and every test must say member.
    Reports hits/total per class; a miss would be a false-negative bug in a test."""
    rng = random.Random(seed)
    res = {}
    def rec(name, ok):
        a, b = res.get(name, (0, 0))
        res[name] = (a + (1 if ok else 0), b + 1)
    # two-block family
    specs = {
        '07 UnequalTwoAPBlock': (lambda p, u, v, G: G > 0 and 8*(p-1)*u <= G*(8-p) and 8*(7-p)*v <= G*p and
                                 (7-p)*v*(1/(8*u)+1/G) <= F(3,4) and (p-1)*u*(1/(8*v)+1/G) <= F(3,4), (2, 6), t_unequal),
        '08a MixedFourTwo': (lambda p, u, v, G: v == 2*u and G >= F(51,4)*u, (4, 4), t_mixed4_two),
        '08b MixedFourParam': (lambda p, u, v, G: v >= 2*u and G > 0 and 9*v*v <= G*(8*u-3*v), (4, 4), t_mixed4_param),
        '08c MixedFourLower': (lambda p, u, v, G: F(8,7)*u <= v <= 2*u and 9*v <= G, (4, 4), t_mixed4_lower),
        '08d UniformFour': (lambda p, u, v, G: 21*max(u,v) <= G, (4, 4), t_uniform4),
        '09a MiddleFiveAll': (lambda p, u, v, G: 7*v >= 6*u and 32*v <= 3*G, (3, 3), t_middle5),
        '09b FullThreeFive': (lambda p, u, v, G: F(32,3)*max(u,v) <= G, (3, 3), t_full35),
        '10 SeparatedTwoAP21': (lambda p, u, v, G: 21*max(u,v) <= G, (2, 6), t_sep21),
        '11 TwoSixNine': (lambda p, u, v, G: 9*max(u,v) <= G, (2, 2), t_two69),
        '12 TwoSixThin': (lambda p, u, v, G: 4*u <= 3*G and 40*u*v <= G*(6*u-5*v), (2, 2), t_two6thin),
    }
    for name, (acc, (plo, phi), fn) in specs.items():
        for _ in range(n):
            def gen():
                u = rnd_frac(rng, 1, 4, 4)
                v = 2 * u if name.startswith('08a') else (rnd_frac(rng, 1, 4, 4) if not name.startswith('08b') else u * rnd_frac(rng, 2, 3, 12))
                return rng.randint(plo, phi), u, v, rnd_frac(rng, 1, 120, 4)
            w = sample(rng, gen, acc)
            if w is None:
                continue
            p, u, v, G = w
            z, B, T = affine_shuffle(rng, sp_unequal(F(0), (p - 1) * u + G, u, v, p))
            rec(name, fn(T)[0] is True)
    for _ in range(n):                       # 04
        p = rng.randint(1, 7); A = rnd_frac(rng, -10, 25, 4)
        base = [F(i) for i in range(p)] + [A + j for j in range(8 - p)]
        if len(set(base)) < 8:
            continue
        z, B, T = affine_shuffle(rng, base)
        rec('04 GeneralTwoAPBlock', t_general2ap(T)[0] is True)
    def gh_rev():
        return rnd_frac(rng, 0, 2, 20), rnd_frac(rng, 0, 2, 20), rng.randint(1, 30), rng.randint(2, 5)
    for _ in range(n):                       # 14
        def acc(g, h, m, p):
            if g <= 0 or h <= 0 or g + h > 2: return False
            Fm = 8 * m - 1; a = ce((Fm * g + 1) / 8); b = ce((Fm * h + 1) / 8)
            return any(Fm*g <= 8*(a+da)-1 and Fm*h <= 8*(b+db)-1 and 8*(a+da+b+db)-3 <= Fm*(g+h) for da in (0, 1, 2) for db in (0, 1, 2))
        w = sample(rng, gh_rev, acc)
        g, h, m, p = w
        q = rng.randint(1, 6 - p)
        z, B, T = affine_shuffle(rng, sp_3block(F(0), g, h, p, q))
        rec('14 ThreeBlockReverseMiddle', t_3block_rev(T)[0] is True)
    def gen4():
        sizes = rng.choice(list(compositions(8, 4)))
        return sizes, rnd_frac(rng, 0, 3, 18), rnd_frac(rng, 0, 3, 18), rnd_frac(rng, 0, 3, 18), rng.randint(1, 30)
    def acc4(sizes, g, h, j, m):
        if g <= 0 or h <= 0 or j <= 0: return False
        G = 8 * m + 1
        a, b, e = [fl((G * x - 1) / 8) for x in (g, h, j)]
        return G * (g + h + j) <= 8 * (a + b + e) + 4
    for _ in range(n):                       # 13 (leaf FourBlockClass), 17
        w = sample(rng, gen4, lambda s, g, h, j, m: acc4(s, g, h, j, m) and g + h + j <= 3 and (s[0] != 1 or g >= 1) and (s[3] != 1 or j >= 1))
        if w is None: continue
        sizes, g, h, j, m = w
        z, B, T = affine_shuffle(rng, sp_fourblock(F(0), g, h, j, *sizes[:3]))
        rec('13 DoubleCovered (leaf FourBlockClass)', t_doublecovered(T)[0] is True)
        pos = rng.randint(1, 6)
        z, B, T = affine_shuffle(rng, sp_fourblock(F(0), g, h, j, *sizes[:3]))
        rec('17 FourBlockInternal', t_fourblock_internal(T, rng.randint(1, 6))[0] is True)
    for _ in range(n):                       # 16
        w = sample(rng, lambda: (rnd_frac(rng, 0, 1, 40), rnd_frac(rng, 0, 4, 12), rnd_frac(rng, 0, 4, 12), rng.randint(1, 9), rng.choice((1, 6))),
                   lambda g, h, j, m, which: g > 0 and h > 0 and j > 0 and (lambda G: (
                       (G*g > 1 and (G-2)*g < 1 and modn(G*(g+h), 8) <= 5 if which == 1 else G*j > 1 and (G-2)*j < 1 and modn(G*(h+j), 8) <= 5)
                       and modn(G*(g+h+j), 8) <= 4))(8*m+1))
        g, h, j, m, which = w
        base = sp_fourpair(F(0), g, h, j)
        z, B, T = affine_shuffle(rng, base)
        pos = T.index(B + z * base[which])
        rec('16 FourPairNative', t_fourpair_native(T, pos)[0] is True)
    for _ in range(n):                       # 18
        w = sample(rng, lambda: (rnd_frac(rng, 0, 1, 40), rnd_frac(rng, 0, 4, 12), rng.randint(1, 9), rng.randint(1, 5), rng.randint(2, 5), rng.choice('AB')),
                   lambda g, h, m, p, q, case: g > 0 and h > 0 and p + q <= (7 if case == 'A' else 6) and (p >= 2 or case == 'B') and (lambda G: (
                       (G*(g if case == 'A' else h) > 1 and (G-2)*(g if case == 'A' else h) < 1) and modn(G*(g+h), 8) <= 3))(8*m+1))
        g, h, m, p, q, case = w
        base = sp_3block(F(0), g, h, p, q)
        idx = p - 1 if case == 'A' else p + q
        z, B, T = affine_shuffle(rng, base)
        pos = T.index(B + z * base[idx])
        rec('18 PartitionNativeBypass', t_partition_bypass(T, pos)[0] is True)
    for _ in range(n):                       # 19
        w = sample(rng, lambda: (rng.randint(1, 8), F(rng.randint(1, 100), 100), F(rng.randint(1, 100), 100), F(rng.randint(0, 100), 100), F(rng.randint(0, 100), 100)),
                   lambda m, gg, ka, sg, rho: ka > 0 and (8*m+1)*gg/ (F(1)) > 0 and (lambda G, g: G*g > 1 and (G-2)*g < 1)(8*m+1, gg/ (8*m+1) * F(1) + F(1, 8*m+1)))
        m, gg, ka, sg, rho = w
        g = gg / (8 * m + 1) + F(1, 8 * m + 1)           # in (1/G, 2/G); keep only g with (G-2) g < 1
        G = 8 * m + 1
        if not ((G - 2) * g < 1 and G * g > 1 and 0 < ka <= 1):
            continue
        base = sp_stepindep(F(0), g, m, ka, sg, rho)
        z, B, T = affine_shuffle(rng, base)
        pos = T.index(B + z * base[1])
        rec('19 FourPairStepIndependent', t_fourpair_stepindep(T, pos)[0] is True)
    for _ in range(n):                       # 20
        def acc(x, W, side):
            return x < F(1, 6) and 2*(1-x)*(6-x) <= (1-6*x)*W and (x >= 0 or (1-x <= W and 4*(6-x) <= 3*W))
        w = sample(rng, lambda: (rnd_frac(rng, -6, 1, 12) / 6 if False else F(rng.randint(-60, 1), 12), F(rng.randint(1, 600), 12), rng.choice((1, -1))), acc)
        x, W, side = w
        # base: P0 = x, AP 1..6, P7 = x + side*W   (y = c+x +- W)
        base = sp_twomover(F(0), x, x + side * W)
        if len(set(base)) < 8: continue
        z, B, T = affine_shuffle(rng, base)
        rec('20 TwoMoverSubject', t_twomover(T)[0] is True)
    # readings classes
    for _ in range(n):                       # 02
        r = rng.randint(1, 5); s = rnd_frac(rng, 1, 6, 4); a = rnd_frac(rng, 1, 30, 4)
        tr = [F(i) for i in range(1, r + 1)] + [a + j for j in range(7 - r)]
        if len(set(tr)) < 7: continue
        rec('02 SplitAPReadings', t_splitap([s * q for q in tr])[0] is True)
    for _ in range(n):                       # 03
        r = rng.randint(1, 5); s = rnd_frac(rng, 1, 6, 4); B = rnd_frac(rng, -12, 12, 8)
        if B.denominator == 1: continue
        tr = [F(i) for i in range(1, r + 1)] + [B + j for j in range(7 - r)]
        ab = [abs(q) for q in tr]
        if len(set(ab)) < 7: continue
        rec('03 SignedAPReadings', t_signed([s * q for q in ab])[0] is True)
    for _ in range(n):                       # 01
        w = sample(rng, lambda: (rng.randint(1, 6), rnd_frac(rng, 1, 5, 4), rnd_frac(rng, 5, 80, 4), rnd_frac(rng, 0, 6, 4)),
                   lambda r, u, x, wd: 8*r*u <= x*(7-r) and wd*(1/(8*u)+1/x) <= F(3, 4))
        r, u, x, wd = w
        C = sorted({x + wd * F(rng.randint(0, 20), 20) for _ in range(7 - r)})
        rd = [j * u for j in range(1, r + 1)] + C
        if len(set(rd)) < 7: continue
        rec('01 APCoreOpening', t_apcore(rd[:7])[0] is True)
    for _ in range(n):                       # 15
        w = sample(rng, lambda: (rnd_frac(rng, 1, 5, 4), rng.randint(1, 9), rnd_frac(rng, 0, 3, 18), rnd_frac(rng, 0, 3, 18), rnd_frac(rng, 0, 3, 18)),
                   lambda u, m, g, h, j: g > 0 and h > 0 and j > 0 and acc4(None, g, h, j, m))
        u, m, g, h, j = w
        types = rng.sample(TYPES, 7)
        rd = sorted({u * (D + e * g + f * h + l * j) for D, e, f, l in types})
        if len(rd) < 7: continue
        rec('15 ThreeGapPacket', t_threegap(rd)[0] is True)
    for _ in range(n):                       # 05
        s = rng.randint(1, 14); a = rng.randint(1, 14)
        p = rng.randint(0, s - 1); q = rng.randint(0, a - 1)
        L = max((p + F(1, 8)) / F(s), (q + F(1, 8)) / F(a)); R = min((p + F(7, 8)) / F(s), (q + F(7, 8)) / F(a))
        if R <= L: continue
        x = F(rng.randint(8, 80))
        if not L + 1 / x <= R: continue
        wd = F(3, 4) / (L + 1 / x) * F(rng.randint(5, 10), 10)
        need = 5 if s != a else 6
        C = sorted({x + wd * F(rng.randint(0, 40), 40) for _ in range(30)})
        if len(C) < need: continue
        C = rng.sample(C, need)
        rd = sorted({F(s), F(a)} | set(C))
        if len(rd) < 7: continue
        rec('05 PairTrainOpening', t_pair(rd)[0] is True)
    for _ in range(n):                       # 06
        nn = rng.randint(0, 6); mm = rng.randint(0, 5); N = 8 * nn + 1
        x = F(rng.randint(10, 120))
        s = x * F(rng.randint(100, 700), 100) / N
        a = (8 * mm + 1) * x / N + x * F(rng.randint(0, 600), 100) / N
        wd = 6 * x / N * F(rng.randint(5, 10), 10)
        fs = {x + wd * F(rng.randint(0, 40), 40) for _ in range(40)}
        if len(fs) < 5: continue
        fs = rng.sample(sorted(fs), 5)
        rd = sorted({s, a} | set(fs))
        if len(rd) < 7: continue
        rec('06 TwoSlowTrain', t_twoslow(rd)[0] is True)
    return res

def sym(r):
    return {True: 'M', False: '.', 'N': '?'}[r[0]]

def build_controls():
    C = controls()
    done14 = False
    for p in range(2, 5):
        for q in range(1, 7 - p + 1):
            if p + q > 6:
                continue
            for gd in range(1, 40):
                for hd in range(1, 40):
                    g, h = F(gd, 20), F(hd, 20)
                    if g + h > 2 or band3rev(g, h) is None:
                        continue
                    T = aff(sp_3block(F(0), g, h, p, q), F(0), F(20))
                    if t_3block_rev(T)[0] is True:
                        C['14 ThreeBlockReverseMiddle'] = (T, None); done14 = True; break
                if done14: break
            if done14: break
        if done14: break
    C['21 CanonicalReturn'] = ([3, 4, 5, 8, 9, 13, 19], None)
    return C

def main():
    from multiprocessing import Pool
    outp = []
    def W(s=''):
        outp.append(s)
        print(s)
    W('newtypes_membership_v1: exact-Fraction membership tests for NewTypes (21 disjuncts; 25 columns once 08 and 09 are split)')
    W('status M = member (test is decisive), . = not member, ? = necessary part passes but membership is not decided')
    W()
    W('=== test strength per class ===')
    for cls in CLASSES:
        W('  %-30s input=%s  %s' % (cls[0], {'S': 'readings', 'T': '8-pt arrangement', 'K': '8-pt arrangement + subject index'}[cls[1]], cls[3]))
    W()
    W('=== derivations (each test function states the finite condition it implements) ===')
    for cls in CLASSES:
        W('--- %s' % cls[0])
        doc = (cls[2].__doc__ or '(two-block family; see run_two_block and the per-class conjunct list)').strip()
        for line in doc.splitlines():
            W('    ' + line.strip())
    W('--- two-block family (04 handled separately; 07, 08a-d, 09a-b, 10, 11, 12)')
    W('    T sorted splits contiguously into Lo|Up, both APs of >=2 points (steps sL, sU), G = min Up - max Lo > 0.')
    W('    V = B+s*speeds c A u v p (sigma i): s>0 makes block 1 the lower block (p=|Lo|, u=sL, v=sU); s<0 makes block 1 the upper block')
    W('    (p=|Up|, u=sU, v=sL).  G = A-(p-1)u is the gap in base units.  Every Lean inequality is homogeneous in (u,v,G), so the unit-step')
    W('    normalisation u=1 is undone by dividing: b=v/u, A-(p-1)=G/u.  Both orientations are tried.  EXACT.')
    W('--- 21 CanonicalReturn: equivalence note (proof sketch in the comment block of this script)')
    W('    The class holds iff the subject is isolated at some instant.  (=>) Lean canonical_isolation.  (<=) take the first lonely instant P; it is')
    W('    the opening of some reader u (d_u P = N+1/8); at Q = P-eps all readers in the way have next opening <= P and no label advances,')
    W('    so every conjunct holds.  So class 21 restates the conjecture for the arrangement; a non-member would be a counterexample.')
    W()
    C = build_controls()
    W('=== controls: positive built from the Lean speeds formulas; "structural" negative = a perturbation rejected at the shape conjunct;')
    W('    "near-miss" negative = shape kept (suffix shifted), rejected at an arithmetic conjunct ===')
    for cls in CLASSES:
        name = cls[0]
        data, pos = C[name]
        W('--- %s' % name)
        shown = [str(x) for x in data]
        rp = eval_control(cls, (data, pos))
        W('   positive %s%s -> %s  [%s]' % (shown, '' if pos is None else ' subject index %d' % pos, sym(rp), rp[1]))
        st, nm = find_negatives(cls, data, pos)
        for lab, ng in (('structural', st), ('near-miss ', nm)):
            if ng is None:
                W('   negative (%s): none found in the perturbation scan' % lab)
            else:
                W('   negative (%s) %s -> %s  [%s]' % (lab, [str(x) for x in ng[0]], sym(ng[1]), ng[1][1]))
    W()
    W('=== completeness self-test (random parameters drawn from the Lean constraints; every draw must be reported a member) ===')
    st = selftest()
    for k in sorted(st):
        W('  %-42s %d / %d members' % (k, st[k][0], st[k][1]))
    W()
    with Pool() as pool:
        res = dict(pool.map(worker, [('surv', S) for S in SURVIVORS]))
    names = [c[0] for c in CLASSES]
    short = [n.split(' ')[0] for n in names]
    W('=== TABLE A (literal arrangement {0} u {d}, subject at the bottom): rows = survivors (readings), cols = class number ===')
    W('%-28s %s' % ('', ' '.join('%-3s' % s for s in short)))
    for S in SURVIVORS:
        W('%-28s %s' % (str(S), ' '.join('%-3s' % sym(res[S][(n, 'lit')]) for n in names)))
    W()
    W('=== TABLE B (supplementary: sign-free arrangement {0} u {eps_i d_i}, any signs; readings-only classes 01,02,03,05,06,15,21 identical to Table A) ===')
    W('%-28s %s' % ('', ' '.join('%-3s' % s for s in short)))
    for S in SURVIVORS:
        W('%-28s %s' % (str(S), ' '.join('%-3s' % sym(res[S][(n, 'sf')]) for n in names)))
    W()
    mem = [(S, n, md) for S in SURVIVORS for n in names for md in ('lit', 'sf') if res[S][(n, md)][0] is True
           and not (md == 'sf' and dict((c[0], c[1]) for c in CLASSES)[n] == 'S')]
    W('members found (readings-only classes counted once): %d' % len(mem))
    for S, n, md in mem:
        W('  MEMBER %s  %s  [%s]: %s' % (S, n, md, res[S][(n, md)][1]))
    nn = [(S, n, md) for S in SURVIVORS for n in names for md in ('lit', 'sf') if res[S][(n, md)][0] == 'N']
    W('necessary-only passes: %d' % len(nn))
    for S, n, md in nn:
        W('  NECESSARY-ONLY %s  %s  [%s]: %s' % (S, n, md, res[S][(n, md)][1]))
    W()
    W('=== first failing conjunct per survivor and class (literal mode; sign-free line only when its status differs) ===')
    for S in SURVIVORS:
        W('--- %s' % (S,))
        for n in names:
            r = res[S][(n, 'lit')]
            if r[0] is True:
                W('  %-28s MEMBER: %s' % (n, r[1]))
            else:
                W('  %-28s %s: %s' % (n, 'necessary-only' if r[0] == 'N' else 'fails', r[1]))
            r2 = res[S][(n, 'sf')]
            if r2[0] != r[0]:
                W('       sign-free: %s %s' % (sym(r2), r2[1]))
    open('/Users/trentpalelei/Desktop/Math Ex/experiments/n8/newtypes_membership_v1.out', 'w').write('\n'.join(outp) + '\n')

if __name__ == '__main__':
    main()
