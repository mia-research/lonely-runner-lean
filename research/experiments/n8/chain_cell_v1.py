#!/usr/bin/env python3
"""chain_cell_v1.py  (Task CF, 2026-10-10).  Exact data for Fresh/ChainCell.lean.  Fractions and integers only.
scipy / sympy are used ONLY in section A1 to find Farkas multipliers, and every multiplier is re-checked exactly
(Fractions); if they are missing, A1 is skipped and says so.  No random sampling anywhere; every loop has a move limit.

Part A  the example cell (chain A,B,C,S0,S1,S2):  A0 the sixteen inequalities against the window and capture conditions of
        A, B, C;  A1 which conditions of the whole chain follow from the sixteen;  A2 an interior point and the cascade there;
        A3 NormalForm data;  A4 per state;  A5 per move (displacement);  A6 lap vector mod 8;  A7 axis brackets of the cell.
Part B  population: all 7-subsets of {1..N}, gcd 1, N = 16, 20, 24 (readings; d_min = least).  Per move record; test whether
        the setter word is a function of (ridx vector, sign of each e at R = 1); collisions; separating differences.
Usage:  python3 chain_cell_v1.py            (everything)
        python3 chain_cell_v1.py --dump N   (prints the per-move table of every stopping cascade for N, large)
"""
import sys, math, itertools, time
from fractions import Fraction as F
from math import gcd
from functools import reduce
from collections import defaultdict, Counter

LIMIT = 200                      # move limit on every cascade loop

# ----------------------------------------------------------------------------------------------- exact helpers
def rnd(x):  return math.floor(x + F(1, 2))          # Lean's round: ties go up
def distInt(x): return abs(x - rnd(x))
def inway(d, t): return distInt(d * t) < F(1, 8)
def nextopen(d, t): return (math.ceil(d * t - F(1, 8)) + F(1, 8)) / d
def m8(y): return y - 8 * math.floor(y / 8)                  # residue in [0,8)
def sres8(y): return y - 8 * rnd(y / 8)                       # signed residue, Lean's RealCase.sres8
def idx_(m, d): return rnd(F(d) / m)                          # NormalForm.idx
def e_(m, d): return F(d) / m - idx_(m, d)                    # NormalForm.edev
def ridx_(m, d): return (idx_(m, d) - 1) % 8 + 1             # QuotientReduction.ridx
def quo_(m, d): return (idx_(m, d) - 1) // 8                  # QuotientReduction.quo
def sgn(x): return (x > 0) - (x < 0)

def cascade_exact(ds, limit=LIMIT):
    m = min(ds); t = F(1, 8) / m; hist = [t]; setters = []
    for _ in range(limit):
        w = [d for d in ds if inway(d, t)]
        if not w: return hist, setters, True
        best = max(w, key=lambda d: nextopen(d, t))
        t = nextopen(best, t); hist.append(t); setters.append(best)
    return hist, setters, False

# ----------------------------------------------------------------------------------------------- Part A data
NAMES = ['A', 'B', 'C', 'S0', 'S1', 'S2']
CHAIN = [   # (setter f, lap K, captured {x: lap}, windows {x: lap}), runners 1..7
 (1, 0,   {2: 26},               {3: 83, 4: 90, 5: 92, 6: 156, 7: 162}),
 (2, 26,  {4: 91, 5: 93, 6: 158}, {1: 0, 3: 84, 7: 163}),
 (4, 91,  {7: 164},              {1: 0, 2: 26, 3: 84, 5: 93, 6: 158}),
 (7, 164, {3: 85},               {1: 0, 2: 26, 4: 91, 5: 93, 6: 158}),
 (3, 85,  {6: 159},              {1: 0, 2: 26, 4: 91, 5: 93, 7: 164}),
 (6, 159, {},                    {1: 0, 2: 26, 3: 85, 4: 91, 5: 93, 7: 164}),
]
def state_ineqs(S):
    out = []
    for si, (f, K, cap, win) in enumerate(S):
        for x, L in cap.items():
            c = [0]*7; c[x-1] += 8*K+1; c[f-1] -= 8*L-1; out.append((tuple(c), True, (NAMES[si], x, 'capLo')))
            c = [0]*7; c[f-1] += 8*L+1; c[x-1] -= 8*K+1; out.append((tuple(c), True, (NAMES[si], x, 'capHi')))
        for x, N in win.items():
            c = [0]*7; c[x-1] += 8*K+1; c[f-1] -= 8*N+1; out.append((tuple(c), False, (NAMES[si], x, 'winLo')))
            c = [0]*7; c[f-1] += 8*N+7; c[x-1] -= 8*K+1; out.append((tuple(c), False, (NAMES[si], x, 'winHi')))
    for si in range(len(S) - 1):
        f, K, cap, win = S[si]; nf = S[si+1][0]
        for y, Ly in cap.items():
            if y != nf:
                c = [0]*7; c[y-1] += 8*cap[nf]+1; c[nf-1] -= 8*Ly+1; out.append((tuple(c), False, (NAMES[si], y, 'linkMax')))
    return out
def vec(d):
    c = [0]*7
    for k, v in d.items(): c[k-1] = v
    return tuple(c)
SIXTEEN = [   # the sixteen inequalities of the external statement: c . a > 0 (strict) or >= 0
 ('h8', vec({2:1,1:-207}), True), ('h11', vec({1:671,3:-1}), False), ('h12', vec({4:1,1:-721}), False),
 ('h14', vec({5:1,1:-737}), False), ('h17', vec({1:1255,6:-1}), False), ('h18', vec({7:1,1:-1297}), False),
 ('h25', vec({3:209,2:-673}), False), ('h27', vec({4:209,2:-727}), True), ('h30', vec({2:745,5:-209}), True),
 ('h31', vec({6:209,2:-1263}), True), ('h32', vec({2:115,6:-19}), True), ('h34', vec({2:69,7:-11}), False),
 ('h36', vec({5:729,4:-745}), False), ('h37', vec({6:729,4:-1265}), False), ('h50', vec({7:243,4:-437}), True),
 ('h51', vec({4:1313,7:-729}), True)]
# the nine further conditions of the branch (Lean: QCell.x1 .. x8; x4 and S2 winLo coincide)
EXTRA = [
 ('x1', vec({5:209,2:-743}), True), ('x2', vec({3:1313,7:-679}), True), ('x3', vec({6:681,3:-1271}), True),
 ('x4', vec({3:1273,6:-681}), True), ('x5', vec({3:735,4:-681}), False), ('x6', vec({3:751,5:-681}), False),
 ('x7', vec({3:1319,7:-681}), False), ('x8', vec({6:1319,7:-1273}), False)]
def norm_(c):
    g = 0
    for x in c: g = math.gcd(g, abs(x))
    return tuple(x // g for x in c) if g else c
def holds(c, strict, a):
    v = sum(F(ci) * ai for ci, ai in zip(c, a))
    return v > 0 if strict else v >= 0
P0 = [F(1), F(207193, 1000), F(670863, 1000), F(721147, 1000), F(369279, 500), F(1252081, 1000), F(259453, 200)]

def inQ(a):      # the 32 inequalities of Lean QCell (positivity and 16 + 8)
    return all(x > 0 for x in a) and all(holds(c, s, a) for _, c, s in SIXTEEN + EXTRA)
def in16(a):
    return all(x > 0 for x in a) and all(holds(c, s, a) for _, c, s in SIXTEEN)

def section_A(out):
    P = out
    P("=" * 100); P("PART A.  The example chain cell"); P("=" * 100)
    ALL = state_ineqs(CHAIN)
    ABC = [x for x in ALL if x[2][0] in ('A', 'B', 'C')]
    P("A0. conditions: chain total %d, of A,B,C %d" % (len(ALL), len(ABC)))
    inabc = {norm_(c): (s, t) for c, s, t in ABC}
    ok16 = True
    for nm, c, s in SIXTEEN:
        k = norm_(c); hit = inabc.get(k)
        P("   %-4s %-34s strict=%-5s  = %s" % (nm, str(c), s, hit))
        ok16 &= hit is not None and hit[0] == s
    P("   each of the sixteen is a binding window / capture / link condition of A, B or C (same strictness): %s" % ok16)
    # A1 Farkas
    P("A1. implication of the remaining conditions by the sixteen (+ positivity), exact multipliers:")
    try:
        import numpy as np
        from scipy.optimize import linprog
        import sympy as sp
        POS = [tuple(1 if i == j else 0 for i in range(7)) for j in range(7)]
        G = [c for nm, c, s in SIXTEEN] + POS
        Gs = [s for nm, c, s in SIXTEEN] + [True]*7
        n16 = {norm_(c) for nm, c, s in SIXTEEN}
        def implied(c):
            A = np.array([[float(x) for x in g] for g in G]).T
            r = linprog(np.zeros(A.shape[1]), A_eq=A, b_eq=np.array([float(x) for x in c]),
                        bounds=[(0, None)]*A.shape[1], method='highs')
            if r.status != 0: return None
            sup = [i for i, l in enumerate(r.x) if l > 1e-12]
            M = sp.Matrix([[sp.Rational(G[i][q]) for i in sup] for q in range(7)])
            b = sp.Matrix([sp.Rational(x) for x in c])
            try: sol, params = M.gauss_jordan_solve(b)
            except Exception: return None
            sol = sol.subs({pp: 0 for pp in params})
            lam = {sup[i]: F(int(sol[i].p), int(sol[i].q)) for i in range(len(sup))}
            if any(l < 0 for l in lam.values()): return None
            # exact re-check:  sum lam_i g_i == c
            for q in range(7):
                if sum(lam[i] * G[i][q] for i in lam) != c[q]: return None
            return lam
        nimp = 0; notimp = []
        for c, s, t in ALL:
            if norm_(c) in n16: continue
            lam = implied(c)
            if lam is not None and ((not s) or any(Gs[i] for i in lam)): nimp += 1
            else: notimp.append((t, c, s))
        P("   conditions of the whole chain (74) minus the sixteen's own: implied (exact multipliers): %d ; not implied: %d" % (nimp, len(notimp)))
        for t, c, s in notimp: P("      not implied by the sixteen: %s  %s strict=%s" % (t, c, s))
        P("   (the Lean file proves the implications it uses by linarith: exChain, cell16_fixes)")
    except Exception as ex:
        P("   skipped (%s)" % ex)
    # A2 point
    P("A2. interior point P0 (m = a1 = 1):  " + ", ".join(str(x) for x in P0))
    P("   inQ(P0) = %s ; in16(P0) = %s" % (inQ(P0), in16(P0)))
    hist, setters, stopped = cascade_exact(P0)
    P("   cascade from 1/(8 a1): stopped=%s, moves=%d, setters (runner index) = %s" % (stopped, len(setters), [P0.index(d)+1 for d in setters]))
    laps_end = [math.floor(a * hist[-1]) for a in P0]
    P("   final lap vector floor(a_x t) = %s ; mod 8 = %s ; distinct residues %d of 7" % (laps_end, [l % 8 for l in laps_end], len(set(l % 8 for l in laps_end))))
    P("   complete residue system: %s (residues %s; missing %s)" % (len(set(l % 8 for l in laps_end)) == 7,
        sorted(set(l % 8 for l in laps_end)), sorted(set(range(8)) - set(l % 8 for l in laps_end))))
    # A3 NormalForm
    m = P0[0]
    P("A3. NormalForm data of the seven readings relative to d_min = a1 (static: independent of the state)")
    P("     x   rho                 idx    ridx quo   e                      class at R=1 (NormalForm.clear_one_iff)")
    for i, a in enumerate(P0):
        ix, rx, q, e = idx_(m, a), ridx_(m, a), quo_(m, a), e_(m, a)
        cl = 'blocked' if (rx == 8 or (rx == 1 and e < 0) or (rx == 7 and e > 0)) else 'clear'
        P("     a%d  %-18s %-6d %-4d %-4d %-22s %s" % (i+1, a, ix, rx, q, e, cl))
    rv = [ridx_(m, a) for a in P0]
    P("   ridx vector %s ; residues mod 8 %s ; distinct %d of 7 ; complete (all of 1..7 once) = %s" % (rv, [r % 8 for r in rv], len(set(r % 8 for r in rv)), sorted(r % 8 for r in rv) == [1,2,3,4,5,6,7]))
    # A4 per state
    P("A4. per state: R = 8 m t, and the reading rho*R of each runner (lap = floor / nearest integer of rho*R/8; residue = rho*R mod 8)")
    Rs = [8 * m * t for t in hist]
    allok = True
    for si, t in enumerate(hist):
        R = 8 * m * t
        P("   state %-3s  t = %s   R = %s   R - 1 = %s" % (NAMES[si], t, R, R - 1))
        for i, a in enumerate(P0):
            rho = a / m; y = rho * R
            kind = 'capt' if abs(sres8(y)) < 1 else 'clear'
            lap = rnd(y / 8) if kind == 'capt' else math.floor(y / 8)
            lf = (ridx_(m, a) + e_(m, a)) * R + 8 * (quo_(m, a) * R - math.floor(quo_(m, a) * R))     # lapfreeReading
            ok = (m8(lf) == m8(y)) and (sres8(lf) == sres8(y))
            allok &= ok
            P("      a%d  rho*R = %-26s lap %-4d  residue %-26s dev %-26s %-5s lapfree==%s" % (i+1, y, lap, m8(y), sres8(y), kind, ok))
    P("   lap-free reading (ridx+e)R + 8 frac(quo R) agrees with rho*R mod 8 and in sres8 at all 6 x 7 entries: %s" % allok)
    # A5 moves
    P("A5. per move: setter, lap L, dev = sres8(rho R), Delta R = (1-dev)/rho, R' = (8L+1)/rho; Delta t = nextOpening - t (DispCell.displacement)")
    cum = F(0)
    for si, d in enumerate(setters):
        R = Rs[si]; rho = d / m; y = rho * R
        L = rnd(y / 8); dev = sres8(y); dR = (1 - dev) / rho
        Rn = (8 * L + 1) / rho
        P("   move %d  %s -> %s : setter a%d  L=%d  dev=%s  Delta R=%s  R'=%s  [R'=R+DeltaR: %s]  Delta t=%s [= nextopen - t: %s]" % (
            si+1, NAMES[si], NAMES[si+1], P0.index(d)+1, L, dev, dR, Rn, Rn == R + dR == Rs[si+1], dR / (8 * m), dR / (8*m) == nextopen(d, hist[si]) - hist[si]))
        cum += dR
    P("   total displacement R* - 1 = sum Delta R = %s ; R* = %s ; inside the d_min window [1,7]: %s" % (cum, Rs[-1], 1 <= Rs[-1] <= 7))
    # first move = NormalForm.first_move_r7
    e2 = e_(m, P0[1]); rho2 = P0[1] / m
    P("   first move vs NormalForm.first_move_r7:  1 + (2 - e)/rho = %s  ; R_B = %s ; equal: %s  (ridx_2 = %d, e_2 = %s)" % (1 + (2 - e2) / rho2, Rs[1], 1 + (2 - e2) / rho2 == Rs[1], ridx_(m, P0[1]), e2))
    # lap_start_split
    P("   lap at R = 1 vs lap_start_split (round(rho/8) = quo + round((ridx+e)/8)):")
    for i, a in enumerate(P0):
        lhs = rnd(a / m / 8); rhs = quo_(m, a) + rnd((ridx_(m, a) + e_(m, a)) / 8)
        P("      a%d: %d = %d + %d : %s" % (i+1, lhs, quo_(m, a), rnd((ridx_(m, a) + e_(m, a)) / 8), lhs == rhs))
    # A7 axis brackets
    P("A7. axis brackets: bisection (60 steps, exact dyadic rationals) along each coordinate from P0 inside the cell QCell")
    for x in range(1, 7):
        for sign in (-1, 1):
            lo = F(0); hi = F(1) * sign * P0[x] / 8       # step range: up to P0[x]/8 either way
            def inside(s):
                a = list(P0); a[x] = P0[x] + s; return inQ(a)
            if inside(hi):
                P("   a%d direction %+d: still inside at step %s (bracket not found)" % (x+1, sign, hi)); continue
            for _ in range(60):
                mid = (lo + hi) / 2
                if inside(mid): lo = mid
                else: hi = mid
            a_in = list(P0); a_in[x] = P0[x] + lo
            P("   a%d direction %+d: last inside point (dyadic step %s of the range): idx %d, ridx %d, quo %d, sign e %d" % (x+1, sign, "2^-60 resolved", idx_(m, a_in[x]), ridx_(m, a_in[x]), quo_(m, a_in[x]), sgn(e_(m, a_in[x]))))
    # ridx keys met inside the cell on a deterministic lattice scan of (a2,a5)
    keys = {}
    for i2 in range(0, 201):
        for i5 in range(0, 201):
            a = list(P0); a[1] = F(207) + F(i2, 100) * F(3, 2); a[4] = F(7375, 10) + F(i5, 100) * F(2)
            if inQ(a): keys.setdefault((tuple(ridx_(m, v) for v in a), tuple(sgn(e_(m, v)) for v in a)), a)
    P("   lattice scan of (a2, a5) in QCell (201 x 201 grid, other coordinates at P0): distinct (ridx, sign e) keys met: %d" % len(keys))
    for k, a in sorted(keys.items()): P("      %s  e.g. a2=%s a5=%s" % (k, a[1], a[4]))

# ----------------------------------------------------------------------------------------------- Part B
def cascade_int(D):
    """D: tuple of 7 distinct positive integers sorted ascending (the readings).  Exact integer arithmetic.
    The state is the opening of reading f on lap K, held as (P = 8K+1, f).  Returns (stopped, moves, ties)
    moves: list of (rank, d, L, P, f) where L is the setter's lap at the state (P, f)."""
    m = D[0]; P = 1; f = m; moves = []; ties = 0
    for step in range(LIMIT + 1):
        best = None; tie = False
        for r, d in enumerate(D):
            L = (d * P + 4 * f) // (8 * f)                     # nearest integer to d P/(8 f), ties up
            if abs(d * P - 8 * L * f) < f:                      # captured: |d t - L| < 1/8
                if best is None: best = (r, d, 8 * L + 1, L); tie = False
                else:
                    lhs = (8 * L + 1) * best[1]; rhs = best[2] * d      # opening (8L+1)/d  vs  best[2]/best[1]
                    if lhs > rhs: best = (r, d, 8 * L + 1, L); tie = False
                    elif lhs == rhs: tie = True
        if best is None: return True, moves, ties
        if step == LIMIT: return False, moves, ties
        if tie: ties += 1
        r, d, num, L = best
        moves.append((r, d, L, P, f))
        P = num; f = d
    return False, moves, ties

def coords(D):
    m = D[0]
    return [(ridx_(m, d), quo_(m, d), e_(m, d)) for d in D]

def part_B(out, N, dump=False):
    P = out
    t0 = time.time()
    pop = 0; nostop = []; ties = 0
    recs = {}                       # D -> (word, lapword, moves)
    for D in itertools.combinations(range(1, N + 1), 7):
        if reduce(gcd, D) != 1: continue
        pop += 1
        ok, mv, tie = cascade_int(D)
        if not ok: nostop.append(D); continue
        ties += tie
        recs[D] = (tuple(r for r, d, L, Pn, f in mv), tuple((r, L) for r, d, L, Pn, f in mv), mv)
    P("-" * 100)
    P("B(N=%d).  7-subsets of {1..%d} with gcd 1: %d ; cascades that stop: %d ; not stopped within %d moves: %d ; ties in max opening: %d ; (%d s)" % (
        N, N, pop, len(recs), LIMIT, len(nostop), ties, int(time.time() - t0)))
    # per-move identities, over every stopping cascade
    bad = Counter(); nmoves = Counter(); first_class = Counter(); nfirst = 0
    for D, (w, lw, mv) in recs.items():
        m = D[0]; c = coords(D)
        nmoves[len(mv)] += 1
        for j, (r, d, L, Pn, f) in enumerate(mv):
            R = F(m * Pn, f); rho = F(d, m)
            if L != rnd(rho * R / 8): bad['lap != round(rho R/8)'] += 1          # the lap is derived
            Rn = F(m * (8 * L + 1), d)
            if Rn * rho != 8 * L + 1: bad['R rho != 8L+1'] += 1
            dev = sres8(rho * R)
            if not abs(dev) < 1: bad['setter not blocked'] += 1
            if Rn != R + (1 - dev) / rho: bad['R != R+(1-dev)/rho'] += 1
            if j == 0:
                ridx, quo, e = c[r]
                if L != quo + rnd((ridx + e) / 8): bad['lap_start_split'] += 1
                # NormalForm.isMove_one_classes: offset by class
                if ridx == 8: off = (1 - e) / rho; cl = 'ridx8'
                elif ridx == 1 and e < 0: off = (-e) / rho; cl = 'ridx1,e<0'
                elif ridx == 7 and e > 0: off = (2 - e) / rho; cl = 'ridx7,e>0'
                else: off = None; cl = 'NOT A BLOCKED CLASS'
                first_class[cl] += 1
                if off is None or 1 + off != Rn: bad['first move != class offset'] += 1
    P("   per-move identities over all stopping cascades (violations by kind): %s" % (dict(bad) if bad else "none"))
    P("   [PROVISIONAL: counting tool] number of moves -> number of sets: %s" % sorted(nmoves.items()))
    P("   [PROVISIONAL: counting tool] class of the first setter at R = 1 -> sets: %s" % dict(first_class))
    # grouping
    def key1(D): c = coords(D); return (tuple(x[0] for x in c), tuple(sgn(x[2]) for x in c))
    def key2(D): c = coords(D); return (tuple(x[0] for x in c), tuple(x[1] for x in c), tuple(sgn(x[2]) for x in c))
    def key3(D): c = coords(D); return (tuple(x[0] for x in c), tuple(x[2] for x in c))
    summary = {}
    for nm, kf in (('(ridx, sign e)', key1), ('(ridx, quo, sign e)', key2), ('(ridx, e)', key3)):
        for wn, wi in (('setter ranks', 0), ('setter ranks + laps', 1)):
            g = defaultdict(set)
            for D, rec in recs.items(): g[kf(D)].add(rec[wi])
            nc = sum(1 for v in g.values() if len(v) > 1)
            summary[(nm, wn)] = nc
            P("   key %-20s -> word = %-20s : groups %d, groups with >1 word (collisions) %d" % (nm, wn, len(g), nc))
    # collisions for the main key / main word
    g = defaultdict(lambda: defaultdict(list))
    for D, rec in recs.items(): g[key1(D)][rec[0]].append(D)
    coll = sorted(k for k, v in g.items() if len(v) > 1)
    P("   COLLISIONS of key (ridx, sign e) with word = setter ranks (rank 0 = d_min): %d groups" % len(coll))
    def l1(A, B): return sum(abs(a - b) for a, b in zip(A, B))
    def decision(D, j):
        """data at the move index j of the cascade of D: list of captured runners (rank, lap, opening R) at that state, or the
        blocked-ness of all runners if it stops."""
        m = D[0]; mv = recs[D][2]
        if j < len(mv): r, d, L, Pn, f = mv[j]
        else:
            r = None; Pn, f = (1, m) if not mv else (8 * mv[-1][2] + 1, mv[-1][1])
        R = F(m * Pn, f)
        cap = []
        for rr, dd in enumerate(D):
            y = F(dd, m) * R; dev = sres8(y)
            if abs(dev) < 1:
                L = rnd(y / 8); cap.append((rr, L, F(m * (8 * L + 1), dd)))
        return R, cap
    shown = 0
    sepstats = []
    quo_resolved = 0; need_e = []
    def nz(t): return {i: v for i, v in enumerate(t) if v != 0}
    for k in coll:
        words = g[k]
        sub = defaultdict(set)
        for w, Ds in words.items():
            for D in Ds: sub[key2(D)].add(w)
        if all(len(v) == 1 for v in sub.values()): quo_resolved += 1
        else: need_e.append(k)
    P("   of these collision groups: separated by quo (the key (ridx, quo, sign e) is word-pure on the group): %d ; NOT separated by quo: %d" % (quo_resolved, len(need_e)))
    for k in coll:
        words = g[k]
        best = None
        ws = sorted(words)
        for i in range(len(ws)):
            for jx in range(i + 1, len(ws)):
                for A in words[ws[i]]:
                    for B in words[ws[jx]]:
                        d_ = l1(A, B)
                        if best is None or (d_, A, B) < best[:3]: best = (d_, A, B)
        d_, A, B = best
        wa, wb = recs[A][0], recs[B][0]
        j = 0
        while j < min(len(wa), len(wb)) and wa[j] == wb[j]: j += 1
        Ra, capa = decision(A, j); Rb, capb = decision(B, j)
        diff = tuple(b - a for a, b in zip(A, B))
        ca, cb = coords(A), coords(B)
        sepstats.append(d_)
        show = (k in need_e) or shown < (6 if N <= 20 else 4)
        if show:
            shown += 1
            P("   key ridx=%s signe=%s %s" % (k[0], k[1], "[needs |e|]" if k in need_e else "[quo separates]"))
            P("      words: %s" % {w: len(v) for w, v in words.items()})
            P("      closest pair (L1 = %d): A=%s word %s ; B=%s word %s ; B-A (nonzero) = %s" % (d_, A, wa, B, wb, nz(diff)))
            P("      Delta quo (B-A, nonzero) = %s ; Delta e (B-A, nonzero) = %s" % (nz(tuple(y[1] - x[1] for x, y in zip(ca, cb))), {i: str(v) for i, v in nz(tuple(y[2] - x[2] for x, y in zip(ca, cb))).items()}))
            P("      first divergence at move %d: A: R=%s captured (rank, lap, opening R) %s ; B: R=%s captured %s" % (j + 1, Ra, [(r_, l_, str(o_)) for r_, l_, o_ in capa], Rb, [(r_, l_, str(o_)) for r_, l_, o_ in capb]))
    if coll:
        P("   [PROVISIONAL: counting tool] closest separating pair per collision group: L1 distance (sum of |differences| of the readings) -> groups: %s ; the tally supports the choice of which pairs to inspect, no existence claim" % sorted(Counter(sepstats).items()))
        P("   (every collision group is listed in full by  python3 chain_cell_v1.py --dump %d )" % N)
    # example per-move records
    P("   examples of per-move records (D | move j: rank, d, lap L [derived], R_before, R_after, ridx, quo, e of the setter):")
    cnt = 0
    for D, (w, lw, mv) in sorted(recs.items()):
        if len(mv) >= 3 and cnt < 3:
            cnt += 1; m = D[0]; c = coords(D)
            for jj, (r, d, L, Pn, f) in enumerate(mv):
                P("      %s | %d: rank %d d %d lap %d R %s -> %s  ridx %d quo %d e %s" % (D, jj + 1, r, d, L, F(m * Pn, f), F(m * (8 * L + 1), d), c[r][0], c[r][1], c[r][2]))
    if dump or (N <= 16 and False):
        P("   per-move table:  D | rank d lap R_before R_after ridx quo e")
        for D, (w, lw, mv) in sorted(recs.items()):
            c = coords(D); m = D[0]
            for (r, d, L, Pn, f) in mv:
                P("   %s | %d %d %d %s %s %d %d %s" % (D, r, d, L, F(m * Pn, f), F(m * (8 * L + 1), d), c[r][0], c[r][1], c[r][2]))
    return recs

def main():
    args = sys.argv[1:]
    buf = []
    def P(s): print(s); sys.stdout.flush()
    if args and args[0] == '--dump':
        part_B(P, int(args[1]), dump=True); return
    P("chain_cell_v1.py  Task CF  exact data (Fractions / integers).  LIMIT = %d moves on every cascade loop." % LIMIT)
    section_A(P)
    P("=" * 100); P("PART B.  Population (readings = integers; d_min = least; start 1/(8 d_min))"); P("=" * 100)
    for N in (16, 20, 24): part_B(P, N)

if __name__ == '__main__':
    main()
