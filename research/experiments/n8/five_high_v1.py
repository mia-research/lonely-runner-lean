#!/usr/bin/env python3
"""five_high_v1.py -- Task CB (2026-10-10): five disparities with the second smallest a >= 57 d_min.

Everything that decides a statement is exact (Python Fractions).  Floats appear in ONE place only (section 6, a linear
programme that STEERS the search for rational points; every point it proposes is then verified by the exact cascade).
Every cascade loop has a move limit (MOVE_LIMIT = 500; the run aborts if it is hit).  Nothing is random: every
population is an explicit grid, enumerated exhaustively.  Counts are observations of these grids ONLY (rule 14); no
sentence is a statement about all arrangements.  Theorem names refer to Fresh/FiveHigh.lean (and Fresh/LadderScale.lean,
Fresh/FourDistinct.lean).

Units: d_min = m = 1, so a reading is its ratio rho = d/m, the start is R = 8 m t = 1; a reading rho is in the way at R
iff dist(rho R / 8, Z) < 1/8, and it sets by R -> (8 j + 1) / rho (j = round(rho R / 8)).  a = rho_a is the least of the
four readings (the second smallest disparity).

Sections
  1  the populations (grids stated in the output) with, for each set: moves N, landing R_fix, first setter, a's in-way events
  2  the predictions of the Lean theorems on every set: N <= 20 (four_cascade_fixes_free); a in the way at most twice after
     its first setting; the first return is at +5 moves, one lap up, a is its setter, 3/2 < z/a < 5/3 (return_ratio);
     no second return (second_return_false); the landing is in R <= 7 (five_disparities_rho57)
  3  the candidate mechanisms of the brief (leads 1 and 2), checked exactly on every set
  4  the exact examples with a returning (CE and its neighbours)
  5  hypothesis tests: five readings (E.card <= 4 dropped), the lap condition, the quotient
  6  the arithmetic polytope of a two-cycle chain (float LP steers, the exact cascade decides)
"""
import sys, itertools
from fractions import Fraction as F
from collections import Counter

MOVE_LIMIT = 500
H = F(1, 8)

def rnd(x):
    return (x + F(1, 2)).__floor__()

def inway(rho, R):
    y = rho * R / 8
    return abs(y - rnd(y)) < H

def cascade(E, R0=F(1)):
    """returns (Rs, sets, laps); sets[i] = list of readings tied for the largest next opening at move i"""
    R = R0
    Rs = [R]; sets = []; laps = []; inways = []
    while True:
        inw = [r for r in E if inway(r, R)]
        if not inw:
            break
        nxt = {r: (8 * rnd(r * R / 8) + 1) / r for r in inw}
        best = max(nxt.values())
        sets.append([r for r in inw if nxt[r] == best])
        laps.append({r: rnd(r * R / 8) for r in inw})
        inways.append(tuple(inw))
        R = best
        Rs.append(R)
        if len(sets) >= MOVE_LIMIT:
            raise RuntimeError("move limit hit")
    return Rs, sets, laps, inways

class Stats:
    def __init__(self, name):
        self.name = name
        self.n = 0
        self.Nhist = Counter()
        self.maxN = 0; self.maxN_ex = None
        self.maxR = F(0); self.maxR_ex = None
        self.first_setter = Counter()          # rank of the first setter among the four readings (0 = a), or 'none'
        self.a_events_hist = Counter()         # number of moves at which a is in the way
        self.a_sets_hist = Counter()           # number of moves at which a is a setter
        self.returns = 0; self.return_ex = None
        self.viol = Counter(); self.viol_ex = {}
        self.ret_k_minus_n = Counter(); self.ret_lapup = Counter(); self.ret_a_setter = Counter()
        self.zmin = None; self.zmax = None
        self.over7 = 0
        self.n0_a_sets = 0                     # a sets at move 0 (in the way at R = 1)
        self.n0_a_sets_ret = 0
        self.maxdisp = F(0)                    # max (R_fix - 1) rho_a / 2: displacement in units of the zone width 1/(4a)
        self.lap_ge9_first = 0
        self.first_a_idx = Counter()

def analyse(E, st):
    """E sorted ascending, E[0] = a."""
    a = E[0]
    Rs, sets, laps, inways = cascade(E)
    N = len(sets)
    st.n += 1
    st.Nhist[N] += 1
    if N > st.maxN: st.maxN = N; st.maxN_ex = E
    Rf = Rs[-1]
    if Rf > st.maxR: st.maxR = Rf; st.maxR_ex = E
    if Rf > 7: st.over7 += 1; st.viol['R_fix > 7'] += 1; st.viol_ex.setdefault('R_fix > 7', E)
    d = (Rf - 1) * a / 2
    if d > st.maxdisp: st.maxdisp = d
    # position law: R_fix <= 1 + 2N/rho_a
    if Rf > 1 + 2 * F(N) / a:
        st.viol['R_fix > 1 + 2N/rho'] += 1; st.viol_ex.setdefault('R_fix > 1 + 2N/rho', E)
    if N > 20:
        st.viol['N > 20'] += 1; st.viol_ex.setdefault('N > 20', E)
    if N:
        # rank of the first setter (ties: the smallest rank among the tied setters)
        st.first_setter[min(E.index(r) for r in sets[0])] += 1
    else:
        st.first_setter['none'] += 1
    ev = [i for i in range(N) if a in inways[i]]
    ast = [i for i in range(N) if a in sets[i]]
    st.a_events_hist[len(ev)] += 1
    st.a_sets_hist[len(ast)] += 1
    if ast:
        st.first_a_idx[ast[0]] += 1
        if ast[0] == 0:
            st.n0_a_sets += 1
        if laps[ast[0]][a] >= 9: st.lap_ge9_first += 1
    # in-way events of a after its first setting
    if ast:
        n = ast[0]
        later = [i for i in ev if i > n]
        if len(later) > 1:
            st.viol['a in the way twice after its first setting'] += 1
            st.viol_ex.setdefault('a in the way twice after its first setting', E)
        if later:
            k = later[0]
            st.returns += 1
            if ast[0] == 0: st.n0_a_sets_ret += 1
            if st.return_ex is None: st.return_ex = E
            st.ret_k_minus_n[k - n] += 1
            st.ret_lapup[laps[k][a] - laps[n][a]] += 1
            st.ret_a_setter[a in sets[k]] += 1
            if k - n != 5: st.viol['return not at +5'] += 1; st.viol_ex.setdefault('return not at +5', E)
            if laps[k][a] - laps[n][a] != 1: st.viol['lap not +1'] += 1; st.viol_ex.setdefault('lap not +1', E)
            if a not in sets[k]: st.viol['a not the setter at the return'] += 1; st.viol_ex.setdefault('a not the setter at the return', E)
            z = sets[n + 1][0]
            ratio = z / a
            if not (F(3, 2) < ratio < F(5, 3)):
                st.viol['z/a outside (3/2, 5/3)'] += 1; st.viol_ex.setdefault('z/a outside (3/2, 5/3)', E)
            if z != max(E[1:]): st.viol['z not the largest reading'] += 1; st.viol_ex.setdefault('z not the largest reading', E)
            if st.zmin is None or ratio < st.zmin: st.zmin = ratio
            if st.zmax is None or ratio > st.zmax: st.zmax = ratio
    return N, Rf

def show(st):
    print("population", st.name)
    print("  sets enumerated =", st.n)
    print("  moves N to the fixed point, histogram:", dict(sorted(st.Nhist.items())))
    print("  max N =", st.maxN, "at", [str(x) for x in st.maxN_ex] if st.maxN_ex else None)
    print("  max landing R_fix =", st.maxR, "at", [str(x) for x in st.maxR_ex] if st.maxR_ex else None)
    print("  sets with R_fix > 7:", st.over7)
    print("  max (R_fix - 1) rho_a / 2 (displacement in units of the zone width 1/(4a)) =", st.maxdisp)
    print("  rank of the first setter (0 = a = the slowest of the four; 1,2,3 = the larger readings):", dict(sorted(st.first_setter.items(), key=lambda kv: str(kv[0]))))
    print("  number of moves at which a is in the way:", dict(sorted(st.a_events_hist.items())))
    print("  number of moves at which a is a setter:", dict(sorted(st.a_sets_hist.items())))
    print("  index of the first setting of a:", dict(sorted(st.first_a_idx.items())))
    print("  a sets at move 0 (in the way at R = 1):", st.n0_a_sets, "; of those a is in the way again later:", st.n0_a_sets_ret)
    print("  lap of a at its first setting >= 9:", st.lap_ge9_first)
    print("  a in the way again after its first setting (returns):", st.returns,
          "; k - n:", dict(st.ret_k_minus_n), "; lap rise:", dict(st.ret_lapup), "; a the setter at k:", dict(st.ret_a_setter))
    if st.returns:
        print("  z/a over the returns: min", st.zmin, "max", st.zmax, "; first example:", [str(x) for x in st.return_ex])
    print("  violations of the Lean-proved predictions:", dict(st.viol) if st.viol else 0, st.viol_ex if st.viol_ex else "")

def run(name, it):
    st = Stats(name)
    for E in it:
        analyse(tuple(sorted(E)), st)
    show(st)
    return st

def main():
    print("=== Sections 1-3: populations of four readings (unit m = 1), exhaustive grids ===")
    # P1: a integer 57..200; the other three a + p/2, p = 1..30 (cluster: other readings within [a, a+15])
    def P1():
        for ai in range(57, 201):
            a = F(ai)
            rest = [a + F(p, 2) for p in range(1, 31)]
            for t in itertools.combinations(rest, 3):
                yield (a,) + t
    run("P1: a integer 57..200 (144 values); other three a + p/2, p = 1..30 (C(30,3) = 4060 triples each)", P1())
    # P2: a integer 57..120 and 125..200 step 5; the other three a * (1 + k/20), k = 1..60 (readings in [a, 4a])
    def P2():
        for ai in list(range(57, 121)) + list(range(125, 201, 5)):
            a = F(ai)
            rest = [a * (1 + F(k, 20)) for k in range(1, 61)]
            for t in itertools.combinations(rest, 3):
                yield (a,) + t
    run("P2: a integer 57..120 and 125..200 step 5 (80 values); other three a (1 + k/20), k = 1..60, i.e. in (a, 4a] (C(60,3) = 34220 triples each)", P2())
    # P3: a in {57, 57.5, ..., 90}; others a + p/8, p = 1..40 (the grid of LadderScale section 5)
    def P3():
        for a2 in range(114, 181):
            a = F(a2, 2)
            rest = [a + F(p, 8) for p in range(1, 41)]
            for t in itertools.combinations(rest, 3):
                yield (a,) + t
    run("P3: a in {57, 57.5, ..., 90} (67 values); other three a + p/8, p = 1..40 (9880 triples each)", P3())
    # P4: a integer 57..200 step 1 (144), one reading near a, two far: a + p/4 (p = 1..8), 2a + q (q = 0..9), 3a + r (r = 0..9) -- mixed scales
    def P4():
        for ai in range(57, 201):
            a = F(ai)
            for p in range(1, 9):
                for q in range(0, 10):
                    for r in range(0, 10):
                        yield (a, a + F(p, 4), 2 * a + q, 3 * a + r)
    run("P4: a integer 57..200 (144 values); readings a + p/4 (p = 1..8), 2a + q (q = 0..9), 3a + r (r = 0..9) (800 per a)", P4())

    print()
    print("=== Section 4: exact examples with a returning ===")
    k = F(875, 12)
    CE = tuple(k * x for x in (F(1), F(26, 25), F(533, 500), F(204, 125)))
    Rs, sets, laps, inw = cascade(CE)
    print("  CE (FourDistinct.not_fourDistinctLaw): rho_a =", CE[0], "; moves =", len(sets), "; R_fix =", Rs[-1])
    print("  setters per move:", [[str(x) for x in s] for s in sets])
    print("  in the way per move:", [[str(x) for x in s] for s in inw])
    print("  laps of a at the moves where it is in the way:", [(i, laps[i][CE[0]]) for i in range(len(sets)) if CE[0] in laps[i]])
    print("  z / a =", CE[3] / CE[0], "; the Lean window (3/2, 5/3) contains it:", F(3, 2) < CE[3] / CE[0] < F(5, 3))
    # scaled copies of CE ratios: the cascade depends on a through the start only (a t0 = rho_a / 8)
    print("  CE ratios (1, 26/25, 533/500, 204/125) with the start R = 1 and rho_a = 875/12 * s for s = 1, 2, 3, 4 (the lap of a at the start rises):")
    for s in (1, 2, 3, 4):
        E = tuple(F(875, 12) * s * x for x in (F(1), F(26, 25), F(533, 500), F(204, 125)))
        Rs, sets, laps, inw = cascade(E)
        ev = [i for i in range(len(sets)) if E[0] in inw[i]]
        print("   s =", s, ": rho_a =", E[0], "; moves", len(sets), "; R_fix", Rs[-1], "; a in the way at moves", ev)

    print()
    print("=== Section 5: hypothesis tests ===")
    # 5a: E.card <= 4 dropped: five readings (six disparities).  max moves, a events, grid p/2, 1..10, K = 5 (exhaustive), a >= 3
    for (Q, M, K) in ((2, 10, 5), (4, 8, 5), (2, 14, 6)):
        n = 0; maxN = 0; ex = None; aev = Counter(); over7 = 0; over20 = 0
        for E in itertools.combinations([F(p, Q) for p in range(Q, M * Q + 1)], K):
            n += 1
            Rs, sets, laps, inw = cascade(E)
            N = len(sets)
            if N > maxN: maxN = N; ex = E
            aev[sum(1 for i in range(N) if E[0] in inw[i])] += 1
            if Rs[-1] > 7: over7 += 1
            if N > 20: over20 += 1
        print("  %d readings p/%d, 1..%d (exhaustive, %d sets; readings from rho = 1): max N = %d at %s ; moves > 20: %d ; R_fix > 7: %d ; a in the way at k moves, k histogram %s" % (K, Q, M, n, maxN, [str(x) for x in ex], over20, over7, dict(sorted(aev.items()))))
    # 5b: the lap at the first setting against rho_a (population P3 grid): which laps occur, with returns
    lapret = Counter(); lapall = Counter()
    for a2 in range(114, 181):
        a = F(a2, 2)
        rest = [a + F(p, 8) for p in range(1, 41)]
        for t in itertools.combinations(rest, 3):
            E = (a,) + t
            Rs, sets, laps, inw = cascade(E)
            ast = [i for i in range(len(sets)) if a in sets[i]]
            if ast:
                lapall[laps[ast[0]][a]] += 1
    print("  P3 grid: lap of a at its first setting (all laps present, counts):", dict(sorted(lapall.items())))
    print("  (laps 9 and >= 11 are the laps at which LadderScale.LapCond fails; return_ratio and second_return_false use no lap hypothesis.)")

    # 5c: 'a least' dropped: a reading that is NOT the least sets and is in the way again after fewer than four moves in between
    cnt = 0; ex = None
    for E in itertools.combinations([F(p, 2) for p in range(2, 25)], 4):
        Rs, sets, laps, inw = cascade(E)
        for n in range(len(sets)):
            for r in sets[n]:
                if r == E[0]: continue
                for kk in range(n + 1, len(inw)):
                    if r in inw[kk]:
                        if kk - n < 5:
                            cnt += 1
                            if ex is None: ex = (E, r, n, kk, [[str(x) for x in s] for s in sets[:kk + 1]])
                        break
    print("  5c: grid p/2, 2..12, K = 4 (exhaustive, readings from rho = 1): settings by a NON-least reading r with a first return at k - n < 5: %d ; first example (E, r, n, k, setters): %s" % (cnt, ex))
    print("      so the +5 law of return_ratio needs 'a least' for the statement, not only for the proof.")

    print()
    print("=== Section 6: the arithmetic polytope of one return cycle and of two consecutive cycles ===")
    try:
        import numpy as np
        from scipy.optimize import linprog
    except Exception as ex:
        print("  scipy unavailable: section skipped (", ex, ")"); return
    e = 1 / 8
    def rows_for(j, A, B, C, A2, order):
        J = j + 1
        rows = []; rhs = []
        def add(c, k): rows.append(c); rhs.append(k)
        add([-1, 0, 0], -(A - e) / (j + e)); add([1, 0, 0], (A + e) / (j + e))
        add([(B - e) / (A + e), -1, 0], 0); add([-(B + e) / (A + e), 1, 0], 0)
        add([0, (C - e) / (B + e), -1], 0); add([0, -(C + e) / (B + e), 1], 0)
        add([-1, 0, (A2 - e) / (C + e)], 0); add([1, 0, -(A2 + e) / (C + e)], 0)
        add([-1, 0, 0], -(A2 + e) / (J + e)); add([1, 0, 0], (A2 + e) / (J - e))
        add([0, -1, 0], -1); add([0, 0, -1], -1); add([-1, 1, 0], 0); add([-1, 0, 1], 0)
        add([0, 1, -1], 0) if order == 0 else add([0, -1, 1], 0)
        return rows, rhs
    def feas(parts):
        rows = []; rhs = []
        for (j, tup, order) in parts:
            r, b = rows_for(j, *tup, order); rows += r; rhs += b
        M = np.array(rows, float); b = np.array(rhs, float)
        nrm = np.linalg.norm(M, axis=1)
        r = linprog(c=[0, 0, 0, -1], A_ub=np.hstack([M, nrm.reshape(-1, 1)]), b_ub=b, bounds=[(None, None)] * 3 + [(0, 1)], method='highs')
        return r.x if r.status == 0 and r.x[3] > 1e-9 else None
    def tuples(j):
        out = []
        for A in range(j + 1, 3 * j + 3):
            for B in range(j + 1, A + 1):
                for C in range(j + 1, A + 1):
                    for A2 in (A + 1, A + 2, A + 3, A + 4):
                        if not ((8 * A - 1) * (8 * j + 7) < (8 * A2 + 1) * (8 * j + 1)): continue
                        if not ((8 * B - 1) * (8 * C - 1) * (8 * A2 - 1) < (8 * A + 1) * (8 * B + 1) * (8 * C + 1)): continue
                        for order in (0, 1):
                            x = feas([(j, (A, B, C, A2), order)])
                            if x is not None: out.append(((j, (A, B, C, A2), order), x))
        return out
    JMAX = 40
    P = {}
    tot_pts = 0; tot_ok = 0; bad = []
    realised = []   # (j, E, N, events of a, laps)
    for j in range(8, JMAX + 2):
        P[j] = tuples(j)
        okc = 0
        for (t, x) in P[j]:
            # exact check: rationalise the LP point, run the exact cascade from t = j + 1/8 (a = 1 normalised: a sits at its opening),
            # with rho_a = 8 (j + 1/8) so that R = 1 is t = j + 1/8 in these units.  Moves are numbered from this start:
            # the predicted pattern is z, p, q, z at moves 0..3 and a in the way (and setting) at move 4.
            z, p, q = (F(float(v)).limit_denominator(10 ** 7) for v in x[:3])
            Eabs = (F(1), p, q, z)
            rho_a = 8 * (j + H)
            Er = tuple(rho_a * r for r in Eabs)
            Rs, sets, laps, inw = cascade(Er)
            N = len(sets)
            ev = [i for i in range(N) if Er[0] in inw[i]]
            tot_pts += 1
            ok = (N >= 5 and len(ev) >= 1 and ev[0] == 4 and Er[0] in sets[4])
            if ok:
                tot_ok += 1; okc += 1
                realised.append((j, Er, N, ev, [laps[i][Er[0]] for i in ev]))
            else:
                bad.append((j, t[1], t[2], N, ev))
        print("  j = %2d : return-cycle tuples (A,B,C,A') with a nonempty arithmetic polytope: %d ; exact cascade from t = j + 1/8 has a in the way and setting at move 4: %d" % (j, len(P[j]), okc))
    print("  total polytope points checked exactly:", tot_pts, "; with the predicted return (a in the way at move 4, as setter):", tot_ok)
    print("  the polytope keeps only the lap windows of z, p, q and a; it drops the conditions that the other readings are clear or smaller-opening at each move,")
    print("  so a point of it need not realise the cycle: points not realised:", len(bad), "; first five:", bad[:5])
    if realised:
        print("  realised returns: j = lap of a before the return; N = moves to the fixed point from t = j + 1/8; events = moves at which a is in the way")
        for (j, Er, N, ev, lp) in realised[:40]:
            ratio = Er[3] / Er[0]
            print("   j=%d N=%d a in the way at %s laps %s ; z/a = %s (in (3/2,5/3): %s)" % (j, N, ev, lp, ratio, F(3, 2) < ratio < F(5, 3)))
        viol = [r for r in realised if len(r[3]) != 1 or r[4] != [r[0] + 1] or not (F(3, 2) < r[1][3] / r[1][0] < F(5, 3))]
        print("  realised returns violating (one event of a, lap j + 1, z/a in (3/2, 5/3)):", len(viol), viol[:3])
        print("  realised returns, max N from the start t = j + 1/8:", max(r[2] for r in realised), "; with a in the way a second time: ", sum(1 for r in realised if len(r[3]) > 1))
    # chain of two consecutive cycles (the same z, p, q at starts j and j + 1)
    chain = 0
    for j in range(9, JMAX + 1):
        for (t1, _) in P[j]:
            for (t2, _) in P[j + 1]:
                if feas([t1, t2]) is not None:
                    chain += 1; print("  two-cycle chain feasible:", t1, t2)
    print("  pairs (cycle at j, cycle at j + 1) with a common (z, p, q) in both arithmetic polytopes, j = 9 .. %d: %d" % (JMAX, chain))
    print("  (second_return_false [L] proves no such pair exists for any j: z/a in (3/2, 5/3) is not within 1/4 of an integer.)")

if __name__ == "__main__":
    main()
