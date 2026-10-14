#!/usr/bin/env python3
"""five_low_v1.py -- Task CA (2026-10-10): five disparities, second smallest a below five times d_min.

Everything is exact (Python Fractions).  No floats decide anything.  Every cascade loop has a move limit (200; the run aborts
if it is hit).  Nothing is random: every population is an explicit grid, enumerated exhaustively.  Counts are observations of
these grids ONLY; no sentence below is a statement about all arrangements (rule 14).

Units: d_min = m = 1.  A reading is its ratio rho = d/m, the start is R = 8 m t = 1, a reading rho is in the way at R iff
dist(rho R / 8, Z) < 1/8, and it sets by R -> (8 j + 1)/rho (j = round(rho R / 8)).  E = the four readings other than d_min,
a = min E, S = E minus {a} (three readings).  Theorem names refer to Fresh/FiveLow.lean (and LadderScale, FiveReach,
FourDistinct).

What each check observes (the proof's steps, FiveLow.reach_four_low):
  C1  R_fix(E) <= (9/7)^7 and <= 7                       (statement of reach_four_low / five_disparities_low)
  C2  first lonely R of S, R_S1 <= 729/343               (FiveReach.reach_three, the covering step)
  C3  case A (a never a setter): R_fix(E) == R_S1         (isMove_erase_of_not_setter: E-moves are S-moves)
  C4  case B (a sets): the states before a's first setting equal the S-cascade states; a*R_k > 7; R_k <= R_S1
  C5  case B: lap of a = 1 and landing 9/a when a < 5      (landing_lap_one)
  C6  case B: a is never in the way after its setting      (FourDistinct.slowest_of_four_never_returns_lap)
  C7  case B: R_fix(E) == first lonely of S from the landing t1, and R_fix <= (729/343) t1  (second use of reach_three)
  C8  a in the way but not the setter: count             (needed? the proof does not need it: reported)
  C9  a sets more than once: count                        (min_sets_once)
  C10 case B only when a > 2401/729                       (reach_four_small: threshold 7/(729/343))
"""
import sys, itertools, time
from fractions import Fraction as F
from collections import Counter

MOVE_LIMIT = 200
B3 = F(729, 343)
B7 = F(9, 7) ** 7
THR = F(2401, 729)

def rnd(x):
    return (x + F(1, 2)).__floor__()

def inway(rho, R):
    y = rho * R / 8
    return abs(y - rnd(y)) < F(1, 8)

def cascade(E, R0=F(1)):
    """Returns (states, moves).  moves[i] = (setters at max, {reading: lap} of all in the way)."""
    R = R0
    Rs = [R]
    moves = []
    while True:
        inw = [r for r in E if inway(r, R)]
        if not inw:
            break
        laps = {r: rnd(r * R / 8) for r in inw}
        nxt = {r: (8 * laps[r] + 1) / r for r in inw}
        best = max(nxt.values())
        moves.append(([r for r in inw if nxt[r] == best], laps))
        R = best
        Rs.append(R)
        if len(moves) >= MOVE_LIMIT:
            raise RuntimeError("move limit hit")
    return Rs, moves

class Stats:
    def __init__(self, name):
        self.name = name
        self.n = 0
        self.maxR = F(0); self.maxR_E = None
        self.over7 = 0; self.overB7 = 0
        self.maxRS1 = F(0)
        self.caseA = 0; self.caseB = 0
        self.A_viol = 0; self.A_ex = None
        self.B_prefix_viol = 0; self.B_gt7_viol = 0; self.B_le_RS1_viol = 0
        self.B_lap1_viol = 0; self.B_lap1_ex = None
        self.B_return_viol = 0; self.B_return_ex = None
        self.B_post_viol = 0; self.B_post_ex = None
        self.B_second_viol = 0
        self.inway_nonsetter = 0; self.inway_nonsetter_ex = None
        self.multi_set = 0
        self.minA_B = None; self.minA_B_E = None
        self.B_ratio_max = F(0); self.B_ratio_E = None   # R_fix / t1
        self.B_landing_ratio_max = F(0)                  # R_fix * a / 9  (= R_fix / (9/a))
        self.maxN = 0; self.maxN_E = None
        self.Ncount = Counter()
        self.firstsetter = Counter()
        self.words = Counter()
        self.caseB_ex_max = None
        self.pos_bound_fail = 0   # N > 3 rho_a  (position_of_moves route: N m <= 3 a fails)
        self.pos_bound_ex = None
        self.a_below_thr_B = 0

    def add(self, E):
        a = E[0]; S = E[1:]
        self.n += 1
        Rs, mv = cascade(E)
        RsS, mvS = cascade(S)
        RS1 = RsS[-1]
        N = len(mv)
        self.Ncount[N] += 1
        if N > self.maxN: self.maxN = N; self.maxN_E = E
        if Rs[-1] > self.maxR: self.maxR = Rs[-1]; self.maxR_E = E
        if Rs[-1] > 7: self.over7 += 1
        if Rs[-1] > B7: self.overB7 += 1
        if RS1 > self.maxRS1: self.maxRS1 = RS1
        if F(N) > 3 * a:
            self.pos_bound_fail += 1
            if self.pos_bound_ex is None: self.pos_bound_ex = (E, N)
        # setters
        aset = [i for i, (st, _) in enumerate(mv) if a in st]
        ainw = [i for i in range(N) if inway(a, Rs[i])]
        if len(aset) > 1: self.multi_set += 1
        if ainw and (not aset or aset[0] != ainw[0]):
            self.inway_nonsetter += 1
            if self.inway_nonsetter_ex is None: self.inway_nonsetter_ex = E
        # first setter rank (E sorted: a < b < c < d)
        if N > 0:
            names = {a: 'a', S[0]: 'b', S[1]: 'c', S[2]: 'd'}
            self.firstsetter[''.join(sorted(names[x] for x in mv[0][0]))] += 1
        if not aset:
            self.caseA += 1
            if Rs[-1] != RS1:
                self.A_viol += 1
                if self.A_ex is None: self.A_ex = (E, Rs[-1], RS1)
        else:
            self.caseB += 1
            k = aset[0]
            Rk = Rs[k]
            if a <= THR:
                self.a_below_thr_B += 1
            if self.minA_B is None or a < self.minA_B: self.minA_B = a; self.minA_B_E = E
            # C4
            if k >= len(RsS) or Rs[:k + 1] != RsS[:k + 1]:
                self.B_prefix_viol += 1
            if not a * Rk > 7: self.B_gt7_viol += 1
            if not Rk <= RS1: self.B_le_RS1_viol += 1
            # C5
            lap = mv[k][1][a]
            t1 = Rs[k + 1]
            if a < 5:
                if not (lap == 1 and t1 == F(9) / a):
                    self.B_lap1_viol += 1
                    if self.B_lap1_ex is None: self.B_lap1_ex = (E, lap, t1)
            # C6
            if any(inway(a, Rs[j]) for j in range(k + 1, len(Rs))):
                self.B_return_viol += 1
                if self.B_return_ex is None: self.B_return_ex = E
            # C7
            RsS2, _ = cascade(S, t1)
            if RsS2[-1] != Rs[-1]:
                self.B_post_viol += 1
                if self.B_post_ex is None: self.B_post_ex = (E, Rs[-1], RsS2[-1])
            if not Rs[-1] <= B3 * t1: self.B_second_viol += 1
            ratio = Rs[-1] / t1
            if ratio > self.B_ratio_max: self.B_ratio_max = ratio; self.B_ratio_E = E
            lr = Rs[-1] * a / 9
            if lr > self.B_landing_ratio_max: self.B_landing_ratio_max = lr
            # word: S-setters before a, a, S-setters after
            names = {a: 'a', S[0]: 'b', S[1]: 'c', S[2]: 'd'}
            w = ''.join(''.join(sorted(names[x] for x in st)) for st, _ in mv)
            self.words[w] += 1
            if self.caseB_ex_max is None or Rs[-1] > self.caseB_ex_max[0]:
                self.caseB_ex_max = (Rs[-1], E, w, [str(x) for x in Rs], [mv[i][1][mv[i][0][0]] for i in range(N)])

    def report(self):
        print("population", self.name, ": sets =", self.n)
        print("  C1  max R_fix(E) =", self.maxR, "attained at", [str(x) for x in self.maxR_E],
              "; count R_fix > 7:", self.over7, "; count R_fix > (9/7)^7:", self.overB7)
        print("  C2  max first lonely R of S (three readings) =", self.maxRS1, "; 729/343 =", B3, "; exceeded:", self.maxRS1 > B3)
        print("  C3  case A (a never a setter) sets =", self.caseA, "; R_fix(E) != R_S1 in case A:", self.A_viol, self.A_ex)
        print("      case B (a sets) sets =", self.caseB, "; a sets more than once:", self.multi_set)
        print("  C4  case B: prefix differs from the S-cascade:", self.B_prefix_viol, "; sets with a R_k <= 7 (a would not be in the way):",
              self.B_gt7_viol, "; sets with R_k > R_S1:", self.B_le_RS1_viol)
        print("  C5  case B, a < 5: lap != 1 or landing != 9/a:", self.B_lap1_viol, self.B_lap1_ex)
        print("  C6  case B: a in the way again after its setting:", self.B_return_viol, self.B_return_ex)
        print("  C7  case B: R_fix != first lonely of S from t1:", self.B_post_viol, self.B_post_ex,
              "; R_fix > 729/343 * t1:", self.B_second_viol)
        print("      case B: max R_fix / t1 =", self.B_ratio_max, "at", [str(x) for x in self.B_ratio_E] if self.B_ratio_E else None,
              "; max R_fix a/9 =", self.B_landing_ratio_max)
        print("  C8  a in the way but not the first setter:", self.inway_nonsetter, self.inway_nonsetter_ex)
        print("  C10 smallest a with case B:", self.minA_B, [str(x) for x in self.minA_B_E] if self.minA_B_E else None,
              "; threshold 2401/729 =", THR, "; case-B sets with a <= threshold:", self.a_below_thr_B)
        print("  moves: max N =", self.maxN, [str(x) for x in self.maxN_E] if self.maxN_E else None,
              "; histogram", dict(sorted(self.Ncount.items())))
        print("  position-law route (needs N <= 3 rho_a): sets with N > 3 rho_a =", self.pos_bound_fail, self.pos_bound_ex)
        print("  first setter (a<b<c<d):", dict(self.firstsetter))
        if self.caseB_ex_max:
            R, E, w, Rs, laps = self.caseB_ex_max
            print("  case B maximum R_fix =", R, "at", [str(x) for x in E], "word", w, "laps", laps)
            print("      states", Rs)
        top = self.words.most_common(8)
        print("  case B words (most common 8 of %d distinct):" % len(self.words), top)
        sys.stdout.flush()

def grid_values(Q, lo, hi):
    return [F(p, Q) for p in range(int(lo * Q), int(hi * Q) + 1)]

def population(name, a_vals, S_vals_fn):
    st = Stats(name)
    for a in a_vals:
        rest = S_vals_fn(a)
        for t in itertools.combinations(rest, 3):
            st.add((a,) + t)
    st.report()
    return st

def main():
    t0 = time.time()
    print("=== Section 1: exhaustive grids, E = (a, b, c, d) in units d_min = 1, 1 <= a < 5 ===")
    # G1: all readings p/2, a in [1, 5), others in (a, 40]
    population("G1: p/2, a in [1, 9/2], b<c<d in (a, 40]",
               [F(p, 2) for p in range(2, 10)],
               lambda a: [F(p, 2) for p in range(2, 81) if F(p, 2) > a])
    print("  elapsed", round(time.time() - t0, 1), "s")
    # G2: p/4, a in [13/4, 19/4] (the range where a can matter), others in (a, 24]
    population("G2: p/4, a in [13/4, 19/4], b<c<d in (a, 24]",
               [F(p, 4) for p in range(13, 20)],
               lambda a: [F(p, 4) for p in range(13, 97) if F(p, 4) > a])
    print("  elapsed", round(time.time() - t0, 1), "s")
    # G3: p/12, a in [10/3, 5), others in (a, 9]
    population("G3: p/12, a in [40/12, 59/12], b<c<d in (a, 9]",
               [F(p, 12) for p in range(40, 60)],
               lambda a: [F(p, 12) for p in range(40, 109) if F(p, 12) > a])
    print("  elapsed", round(time.time() - t0, 1), "s")
    # G4: a below the threshold 2401/729 = 3.29..: finer, to see case B never occurs there
    population("G4: p/12, a in [1, 39/12], b<c<d in (a, 9]",
               [F(p, 12) for p in range(12, 40, 3)],
               lambda a: [F(p, 12) for p in range(12, 109) if F(p, 12) > a])
    print("  elapsed", round(time.time() - t0, 1), "s")

def returns_after_setting(E, x):
    """x sets at some move and is in the way at a later state."""
    Rs, mv = cascade(E)
    sets = [i for i, (st, _) in enumerate(mv) if x in st]
    if not sets: return None
    k = sets[0]
    return any(inway(x, Rs[j]) for j in range(k + 1, len(Rs)))

def show_cascade(label, E):
    Rs, mv = cascade(E)
    names = {}
    for r, nm in zip(sorted(E), "abcde"):
        names[r] = nm
    print("  %s: readings %s" % (label, [str(x) for x in sorted(E)]))
    print("      states R:", [str(x) for x in Rs])
    print("      setters (reading, lap):", [[(names[r], str(r), mv[i][1][r]) for r in mv[i][0]] for i in range(len(mv))])
    return Rs, mv

def coordinate_ascent(E0, steps):
    """Deterministic coordinate ascent on R_fix over rational readings; a = min kept in [1, 5); distinct; max <= 80."""
    E = list(E0)
    def val(E):
        return cascade(E)[0][-1]
    best = val(E)
    for step in steps:
        improved = True
        while improved:
            improved = False
            for i in range(len(E)):
                for sgn in (1, -1):
                    E2 = list(E); E2[i] = E2[i] + sgn * step
                    if len(set(E2)) < len(E2) or min(E2) < 1 or min(E2) >= 5 or max(E2) > 80: continue
                    v = val(E2)
                    if v > best:
                        E, best, improved = E2, v, True
    return best, sorted(E)

def section2():
    print()
    print("=== Section 2: hypothesis tests (exact) ===")
    # 2.1  a least: replace the distinguished reading a by an arbitrary x of E
    tot = Counter(); viol = Counter(); ex = {}
    vals = [F(p, 2) for p in range(2, 31)]
    for E in itertools.combinations(vals, 4):
        for idx, x in enumerate(E):
            r = returns_after_setting(E, x)
            if r is None: continue
            key = "least" if idx == 0 else "not least"
            tot[key] += 1
            if r:
                viol[key] += 1
                ex.setdefault(key, (E, x))
    print("  2.1  readings p/2, 1..15, all 4-subsets (%d sets): x sets, and is in the way again later" % len(list(itertools.combinations(vals, 4))))
    for key in ("least", "not least"):
        print("       x %-9s: sets of x = %d ; x in the way again afterwards = %d ; example %s" % (key, tot[key], viol[key],
              ([str(y) for y in ex[key][0]], str(ex[key][1])) if key in ex else None))
    # 2.2  E.card <= 4 dropped
    print("  2.2  five readings (E.card = 5), a < 5, readings p/2, 1..16 (exhaustive):")
    n = 0; maxR = F(0); mE = None; over7 = 0; ret = 0; retex = None; multi = 0
    vals5 = [F(p, 2) for p in range(2, 33)]
    for E in itertools.combinations(vals5, 5):
        if E[0] >= 5: break
        n += 1
        Rs, mv = cascade(E)
        if Rs[-1] > maxR: maxR = Rs[-1]; mE = E
        if Rs[-1] > 7: over7 += 1
        a = E[0]
        r = returns_after_setting(E, a)
        if r:
            ret += 1
            if retex is None: retex = E
    print("       sets = %d ; max R_fix = %s at %s ; R_fix > 7: %d ; a in the way again after setting: %d %s" %
          (n, maxR, [str(x) for x in mE], over7, ret, [str(x) for x in retex] if retex else None))
    E5 = [F(6441, 1000), F(7001, 1000), F(627, 125), F(1951, 500), F(1421, 250)]
    Rs, mv = cascade(E5)
    print("       E_five of FiveReach (a = %s < 5): moves = %d, R_fix = %s" % (min(E5), len(mv), Rs[-1]))
    # 2.3  the lap hypothesis dropped
    k = F(875, 12)
    CE = [k * x for x in (F(1), F(26, 25), F(533, 500), F(204, 125))]
    Rs, mv = cascade(CE)
    a = min(CE)
    aset = [(i, mv[i][1][a]) for i in range(len(mv)) if a in mv[i][0]]
    print("  2.3  CE of FourDistinct (rho_a = %s, outside rho_a < 24353/729): a sets at (move, lap) = %s ; R_fix = %s ; a in the way again after its first setting: %s" %
          (a, aset, Rs[-1], returns_after_setting(CE, a)))
    # 2.4  threshold example: a just above 2401/729 sets
    print("  2.4  the threshold 2401/729 = %s (= 7/(729/343)); an exact set with a just above it that sets:" % THR)
    E = (F(331, 100), F(17, 4), F(273, 50), F(701, 100))
    Rs, mv = show_cascade("a = 331/100", E)
    print("      a R at the state before its setting:", [str(E[0] * Rs[i]) for i in range(len(mv)) if E[0] in mv[i][0]],
          "; landing 9/a =", F(9) / E[0], "; R_fix =", Rs[-1])
    # 2.5  sup lower bound found by deterministic coordinate ascent (exact values; not a supremum claim)
    print("  2.5  deterministic coordinate ascent on R_fix over a < 5 (exact value of the set found; a lower bound for the supremum over this family only):")
    starts = [(F(331, 100), F(17, 4), F(273, 50), F(701, 100)), (F(4), F(5), F(6), F(15, 2)), (F(9, 2), F(21, 4), F(29, 4), F(25, 2))]
    for E0 in starts:
        best, E = coordinate_ascent(E0, [F(1, 8), F(1, 32), F(1, 128), F(1, 512), F(1, 2048)])
        print("       start %s -> R_fix = %s (%s) at %s" % ([str(x) for x in E0], best, float(best), [str(x) for x in E]))

if __name__ == "__main__":
    main()
    section2()
