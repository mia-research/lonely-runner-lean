#!/usr/bin/env python3
"""ladder_scale_v1.py -- Task BE (2026-10-09): the lap of the slowest reading against its ratio to d_min, the chain
argument for four readings, and what the large-quotient regime does.

Everything is exact (Python Fractions).  No floats decide anything.  Every cascade loop has a move limit (500; the run
aborts if it is hit).  Nothing is random: every population is an explicit grid, enumerated exhaustively.  Counts are
observations of these grids ONLY; no sentence below is a statement about all arrangements (rule 14).

Units: d_min = m = 1, so a reading is its ratio rho = d/m, the start is R = 8 m t = 1, and the cascade acts on R:
a reading rho is in the way at R iff dist(rho R / 8, Z) < 1/8; it sets by R -> (8 j + 1) / rho (j = round(rho R / 8)).
Theorem names refer to Fresh/LadderScale.lean (and Fresh/FourDistinct.lean, Fresh/Ladder5.lean).

Sections
  1  lap of the slowest reading a at its first setting against rho_a (the relation proved in Lean: lap_lt_of_ratio_bound,
     lap_le_eight_of_ratio_bound, and the additive time bound R_n < 1 + 2 n / rho_a)
  2  the chain facts for four readings: a sets in the first 8 moves; a sets once; the cascade ends within 15 moves
     (window_has_setter, min_sets_once, four_cascade_fixes)
  3  the additive position bound R_fix < 1 + 2 k / rho_a and the resulting range rho_a >= 5 (reach_four_of_ratio, five_disparities_of_ratio)
  4  where the range stops: rho_a < 5 (position law) and rho_a >= 57 (lap hypothesis); exact data and the exact examples
  5  hypothesis audit: what happens to 'a sets once' when the lap condition is dropped (exact first-return examples)
  6  five readings: the first return of a passes through all four others; a returns (exact examples), the count is not bounded
     by these laws
"""
import sys, itertools
from fractions import Fraction as F
from collections import Counter

MOVE_LIMIT = 500

def rnd(x):
    """round half up, exact (Lean's round: floor(x + 1/2))."""
    return (x + F(1, 2)).__floor__()

def inway(rho, R):
    """rho in the way at R: |rho R / 8 - round| < 1/8."""
    y = rho * R / 8
    return abs(y - rnd(y)) < F(1, 8)

def cascade(E, R0=F(1)):
    """E: list of readings (units of m).  Returns (R list, setters list (list of lists, ties kept), laps list)."""
    R = R0
    Rs = [R]
    sets = []
    laps = []
    while True:
        inw = [r for r in E if inway(r, R)]
        if not inw:
            break
        nxt = {}
        for r in inw:
            j = rnd(r * R / 8)
            nxt[r] = (8 * j + 1) / r
        best = max(nxt.values())
        sets.append([r for r in inw if nxt[r] == best])
        laps.append({r: rnd(r * R / 8) for r in inw})
        R = best
        Rs.append(R)
        if len(sets) >= MOVE_LIMIT:
            raise RuntimeError("move limit hit")
    return Rs, sets, laps

def analyse(E):
    a = min(E)
    Rs, sets, laps = cascade(E)
    k = len(sets)
    a_idx = [i for i, s in enumerate(sets) if a in s]
    wsum = sum(F(1) / min(s) for s in sets)   # sum of 1/rho over the (least) setter of each move
    wsum_a = sum(F(1) / a for _ in sets)
    return dict(a=a, Rs=Rs, sets=sets, laps=laps, k=k, a_idx=a_idx, Rfix=Rs[-1], wsum=wsum, wsum_a=wsum_a)

def pop_grid(Q, M, K):
    vals = [F(p, Q) for p in range(Q, M * Q + 1)]
    return itertools.combinations(vals, K)

def section1_4(name, sets_iter):
    n = 0
    maxk = 0; maxR = F(0); maxR_set = None
    firstA_max = -1
    a_multi = 0; a_multi_ex = None; a_none = 0
    lap_viol = 0; lap_viol_ex = None   # rho_a < 57 and lap of a at first setting > 8
    add_viol = 0; add_viol_ex = None   # R_fix >= 1 + 2k/rho_a  (should never happen)
    n_add_viol = 0
    maxlap_by_rho = {}
    k_by_class = Counter()
    over7_hi = 0   # rho_a >= 5 and R_fix > 7
    over7_lo = 0; over7_lo_ex = None
    maxR_lo = F(0); maxR_hi = F(0)
    k_ge_rho = 0
    win_viol = 0; win_viol_ex = None; max_slack = F(0); max_slack_set = None
    for E in sets_iter:
        d = analyse(E)
        n += 1
        a = d['a']; k = d['k']
        if k > maxk: maxk = k
        if d['Rfix'] > maxR: maxR = d['Rfix']; maxR_set = E
        # window_has_setter: every element sets in every window of 8 consecutive moves (all non-fixed since index < k)
        for x in E:
            for st in range(0, k - 7):
                if all(x not in d['sets'][i] for i in range(st, st + 8)):
                    win_viol += 1; win_viol_ex = win_viol_ex or (E, x, st); break
        if k > 0:
            slack = F(k) / (3 * a)     # N m / (3 a) in units m = 1: lonely_window_of_moves needs <= 1
            if slack > max_slack: max_slack = slack; max_slack_set = E
        if d['a_idx']:
            firstA_max = max(firstA_max, d['a_idx'][0])
            n0 = d['a_idx'][0]
            lap = d['laps'][n0][a]
            if a < 57 and lap > 8:
                lap_viol += 1; lap_viol_ex = lap_viol_ex or (E, lap)
            key = min(int(a), 80)
            maxlap_by_rho[key] = max(maxlap_by_rho.get(key, 0), lap)
            if len(d['a_idx']) > 1 and (lap <= 8 or lap == 10):
                a_multi += 1; a_multi_ex = a_multi_ex or (E, d['a_idx'], lap)
        else:
            a_none += 1
        # additive position bound: R_fix - 1 < 2 * sum 1/rho_setter  <= 2 k / rho_a
        if not (d['Rfix'] - 1 < 2 * d['wsum'] or k == 0):
            n_add_viol += 1; add_viol_ex = add_viol_ex or E
        if not (d['wsum'] <= d['wsum_a']):
            n_add_viol += 1
        if a >= 5:
            maxR_hi = max(maxR_hi, d['Rfix'])
            if d['Rfix'] > 7: over7_hi += 1
        else:
            maxR_lo = max(maxR_lo, d['Rfix'])
            if d['Rfix'] > 7:
                over7_lo += 1; over7_lo_ex = over7_lo_ex or E
    print("population", name, ": sets =", n)
    print("  max number of moves to the fixed point =", maxk, "(window_has_setter + min_sets_once give <= 15 under LapCond; lapCond_of_ratio gives LapCond for rho_a < 57)")
    print("  max R at the fixed point =", maxR, "attained at readings", [str(x) for x in maxR_set])
    print("  max first-setting index of a (when a sets) =", firstA_max, "; sets where a never sets =", a_none)
    print("  a sets twice with lap <= 8 or = 10 (must be 0 by min_sets_once):", a_multi, a_multi_ex)
    print("  rho_a < 57 with lap of a at its first setting > 8 (must be 0 by lapCond_of_ratio):", lap_viol, lap_viol_ex)
    print("  violations of the additive bound R_fix - 1 < 2 sum 1/rho (must be 0):", n_add_viol, add_viol_ex)
    print("  rho_a >= 5: max R_fix =", maxR_hi, "; count with R_fix > 7 =", over7_hi)
    print("  rho_a <  5: max R_fix =", maxR_lo, "; count with R_fix > 7 =", over7_lo, over7_lo_ex)
    print("  8-windows of consecutive moves with no setting of some element (window_has_setter says 0 for K=4):", win_viol, win_viol_ex)
    print("  max of N m / (3 a) over the population (lonely_window_of_moves needs <= 1):", max_slack, [str(x) for x in max_slack_set] if max_slack_set else None)
    print("  max lap of a at its first setting by floor(rho_a):", dict(sorted(maxlap_by_rho.items())))
    return maxk

def main():
    print("=== Section 1-4: populations of four readings (unit m = 1), exhaustive grids ===")
    # grid A: readings p/4, 1 <= rho <= 12
    section1_4("A: p/4, 1..12, K=4 (exhaustive)", pop_grid(4, 12, 4))
    # grid B: readings p/2, 1 <= rho <= 30
    section1_4("B: p/2, 1..30, K=4 (exhaustive)", pop_grid(2, 30, 4))
    # grid C: a in [50, 80] integer, the other three from a small explicit grid above a (rho_a in the lap-boundary range)
    def popC():
        for a in range(50, 81):
            rest = [F(a) + F(p, 4) for p in range(1, 4 * 12)]
            for t in itertools.combinations(rest, 3):
                yield (F(a),) + t
    section1_4("C: a integer 50..80, three others a + p/4 (p=1..47) (exhaustive)", popC())

    print()
    print("=== Section 5: the lap condition cannot be dropped: exact first-return examples at rho_a >= 57 ===")
    # the Lean counterexample CE in units m = 12/875: readings 875/12 * {1, 26/25, 533/500, 204/125}
    k = F(875, 12)
    CE = [k * x for x in (F(1), F(26, 25), F(533, 500), F(204, 125))]
    d = analyse(CE)
    print("  CE (FourDistinct.not_fourDistinctLaw), rho_a =", CE[0], ": a sets at moves", d['a_idx'], "laps of a there",
          [d['laps'][i][CE[0]] for i in d['a_idx']], "; moves =", d['k'], "; R_fix =", d['Rfix'])
    print("  setters per move:", [[str(x) for x in s] for s in d['sets']])
    # exhaustive grid: a in {57, 57.5, ..., 90}, the other three a + p/8 (p = 1..40).  For each a: does a's first setting
    # (index <= 7) have lap >= 9?  does a set twice?  what is R_fix?
    first_lap9 = None; first_double = None; n_lap9 = 0; n_double = 0; max_R_double = F(0); maxR_all = F(0)
    lap_hist = Counter(); double_laps = Counter()
    for a2 in range(114, 181):
        a = F(a2, 2)
        rest = [a + F(p, 8) for p in range(1, 41)]
        for t in itertools.combinations(rest, 3):
            E = (a,) + t
            dd = analyse(E)
            maxR_all = max(maxR_all, dd['Rfix'])
            if dd['a_idx']:
                n0 = dd['a_idx'][0]
                lap0 = dd['laps'][n0][a]
                lap_hist[(int(a), lap0)] += 0
                if lap0 >= 9:
                    n_lap9 += 1
                    if first_lap9 is None or a < first_lap9[0]:
                        first_lap9 = (a, [str(x) for x in t], n0, lap0)
                if len(dd['a_idx']) > 1:
                    n_double += 1
                    double_laps[tuple(dd['laps'][i][a] for i in dd['a_idx'])] += 1
                    max_R_double = max(max_R_double, dd['Rfix'])
                    if first_double is None or a < first_double[0]:
                        first_double = (a, [str(x) for x in t], dd['a_idx'], [dd['laps'][i][a] for i in dd['a_idx']])
    print("  grid a = 57..90 step 1/2, others a + p/8 (p=1..40), exhaustive (67 values of a, 9880 triples each):")
    print("    sets with lap of a at its first setting >= 9:", n_lap9, "; smallest rho_a:", first_lap9)
    print("    sets with a set twice:", n_double, "; smallest rho_a:", first_double, "; laps of the two settings:", dict(double_laps))
    print("    max R_fix over the whole grid:", maxR_all, "; max R_fix among sets with a set twice:", max_R_double)

    print()
    print("=== Section 6: five readings (six disparities): the first return of a passes through all four others ===")
    n = 0; bad = 0; multi = 0; maxk = 0; maxRfix = F(0); ex_multi = None; first_ret_not_all = 0
    for E in pop_grid(2, 8, 5):
        a = min(E)
        Rs, sets, laps = cascade(list(E))
        n += 1
        k = len(sets)
        maxk = max(maxk, k); maxRfix = max(maxRfix, Rs[-1])
        idx = [i for i, s in enumerate(sets) if a in s]
        if len(idx) > 1:
            multi += 1
            if ex_multi is None: ex_multi = (E, idx)
            i0, i1 = idx[0], idx[1]
            # first return: first state s > i0 at which a is in the way
            ret = next(s for s in range(i0 + 1, len(Rs)) if inway(a, Rs[s]))
            vals = set()
            for s in range(i0 + 1, ret):
                vals.update(x for x in sets[s])
            if vals != set(E) - {a}:
                first_ret_not_all += 1
    print("  population p/2, 1..8, K=5 exhaustive: sets =", n, "; max moves =", maxk, "; max R_fix =", maxRfix)
    print("  a sets twice:", multi, "example", ex_multi and ([str(x) for x in ex_multi[0]], ex_multi[1]))
    print("  among those, first return of a NOT through all four other readings (five_first_return_all_others_lap, lap<=8):", first_ret_not_all)

def section7():
    print()
    print("=== Section 7: the covers of FiveReach (E_five, E_six), unit m = 1 (their least reading is not m): position law check ===")
    E5=[F(6441,1000),F(7001,1000),F(627,125),F(1951,500),F(1421,250)]
    E6=[F(700251,100000),F(7809,3125),F(562313,100000),F(19899,6250),F(197403,50000),F(88263,20000)]
    for name, E in (("E_five (5 readings)", E5), ("E_six (6 readings)", E6)):
        d = analyse(E)
        a = d['a']
        print("  %s: moves N = %d, R_fix = %s, rho_a = %s, N/(3 rho_a) = %s, 1 + 2N/rho_a = %s" % (name, d['k'], d['Rfix'], a, F(d['k'])/(3*a), 1 + 2*F(d['k'])/a))
        miss = [(str(x), st) for x in E for st in range(0, d['k'] - 7) if all(x not in d['sets'][i] for i in range(st, st + 8))]
        print("    8-windows with no setting of an element:", len(miss), miss[:3])
    print("  (E_five: Reach 5 fails at R <= 4398/1000 (FiveReach.not_reach_five); the position law holds with N m <= 3 a here.  E_six: N m = 20 > 3 a = 7.5, R_fix > 7: the gate is crossed, FiveReach.cover_six.)")

if __name__ == "__main__":
    main()
    section7()
