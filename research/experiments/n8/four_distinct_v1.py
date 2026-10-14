#!/usr/bin/env python3
"""four_distinct_v1.py -- Task AZ (2026-10-09): the FourDistinctLaw of Fresh/Ladder5.lean, exact data.

Everything that decides anything is exact (Python Fractions / integers).  scipy's linprog is used ONLY to steer the search for
real-valued witnesses (rule 15); every witness is then re-verified by an exact cascade.  Nothing is random except where marked,
and the seeds are fixed.  Every cascade loop has a move limit (500, raises).
Theorem names refer to Fresh/FourDistinct.lean.

Sections
  1  the exact counterexample to FourDistinctLaw (not_fourDistinctLaw): cascade table, hypotheses
  2  the budget system for words on three setter values: exact Fourier-Motzkin, all words of length 2..9, minimal infeasible
     subsystems (which exact constraint excludes which word)
  3  the lap arithmetic of the word z y x z (lap_arith): exact integer scan over the slowest's lap j = 0..60
  4  exact three-valued first returns for every j in 9..40 (autonomous window and full cascade with a sets at n = 0)
  5  hypothesis audit: m = a (UNDECIDED, search log); a not the minimum (exact counterexample); the gate form a <= 10 m
"""
import sys, itertools, time
from fractions import Fraction as F
import math

LIMIT = 500

def rnd(x):
    return math.floor(x + F(1, 2))

def inway(d, t):
    x = d * t
    n = rnd(x)
    return abs(x - n) < F(1, 8), n

def cascade(E, t0, limit=LIMIT):
    t = t0
    seq = [t]; setters = []; laps = []
    for _ in range(limit):
        best = None
        for d in E:
            iw, n = inway(d, t)
            if iw:
                o = (n + F(1, 8)) / d
                if best is None or o > best[0]:
                    best = (o, d, n)
        if best is None:
            return seq, setters, laps, True
        t = best[0]
        seq.append(t); setters.append(best[1]); laps.append(best[2])
    raise RuntimeError("move limit reached")

def first_returns_of_min(E, t0):
    """(n, k, intermediate setters, their laps, lap of a at n) for every setting n of a = min E with a later visit."""
    a = min(E)
    seq, st, lp, done = cascade(E, t0)
    out = []
    for n in range(len(st)):
        if st[n] != a:
            continue
        for k in range(n + 1, len(seq)):
            if inway(a, seq[k])[0]:
                out.append((n, k, st[n + 1:k], lp[n + 1:k], lp[n]))
                break
    return out, seq, st, lp

def fs(x):
    return str(x)

# ---------------------------------------------------------------------------------------------------------------------
print("=" * 110)
print("1. THE EXACT COUNTEREXAMPLE TO FourDistinctLaw  (Lean: not_fourDistinctLaw, slowest_of_four_can_return)")
print("=" * 110)
E = [F(1), F(26, 25), F(533, 500), F(204, 125)]
t0 = F(875, 96)
m = 1 / (8 * t0)
print("E =", [fs(x) for x in E], "   m =", fs(m), "   seq 0 = 1/(8m) =", fs(t0), "   m <= every reading:", all(m <= d for d in E))
seq, st, lp, done = cascade(E, t0)
print("cascade reaches a fixed point:", done, "   states", len(seq))
for s, t in enumerate(seq):
    iw = [(fs(d), fs(d * t), float(d * t), inway(d, t)[0], inway(d, t)[1]) for d in E]
    print("  state %d  t = %-14s  readings d*t (in the way?, lap): %s" % (s, fs(t), "; ".join("%s: %s%s" % (a_, "Y" if c_ else "n", ("L%d" % l_) if c_ else "") for a_, _, _, c_, l_ in iw)))
print("  setters of moves 0..%d: %s   laps %s" % (len(st) - 1, [fs(x) for x in st], lp))
out, _, _, _ = first_returns_of_min(E, t0)
for (n, k, w, l, j) in out:
    print("  first return of the slowest a = 1: sets at n = %d (lap j = %d), in the way at k = %d; intermediate setters %s, laps %s; DISTINCT = %d"
          % (n, j, k, [fs(x) for x in w], l, len(set(w))))
    print("  FourDistinctLaw needs 3 < distinct; here distinct = %d  =>  the law is FALSE" % len(set(w)))
    A = [a_ for a_ in E]
    print("  a/m = %s (= %.2f); seq n = %s <= 7/(8m) = %s (inside the first window): %s" % (fs(min(E) / m), float(min(E) / m), fs(seq[n]), fs(7 / (8 * m)), seq[n] <= 7 / (8 * m)))
assert len(out) == 1 and len(set(out[0][2])) == 3 and out[0][4] == 9

# ---------------------------------------------------------------------------------------------------------------------
print()
print("=" * 110)
print("2. BUDGET SYSTEM FOR WORDS ON THREE SETTER VALUES (exact Fourier-Motzkin).  Lean: word_4 .. word_7, three_distinct_shape")
print("=" * 110)
print("""Letters x < y < z (setter values, all > a), weights u = a/w:  1 > u_x > u_y > u_z > 0.  A word w_1..w_L has no immediate repeat.
Constraints (all LINEAR in u):  (A)  3 < sum_s u_{w_s}   (return of a);  (B_ij)  w_i = w_j  =>  3 u_{w_i} < sum_{i<s<j} u_{w_s}  (return of a repeated setter).""")

def fm_feasible(cons, nvars):
    cons = [(tuple(F(x) for x in c), F(r), s) for c, r, s in cons]
    for v in range(nvars):
        pos = []; neg = []; zero = []
        for c, r, s in cons:
            if c[v] > 0: pos.append((c, r, s))
            elif c[v] < 0: neg.append((c, r, s))
            else: zero.append((c, r, s))
        new = zero[:]
        for c1, r1, s1 in pos:
            for c2, r2, s2 in neg:
                a_ = -c2[v]; b_ = c1[v]
                new.append((tuple(a_ * x + b_ * y for x, y in zip(c1, c2)), a_ * r1 + b_ * r2, s1 or s2))
        cons = list(dict.fromkeys(new))
        if len(cons) > 50000:
            raise RuntimeError("blow-up")
    for c, r, s in cons:
        if s and not (0 < r): return False
        if (not s) and not (0 <= r): return False
    return True

ORDER = [("u_y<u_x", ((-1, 1, 0), 0, True)), ("u_z<u_y", ((0, -1, 1), 0, True)), ("0<u_z", ((0, 0, -1), 0, True)), ("u_x<1", ((1, 0, 0), 1, True))]

def labelled(word):
    L = len(word)
    cons = [(nm, c) for nm, c in ORDER]
    co = [0, 0, 0]
    for c in word: co[c] -= 1
    cons.append(("A", (tuple(co), -3, True)))
    for i in range(L):
        for j in range(i + 2, L):
            if word[i] == word[j]:
                co = [0, 0, 0]
                for s in range(i + 1, j): co[word[s]] -= 1
                co[word[i]] += 3
                cons.append(("B(%d,%d)" % (i + 1, j + 1), (tuple(co), 0, True)))
    return cons

def minimal_core(word):
    cons = labelled(word)
    if fm_feasible([c for _, c in cons], 3):
        return None
    core = list(cons)
    changed = True
    while changed:
        changed = False
        for item in list(core):
            trial = [x for x in core if x is not item]
            if not fm_feasible([c for _, c in trial], 3):
                core = trial; changed = True
    return [nm for nm, _ in core if nm not in dict(ORDER)], [nm for nm, _ in core if nm in dict(ORDER)]

LET = "xyz"
summary = {}
for L in range(2, 10):
    feas = []; infeas = 0
    for w in itertools.product(range(3), repeat=L):
        if any(w[i] == w[i + 1] for i in range(L - 1)): continue
        if fm_feasible([c for _, c in labelled(w)], 3): feas.append("".join(LET[c] for c in w))
        else: infeas += 1
    summary[L] = (feas, infeas)
    print("  length %d: words without an immediate repeat = %d;  budget-FEASIBLE = %s;  infeasible = %d" % (L, len(feas) + infeas, feas, infeas))
print("""  => the only word on at most three values that satisfies every budget is  z x y z  or  z y x z  (length 4).""")
print()
print("  Minimal infeasible subsystem (which budgets exclude the word), length 4, all 18 words with three letters + the 2-letter ones:")
for w in itertools.product(range(3), repeat=4):
    if any(w[i] == w[i + 1] for i in range(3)): continue
    name = "".join(LET[c] for c in w)
    core = minimal_core(w)
    print("    %-5s  %s" % (name, "FEASIBLE (needs the lap arithmetic of section 3)" if core is None else "excluded by %s  with order facts %s" % (core[0], core[1])))
print()
print("  Length 5, 6, 7: every word excluded; sizes of the minimal cores (number of budget constraints used):")
for L in (5, 6, 7):
    sizes = {}
    for w in itertools.product(range(3), repeat=L):
        if any(w[i] == w[i + 1] for i in range(L - 1)): continue
        core = minimal_core(w)
        assert core is not None
        sizes[len(core[0])] = sizes.get(len(core[0]), 0) + 1
    print("    length %d: %s" % (L, sorted(sizes.items())))
print("  Length >= 8: not enumerated.  Lean (three_distinct_shape): a window of >= 8 moves with three values repeats the smallest value")
print("  (every 4 consecutive moves contain it, window_has_min), which min_once excludes (>= 4 values).")

# ---------------------------------------------------------------------------------------------------------------------
print()
print("=" * 110)
print("3. LAP ARITHMETIC OF  z y x z  (Lean: lap_arith)  -- exact integers, scaled by 8")
print("=" * 110)
print("""h1:  (8A-1)(8j+7) < (8A'+1)(8j+1)          (z at a's exit and at a's return)
h2:  (8B-1)(8C-1)(8A'-1) < (8A+1)(8B+1)(8C+1)   (the cycle z -> y -> x -> z), laps A' >= A+1, A,B,C >= j+1.
h2 is easiest at B = C = j+1 (the left factor increases in B, C).""")
solv = {}
for j in range(0, 61):
    sol = []
    for A in range(j + 1, 3 * j + 12):
        for Ap in range(A + 1, A + 15):
            if not ((8 * A - 1) * (8 * j + 7) < (8 * Ap + 1) * (8 * j + 1)): continue
            B = C = j + 1
            if (8 * B - 1) * (8 * C - 1) * (8 * Ap - 1) < (8 * A + 1) * (8 * B + 1) * (8 * C + 1):
                sol.append((A, Ap))
    solv[j] = sol
nosol = [j for j in range(0, 61) if not solv[j]]
print("  j with NO integer solution (A, A') in 0..60:", nosol)
print("  j with a solution:", [j for j in range(0, 61) if solv[j]])
print("  first solutions:", {j: solv[j][:2] for j in range(8, 16)})
assert set(nosol) == set(list(range(0, 9)) + [10])
print("  => matches the Lean theorem: 9 <= j and j != 10 (three_distinct_lap).")

# ---------------------------------------------------------------------------------------------------------------------
print()
print("=" * 110)
print("4. EXACT THREE-VALUED FIRST RETURNS, j = 9 .. 40")
print("=" * 110)
try:
    import numpy as np
    from scipy.optimize import linprog
    have_lp = True
except Exception:
    have_lp = False
e8 = 1 / 8.0

def lp_rho(j, A, B, C, A2):
    """steering only: a feasible (rho_z, rho_y', rho_x') for the word z, p, q, z on laps A, B, C, A2 (floats)."""
    e = e8
    rows = []; rhs = []
    def lt(c, b, sl=1.0):
        rows.append(list(c) + [sl]); rhs.append(b)
    u0 = j + e
    lt([u0, 0, 0], A + e); lt([-u0, 0, 0], -(A - e))
    lt([-(B + e), (A + e), 0], 0); lt([(B - e), -(A + e), 0], 0)
    lt([0, -(C + e), (B + e)], 0); lt([0, (C - e), -(B + e)], 0)
    lt([(C + e), 0, -(A2 + e)], 0); lt([-(C + e), 0, (A2 - e)], 0)
    lt([0, 0, -(j + 7 * e)], -(C + e), 0.0)
    lt([0, -(j + 7 * e), 0], -(B + e), 0.0)
    lt([-(j + 7 * e), 0, 0], -(A + e), 0.0)
    lt([(j + 7 * e), 0, 0], A2 + e); lt([-(j + 9 * e), 0, 0], -(A2 + e))
    lt([0, 0, -1], -1)
    res = linprog([0, 0, 0, -1.0], A_ub=np.array(rows), b_ub=np.array(rhs), bounds=[(1, 6), (1, 6), (1, 6), (0, 1)], method="highs")
    if res.status == 0 and -res.fun > 1e-9:
        return list(res.x[:3])
    return None

def window_exact(Eset, j):
    a = min(Eset); t = (F(j) + F(1, 8)) / a; ws = []
    for _ in range(LIMIT):
        if inway(a, t)[0]:
            return ws, True
        best = None
        for d in Eset:
            iw, n = inway(d, t)
            if iw:
                o = (n + F(1, 8)) / d
                if best is None or o > best[0]: best = (o, d, n)
        if best is None:
            return ws, False
        t = best[0]; ws.append((best[1], best[2]))
    raise RuntimeError("move limit")

examples = {}
if have_lp:
    for j in range(0, 41):
        found = None
        for A in range(j + 1, 3 * j + 8):
            for B in range(j + 1, j + 7):
                for C in range(B, j + 7):
                    rho = lp_rho(j, A, B, C, A + 1)
                    if rho is None: continue
                    for den in (10, 20, 50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000, 50000):
                        p_, q_, r_ = [F(round(x * den), den) for x in rho]
                        if len({p_, q_, r_, F(1)}) < 4 or min(p_, q_, r_) <= 1: continue
                        Ew = [F(1), p_, q_, r_]
                        ws, ret = window_exact(Ew, j)
                        if ret and len({w for w, _ in ws}) <= 3:
                            found = (Ew, ws); break
                    if found: break
                if found: break
            if found: break
        examples[j] = found
    for j in range(0, 41):
        f = examples[j]
        if f is None:
            print("  j = %2d: no three-valued return found (search over laps A in [j+1,3j+7], B,C in [j+1,j+6])" % j)
        else:
            Ew, ws = f
            print("  j = %2d: E = %s  setters (value, lap) = %s" % (j, [fs(x) for x in Ew], [(fs(w), n) for w, n in ws]))
    print("  j with an exact example in 0..40:", [j for j in range(41) if examples[j]])
    print("  j without (0..40):", [j for j in range(41) if not examples[j]])
    # full cascade: start t0 = the smallest left end of a zone of another reading that contains j + 1/8, so that a sets at move 0
    print()
    print("  Full cascades from 1/(8m): a = 1 sets at n = 0 on lap j, first return, three setter values (each is a counterexample to FourDistinctLaw):")
    for j in range(9, 41):
        f = examples[j]
        if f is None: continue
        Ew, ws = f
        u1 = F(j) + F(1, 8)
        lefts = []
        for d in Ew[1:]:
            iw, n = inway(d, u1)
            if iw: lefts.append((n - F(1, 8)) / d)
        t0j = min(lefts)
        outj, seqj, stj, lpj = first_returns_of_min(Ew, t0j)
        ok = [o for o in outj if o[0] == 0 and len(set(o[2])) <= 3]
        mj = 1 / (8 * t0j)
        print("   j = %2d: E = %s  m = %s  a/m = %.2f  first return: n=0, k=%d, setters %s, distinct %d, m <= all: %s"
              % (j, [fs(x) for x in Ew], fs(mj), float(1 / mj), ok[0][1] if ok else -1, [fs(x) for x in ok[0][2]] if ok else None,
                 len(set(ok[0][2])) if ok else -1, all(mj <= d for d in Ew)))
        assert ok
else:
    print("  scipy not available: section skipped")

# ---------------------------------------------------------------------------------------------------------------------
print()
print("=" * 110)
print("5. HYPOTHESIS AUDIT")
print("=" * 110)
print("""(i)   m (lower bound, seq 0 = 1/(8m)): the counterexample has m = %s << a = 1.  The theorems four_distinct_of_lap / three_distinct_lap
      do not mention m: NOT REQUIRED.  The statement FourDistinctLaw, which quantifies over every m, is FALSE.""" % fs(m))
# (ii) a not the minimum of E: AY's one-move return
Ea = [F(17, 4), F(25, 4), F(59, 4), F(16)]
seq_a, st_a, lp_a, _ = cascade(Ea, F(1, 8))
idx = [i for i, x in enumerate(st_a) if x == F(59, 4)]
print("(ii)  a not the minimum: E = %s, start 1/8 (m = 1): setters %s; 59/4 sets at moves %s; at moves 4 and 6 with 17/4 between (ratio 59/17 > 3): a return after one move, so the"
      % ([fs(x) for x in Ea], [fs(x) for x in st_a], idx))
print("      hypothesis 'a at most every reading' is REQUIRED (exact counterexample to the statement without it: 1 intermediate value).")
assert 4 in idx and 6 in idx and st_a[5] == F(17, 4)
# (iii) m = a
import random
BASE = [F(26, 25), F(533, 500), F(204, 125)]
trials = 0; reached9 = 0; hits = []
for seed in range(8):
    rng = random.Random(seed)
    for _ in range(5000):
        ne = rng.choice([1, 2, 3, 4, 5])
        ext = set()
        while len(ext) < ne:
            den = rng.choice([20, 50, 100, 200, 500])
            ext.add(F(rng.randint(den, 6 * den), den))
        Em = [F(1)] + BASE + sorted(ext)
        if len(set(Em)) < len(Em): continue
        trials += 1
        outm, seqm, stm, lpm = first_returns_of_min(Em, F(1, 8))   # m = a = 1
        if any(l >= 9 for x, l in zip(stm, lpm) if x == 1): reached9 += 1
        for (n, k, w, l, j) in outm:
            if len(set(w)) <= 3: hits.append((Em, n, k, w, l, j))
print("(iii) m = a (the unit is the slowest reading itself, start 1/(8a)): by Gate.dmin_clear_first_window a is clear on R in [1,7], so a is in the way")
print("      only on a lap j >= 1, after the gap R in [1,7] has been crossed by the other readings.  Exact search (seeds 0..7): E = {1} + the j = 9")
print("      letters {26/25, 533/500, 204/125} + 1..5 random extra readings in [1,6], start 1/8: %d cascades, %d with a set on a lap >= 9, %d three-valued first returns."
      % (trials, reached9, len(hits)))
print("      UNDECIDED whether FourDistinctLaw holds for m = a (no proof, no counterexample).")
print("""(iv)  gate form: four_distinct_in_gate (a <= 10 m and a set inside the first window seq n <= 7/(8m)) is a THEOREM: the lap j <= 8
      (a * seq n <= 70/8, j < a*seq n + 1/8 < 9).  a <= 10 m is REQUIRED in this form: the counterexample has a = 875/12 m = 72.9 m inside the window.
      The sharp lap condition is j <= 8 or j = 10 (j = 9 and j = 11..40 have exact three-valued returns, section 4).""")
print("""(v)   first return (no visit of a strictly between): used by a_lt_w (a < every intermediate setter).  REQUIRED by this proof;
      necessity UNDECIDED.
(vi)  0 < seq 0, positive disparities, a the SETTER at n: used; AY's audit (ladder5_v2.out section 4) gives the exact counterexample for
      'in the way' instead of 'setter' (REQUIRED).""")
print()
print("DONE")
