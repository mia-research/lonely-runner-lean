#!/usr/bin/env python3
"""time_budget_v1.py -- exact data for Task BG (Fresh/TimeBudget.lean).  2026-10-09.

Exact Fractions only; no floats; no random sampling; the cascade is deterministic.  Every cascade loop has a move limit.

What is computed (all by full enumeration within the stated bounds):
 (A) every 8-subset of {1..BOUND} of integer disparities with NO lonely instant (least-clear-opening test: opening j of
     flank e is lonely iff d(8j+1) mod 8e lies in [e,7e] for every d; j in 0..e-1 suffices, Localisation).  For each such
     set the cascade from t0 = 1/(8 d_min) is run until its state repeats modulo 1/g (g = gcd of the set; shift invariance
     of the move), which exhibits the period exactly.
 (B) for each set: the period quantities c_x, rho_x, sigma = sum rho_x, S = sum c_x/x, and EVERY inequality of the Lean file
     on EVERY stretch [n, m) of a three-period unrolling (all pairs n < m):
       advance < 1/(4 setter)                         (advance_lt_zone)
       L < S/4                                        (length_lt_sum_cnt)
       c_x <= floor(x L) + 1                          (cnt_le_floor)
       sum rho > 4, rho_x <= 1 + 1/(xL)               (rho_sum_gt_four, rho_le)
       3(c_x - 1) <= x sum_{y!=x} c_y / y             (return_budget_stretch; strict when c_x >= 2)
       rho form: sum_{y!=x} rho_y >= 3 rho_x - 3/(xL) (reading_constraint)
       4 c_x <= x S + 3                               (budget_cnt_form)
       (4 - n) S <= 3 H                               (budget_all_readings)
     and on the unrolled word: budget_sum (every pair n<k with x the setter at n and in the way at seq k), pair_law,
     triple_clause, no_return_in_three, lap_budget (consecutive settings), entry_budget (from the start), two_step_lower,
     per_lap_decrease, setter_not_twice_in_row, entered_anew.
     The limit form DensitySystem (rho_x <= 1, sigma >= 4, sum_{y!=x} rho_y >= 3 rho_x) is checked on the period.
 (C) the density system as an exact linear system: Fourier-Motzkin elimination over the rationals for n = 1..7 readings
     (limit form), with the result (infeasible / feasible) and exact rational witnesses.
 (D) candidate further laws tested on the data, and whether adding each (when it is a density statement) keeps seven
     readings feasible.
"""
from fractions import Fraction as F
from math import gcd, ceil, floor
from functools import reduce
import itertools, sys

THR = F(1, 8)
BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 40
MOVE_LIMIT = 20000          # no cascade loop runs longer than this many moves
UNROLL = 3                  # periods unrolled for the stretch tests


def frac(x):
    return x - (x.numerator // x.denominator)


def cd(x):
    f = frac(x)
    return min(f, 1 - f)


def in_way(d, t):
    return cd(d * t) < THR


def next_opening(d, t):
    q = ceil(d * t - THR)
    return (F(q) + THR) / d


def lap(d, t):
    return round(d * t)        # python rounds half to even; |d t - lap| < 1/8 whenever d is in the way, so no tie arises


def lonely_exists(S):
    for e in S:
        for j in range(e):
            ok = True
            for d in S:
                r = (d * (8 * j + 1)) % (8 * e)
                if not (e <= r <= 7 * e):
                    ok = False
                    break
            if ok:
                return True
    return False


def move(S, t):
    ops = {d: next_opening(d, t) for d in S if in_way(d, t)}
    if not ops:
        return None
    top = max(ops.values())
    return top, sorted(d for d, o in ops.items() if o == top)


def run_cascade(S, nmoves, pick="low"):
    """The cascade from 1/(8 d_min), exactly nmoves moves (never longer); returns states and setters."""
    assert nmoves <= MOVE_LIMIT
    t = F(1, 8 * min(S))
    states = [t]
    setters = []
    ties = 0
    for _ in range(nmoves):
        r = move(S, t)
        if r is None:
            raise RuntimeError("cascade fixed: set is lonely")
        top, tl = r
        if len(tl) > 1:
            ties += 1
        setters.append(tl[0] if pick == "low" else tl[-1])
        t = top
        states.append(t)
    return states, setters, ties


def find_period(S):
    g = reduce(gcd, S)
    t = F(1, 8 * min(S))
    seen = {}
    states = [t]
    for k in range(MOVE_LIMIT):
        key = t % F(1, g)
        if key in seen:
            return seen[key], k, g, states      # start index, end index
        seen[key] = k
        r = move(S, t)
        if r is None:
            return None
        t = r[0]
        states.append(t)
    raise RuntimeError("move limit reached")


# ----------------------------------------------------------------------------------------------- (A)
def enumerate_sets(bound):
    return [S for S in itertools.combinations(range(1, bound + 1), 8) if not lonely_exists(S)]


# ----------------------------------------------------------------------------------------------- (B)
class Counter:
    def __init__(self):
        self.n = {}
        self.bad = {}

    def check(self, name, ok, info=None):
        self.n[name] = self.n.get(name, 0) + 1
        if not ok:
            self.bad.setdefault(name, []).append(info)


def stretch_tests(S, states, setters, cn):
    M = len(setters)
    E = list(S)
    H = sum(F(1) / x for x in E)
    # per-move advance
    for s in range(M):
        x = setters[s]
        adv = states[s + 1] - states[s]
        cn.check("advance in (0, 1/(4 setter))", 0 < adv < F(1, 4) / x, (S, s))
    # prefix counts for fast stretch tests
    pref = {x: [0] for x in E}
    for s in range(M):
        for x in E:
            pref[x].append(pref[x][-1] + (1 if setters[s] == x else 0))
    nE = F(len(E))
    for n in range(M):
        for m in range(n + 1, M + 1):
            L = states[m] - states[n]
            c = {x: pref[x][m] - pref[x][n] for x in E}
            Ssum = sum(F(c[x]) / x for x in E)
            cn.check("L < S/4", L < Ssum / 4, (S, n, m))
            for x in E:
                cn.check("c_x <= floor(xL)+1", c[x] <= floor(x * L) + 1, (S, n, m, x))
            rho = {x: F(c[x]) / (x * L) for x in E}
            cn.check("sum rho > 4", sum(rho.values()) > 4, (S, n, m))
            for x in E:
                cn.check("rho_x <= 1 + 1/(xL)", rho[x] <= 1 + F(1) / (x * L), (S, n, m, x))
                R = x * sum(F(c[y]) / y for y in E if y != x)
                cn.check("3(c_x-1) <= x sum_{y!=x} c_y/y", 3 * (c[x] - 1) <= R, (S, n, m, x))
                if c[x] >= 2:
                    cn.check("strict when c_x>=2", 3 * (c[x] - 1) < R, (S, n, m, x))
                cn.check("rho form: sum_{y!=x} rho_y >= 3 rho_x - 3/(xL)",
                         sum(rho[y] for y in E if y != x) >= 3 * rho[x] - F(3) / (x * L), (S, n, m, x))
                cn.check("4 c_x <= x S + 3", 4 * c[x] <= x * Ssum + 3, (S, n, m, x))
            cn.check("(4-n) S <= 3H", (4 - nE) * Ssum <= 3 * H, (S, n, m))


def word_tests(S, states, setters, cn):
    M = len(setters)
    E = list(S)
    m0 = min(S)
    lp = lambda d, t: lap(d, t)
    # budget_sum: x setter at n, x in the way at seq k > n
    for n in range(M):
        x = setters[n]
        acc = F(0)
        for k in range(n + 1, M + 1):
            # intermediate setters are s = n+1 .. k-1
            if k - 1 >= n + 1:
                acc += x / setters[k - 1]
            if in_way(x, states[k]):
                cn.check("budget_sum: 3 < sum_{n<s<k} x/w_s (x in the way at seq k)", acc > 3, (S, n, k))
                # lap_budget when x sets again at k
                if k < M and setters[k] == x:
                    j = lap(x, states[k]) - lap(x, states[n])
                    cn.check("lap_budget: 4j-1 < sum (x sets at n and k)", 4 * j - 1 < acc, (S, n, k))
                    cn.check("lap_identity", x * (states[k + 1] - states[n + 1]) == j, (S, n, k))
    # pair_law, triple_clause, no_return_in_three
    for n in range(M - 3):
        x, y, z = setters[n], setters[n + 1], setters[n + 2]
        if in_way(x, states[n + 3]):
            cn.check("pair_law: 3 < x/y + x/z", 3 < x / y + x / z, (S, n))
            if x <= y and x <= z:
                cn.check("no_return_in_three (must never fire)", False, (S, n))
            else:
                cn.check("no_return_in_three (contrapositive consistent)", True)
    for n in range(M - 2):
        x, y = setters[n], setters[n + 1]
        if setters[n + 2] == x:
            cn.check("triple_clause: 3y < x", 3 * y < x, (S, n))
    # entry_budget from the start (all y in the way at seq k)
    for k in range(1, M + 1):
        for y in E:
            if in_way(y, states[k]):
                tot = sum(y / setters[s] for s in range(k))
                cn.check("entry_budget: 7/2 - y/(2m) < sum_{s<k} y/w_s", F(7, 2) - y / (2 * m0) < tot, (S, k, y))
    # two_step_lower, entered_anew, setter_not_twice_in_row, per_lap_decrease
    for s in range(M - 1):
        x = setters[s + 1]
        cn.check("two_step_lower: seq(s+2)-seq(s) >= 1/(4x)", states[s + 2] - states[s] >= F(1, 4) / x, (S, s))
        cn.check("setter_not_twice_in_row", setters[s] != setters[s + 1], (S, s))
    for s in range(M):
        t, t2 = states[s], states[s + 1]
        for y in E:
            if in_way(y, t2):
                cn.check("entered_anew: y t <= lap - 1/8", y * t <= lap(y, t2) - THR, (S, s, y))
    for n in range(M):
        for m in range(n + 1, M):
            if lap(setters[n], states[n]) == lap(setters[m], states[m]):
                cn.check("per_lap_decrease: same lap => later setter slower", setters[m] < setters[n], (S, n, m))


def analyse(S, cn, full=True):
    st, en, g, states0 = find_period(S)
    assert st == 0
    M = en - st
    states_p = states0[st:en + 1]
    L = states_p[-1] - states_p[0]
    states, setters, ties = run_cascade(S, UNROLL * M)
    # period counts (setters of the first M moves)
    c = {x: sum(1 for s in range(M) if setters[s] == x) for x in S}
    rho = {x: F(c[x]) / (x * L) for x in S}
    sigma = sum(rho.values())
    Ssum = sum(F(c[x]) / x for x in S)
    # the period repeats exactly (shift by L per period)
    rep_ok = all(setters[s] == setters[s + M] for s in range(2 * M)) and \
        all(states[s + M] - states[s] == L for s in range(2 * M + 1))
    cn.check("period repeats exactly", rep_ok, S)
    cn.check("no ties of next openings", ties == 0, (S, ties))
    # limit form on the period
    cn.check("DensitySystem: 0<=rho<=1", all(0 <= rho[x] <= 1 for x in S), S)
    cn.check("DensitySystem: sigma >= 4", sigma >= 4, S)
    cn.check("DensitySystem: 3 rho_x <= sum_{y!=x} rho_y", all(3 * rho[x] <= sigma - rho[x] for x in S), S)
    cn.check("L < S/4 on the period", L < Ssum / 4, S)
    if full:
        stretch_tests(S, states, setters, cn)
        word_tests(S, states, setters, cn)
    return dict(S=S, g=g, M=M, L=L, c=c, rho=rho, sigma=sigma, Ssum=Ssum, states=states_p, words=setters[:M])


# ----------------------------------------------------------------------------------------------- (C)
def fm_feasible(cons, nvars, cap=60000):
    """cons: list of (coeff tuple, rhs) meaning coeff . x <= rhs.  Fourier-Motzkin over Q; True/False/None (cap hit)."""
    def norm(c):
        a, b = c
        g = 0
        for v in list(a) + [b]:
            if v != 0:
                g = v if g == 0 else g
        mx = max(abs(v) for v in list(a) + [b]) or 1
        a = tuple(F(v) / mx for v in a)
        return (a, F(b) / mx)
    cur = list({norm(c) for c in cons})
    for v in range(nvars):
        pos = [c for c in cur if c[0][v] > 0]
        neg = [c for c in cur if c[0][v] < 0]
        zer = [c for c in cur if c[0][v] == 0]
        new = set(norm(c) for c in zer)
        for p in pos:
            for q in neg:
                lam, mu = -q[0][v], p[0][v]
                a = tuple(lam * pa + mu * qa for pa, qa in zip(p[0], q[0]))
                b = lam * p[1] + mu * q[1]
                new.add(norm((a, b)))
        # drop trivially true rows 0 <= b
        cur = [c for c in new if not (all(x == 0 for x in c[0]) and c[1] >= 0)]
        if any(all(x == 0 for x in c[0]) and c[1] < 0 for c in cur):
            return False
        if len(cur) > cap:
            return None
    return True


def density_system(n, extra=None):
    cons = []
    for i in range(n):
        e = [F(0)] * n
        e[i] = F(-1)
        cons.append((tuple(e), F(0)))               # -rho_i <= 0
        e = [F(0)] * n
        e[i] = F(1)
        cons.append((tuple(e), F(1)))               # rho_i <= 1
        e = [F(-1)] * n
        e[i] += F(4)
        cons.append((tuple(e), F(0)))               # 4 rho_i - sum <= 0   (3 rho_i <= sum - rho_i)
    cons.append((tuple([F(-1)] * n), F(-4)))        # -sum <= -4
    if extra:
        cons += extra(n)
    return cons


def check_point(cons, pt):
    return all(sum(a * p for a, p in zip(c[0], pt)) <= c[1] for c in cons)



def fmt(fr):
    return str(fr)


def main():
    out = print
    out("time_budget_v1.py  BOUND =", BOUND, " MOVE_LIMIT =", MOVE_LIMIT, " UNROLL =", UNROLL)
    from math import comb
    sets = enumerate_sets(BOUND)
    out("\n== (A) 8-subsets of {1..%d} with no lonely instant: full enumeration of C(%d,8) = %d subsets, %d found"
        % (BOUND, BOUND, comb(BOUND, 8), len(sets)))
    reps = [S for S in sets if reduce(gcd, S) == 1]
    out("   gcd 1: %d sets; gcd > 1 (scaled copies): %d sets" % (len(reps), len(sets) - len(reps)))
    cn = Counter()
    res = {}
    for S in sets:
        res[S] = analyse(S, cn, full=(reduce(gcd, S) == 1))
    out("\n== (B) period data (exact).  c = moves per period by setter, L = period length in t, rho_x = c_x/(x L)")
    for S in sets:
        r = res[S]
        rho = r["rho"]
        above = sum(1 for x in S if rho[x] > F(1, 2))
        ge = sum(1 for x in S if rho[x] >= F(1, 2))
        out("S =", S, " gcd", r["g"], " moves", r["M"], " L =", r["L"])
        out("   c =", {x: r["c"][x] for x in S})
        out("   rho =", {x: fmt(rho[x]) for x in S})
        out("   sum rho = %s   S=sum c/x = %s   L < S/4: %s   readings with rho>1/2: %d   with rho>=1/2: %d"
            % (r["sigma"], r["Ssum"], r["L"] < r["Ssum"] / 4, above, ge))
        out("   min_x (sum_{y!=x} rho_y)/rho_x = %s   max_x rho_x/(sigma/4) = %s"
            % (min((r["sigma"] - rho[x]) / rho[x] for x in S), max(rho[x] / (r["sigma"] / 4) for x in S)))
    out("\n   scaled copies have the rho of the primitive set:")
    for S in sets:
        g = reduce(gcd, S)
        if g > 1:
            P = tuple(x // g for x in S)
            same = P in res and all(res[S]["rho"][x] == res[P]["rho"][x // g] for x in S)
            out("   ", S, "= %d x" % g, P, " same rho:", same, " same word:", [w // g for w in res[S]["words"]] == res[P]["words"])
    out("\n== (B) checks over all stretches and words of the %d-period unrolling (gcd 1 sets): number of tests / violations" % UNROLL)
    for name in sorted(cn.n):
        out("   %-72s %9d tests   %d violations" % (name, cn.n[name], len(cn.bad.get(name, []))))
    for name, lst in cn.bad.items():
        out("   VIOLATION", name, lst[:5])
    owner = res.get((1, 2, 3, 4, 5, 6, 7, 8))
    if owner:
        out("\n   owner's check, {1..8}: c =", owner["c"], " moves", owner["M"], " sum rho =", owner["sigma"],
            " readings above 1/2:", sorted(x for x in owner["rho"] if owner["rho"][x] > F(1, 2)))
    # (C)
    out("\n== (C) the density system (limit form): rho_i in [0,1], sum >= 4, 3 rho_i <= sum_{j!=i} rho_j.  Fourier-Motzkin over Q")
    for n in range(1, 6):
        f = fm_feasible(density_system(n), n)
        out("   n = %d readings: %s" % (n, {True: "FEASIBLE", False: "INFEASIBLE", None: "undecided (size cap)"}[f]))
    out("   n >= 6: the system is invariant under permuting the readings and convex, so it is feasible iff the constant point")
    out("   rho_i = r is: r in [0,1], n r >= 4, 4 r <= n r  ->  feasible iff n >= 4, with r = 1 (n >= 5: also every r in [4/n, 1]).")
    for n, pt in [(4, [F(1)] * 4), (5, [F(1)] * 5), (7, [F(9, 10)] * 7), (7, [F(1)] + [F(x - 1, x) for x in range(2, 8)])]:
        out("   witness n=%d %s satisfies the system: %s" % (n, [str(p) for p in pt], check_point(density_system(n), pt)))
    out("   n = 4: the system forces rho = (1,1,1,1) (sum >= 4, each <= 1); n <= 3: summing 3 rho_i <= sum - rho_i gives (4-n) sum <= 0.")
    # (D)
    out("\n== (D) candidate further laws, tested on the endless 8-disparity data (gcd 1 sets)")
    K = {k: [0, 0] for k in ["K1 rho_dmin = 1", "K2 c_x <= xL - 1 for x != d_min", "K3 sigma/4 >= max rho (budget)",
                             "K4 cascade lands exactly at R = 7 (t = 7/(8 d_min)) in the period",
                             "K5 last move of the period is by d_min from a state in (7,9) in R",
                             "K6 sigma <= 8 (two_step_lower consequence)"]}
    mingap = None
    minslack = None
    for S in reps:
        r = res[S]
        m0 = min(S)
        L = r["L"]
        ok = lambda k, v: (K[k].__setitem__(0, K[k][0] + 1), K[k].__setitem__(1, K[k][1] + (1 if v else 0)))
        ok("K1 rho_dmin = 1", r["rho"][m0] == 1)
        ok("K2 c_x <= xL - 1 for x != d_min", all(r["c"][x] <= x * L - 1 for x in S if x != m0))
        ok("K3 sigma/4 >= max rho (budget)", r["sigma"] / 4 >= max(r["rho"].values()))
        R = [8 * m0 * t for t in r["states"]]
        ok("K4 cascade lands exactly at R = 7 (t = 7/(8 d_min)) in the period", any((v - 7) % 8 == 0 for v in R))
        ok("K5 last move of the period is by d_min from a state in (7,9) in R", r["words"][-1] == m0 and 7 < R[-2] < 9)
        ok("K6 sigma <= 8 (two_step_lower consequence)", r["sigma"] <= 8)
        for s in range(r["M"]):
            x = r["words"][s]
            gap = 8 * x * (r["states"][s + 1] - r["states"][s])
            if mingap is None or gap < mingap[0]:
                mingap = (gap, S, s, x)
    for k, (a, b) in K.items():
        out("   %-72s holds in %d of %d sets" % (k, b, a))
    out("   smallest gap (8 x advance) over all moves of all sets: %s at S=%s move %d setter %s (gap lies in (0,2))" % mingap)
    sig = [res[S]["sigma"] for S in reps]
    out("   range of sum rho over the sets: min %s  max %s  (every set has 8 readings)" % (min(sig), max(sig)))
    for n in (7, 8):
        pt = [F(1)] + [F(9, 10)] * (n - 1)
        cons = density_system(n) + [(tuple([F(-1)] + [F(0)] * (n - 1)), F(-1)), (tuple([F(1)] * n), F(8))]
        out("   n = %d: witness %s satisfies the system with rho_1 = 1 and sum <= 8 added: %s" % (
            n, [str(p) for p in pt], check_point(cons, pt)))
    out("   done.")


if __name__ == "__main__":
    main()
