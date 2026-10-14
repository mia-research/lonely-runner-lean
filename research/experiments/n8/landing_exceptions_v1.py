"""Task AN: why the landing opener (x,k) is what it is.  Exact integer/Fraction arithmetic only; no floats.

Population: all 7-subsets D of {1..N} with gcd 1 (integer disparity sets, period 1).  Lonely at t iff ||d t|| >= 1/8
for all d in D.  The landing t* is the least positive lonely t; it is an opening t* = (8k+1)/(8x) of some x in D.
Two computations of t* are compared: (cascade) the framework's cascade from 1/(8 d_min), and (openings) the least
clear opening by the Theorem-10 congruence  x <= d(8k+1) mod 8x <= 7x  for all d.
All counts are [OBS]; every identity checked on every set is reported with its number of instances.
Usage: python3 landing_exceptions_v1.py
"""
import sys
from fractions import Fraction as F
from math import gcd, floor, ceil
from itertools import combinations
from functools import reduce
from collections import Counter, defaultdict

def lcm(a, b): return a * b // gcd(a, b)
def frs(x): return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"

def dist_int(x):
    f = x - floor(x)
    return min(f, 1 - f)

def cascade(D):
    t = F(1, 8 * D[0]); chain = []
    while True:
        inway = [d for d in D if dist_int(d * t) < F(1, 8)]
        if not inway: return t, chain
        best = None
        for d in inway:
            j = ceil(d * t - F(1, 8)); nt = (j + F(1, 8)) / d
            if best is None or nt > best[0]: best = (nt, d, j)
        chain.append((t, tuple(inway), (best[1], best[2])))
        t = best[0]

def clear_opening(D, x, k):
    n = 8 * k + 1; m = 8 * x
    return all(x <= (d * n) % m <= 7 * x for d in D)

def landing_openings(D):
    cands = sorted({(F(8 * k + 1, 8 * x)) for x in D for k in range(x)})
    for t in cands:
        p, q = t.numerator, t.denominator
        # t = (8k+1)/(8x): test via any (x,k) that produces it
        pass
    # direct: sort (t,x,k)
    lst = sorted((F(8 * k + 1, 8 * x), x, k) for x in D for k in range(x))
    for t, x, k in lst:
        if clear_opening(D, x, k): return t
    return None

def openers_at(D, t):
    out = []
    for d in D:
        y = d * t
        if y - floor(y) == F(1, 8): out.append((d, floor(y)))
    return out

def pop(N): return [D for D in combinations(range(1, N + 1), 7) if reduce(gcd, D) == 1]

def pr(*a): print(*a)

def analyse_pop(N, verbose_lists=True):
    S = pop(N)
    rec = []
    for D in S:
        t, ch = cascade(D)
        rec.append((D, t, ch))
    pr(f"\n{'='*100}\nPOPULATION N={N}: {len(S)} sets (7-subsets of 1..{N}, gcd 1)\n{'='*100}")
    # (0) independent check
    bad = 0
    for D, t, ch in rec:
        if landing_openings(D) != t: bad += 1
    pr(f"[OBS] landing by cascade == least clear opening (Theorem-10 congruence), mismatches: {bad} of {len(S)}")
    ops = {D: openers_at(D, t) for D, t, ch in rec}
    pr(f"[OBS] every landing is an opening of some x in D: {all(ops[D] for D,_,_ in rec)}; max t* = {frs(max(t for _,t,_ in rec))} (<= 1/2: {max(t for _,t,_ in rec) <= F(1,2)})")
    kbound = all(8 * k + 1 <= 4 * x for D, t, ch in rec for (x, k) in ops[D])
    pr(f"[OBS] 8k+1 <= 4x for every landing opener (k < x/2; consequence of t* <= 1/2): {kbound}")
    # (1) classes by rank and lap
    cl = Counter(); Rr = defaultdict(list); chainlen = defaultdict(Counter)
    for D, t, ch in rec:
        key = tuple(sorted((D.index(x) + 1, k) for x, k in ops[D]))
        cl[key] += 1; Rr[key].append(8 * D[0] * t); chainlen[key][len(ch)] += 1
    pr(f"\n-- (1) classes by (rank of opener, lap k); ties listed together; {len(cl)} classes --")
    pr("class | sets | R* min..max | chain lengths (len:count)")
    for key, v in sorted(cl.items(), key=lambda kv: -kv[1])[:30]:
        pr(f"  {key} | {v} | {frs(min(Rr[key]))}..{frs(max(Rr[key]))} | {dict(sorted(chainlen[key].items()))}")
    byrank = Counter(); byk = Counter()
    for D, t, ch in rec:
        # single "primary" opener: the fastest-rank? use set of all openers; count each opener once
        for x, k in ops[D]:
            byrank[D.index(x) + 1] += 1; byk[k] += 1
    pr("opener rank (count over openers):", dict(sorted(byrank.items())))
    pr("opener lap k (count over openers):", dict(sorted(byk.items())))
    # rank-1 only at lap 0?
    r1 = Counter(k for D, t, ch in rec for x, k in ops[D] if x == D[0])
    pr(f"[OBS] laps at which rank 1 (x = d_min) is an opener of the landing: {dict(r1)};  max R* over the population = {frs(max(8*D[0]*t for D,t,_ in rec))} (< 9, so k>=1 for rank 1 would need R*=8k+1>=9: excluded in this population by that observation, not by a proof)")
    # lap-0 opener must be d_min
    pr(f"[L-style, Theorem 7] a lap-0 opener at the landing is d_min (t* >= 1/(8 d_min) > 1/(8x) for x > d_min): {all(x == D[0] for D,t,ch in rec for (x,k) in ops[D] if k == 0)}")
    # (1b) last-setter identity
    ok = 0; tot = 0
    for D, t, ch in rec:
        tot += 1
        last = (D[0], 0) if not ch else ch[-1][2]
        if last in ops[D]: ok += 1
    pr(f"[OBS] the final cascade setter (or d_min at lap 0 if there is no move) is one of the landing openers: {ok} of {tot}")
    # (1c) blocking certificates
    nopen = 0; nver = 0; viol = 0; blockerrel = Counter(); lapcmp = Counter()
    for D, t, ch in rec:
        bounds = [c[0] for c in ch] + [t]       # t_0 .. t_n
        t0 = bounds[0]
        for x in D:
            for k in range(x):
                tt = F(8 * k + 1, 8 * x)
                if tt >= t: break
                nopen += 1
                if tt < t0: z = D[0]
                else:
                    i = max(i for i in range(len(bounds) - 1) if bounds[i] <= tt)   # tt in [t_i, t_{i+1})
                    z = ch[i][2][0]
                r = (z * (8 * k + 1)) % (8 * x)
                if r < x or r > 7 * x: nver += 1
                else: viol += 1
                blockerrel['z<x' if z < x else ('z=x' if z == x else 'z>x')] += 1
    pr(f"\n-- (1c) blocking certificates --\nearlier openings (x',k') with t' < t*: {nopen}; blocked by the named runner z (z(8k'+1) mod 8x' < x' or > 7x'): {nver}; violations: {viol}")
    pr("[OBS] named blocker vs blocked opener runner:", dict(blockerrel))
    # (1d) ties
    tiebad = 0
    for D, t, ch in rec:
        p, q = t.numerator, t.denominator; c = q // 8
        pred = sorted(d for d in D if d % c == 0 and (d // c) % 8 == p % 8)
        if pred != sorted(x for x, k in ops[D]): tiebad += 1
    pr(f"[OBS] openers at t*=p/(8c) are exactly the d in D with c | d and d/c = p (mod 8): mismatches {tiebad} of {len(S)}")
    multi = Counter(len(ops[D]) for D, t, ch in rec)
    pr("number of simultaneous openers (mult:sets):", dict(sorted(multi.items())))
    # (2) p, g, c
    pr("\n-- (2) p = reduced numerator, g = gcd(8k+1,x), c = x/g --")
    gc = Counter(); pc = Counter(); pmod = Counter(); idbad = 0
    pairs_real = defaultdict(Counter)
    for D, t, ch in rec:
        p, q = t.numerator, t.denominator
        for x, k in ops[D]:
            g = gcd(8 * k + 1, x)
            if (p * g) % 8 != 1 or p % 8 != g % 8 or q != 8 * x // g or p != (8*k+1)//g: idbad += 1
            gc[g] += 1; pmod[p % 8] += 1; pairs_real[g][(x, k)] += 1
    pr(f"[L: Boundaries.opener_unit] p*g = 8k+1, p = g (mod 8), q = 8x/g, checked on every opener: failures {idbad}")
    pr("g over openers:", dict(sorted(gc.items())))
    pr("p mod 8 over openers (= g mod 8):", dict(sorted(pmod.items())))
    pr("p over sets with p<=40 (first opener):", dict(sorted(Counter(t.numerator for D,t,ch in rec).items())[:40]))
    # admissible pairs
    for g in (3, 5, 7, 11, 13, 15, 19, 21):
        adm = [(x, k) for x in range(1, N + 1) if x % g == 0 for k in range(x) if (8 * k + 1) % g == 0 and 8 * k + 1 <= 4 * x and gcd(8*k+1, x) == g]
        real = pairs_real.get(g, {})
        if adm or real:
            pr(f"g={g}: admissible (x,k) with gcd(8k+1,x)=g and 8k+1<=4x: {len(adm)}; realised as landing opener: {len(real)}; sets: {sum(real.values())}")
            if len(adm) <= 12: pr("    admissible:", adm, " realised counts:", {k_: real[k_] for k_ in adm if k_ in real})
    pr(f"landing sets with p mod 8 = 7: {sum(1 for D,t,ch in rec if t.numerator % 8 == 7)}; = 5: {sum(1 for D,t,ch in rec if t.numerator % 8 == 5)}; = 3: {sum(1 for D,t,ch in rec if t.numerator % 8 == 3)}; = 1: {sum(1 for D,t,ch in rec if t.numerator % 8 == 1)}")
    return rec, ops

def rare_detail(N, rec, ops):
    pr(f"\n-- rare classes at N={N} --")
    for target in (7, 5, 3):
        sel = [(D, t, ch) for D, t, ch in rec if t.numerator % 8 == target]
        grp = defaultdict(list)
        for D, t, ch in sel: grp[t].append(D)
        pr(f"p = {target} (mod 8): {len(sel)} sets; distinct landing instants: {len(grp)}")
        for t, Ds in sorted(grp.items(), key=lambda kv: -len(kv[1]))[:12]:
            core = set(Ds[0])
            for D in Ds: core &= set(D)
            ox = sorted({(x,k) for D in Ds for (x,k) in ops[D]})
            pr(f"   t*={frs(t)} (p={t.numerator}, c={t.denominator//8}) sets {len(Ds)} openers {ox} common core {sorted(core)}  R* range {frs(min(8*D[0]*t for D in Ds))}..{frs(max(8*D[0]*t for D in Ds))}")
        if target == 7:
            for D in [s[0] for s in sel]: pr("     ", D)
    # degenerate landing cell (touch) rate among rare classes
    def landing_cell_is_point(D, t):
        # t is a touch point iff a small step to the right is not lonely: test t + 1/(8*L*...) via entry check
        L = reduce(lcm, D); eps = F(1, 64 * L * L)
        return not all(dist_int(d * (t + eps)) >= F(1, 8) for d in D)
    for target in (7, 5, 3, 1):
        sel = [(D, t) for D, t, ch in rec if t.numerator % 8 == target]
        pts = sum(1 for D, t in sel if landing_cell_is_point(D, t))
        pr(f"[OBS] p={target} (mod 8): landing cell is a single point (touch) in {pts} of {len(sel)} sets")

def residues(N, rec, ops):
    pr(f"\n-- (4) residue view, N={N} --")
    def cls(D): return tuple(sorted((D.index(x) + 1, k) for x, k in ops[D]))
    grp = defaultdict(Counter)
    for D, t, ch in rec: grp[tuple(d % 8 for d in D)][cls(D)] += 1
    pur = sum(1 for k, c in grp.items() if len(c) == 1)
    pr(f"(caveat: {len(grp)} patterns for {len(rec)} sets, so a pure pattern is often a single set; purity is weak evidence)")
    pr(f"ordered residue pattern (d_i mod 8, rank order): {len(grp)} patterns, {pur} determine the class (rank,k), {len(grp)-pur} do not")
    ex = [(k, dict(c)) for k, c in grp.items() if len(c) > 1]
    ex.sort(key=lambda kv: (sum(kv[1].values()), kv[0]))
    # minimal counterexample: smallest max element
    best = None
    for D, t, ch in rec:
        for D2, t2, ch2 in [(D, t, ch)]:
            pass
    byp = defaultdict(list)
    for D, t, ch in rec: byp[tuple(d % 8 for d in D)].append((D, cls(D)))
    cands = []
    for pat, L in byp.items():
        cs = {c for _, c in L}
        if len(cs) > 1:
            Ls = sorted(L, key=lambda x: (max(x[0]), x[0]))
            a = Ls[0]
            b = next(y for y in Ls if y[1] != a[1])
            cands.append((max(max(a[0]), max(b[0])), a, b, pat))
    cands.sort()
    for m, a, b, pat in cands[:3]:
        pr(f"   same residues {pat}: {a[0]} -> {a[1]}   vs   {b[0]} -> {b[1]}")
    grp1 = defaultdict(Counter)
    for D, t, ch in rec:
        if D[0] == 1: grp1[tuple(d % 8 for d in D)][cls(D)] += 1
    pur1 = sum(1 for k, c in grp1.items() if len(c) == 1)
    pr(f"d_1 = 1 only (integer ratios; here R = rho x residue mod 8): {len(grp1)} patterns, {pur1} pure")
    # d1 = 1: lap-0 class iff no zero residue
    ok1 = all((cls(D) == ((1, 0),) or (1,0) in cls(D)) == all(d % 8 for d in D) for D, t, ch in rec if D[0] == 1)
    n1 = sum(1 for D, t, ch in rec if D[0] == 1)
    pr(f"[OBS+hand proof] d_1 = 1: landing is (1,0) iff no d = 0 mod 8: holds for all {n1} sets: {ok1}")
    # d_1 > 1: residues mod 8 do not decide lap 0
    fail = 0; tot = 0; exm = None
    for D, t, ch in rec:
        if D[0] > 1:
            tot += 1
            pred = all(d % 8 for d in D); act = (1, 0) in cls(D)
            if pred != act:
                fail += 1
                if exm is None or max(D) < max(exm): exm = D
    pr(f"d_1 > 1: 'no residue 0 mod 8' predicts lap-0 landing wrongly in {fail} of {tot} sets; smallest-max example {exm}")
    # exact lap-0 criterion: d mod 8 d_1 in [d_1, 7 d_1]
    ok2 = all(((1, 0) in cls(D)) == all(D[0] <= d % (8 * D[0]) <= 7 * D[0] for d in D) for D, t, ch in rec)
    pr(f"[L-style, Theorem 7 + certificate] (1,0) is a landing opener iff every d has d mod 8 d_1 in [d_1, 7 d_1]: {ok2} on all {len(rec)} sets")
    # d_1 = 1 with exactly one multiple of 8: first move lap = quotient
    one = [(D, t, ch) for D, t, ch in rec if D[0] == 1 and sum(1 for d in D if d % 8 == 0) == 1]
    first_ok = 0; first_land = 0
    for D, t, ch in one:
        m8 = next(d for d in D if d % 8 == 0)
        z0 = ch[0][2]
        if z0 == (m8, m8 // 8): first_ok += 1
        if len(ch) == 1: first_land += 1
    pr(f"d_1=1, exactly one multiple 8m of 8: {len(one)} sets; first setter is (8m, lap m): {first_ok}; landing after that single move: {first_land}")
    # the lap of the first setter is the quotient: residue pattern cannot see it
    qs = Counter()
    for D, t, ch in one:
        qs[(tuple(d % 8 for d in D), ch[0][2][1])] += 1
    pats = defaultdict(set)
    for (pat, j), v in qs.items(): pats[pat].add(j)
    pr(f"   residue patterns (one zero) whose first-setter lap takes >1 value: {sum(1 for p in pats.values() if len(p) > 1)} of {len(pats)}")

def k_positive_list(N):
    S = pop(N); out = []
    for D in S:
        t, ch = cascade(D); ops = openers_at(D, t)
        if all(k > 0 for x, k in ops) or True:
            out.append((D, t, ch, ops))
    pr(f"\n{'='*100}\n(3) k>0 sets, complete list for N={N}\n{'='*100}")
    kpos = [(D, t, ch, ops) for D, t, ch, ops in out if (D[0], 0) not in ops]
    pr(f"sets {len(out)}; landing not at 1/(8 d_min): {len(kpos)}")
    forb_ok = all((((D[0], 0) not in ops) == any(not (D[0] <= d % (8 * D[0]) <= 7 * D[0]) for d in D)) for D, t, ch, ops in out)
    pr(f"[OBS] landing not at lap 0 of d_min  iff  some d has d mod 8 d_1 outside [d_1,7 d_1] (a forbidden zone |d - 8 m d_1| < d_1, m>=1): {forb_ok}")
    for D, t, ch, ops in kpos:
        pr(f"  {D} t*={frs(t)} openers {[(D.index(x)+1,x,k) for x,k in ops]} forbidden d {[d for d in D if not (D[0] <= d % (8*D[0]) <= 7*D[0])]} first setter {ch[0][2]} chain {[c[2] for c in ch]}")

def kpos_stats(N, rec, ops):
    pr(f"\n-- (3) k>0 statistics, N={N} --")
    kp = [(D, t, ch) for D, t, ch in rec if (D[0], 0) not in ops[D]]
    pr(f"sets with landing not at 1/(8 d_min): {len(kp)} of {len(rec)}")
    ok = all(any(not (D[0] <= d % (8 * D[0]) <= 7 * D[0]) for d in D) for D, t, ch in kp) and \
         all((D[0], 0) not in ops[D] for D, t, ch in rec if any(not (D[0] <= d % (8 * D[0]) <= 7 * D[0]) for d in D))
    pr(f"[OBS] k>0 set == {{some d in a forbidden zone of d_min}}, equality of the two sets of arrangements: {ok}")
    # forbidden zone index m of the first setter
    fm = Counter(); fr = Counter(); smallest_in_F = 0
    for D, t, ch in kp:
        z, j = ch[0][2]
        fm[j] += 1; fr[D.index(z) + 1] += 1
        F_ = [d for d in D if not (D[0] <= d % (8 * D[0]) <= 7 * D[0])]
        if z == min(F_): smallest_in_F += 1
    pr("zone index m (= lap j) of the first setter:", dict(sorted(fm.items())))
    pr("rank of first setter:", dict(sorted(fr.items())))
    pr(f"first setter is the smallest element of the forbidden set F: {smallest_in_F} of {len(kp)}")
    # lap k vs R*: k = floor(R* rho_x / 8)
    kk = all(k == floor(8 * D[0] * t * F(x, D[0]) / 8) for D, t, ch in rec for x, k in ops[D])
    pr(f"[algebra] k = floor(R* rho_x / 8) with rho_x = x/d_min, R* rho_x = 8k+1, on every opener: {kk}")
    # classes for k>0 by lap and rank
    c = Counter((D.index(x) + 1, k) for D, t, ch in kp for x, k in ops[D] if k > 0)
    pr("(rank,k) over k>0 openers, top 20:", c.most_common(20))


def sweep_and_firstsetter(N, rec, ops):
    pr(f"\n-- sweep-down rule and first-setter rule, N={N} --")
    viol = 0; inst = 0; landed_bad = 0; landed_chk = 0
    for D, t, ch in rec:
        d1 = D[0]
        states = [c[0] for c in ch] + [t]
        for i, c in enumerate(ch):
            z, j = c[2]; tn = states[i + 1]
            R = 8 * d1 * tn
            if R < 2 and (z - d1) in D and (z - d1) > 0:
                inst += 1
                inway_next = ch[i + 1][1] if i + 1 < len(ch) else ()
                if (z - d1) not in inway_next: viol += 1
        z, j = ch[-1][2] if ch else (d1, 0)
        if ch and 8 * d1 * t < 2:
            landed_chk += 1
            if (z - d1) in D: landed_bad += 1
    pr(f"[L: neighbour_in_way] at an opening (y,j) with R = 8 d_min t < 2, the runner y - d_min (if in D) is in the way: instances {inst}, violations {viol}")
    pr(f"[consequence] landing opener x with R* < 2 has x - d_min not in D: checked on {landed_chk} landings (chain>=1), violations {landed_bad}")
    # first setter vs smallest forbidden
    D0 = (2, 3, 4, 5, 6, 17, 31)
    t0, ch0 = cascade(D0)
    Fb = [d for d in D0 if not (D0[0] <= d % (8 * D0[0]) <= 7 * D0[0])]
    pr(f"[exception to 'first setter = least forbidden'] D={D0}, d_min 2: forbidden {Fb}; the next opening of 17 (zone m=1) is at R = {frs(F(18,17))}, of 31 (zone m=2) at R = {frs(F(34,31))}, and {frs(F(34,31))} > {frs(F(18,17))}: {F(34,31) > F(18,17)}; first setter is {ch0[0][2]}; landing {frs(t0)}")

def lap_table(N, rec, ops):
    pr(f"\n-- lap k and the divisors of 8k+1, N={N} --")
    pr("k | 8k+1 | divisors mod 8 | p=1 (mod 8) forced? | landing openers at this lap by g")
    cnt = defaultdict(Counter)
    for D, t, ch in rec:
        for x, k in ops[D]: cnt[k][gcd(8 * k + 1, x)] += 1
    for k in range(0, 9):
        n = 8 * k + 1
        divs = [d for d in range(1, n + 1) if n % d == 0]
        cls = sorted({d % 8 for d in divs})
        pr(f"  {k} | {n} | {cls} | {cls == [1]} | {dict(sorted(cnt[k].items()))}")

def growth(N):
    from multiprocessing import Pool
    S = pop(N)
    with Pool(8) as P: R = P.map(landing_pg, S, chunksize=2000)
    pm = Counter(); xs = defaultdict(Counter)
    for pnum, ops in R:
        pm[pnum % 8] += 1
        for x, k in ops:
            g = gcd(8 * k + 1, x)
            if g % 8 != 1: xs[g][(x, k)] += 1
    pr(f"N={N}: sets {len(S)}; landing p mod 8 (per set): {dict(sorted(pm.items()))}")
    for g in sorted(xs):
        pr(f"    g={g} (not 1 mod 8): distinct landing-opener pairs (x,k) {len(xs[g])}, openers {sum(xs[g].values())}")
    sys.stdout.flush()

def landing_pg(D):
    t, ch = cascade(D)
    return t.numerator, openers_at(D, t)

if __name__ == "__main__":
    k_positive_list(11)
    for N in (14, 18, 22):
        rec, ops = analyse_pop(N)
        kpos_stats(N, rec, ops)
        rare_detail(N, rec, ops)
        residues(N, rec, ops)
        sweep_and_firstsetter(N, rec, ops)
        lap_table(N, rec, ops)
    pr('\n' + '='*100 + '\nGROWTH of the g != 1 (mod 8) classes with the population bound N\n' + '='*100)
    for N in (22, 26, 30): growth(N)
