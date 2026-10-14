# Task CJ, second stage of the one-multiple family.  [OBS] Fractions only, deterministic populations, no sampling.
# Family: D' = k-subset of the non-multiples of 8 in {1..N}, c in {1..Cmax}, x = 8c.  Populations listed in POPS.
# Cells of D' in [0,1] (one_multiple_cells_v1.cells).  Dominant class as in one_multiple_residue_v1.py: the cell 0 of D'
# dies under x (disp x u0 > w0) and x u0 is an integer and 8 min(D',x) u0 is an integer.  Later cells i >= 1 are walked
# until a cell passes (disp x u <= w).  Left end u of each walked cell is a D' opener u = (8j+1)/(8d).
# Residue prediction (Lean: SecondStage.displacement_at_opening): r = c(8j+1) mod d;
#   d <= 8r <= 7d : clear, step 0;  8r < d : step (1/8 - r/d)/x;  7d < 8r : step (9/8 - r/d)/x.
# Every cascade loop below has move limit 400 (cascade() of one_multiple_cells_v1).
import sys
from fractions import Fraction as F
from math import gcd, floor
from itertools import combinations
from collections import Counter
sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/experiments/n8')
from one_multiple_cells_v1 import cells, clear, disp, cascade

POPS = [(4, 20, 12), (5, 18, 8), (6, 16, 8)]


def openers(D, u):
    out = []
    for d in D:
        v = 8 * d * u - 1
        if v.denominator == 1 and v >= 0 and v % 8 == 0:
            out.append((d, int(v) // 8))
    return out


def predict(c, d, j):
    r = (c * (8 * j + 1)) % d
    x = 8 * c
    if d <= 8 * r <= 7 * d:
        return r, 'clear', F(0)
    if 8 * r < d:
        return r, 'below', (F(1, 8) - F(r, d)) / x
    return r, 'above', (F(9, 8) - F(r, d)) / x


def walk(k, N, Cmax):
    """Yield one record per walked cell end (dominant class)."""
    nonmult = [d for d in range(1, N + 1) if d % 8]
    recs = []
    pairs = 0
    dom = 0
    nosurv = []
    for D in combinations(nonmult, k):
        C = cells(D)
        if not C:
            continue
        u0, w0 = C[0]
        for c in range(1, Cmax + 1):
            pairs += 1
            x = 8 * c
            if disp(x, u0) <= w0:
                continue
            if not ((8 * min(min(D), x) * u0).denominator == 1 and x * u0 == int(x * u0)):
                continue
            dom += 1
            surv = None
            for i in range(1, len(C)):
                u, w = C[i]
                ops = openers(D, u)
                recs.append(dict(D=D, c=c, i=i, u=u, w=w, ops=ops, x=x))
                p = disp(x, u)
                if p <= w:
                    surv = i
                    break
            if surv is None:
                nosurv.append((D, c))
    return recs, pairs, dom, nosurv


def main():
    print("[OBS] second_stage_v1: Fractions only; populations", POPS)
    allfail = {}
    for (k, N, Cmax) in POPS:
        recs, pairs, dom, nosurv = walk(k, N, Cmax)
        print()
        print(f"== [OBS] population k={k} N={N} Cmax={Cmax}: pairs={pairs}, dominant-class pairs={dom}, "
              f"walked cell ends={len(recs)}, dominant pairs with no passing cell among cells 1..end: {len(nosurv)}")
        mism = 0          # residue prediction against DispCell step, over every opener of every walked end
        noop = 0
        multi_disagree = 0
        st = Counter()
        fails = []
        dvd_cnt = Counter()
        for R in recs:
            D, c, i, u, w, x = R['D'], R['c'], R['i'], R['u'], R['w'], R['x']
            if not R['ops']:
                noop += 1
                continue
            actual = disp(x, u) - u
            sts = set()
            for (d, j) in R['ops']:
                r, s, step = predict(c, d, j)
                if step != actual:
                    mism += 1
                sts.add((s, step))
            if len(sts) > 1:
                multi_disagree += 1
            d, j = R['ops'][0]
            r, s, step = predict(c, d, j)
            fit = step <= w - u
            st[(s, fit)] += 1
            if r == 0:
                dvd_cnt[(s, step == F(1, 8 * x), fit)] += 1
            if not fit:
                fails.append((D, c, i, d, j, r, s, w - u, step))
        print(f"  [OBS] ends without D' opener: {noop}; ends where residue prediction differs from DispCell step "
              f"(counted per opener): {mism}; ends where two openers give different predictions: {multi_disagree}")
        print("  [OBS] (status, step fits in cell) counts:", dict(sorted(st.items())))
        print("  [OBS] ends with d | c(8j+1) (r = 0): (status, step == 1/(8x), cell passes) counts:",
              dict(sorted(dvd_cnt.items())))
        print(f"  [OBS] failing cell ends (step > cell length): {len(fails)}; by cell index:",
              dict(sorted(Counter(f[2] for f in fails).items())))
        allfail[(k, N, Cmax)] = (fails, recs)
        if k == 4:
            print("  [OBS] every failing cell end at k = 4: (D', c, cell index i, d, j, r, status, cell length w-u, extra step)")
            for f in fails:
                print("   ", f[0], f[1], f[2], f[3], f[4], f[5], f[6], str(f[7]), str(f[8]))
        else:
            tab = Counter()
            for (D, c, i, d, j, r, s, L, step) in fails:
                tab[(d, j, gcd(8 * j + 1, d), r if s == 'below' else r, s)] += 1
            print("  [OBS] table of failing ends (d, j, gcd(8j+1,d), r, status): count")
            for key, v in sorted(tab.items()):
                print("   ", key, v)
        # pattern tests on the whole population of failing ends
        pb = [f for f in fails if f[6] == 'below']
        pa = [f for f in fails if f[6] == 'above']
        exb = [f for f in pb if f[5] != 0]
        exa = [f for f in pa if f[3] - f[5] != 1]
        print(f"  [OBS] pattern PB: every failing 'below' end has r = 0 (d | c(8j+1)): "
              f"{len(pb) - len(exb)} of {len(pb)}; others: {len(exb)}")
        for f in exb:
            print("      PB exception:", f[0], f[1], "i=", f[2], "d,j,r=", f[3], f[4], f[5], "len", str(f[7]), "step", str(f[8]))
        print(f"  [OBS] pattern PA: every failing 'above' end has d - r = 1: "
              f"{len(pa) - len(exa)} of {len(pa)}; others: {len(exa)}")
        for f in exa:
            print("      PA exception:", f[0], f[1], "i=", f[2], "d,j,r=", f[3], f[4], f[5], "len", str(f[7]), "step", str(f[8]))
        exs = [f for f in fails if not ((f[6] == 'below' and f[5] <= 1) or (f[6] == 'above' and f[3] - f[5] <= 2))]
        print(f"  [OBS] pattern P*: every failing end has (below and r <= 1) or (above and d - r <= 2): "
              f"{len(fails) - len(exs)} of {len(fails)}; others: {len(exs)}")
        for f in exs:
            print("      P* exception:", f[0], f[1], "i=", f[2], "d,j,r=", f[3], f[4], f[5], f[6], "len", str(f[7]), "step", str(f[8]))
        print("  [OBS] j values among failing ends:", dict(sorted(Counter(f[4] for f in fails).items())),
              "; (d - r) among failing above ends:", dict(sorted(Counter(f[3] - f[5] for f in pa).items())),
              "; r among failing below ends:", dict(sorted(Counter(f[5] for f in pb).items())))
        # quantities of the failing cells in x-units
        mx_b = max((8 * f[1] * f[7] for f in pb), default=None)
        mx_a = max((8 * f[1] * f[7] for f in pa), default=None)
        print("  [OBS] largest x*(w-u) among failing below ends:", mx_b, "; among failing above ends:", mx_a)
        print("  [OBS] failing ends with cell length 0 (a touch):", sum(1 for f in fails if f[7] == 0),
              "; with 0 < length:", sum(1 for f in fails if f[7] > 0))
        # ends in the same population where x is blocked and the cell passes (pattern is not sufficient)
        blocked_pass = Counter()
        for R in recs:
            if not R['ops']:
                continue
            d, j = R['ops'][0]
            r, s, step = predict(R['c'], d, j)
            if s != 'clear' and step <= R['w'] - R['u']:
                blocked_pass[(s, r == 0 if s == 'below' else d - r == 1)] += 1
        print("  [OBS] ends with x blocked and the cell passing, by (status, in-pattern):", dict(sorted(blocked_pass.items())))
        # cascade cross-check (move limit 400) for the pairs with a failing end
        pairs_fail = sorted(set((f[0], f[1]) for f in fails))
        agree = dis = unfinished = 0
        for (D, c) in pairs_fail:
            C = cells(D)
            x = 8 * c
            land = None
            for (u, w) in C:
                if disp(x, u) <= w:
                    land = disp(x, u)
                    break
            t, n = cascade(list(D) + [x], 400)
            if t is None:
                unfinished += 1
            elif t == land:
                agree += 1
            else:
                dis += 1
        print(f"  [OBS] pairs with a failing end: {len(pairs_fail)}; cascade (limit 400) lands at the DispCell landing of the "
              f"first passing cell in [0,1]: {agree}; differs: {dis}; unfinished: {unfinished}")

    # D. period d in c, residue against DispCell on a grid of (d, j, c)
    print()
    print("== [OBS] grid test: d in 1..40, j in 0..12, c in 1..3d (u = (8j+1)/(8d)), deterministic")
    bad_pred = bad_per = bad_clear = 0
    tot = 0
    for d in range(1, 41):
        for j in range(0, 13):
            u = F(8 * j + 1, 8 * d)
            for c in range(1, 3 * d + 1):
                x = 8 * c
                tot += 1
                r, s, step = predict(c, d, j)
                if disp(x, u) - u != step:
                    bad_pred += 1
                if clear(x, u) != (s == 'clear'):
                    bad_clear += 1
                c2 = c + d
                x2 = 8 * c2
                r2, s2, step2 = predict(c2, d, j)
                if (r2, s2) != (r, s) or x2 * (disp(x2, u) - u) != x * (disp(x, u) - u):
                    bad_per += 1
    print(f"  triples={tot}; residue prediction differs from DispCell step: {bad_pred}; clear status differs: {bad_clear}; "
          f"(status, x*displacement) differs between c and c+d: {bad_per}")
    # lap line
    bad_lap = 0
    nlap = 0
    for d in range(1, 41):
        for j in range(0, 13):
            u = F(8 * j + 1, 8 * d)
            for c in range(1, 3 * d + 1):
                x = 8 * c
                dv = ((c * (8 * j + 1)) % d == 0)
                if dv != ((x * u).denominator == 1):
                    bad_lap += 1
                if dv:
                    nlap += 1
                    if disp(x, u) - u != F(1, 8 * x):
                        bad_lap += 1
                else:
                    if disp(x, u) - u == F(1, 8 * x):
                        bad_lap += 1
    print(f"  [OBS] d | c(8j+1) iff x u integer, and step == 1/(8x) iff d | c(8j+1): violations {bad_lap} (cases with d | c(8j+1): {nlap})")

    # E. number of clear residues, coprime classes
    print()
    print("== [OBS] number of clear residues r in [0,d): d <= 8r <= 7d against floor(7d/8) - ceil(d/8) + 1, d in 1..200")
    badc = 0
    for d in range(1, 201):
        n = sum(1 for r in range(d) if d <= 8 * r <= 7 * d)
        f = (7 * d) // 8 - (-(-d // 8)) + 1
        if n != f:
            badc += 1
    print("  mismatches:", badc)
    print("  small d (d: count):", {d: sum(1 for r in range(d) if d <= 8 * r <= 7 * d) for d in range(1, 17)})
    badk = 0
    ntest = 0
    badg = 0
    ngt = 0
    for d in range(1, 61):
        for kk in range(0, 25):
            a = 8 * kk + 1
            cnt = sum(1 for c in range(d) if d <= 8 * ((c * a) % d) <= 7 * d)
            if gcd(a, d) == 1:
                ntest += 1
                if cnt != (7 * d) // 8 - (-(-d // 8)) + 1:
                    badk += 1
            else:
                g = gcd(a, d)
                ngt += 1
                pred = g * sum(1 for r in range(d) if r % g == 0 and d <= 8 * r <= 7 * d)
                if cnt != pred:
                    badg += 1
    print(f"  classes c mod d leaving x clear, gcd(8k+1,d) = 1: formula violated in {badk} of {ntest} (d,k);"
          f" gcd > 1: count == g * #{{clear residues divisible by g}} violated in {badg} of {ngt} (d,k)  [OBS for gcd > 1]")


main()
