# Task CL (2026-10-11): one-multiple family, larger exact populations, chain of failing cells.
# D' = every k-subset of the non-multiples of 8 in {1..N}; x = 8c, c in {1..C}.  Exact integer arithmetic (no floats,
# no random sampling).  Cells of D' = closed gaps between merged open zones inside [0,1] (a touch is a gap of length 0).
# A cell [u,w] survives x iff disp x u <= w (DispCell.survive_iff).  The residue form (SecondStage.survives_cell_extraStep_iff)
# is used for speed; the Fraction form disp x u <= w is run on every traversed cell when VERIFY=1, and the full cascade
# (move limit 400) is run on every pair that has at least one failing cell.
# usage: python3 one_multiple_exists_v1.py k N C [verify_all(0/1)] [list_min_chain]
import sys
from fractions import Fraction as F
from itertools import combinations
from math import floor, gcd
from multiprocessing import Pool

def lcm(a, b): return a // gcd(a, b) * b

def cells_int(D):
    """cells of D' as integer pairs (U, W) over S = 8*lcm(D); also returns L, S"""
    L = 1
    for d in D: L = lcm(L, d)
    S = 8 * L
    Z = []
    for d in D:
        a = L // d
        for j in range(d + 1):
            Z.append((a * (8 * j - 1), a * (8 * j + 1)))
    Z.sort()
    out = []; e = None
    for s, t in Z:
        if e is None: e = t; continue
        if s < e:
            if t > e: e = t
        else:
            out.append((e, s)); e = t
    return [(u, w) for (u, w) in out if u >= 0 and w <= S], L, S

def opener(D, U, L):
    res = []
    for d in D:
        q, rem = divmod(d * U, L)
        if rem == 0:
            v = q - 1
            if v >= 0 and v % 8 == 0: res.append((d, v // 8))
    return res

def clearF(d, t):
    f = d * t - floor(d * t); return F(1, 8) <= f <= F(7, 8)
def dispF(x, a):
    if clearF(x, a): return a
    j = floor(x * a + F(1, 8)); return F(8 * j + 1, 8 * x)
def cascadeF(ds, limit=400):
    m = min(ds); t = F(1, 8 * m); n = 0
    while n < limit:
        bl = [d for d in ds if not clearF(d, t)]
        if not bl: return t, n
        d = max(bl, key=lambda d: F(8 * floor(d * t + F(1, 8)) + 1, 8 * d))
        t = F(8 * floor(d * t + F(1, 8)) + 1, 8 * d); n += 1
    return None, n

def work(args):
    first, nonmult, k, C, verify_all, list_min = args
    rest = [d for d in nonmult if d > first]
    st = dict(pairs=0, chain={}, surv_idx={}, nosurv=0, law_mismatch=0, casc_checked=0, casc_mismatch=0, casc_unfinished=0,
              fail_kind={'touch': 0, 'positive': 0}, listed=[], same_zone=0, diff_zone=0, sets=0, sets_cells0=0)
    for tail in combinations(rest, k - 1):
        D = (first,) + tail
        cs, L, S = cells_int(D)
        st['sets'] += 1
        if not cs: st['sets_cells0'] += 1; continue
        ops = [opener(D, U, L)[0] for (U, W) in cs]   # (d, j); every cell left end is an opening (LonelyCells.cell_left_end_is_opening)
        for c in range(1, C + 1):
            x = 8 * c; st['pairs'] += 1
            f = 0; rows = []; surv = None
            for i, (U, W) in enumerate(cs):
                d, j = ops[i]; M = c * (8 * j + 1); r = M % d
                if d <= 8 * r <= 7 * d: ok = True; sn = 0
                else:
                    sn = (d - 8 * r) if 8 * r < d else (9 * d - 8 * r)
                    ok = sn * S <= (W - U) * 64 * c * d
                if verify_all or True:
                    pass
                if verify_all:
                    okF = dispF(x, F(U, S)) <= F(W, S)
                    if okF != ok: st['law_mismatch'] += 1
                rows.append((i, U, W, d, j, r, sn, ok))
                if ok: surv = i; break
                f += 1
            if surv is None:
                st['nosurv'] += 1; st['listed'].append(('NOSURV', D, c)); continue
            st['chain'][f] = st['chain'].get(f, 0) + 1
            st['surv_idx'][surv] = st['surv_idx'].get(surv, 0) + 1
            if f >= 1:
                for (i, U, W, d, j, r, sn, ok) in rows[:-1]:
                    st['fail_kind']['touch' if U == W else 'positive'] += 1
                # law and cascade check on this pair
                for (i, U, W, d, j, r, sn, ok) in rows:
                    if (dispF(x, F(U, S)) <= F(W, S)) != ok: st['law_mismatch'] += 1
                t, n = cascadeF(list(D) + [x])
                st['casc_checked'] += 1
                i, U, W, d, j, r, sn, ok = rows[-1]
                if t is None: st['casc_unfinished'] += 1
                else:
                    # first lonely instant of the union at or after the cascade start 1/(8 d_min) must equal the first surviving
                    # cell's survivor point disp x u (law); the cascade lands at the least lonely instant (LonelyCells)
                    if t != dispF(x, F(U, S)): st['casc_mismatch'] += 1
                if f >= list_min:
                    zs = [round(F(x * rr[1], S)) for rr in rows]
                    if len(set(zs[:-1])) == 1: st['same_zone'] += 1
                    else: st['diff_zone'] += 1
                    st['listed'].append(('CHAIN', D, c, f, [(rr[0], str(F(rr[1], S)), str(F(rr[2], S)), rr[3], rr[4], rr[5], str(F(rr[6], 64 * c * rr[3])) if rr[6] else '0', str(F(rr[2] - rr[1], S)), 'pass' if rr[7] else 'fail', int(round(F(x * rr[1], S)))) for rr in rows]))
            elif verify_all and False:
                pass
    return st

def merge(a, b):
    for key in ('pairs', 'nosurv', 'law_mismatch', 'casc_checked', 'casc_mismatch', 'casc_unfinished', 'same_zone', 'diff_zone', 'sets', 'sets_cells0'):
        a[key] += b[key]
    for key in ('chain', 'surv_idx', 'fail_kind'):
        for kk, v in b[key].items(): a[key][kk] = a[key].get(kk, 0) + v
    a['listed'] += b['listed']

def main(k, N, C, verify_all, list_min):
    nonmult = [d for d in range(1, N + 1) if d % 8]
    tasks = [(first, nonmult, k, C, verify_all, list_min) for first in nonmult if len([d for d in nonmult if d > first]) >= k - 1]
    tot = None
    with Pool(10) as p:
        for st in p.imap_unordered(work, tasks, chunksize=1):
            if tot is None: tot = st
            else: merge(tot, st)
    ch = dict(sorted(tot['chain'].items()))
    print(f"POP k={k} N={N} C={C} verify_all={verify_all}: sets={tot['sets']} pairs={tot['pairs']} nosurvivor={tot['nosurv']} "
          f"leading-failing-cells(counts of pairs)={ch} max={max(ch)} survivor-index={dict(sorted(tot['surv_idx'].items()))} "
          f"failing-cells touch/positive={tot['fail_kind']} law-vs-residue mismatches={tot['law_mismatch']} "
          f"cascade checked on pairs with >=1 failing cell={tot['casc_checked']} cascade mismatches={tot['casc_mismatch']} unfinished={tot['casc_unfinished']} "
          f"chains>= {list_min}: same x-zone for all failing cells={tot['same_zone']}, different zones={tot['diff_zone']}", flush=True)
    for e in sorted(tot['listed'], key=lambda e: (e[1], e[2])):
        if e[0] == 'NOSURV': print("NOSURVIVOR", e[1], e[2])
        else:
            print(f"  CHAIN D'={e[1]} c={e[2]} failing={e[3]}")
            for row in e[4]:
                print("     cell#%d [u=%s, w=%s] opener (d=%d, j=%d) r=%d step=%s len=%s %s xzone N=%d" % (row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7], row[8], row[9]))

if __name__ == "__main__":
    k, N, C = map(int, sys.argv[1:4])
    va = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    lm = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    main(k, N, C, va, lm)
