# scale_hierarchy_v1.py  (Task BB, 2026-10-09).  Exact Fractions, no floats, no sampling; every loop is over a finite
# explicit range (subsets of [1,N], windows m <= MW, stages <= 6, laps in carve()), so there is no cascade loop.
#
# Coarse-to-fine insertion of the readings of one subject into the lonely set, in the cascade coordinate R = 8 d_min t
# with readings rho_i = D_i / D_1 (D_1 < ... < D_7 integer disparities, D_1 = d_min).  The window m of d_min is
# [8m+1, 8m+7].  Reading y has zones ((8n-1)/rho, (8n+1)/rho) (width 2/rho) and clear windows [(8n+1)/rho, (8n+7)/rho]
# (length 6/rho).  K_k(m) = the cells of the first k readings inside window m, as exact intervals.  At stage k -> k+1
# the next reading is x = rho_{k+1}; each cell [u,w] of K_k(m) is classified:
#   LC  long-cell survival   : w - u >= 2/x                           (DispCell.long_cell_survives)
#   CL  clear at the left end: not LC, x clear at u                    (survives_iff_opening_or_clear, 1st alternative)
#   OP  opening inside cell  : not LC, x in the way at u, next opening of x is <= w   (2nd alternative)
#   SK  skipped              : otherwise                               (skipped_iff)
# Cross-check on every record: (some cell is not SK)  iff  (K_{k+1}(m) nonempty)   (DispCell.survive_iff).
import sys, itertools
from fractions import Fraction as F
from math import comb
MW = 3          # windows m = 0..MW analysed for every arrangement (the landing window is also reported)
MMAX = 12       # landing window search bound

def clear(x, R):
    return 1 <= (x * R) % 8 <= 7

def next_open(x, u):
    n = int((x * u - 1) // 8)
    cand = F(8 * n + 1) / x
    if cand < u:
        cand = F(8 * (n + 1) + 1) / x
    return cand

def carve(cells, x):
    out = []
    for (u, w) in cells:
        n0 = int((u * x) // 8) - 1
        n1 = int((w * x) // 8) + 1
        for n in range(n0, n1 + 1):
            a = max(u, F(8 * n + 1) / x); b = min(w, F(8 * n + 7) / x)
            if a <= b:
                out.append((a, b))
    return out

def classify(cells, x):
    z = F(2) / x
    ts = []
    for (u, w) in cells:
        if w - u >= z: ts.append('LC')
        elif clear(x, u): ts.append('CL')
        elif next_open(x, u) <= w: ts.append('OP')
        else: ts.append('SK')
    return ts

def window_recs(rho, m):
    """records of stages 1..6 in window m; stops at the first stage whose cell list is empty (dead)."""
    cells = [(F(8 * m + 1), F(8 * m + 7))]
    recs = []
    for k in range(1, 7):
        x = rho[k]
        ts = classify(cells, x)
        nxt = carve(cells, x)
        assert any(t != 'SK' for t in ts) == bool(nxt)
        Lmax = max(w - u for (u, w) in cells)
        recs.append(dict(k=k, x=x, rk=rho[k - 1], cells=cells, Lmax=Lmax, types=ts, nxt=nxt))
        cells = nxt
        if not cells: break
    return recs, bool(cells) and len(recs) == 6

def landing(rho):
    for m in range(MMAX + 1):
        recs, alive = window_recs(rho, m)
        if alive: return m
    return None

THRS = [F(1), F(3, 2), F(2), F(3), F(4), F(6), F(8), F(9), F(16)]

class Acc:
    def __init__(s):
        s.pairs = 0
        s.ff = {}            # (m,k,typeset,outcome) -> [count, example]
        s.allLC = {}         # m -> count (alive, never left LC)
        s.alive = {}         # (m,k) -> number of windows with K_k nonempty (k = cells entering stage k), k=1..7
        s.LC = {}            # (m,k) -> number with an LC cell
        s.typ = {}           # k -> {typeset: count}  (all windows)
        s.qbin = {}          # k -> {bin: count}
        s.tneed = {}         # k -> (max T_need, example)
        s.zeroL = {}         # k -> (count, examples)
        s.viol = {T: {} for T in THRS}
        s.tot = {T: {} for T in THRS}
        s.vex = {T: None for T in THRS}
        s.opener = {}        # (k, j, intratio) -> count of non-LC CL cells
        s.opens = {}         # (k) -> count of non-LC OP cells
        s.land = {}

def bump(d, k, v=1):
    d[k] = d.get(k, 0) + v

def add(acc, D):
    D1 = D[0]; rho = [F(d, D1) for d in D]
    lm = landing(rho)
    bump(acc.land, lm)
    acc.pairs += 1
    for m in range(MW + 1):
        recs, alive = window_recs(rho, m)
        ff = None
        for r in recs:
            k = r['k']
            bump(acc.alive, (m, k))
            hasLC = 'LC' in r['types']
            if hasLC: bump(acc.LC, (m, k))
            key = ''.join(sorted(set(r['types'])))
            acc.typ.setdefault(k, {})
            bump(acc.typ[k], key)
            L = r['Lmax']; x = r['x']; rk = r['rk']
            if L == 0:
                c = acc.zeroL.setdefault(k, [0, []])
                c[0] += 1
                if len(c[1]) < 3: c[1].append((D, m, r['types']))
            else:
                tn = F(2) / (L * rk)
                if k not in acc.tneed or tn > acc.tneed[k][0]: acc.tneed[k] = (tn, (D, m))
                q = (F(2) / x) / L
                b = 'q<=1/2' if q <= F(1, 2) else ('q<=1' if q <= 1 else ('q<=2' if q <= 2 else 'q>2'))
                acc.qbin.setdefault(k, {}); bump(acc.qbin[k], b)
            ratio = x / rk
            for T in THRS:
                if ratio >= T:
                    bump(acc.tot[T], k)
                    if not hasLC:
                        bump(acc.viol[T], k)
                        if acc.vex[T] is None or ratio > acc.vex[T][0]:
                            acc.vex[T] = (ratio, D, m, k, r['types'], L)
            if not hasLC:
                for (u, w), t in zip(r['cells'], r['types']):
                    if t == 'CL':
                        for j in range(k):
                            if (rho[j] * u) % 8 == 1:
                                bump(acc.opener, (k, j + 1, 'int' if (rho[k] / rho[j]).denominator == 1 else 'frac')); break
                        else:
                            bump(acc.opener, (k, 0, 'none'))
                    elif t == 'OP':
                        bump(acc.opens, k)
            if ff is None and not hasLC:
                outc = 'survive' if r['nxt'] else 'dead'
                ff = (m, k, key, outc)
        if ff is None:
            if alive: bump(acc.allLC, m)
            else: ff = (m, 0, 'allLC-then-dead?', 'x')
        if ff is not None and ff[1] != 0:
            c = acc.ff.setdefault(ff, [0, D]); c[0] += 1
    # (a window can only be dead through a non-LC stage: checked by the assert below)

def report(name, acc, out):
    P = lambda *a: print(*a, file=out)
    P("== population %s: %d arrangements; landing window m* %s" % (name, acc.pairs, dict(sorted(acc.land.items(), key=lambda t: (t[0] is None, t[0])))))
    for m in range(MW + 1):
        P("  window m=%d: cells entering stage k (alive), with an LC cell:" % m)
        P("     alive  %s" % [acc.alive.get((m, k), 0) for k in range(1, 7)])
        P("     LC     %s" % [acc.LC.get((m, k), 0) for k in range(1, 7)])
        P("     alive through all seven readings and every stage had an LC cell: %d" % acc.allLC.get(m, 0))
        for key in sorted(k for k in acc.ff if k[0] == m):
            c = acc.ff[key]
            P("     first non-LC stage %d->%d  types %-9s outcome %-8s count %8d  e.g. D=%s" % (key[1], key[1] + 1, key[2], key[3], c[0], c[1]))
    P("  cell-type-set histogram per stage (all windows):")
    for k in range(1, 7): P("     stage %d: %s" % (k, dict(sorted(acc.typ.get(k, {}).items()))))
    P("  q = (2/x)/Lmax (long-cell ratio of the longest cell), histogram per stage:")
    for k in range(1, 7): P("     stage %d: %s" % (k, dict(sorted(acc.qbin.get(k, {}).items()))))
    P("  T_need = 2/(Lmax*rho_k) = the least x/rho_k that makes the longest cell long; max per stage (exact):")
    for k in range(1, 7):
        if k in acc.tneed: P("     stage %d: %s  at D,m=%s" % (k, acc.tneed[k][0], acc.tneed[k][1]))
    P("  records whose longest cell has length 0 (touch cells; T_need undefined = infinite): per stage count, first examples")
    for k in range(1, 7):
        if k in acc.zeroL: P("     stage %d: %d  %s" % (k, acc.zeroL[k][0], acc.zeroL[k][1]))
    P("  non-LC clear-left cells by (stage k, index j of the reading whose opening is the left end, x_{k+1}/rho_j integer?):")
    P("     %s" % dict(sorted(acc.opener.items())))
    P("  non-LC opening-inside cells by stage: %s" % dict(sorted(acc.opens.items())))
    P("  hypothesis H(T): x_{k+1} >= T x_k  =>  some cell of K_k(m) is long.  violations / records with ratio >= T per stage k=1..6, worst ratio:")
    for T in THRS:
        P("     T=%-5s viol %s of %s  worst %s" % (T, [acc.viol[T].get(k, 0) for k in range(1, 7)], [acc.tot[T].get(k, 0) for k in range(1, 7)], acc.vex[T]))
    P("")
    out.flush()

def run(name, sets, out):
    acc = Acc()
    for D in sets: add(acc, D)
    report(name, acc, out)

def cascade_landing(rho, limit=400):
    """exact cascade in R: start at 1; move to the largest next opening among the readings in the way; fixed point = landing.
    Move limit `limit` (returns None if reached)."""
    R = F(1)
    for _ in range(limit):
        best = None
        for r in rho:
            y = r * R
            # in the way iff distance of y to the nearest multiple of 8 is < 1
            n = round(y / 8)
            if abs(y - 8 * n) < 1:
                # next opening: the least (8n'+1)/r that is >= R  where y within (8n-1, 8n+1)
                cand = F(8 * n + 1) / r
                if best is None or cand > best: best = cand
        if best is None: return R
        R = best
    return None

def xcheck(out, N):
    # cross-check of the window carving against the exact cascade: the cascade's landing R* is the left end of the first cell
    # of the lonely set; in particular R* lies in window 0 iff K_7(0) is nonempty, and then R* = left end of its first cell.
    ok = bad = 0
    for D in itertools.combinations(range(1, N + 1), 7):
        rho = [F(d, D[0]) for d in D]
        Rs = cascade_landing(rho)
        recs, alive = window_recs(rho, 0)
        if alive:
            first = min(u for (u, w) in recs[-1]['nxt'])
            if Rs == first: ok += 1
            else: bad += 1
        else:
            if Rs is not None and Rs > 7: ok += 1
            else: bad += 1
    print("== xcheck N=%d: cascade landing vs first cell of K_7(0): agree %d, disagree %d (cascade move limit 400)" % (N, ok, bad), file=out)

def witness(out):
    # Exact window-level refutation of H(T) for every T: stage-6 prefixes whose longest cell in window m has length 0
    # (touch cells; T_need infinite), then a seventh disparity D7 with D7/D6 >= T.  The prefix cells do not depend on D7.
    P = lambda *a: print(*a, file=out)
    P("== witness: H(T) fails at window level for every T (prefix with only touch cells in window m, then D7 >= T*D6)")
    N = 16
    shown = 0
    for D6 in itertools.combinations(range(1, N + 1), 6):
        rho = [F(d, D6[0]) for d in D6]
        for m in range(0, MW + 1):
            cells = [(F(8 * m + 1), F(8 * m + 7))]
            for k in range(1, 6):
                cells = carve(cells, rho[k])
                if not cells: break
            if cells and max(w - u for (u, w) in cells) == 0:
                shown += 1
                if shown <= 3:
                    P("   prefix D=%s window m=%d: cells entering stage 6 = %s" % (D6, m, [(str(u), str(w)) for (u, w) in cells]))
                    for T in (2, 3, 4, 8, 16, 100, 1000):
                        D7 = D6[-1] * T + 1
                        Dfull = D6 + (D7,)
                        rho7 = [F(d, Dfull[0]) for d in Dfull]
                        ts = classify(cells, rho7[6])
                        recs, alive = window_recs(rho7, m)
                        P("      T=%-4d D7=%d ratio D7/D6=%s: types at stage 6->7 %s ; window m=%d K_7 nonempty: %s" % (T, D7, F(D7, D6[-1]), ts, m, alive))
    P("   prefixes (6-subsets of [1,%d], windows 0..%d) whose cells in some window are all touch cells: %d" % (N, MW, shown))
    # exact check of touch_survives_at_eighths: a touch cell at R = a (x*u = M/8 with M = a*D7/D1 an integer) is cleared by D7
    # iff 8 does not divide M.  D7 runs over D6+1 .. D6+400 for every touch prefix; cells with M not an integer are skipped.
    agree = disagree = skipped = 0
    for D6 in itertools.combinations(range(1, N + 1), 6):
        rho = [F(d, D6[0]) for d in D6]
        for m in range(0, MW + 1):
            cells = [(F(8 * m + 1), F(8 * m + 7))]
            for k in range(1, 6):
                cells = carve(cells, rho[k])
                if not cells: break
            if cells and max(w - u for (u, w) in cells) == 0:
                for D7 in range(D6[-1] + 1, D6[-1] + 401):
                    x = F(D7, D6[0])
                    for (u, w) in cells:
                        M = x * u
                        if M.denominator != 1:
                            skipped += 1; continue
                        pred = (int(M) % 8 != 0)
                        act = (classify([(u, w)], x)[0] != 'SK')
                        if pred == act: agree += 1
                        else: disagree += 1
    P("   touch_survives_at_eighths check over all touch prefixes, D7 in D6+1..D6+400: agree %d, disagree %d, skipped (x*R not an integer) %d" % (agree, disagree, skipped))
    out.flush()

if __name__ == '__main__':
    out = sys.stdout
    which = sys.argv[1:] or ['16', '20', '24', 'fam']
    if 'xcheck' in which:
        xcheck(out, 16); xcheck(out, 20)
    if 'witness' in which:
        witness(out)
    for N in (16, 20, 24):
        if str(N) in which: run("7-subsets of [1,%d] (%d)" % (N, comb(N, 7)), itertools.combinations(range(1, N + 1), 7), out)
    if 'fam' in which:
        run("scaled family {1..6, 8j}, j=1..40", [tuple(list(range(1, 7)) + [8 * j]) for j in range(1, 41)], out)
        run("{1..6, 8j+r}, j=1..12, r=1..7", [tuple(list(range(1, 7)) + [8 * j + r]) for j in range(1, 13) for r in range(1, 8)], out)
        for K in range(1, 7):
            fam = [tuple(list(range(1, K + 1)) + list(rest)) for rest in itertools.combinations(range(K + 1, 25), 7 - K)]
            run("K-block family: AP prefix {1..%d} then %d readings in [%d,24] (%d)" % (K, 7 - K, K + 1, len(fam)), fam, out)
