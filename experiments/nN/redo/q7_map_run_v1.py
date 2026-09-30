"""E213/E214 (2026-10-01): the Q7 map run.  Why the slowest reading's first clear stretch closes only in the band.

Owner: "yes, design the Q7 map run first, then run it".  Design: log E213.  Units: readings s = d/m (m the least), R = 8mt.
A reading is in the way while its position s*R mod 8 lies in (-1, 1) (strict; boundary points clear, BSM).  Its exit on
lap k is R = (8k+1)/s, its entry (8k-1)/s.  The first clear stretch is R in [1, 7].

Parts:
  A. The tight wide set (E212) perturbed through the exact cascade, one reading at a time (least fixed as the scale),
     delta in {+-1, +-3, +-10, +-30, +-100, +-300, +-1000} at scale 27,720: landing R, setter, queue front (E204), in [1,7].
     The grid/deviation split (E208) of its two tight junctions on the slowest reading's grid.
  B. The 300 final sets of E212's wide walk: every such move; where the cascade lands next, against the interval holding
     the landing before the move: s same interval; e another interval already clear; n a place newly uncovered by the
     move; m n bounded by the old landing's pair (by rank) in mirror orientation; x beyond 7.  Every x listed.
  C. The band's closures: the same walk with spread in (7, 9]; at each step that empties the first stretch: the moved
     reading, the slivers its move uncovered in [1, 7] (M4-2), which readings cover each sliver afterwards and on which
     lap, and whether a coverer bounded an interval that closed.
Checks (the only pass conditions): C1, the cascade's landing equals the least clear point from `clear_set` (no cascade);
M4-1, that point is R = 1 or an exit; M4-3, the mirror algebra at the tight set.
"""
import sys, math, random
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from e151_block_v1 import trace
import wide_first_stretch_walk_v1 as W

D = W.D
TIGHT = (27720, 85358, 117495, 140959, 159149, 200880, 258489)
DELTAS = [1, 3, 10, 30, 100, 300, 1000]


def pos(s, R):
    return (s * R) % 8


def landing(T):
    """The exact cascade: landing R, setter values, queue front value, the checks."""
    T = tuple(sorted(T)); m = T[0]; s = [F(d, m) for d in T]
    ts, moves = trace(T)
    R = 8 * m * ts
    setter = moves[-1][2] if moves else ()
    q = sorted(((F(7, 8) - (c * ts - math.floor(c * ts))) / c, c) for c in T)
    front = q[0][1]
    hi = max(F(40), R + 1)
    least = clear_set(s, F(1), hi)[0][0]
    c1 = (least == R)
    m41 = (least == 1) or any(pos(x, least) == 1 for x in s)
    return R, setter, front, c1, m41


def intervals(T, lo=F(1), hi=F(7)):
    T = tuple(sorted(T)); return clear_set([F(d, T[0]) for d in T], lo, hi)


def bounding(T, iv):
    """Values of the readings at the interval's ends: exiting (position 1) at the left, entering (position 7) at the right."""
    T = tuple(sorted(T)); a, b = iv
    left = tuple(d for d in T if pos(F(d, T[0]), a) == 1)
    right = tuple(d for d in T if pos(F(d, T[0]), b) == 7)
    return left, right


def holding(ivs, R):
    return next((iv for iv in ivs if iv[0] <= R <= iv[1]), None)


def moved(T, i, dl, lo=9, hi=12):
    U = list(T); U[i] += dl
    if len(set(U)) < 7 or min(U) != T[0] or U.index(min(U)) != 0:
        return None
    U = tuple(sorted(U))
    if not (lo * D < U[-1] <= hi * D):
        return None
    return U


# ---------------- A -------------------------------------------------------------------------------------------
def part_a(w):
    w("\n== A. the tight wide set %s, spread %.4f ==" % (TIGHT, TIGHT[-1] / D))
    s = [F(d, D) for d in TIGHT]
    ivs = intervals(TIGHT)
    w("  first stretch: %s" % [(str(a), str(b)) for a, b in ivs])
    a, b = 2, 6                                                     # ranks of 117495 and 258489
    w("  CHECK M4-3: ratio %s; 33*25 == 15*55: %s; s_b*15 == s_a*33: %s; s_a*55 == s_b*25: %s" %
      (s[b] / s[a], 33 * 25 == 15 * 55, s[b] * 15 == s[a] * 33, s[a] * 55 == s[b] * 25))
    n = [round(x) for x in s]; dv = [x - k for x, k in zip(s, n)]
    for name, X, PX, Y, PY in (('b exits at 33, a enters at 15', b, 33, a, 15), ('a exits at 25, b enters at 55', a, 25, b, 55)):
        G = PY * s[X] - PX * s[Y]
        g = PY * n[X] - PX * n[Y]
        w("  junction %s: gap %s = grid %s + deviation %s (grid readings %s, %s)" % (name, G, g, G - g, n[X], n[Y]))
    R0, st, fr, c1, m41 = landing(TIGHT)
    w("  landing R %s (%.5f), setter %s, queue front %s; C1 %s; M4-1 %s" % (R0, float(R0), st, fr, c1, m41))
    w("  perturbations (rank moved, delta): landing R, in [1,7], setter, front, clear intervals in [1,7]")
    bad = 0
    for i in range(1, 7):
        for sg in (1, -1):
            for d in DELTAS:
                U = moved(TIGHT, i, sg * d, lo=7, hi=20)
                if U is None:
                    w("    rank %d %+d: skipped (order or scale changed)" % (i, sg * d)); continue
                R, st, fr, c1, m41 = landing(U)
                bad += (not c1) + (not m41)
                iv = intervals(U)
                w("    rank %d %+5d: R %.5f %s setter %s front %s | %d intervals, widest %.3g" %
                  (i, sg * d, float(R), 'in' if R <= 7 else 'OUT', st, fr, len(iv), float(max((y - x for x, y in iv), default=-1))))
    w("  CHECK C1 and M4-1 over part A: %d failures" % bad)


# ---------------- B -------------------------------------------------------------------------------------------
def final_sets():
    rng = random.Random(212); starts = []
    from coverB_fine_v1 import late_shapes
    L = late_shapes()
    for T in rng.sample(L, 150):
        p = rng.randrange(1, 6); u = rng.choice((9.001, 9.05, 9.5))
        S = sorted((set(T) - {T[p]}) | {int(u * D)})
        if len(S) == 7:
            starts.append(S)
    while len(starts) < 300:
        Wt = int(rng.uniform(9.001, 12) * D)
        S = sorted({D, Wt} | {rng.randrange(D + 1, Wt) for _ in range(5)})
        if len(S) == 7:
            starts.append(S)
    return starts


def study_b(T):
    T = tuple(sorted(T))
    R0, st0, fr0, c1, m41 = landing(T)
    pre = intervals(T)
    I0 = holding(pre, R0)
    pair0 = bounding(T, I0)
    rows = []; checks = (not c1) + (not m41)
    for i in range(1, 7):
        for sg in (1, -1):
            for d in DELTAS:
                U = moved(T, i, sg * d)
                if U is None:
                    rows.append(('skip', i, sg * d, None)); continue
                R, st, fr, c1, m41 = landing(U)
                checks += (not c1) + (not m41)
                if R > 7:
                    rows.append(('x', i, sg * d, U)); continue
                post = intervals(U)
                I1 = holding(post, R)
                if I1[0] <= I0[1] and I0[0] <= I1[1]:
                    cls = 's'
                elif any(I1[0] <= b and a <= I1[1] for a, b in pre):
                    cls = 'e'
                else:
                    new = T[i] + sg * d
                    orig = lambda v: T[i] if v == new else v             # identity: the moved reading keeps its name
                    l1 = {orig(v) for v in bounding(U, I1)[0]}; r1 = {orig(v) for v in bounding(U, I1)[1]}
                    mirror = bool(l1 & set(pair0[1])) and bool(r1 & set(pair0[0]))
                    cls = 'm' if mirror else 'n'
                    rows.append((cls, i, sg * d, (T[i] in l1, T[i] in r1, tuple(l1), tuple(r1)))); continue
                rows.append((cls, i, sg * d, None))
    return T, pair0, len(pre), rows, checks


def part_b(w, pool):
    starts = final_sets()
    res = pool.map(W.walk, [(k, s, 4000) for k, s in enumerate(starts)])
    finals = [r[1] for r in res]
    out = pool.map(study_b, finals)
    checks = sum(o[4] for o in out)
    w("\n== B. the %d final sets of E212's wide walk, every move ==" % len(out))
    w("  CHECK C1 and M4-1 over part B: %d failures" % checks)
    C = Counter(); Cin = Counter(); nleft = Counter(); X = []
    for T, pair0, npre, rows, _ in out:
        inpair = set(pair0[0]) | set(pair0[1])
        for cls, i, dl, info in rows:
            C[cls] += 1
            if cls != 'skip':
                Cin[(T[i] in inpair, cls)] += 1
            if cls == 'x':
                X.append((T, i, dl, info))
            if cls in ('n', 'm'):
                nleft[(cls, 'moved reading exits at the new left end' if info[0] else 'another reading exits there',
                       'moved reading enters at the new right end' if info[1] else 'another enters there')] += 1
    w("  classes over all moves: %s" % dict(C))
    w("  by (moved reading bounds the old landing interval, class): %s" % dict(sorted(Cin.items())))
    w("  newly uncovered landings, by who bounds them: %s" % dict(nleft))
    w("  x (first stretch emptied by one move): %d" % len(X))
    for T, i, dl, U in X[:40]:
        w("    %s rank %d %+d -> %s" % (T, i, dl, U))
    npre = Counter(min(o[2], 6) for o in out)
    w("  clear intervals in [1,7] at the final sets: %s" % dict(sorted(npre.items())))


# ---------------- C -------------------------------------------------------------------------------------------
def walk_band(args):
    seed, start, steps = args
    rng = random.Random(seed); T = list(start); best = W.widest(T)
    for _ in range(steps):
        U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-600, 601); U = sorted(set(U))
        if len(U) < 7 or U[0] != D or not (7 * D < U[-1] <= 9 * D):
            continue
        sc = W.widest(U)
        if sc <= best:
            if sc < 0 <= best:
                return (tuple(T), tuple(U))
            T, best = U, sc
    return None


def windows(x, lo=F(1), hi=F(7)):
    out = []
    k = max(0, math.floor((lo * x + 1) / 8) - 1)
    while True:
        a, b = F(8 * k - 1) / x, F(8 * k + 1) / x
        if a > hi:
            break
        if b > lo:
            out.append((max(a, lo), min(b, hi), k))
        k += 1
    return out


def minus(A, B):
    """Intervals of A not inside B (A, B lists of (lo, hi, ...)); open/closed ends ignored at this resolution."""
    res = []
    for a in A:
        pieces = [(a[0], a[1])]
        for b in B:
            nxt = []
            for lo, hi in pieces:
                if b[1] <= lo or b[0] >= hi:
                    nxt.append((lo, hi)); continue
                if lo < b[0]:
                    nxt.append((lo, b[0]))
                if b[1] < hi:
                    nxt.append((b[1], hi))
            pieces = nxt
        res += pieces
    return [p for p in res if p[1] > p[0]]


def study_c(ev):
    pre, post = ev
    x0 = next(d for d in pre if d not in post); x1 = next(d for d in post if d not in pre)
    s0, s1 = F(x0, D), F(x1, D)
    ivs = intervals(pre)
    closers = [bounding(pre, iv) for iv in ivs]
    rk_pre = sorted(pre).index(x0)
    x_bounds = any(x0 in l or x0 in r for l, r in closers)
    bound_vals = {v for l, r in closers for v in l + r if v != x0}
    slivers = minus(windows(s0), windows(s1))
    others = [F(d, D) for d in post if d != x1]
    cov = []
    for lo, hi in slivers:
        mid = (lo + hi) / 2
        inway = [y for y in others if (y * mid) % 8 > 7 or (y * mid) % 8 < 1]
        who = [(int(y * D), math.floor((y * mid + 1) / 8)) for y in inway]     # (value, lap) at the sliver's midpoint
        partner = any(int(y * D) in bound_vals for y in inway)
        cov.append((float(lo), float(hi), who, partner))
    R, st, fr, c1, m41 = landing(post)
    return dict(pre=pre, post=post, x=(rk_pre, x0, x1, 'faster' if x1 > x0 else 'slower'), n_pre=len(ivs),
                closed=[(str(a), str(b), bounding(pre, (a, b))) for a, b in ivs], x_bounds=x_bounds, slivers=cov,
                R=R, c1=c1, m41=m41, spread=pre[-1] / D)


def part_c(w, pool):
    rng = random.Random(213); starts = []
    while len(starts) < 600:
        Wt = int(rng.uniform(7.001, 9) * D)
        S = sorted({D, Wt} | {rng.randrange(D + 1, Wt) for _ in range(5)})
        if len(S) == 7:
            starts.append(S)
    evs = [e for e in pool.map(walk_band, [(k, s, 4000) for k, s in enumerate(starts)]) if e]
    out = pool.map(study_c, evs)
    w("\n== C. the band's closures: %d walks of 600 emptied the first stretch ==" % len(out))
    w("  CHECK C1 and M4-1 at the closed sets: %d failures" % sum((not o['c1']) + (not o['m41']) for o in out))
    w("  the moved reading: rank %s; direction %s" % (dict(sorted(Counter(o['x'][0] for o in out).items())),
                                                      dict(Counter(o['x'][3] for o in out))))
    w("  clear intervals in [1,7] just before the closing move: %s" % dict(sorted(Counter(o['n_pre'] for o in out).items())))
    w("  the moved reading bounded a closing interval: %s" % dict(Counter(o['x_bounds'] for o in out)))
    w("  landing after the closing move (R): %s" % dict(sorted(Counter(math.floor(o['R']) for o in out).items())))
    ns = Counter(len(o['slivers']) for o in out)
    w("  slivers uncovered by the closing move inside [1,7]: %s" % dict(sorted(ns.items())))
    pc = Counter(sl[3] for o in out for sl in o['slivers'])
    w("  slivers covered by a reading that bounded a closing interval: %s" % dict(pc))
    ncov = Counter(len(sl[2]) for o in out for sl in o['slivers'])
    w("  number of readings covering a sliver: %s" % dict(sorted(ncov.items())))
    for o in out[:12]:
        w("    %s spread %.4f move rank %d %s (%d -> %d); closed %s; slivers %s; lands R %.4f" %
          (o['pre'], o['spread'], o['x'][0], o['x'][3], o['x'][1], o['x'][2], o['closed'],
           [(round(a, 5), round(b, 5), who) for a, b, who, p in o['slivers']], float(o['R'])))


if __name__ == '__main__':
    out = open('q7_map_run_v1.out', 'w'); out.write(__doc__ + "\n"); w = lambda s: (out.write(s + "\n"), out.flush())
    part_a(w)
    with Pool(8) as pool:
        part_b(w, pool)
        part_c(w, pool)
    out.close()
    print(open('q7_map_run_v1.out').read()[len(__doc__):])
