"""Map of deformations through crowded slots (owner, 2026-09-26: two runners crowding a single slot; sensitive, it
slips into a different scale).  Exact.  Along a path moving one runner, for each subject:
  R = 8 d_min t* (the event on the subject's AP scale), the moves, the event's lonely CELL [t*, t_end] with its length
  L = d_min (t_end - t*) in laps of the nearest runner (L = 0: an isolated, doubly pinned instant = tight), the runner
  pinning the start (reads exactly 1/8) and the runner closing the cell.
Jumps (R changes) and tight points (no lonely cell of positive length for R <= 16) are what the deformation theorem's local-stability hypothesis must handle:
L > 0 is margin (lonelyAt_of_close); L = 0 needs a two-pinner lemma.  Speeds all positive, nobody at rest."""
from fractions import Fraction as F
from math import floor, ceil
from arrangement_lib import nd
G = 840
def cascade(ds):
    t = F(1, 8 * min(ds)); n = 0
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, n
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way); n += 1
def cell(ds, t):
    # first instant > = t at which some runner enters a zone: zone left end (m - 1/8)/d with m - 1/8 >= d t
    best = None; who = None
    for d in ds:
        m = ceil(d * t + F(1, 8))
        te = (m - F(1, 8)) / d
        if best is None or te < best: best, who = te, d
    return best, who
def best_cell(ds, Rmax=16):
    """longest lonely cell with t in (0, Rmax/(8 d_min)], by the boundary set method: the zone endpoints
    (m +/- 1/8)/d cut the axis into cells; a cell is decided by an interior point (its midpoint); isolated lonely
    points (both neighbouring cells blocked) have length 0.  Returns (length in laps of d_min, any lonely instant?)."""
    dmin = min(ds); T = F(Rmax, 8 * dmin)
    pts = {T}
    for d in ds:
        for m in range(0, int(d * T) + 2):
            for e in (m - F(1, 8), m + F(1, 8)):
                x = e / d
                if 0 < x <= T: pts.add(x)
    pts = sorted(pts); best = F(-1)
    for a, b in zip(pts, pts[1:]):
        mid = (a + b) / 2
        if all(nd(d * mid) >= F(1, 8) for d in ds): best = max(best, b - a)
    if best < 0:
        if any(all(nd(d * x) >= F(1, 8) for d in ds) for x in pts): best = F(0)
    return dmin * best
def row(V, sub):
    vs = V[sub]; ds = sorted({abs(v - vs) for i, v in enumerate(V) if i != sub})
    t, n = cascade(ds); dmin = min(ds); R = 8 * dmin * t
    te, closer = cell(ds, t); L = dmin * (te - t)
    pin = [i + 1 for i, v in enumerate(V) if i != sub and nd(abs(v - vs) * t) == F(1, 8) and (abs(v - vs) * t) % 1 == F(1, 8)]
    cl = [i + 1 for i, v in enumerate(V) if i != sub and abs(v - vs) == closer]
    Lmax = best_cell(ds)
    return R, n, L, pin, cl, Lmax
def path(name, base, j, deltas, subjects):
    print(f"\n=== {name}: runner {j} moved from speed {base[j-1]}")
    for sub in subjects:
        print(f"  subject runner {sub}")
        prevR = None; tight = jumps = 0; lines = []
        for dl in deltas:
            V = list(base); V[j - 1] += dl
            if len(set(V)) < 8 or min(V) <= 0: continue
            R, n, L, pin, cl, Lmax = row(V, sub - 1)
            flag = ''
            if L == 0: flag += ' first-cell-point'
            if Lmax == 0: flag += ' TIGHT(no cell with interior in R<=16)'; tight += 1
            if prevR is not None and R != prevR: flag += ' jump'; jumps += 1
            lines.append(f"    delta={dl:>5d}  R={str(R):>9s} ({float(R):6.3f})  moves={n:>2d}  cell L={float(L):6.4f} longest cell {float(Lmax):6.4f}  pinned by {pin} closed by {cl}{flag}")
            prevR = R
        for l in lines: print(l)
        print(f"    -> jumps {jumps}, tight points {tight}")
# 1. the AP with runners 3 and 4 crowded into one slot: runner 4 moved down toward 3
ap = [k * G for k in range(1, 9)]
crowd = list(ap); crowd[3] = 3 * G + 60          # runner 4 sits 60 above runner 3 (a crowded slot)
path("AP with runners 3,4 crowding one slot; runner 4 moved", crowd, 4,
     [-50, -30, -10, 0, 10, 30, 60, 100, 150, 210, 280, 360, 450, 560, 700], [1, 3, 4, 8])
# 2. crowded pair at the top: runners 7, 8 close; runner 8 moved
crowd2 = list(ap); crowd2[7] = 7 * G + 40
path("AP with runners 7,8 crowding one slot; runner 8 moved", crowd2, 8,
     [-30, -10, 0, 20, 60, 120, 200, 300, 420, 560, 700, 790], [1, 7, 8, 4])
# 3. a late-event arrangement (two other runners close), its close pair pulled apart
late = [1, 31, 75, 97, 128, 160, 176, 225]
path("late case (1,31,75,97,128,160,176,225): runner 7 (176, close to 160) moved", late, 7,
     [-12, -8, -4, -2, -1, 0, 1, 2, 4, 8, 12, 20, 30, 40], [1, 8])
