"""Before proving the neighbour bound in Case C (R = 8 g_1 t <= 15 for the slowest runner, g_1 its gap to the nearer
neighbour, W > 24 g_1), push R itself as high as the cascade allows.  Exact.  Starts: the 1,350 Case C arrangements'
every 10th, plus hand-built shapes that make the nearest band tight (runner 3 also close: d_2 in (g_1, 2 g_1)), trains
of 3..6 near d_2 and near the top, and near-progressions of the six at step ~ g_1..3 g_1 with one far outlier.
Moves: one of the six other speeds by an integer step (speeds x16, g_1 and the subject fixed; order, distinctness,
W > 24 g_1 kept; every speed positive), accepted when R does not fall.  Report the largest R found, its readings in
units of g_1, and whether it lies in the first band (R <= 7), the second (9 <= R <= 15), or beyond."""
import sys, random
from fractions import Fraction as F
from multiprocessing import Pool
from arrangement_lib import cascade

def R_of(V):
    ds = sorted(v - V[0] for v in V[1:]); t, mv = cascade(ds)
    return 8 * ds[0] * t, ds

def ok(V, g1):
    return all(V[i] < V[i + 1] for i in range(7)) and V[1] - V[0] == g1 and V[7] - V[0] > 24 * g1

def climb(args):
    V, seed, iters = args
    rnd = random.Random(seed); g1 = V[1] - V[0]; cur, _ = R_of(V)
    for _ in range(iters):
        j = rnd.randrange(2, 8)
        span = max(1, (V[j] - V[j - 1]) // rnd.choice((2, 8, 32, 128)))
        W = list(V); W[j] += rnd.choice((-1, 1)) * rnd.randint(1, span)
        if not ok(W, g1): continue
        r, _ = R_of(W)
        if r >= cur: V, cur = W, r
    r, ds = R_of(V)
    return float(r), [round(float(F(d, ds[0])), 4) for d in ds], V

def starts():
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        import case_c_map_v1 as cm
    cm.rnd.seed(26); out = []; n = 0
    for shape in ('even', 'clumped+outliers', 'even+clump'):
        for g1div in (30, 100, 1000):
            c = 0
            while c < 150:
                g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
                if g1 + W6 <= 22 * g1: continue
                V = cm.arrangement([g1] + g)
                if len(set(V)) < 8: continue
                c += 1; n += 1
                if n % 10 == 0 and V[-1] - V[0] > 24 * g1: out.append([16 * v for v in V])
    rnd = random.Random(99); g1 = 64
    for _ in range(60):                       # hand-built shapes, g_1 = 64 (x16 units)
        kind = rnd.randrange(4); base = 1000
        if kind == 0:   # runner 3 also close; the rest spread to W > 24 g1
            r = [g1, g1 + rnd.randint(1, g1)] ; x = r[-1]
            for _ in range(5): x += rnd.randint(g1, 12 * g1); r.append(x)
        elif kind == 1: # a train of k near d_2
            k = rnd.randint(3, 6); D = rnd.randint(2 * g1, 6 * g1); r = [g1] + [D + rnd.randint(0, g1 // 2) * i for i in range(k)]
            x = r[-1]
            while len(r) < 7: x += rnd.randint(g1, 20 * g1); r.append(x)
        elif kind == 2: # near-progression of the six with step ~ g1..3 g1, one far outlier
            step = rnd.randint(g1, 3 * g1); r = [g1] + [g1 + step * i + rnd.randint(-2, 2) for i in range(1, 6)]
            r.append(r[-1] + rnd.randint(25 * g1, 60 * g1))
        else:           # a train at the top
            r = [g1, g1 + rnd.randint(g1, 4 * g1)]; D = rnd.randint(25 * g1, 80 * g1)
            r += sorted(set(D + rnd.randint(0, 3 * g1) for _ in range(5)))
        r = sorted(set(r))
        if len(r) != 7 or r[0] != g1 or r[-1] <= 24 * g1: continue
        out.append([base] + [base + d for d in r])
    return out

if __name__ == '__main__':
    iters = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    S = starts()
    with Pool() as pool: res = pool.map(climb, [(V, 11 + i, iters) for i, V in enumerate(S)])
    res.sort(key=lambda r: -r[0])
    print(f"starts {len(S)}, {iters} proposals each")
    print(f"R reached: first band (<= 7) {sum(r[0] <= 7 for r in res)}, (7, 9) {sum(7 < r[0] < 9 for r in res)}, "
          f"second band [9, 15] {sum(9 <= r[0] <= 15 for r in res)}, beyond 15 {sum(r[0] > 15 for r in res)}")
    for r in res[:15]:
        print(f"  R {r[0]:.4f}  readings/g1 {r[1]}  V {r[2]}")
