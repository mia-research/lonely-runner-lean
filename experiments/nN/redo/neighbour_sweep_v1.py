"""Owner: "test the cascade and find out" what "runners are always bound by their neighbours' speed" means for the
isolation.  Sweep each runner of an arrangement through its whole range between its two speed neighbours (slowest:
(v_2/8, v_2); fastest: (v_7, v_7 + (v_7 - v_1)); positive speeds throughout), 240 exact steps, and at every step run the
cascade for EVERY runner as subject.  Record R = 8 d_min t of each runner's event, where d_min is its gap to its nearer
speed neighbour; whether it lies in the nearer neighbour's first clear band (R <= 7); and, when it does not, the
subject's spread ratio S = d_max/d_min.  Exact (Fraction); the cascade is capped at 10^5 moves (a cap hit is reported)."""
import random
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import readings, cascade

def sweep(args):
    V, i = args; steps = 240
    if i == 0: lo, hi = F(V[1], 8), F(V[1])
    elif i == 7: lo, hi = F(V[6]), F(V[6] + (V[6] - V[0]))
    else: lo, hi = F(V[i - 1]), F(V[i + 1])
    out = []
    for q in range(1, steps):
        W = list(map(F, V)); W[i] = lo + (hi - lo) * q / steps
        for k in range(8):
            ds = readings(W, k)
            t, mv = cascade(ds)
            R = 8 * ds[0] * t; S = ds[-1] / ds[0]
            out.append((i, k, R, S, mv))
    return out

if __name__ == '__main__':
    rnd = random.Random(2610); arrs = []
    for _ in range(20): arrs.append(sorted(rnd.sample(range(1, 400), 8)))
    with Pool() as pool: res = [x for part in pool.map(sweep, [(V, i) for V in arrs for i in range(8)]) for x in part]
    n = len(res); R7 = sum(1 for r in res if r[2] <= 7)
    print(f"sweeps: 20 arrangements x 8 runners x 239 steps; subject events {n}")
    print(f"  every event found (no cap hit): {all(r[2] is not None for r in res)}")
    print(f"  event in the nearer neighbour's first clear band (R <= 7): {R7} of {n}")
    late = [r for r in res if r[2] > 7]
    print(f"  events past it: {len(late)}; R range {float(min(r[2] for r in late)) if late else '-'} .. {float(max(r[2] for r in late)) if late else '-'}")
    print(f"  their spread ratio S: min {float(min(r[3] for r in late)) if late else '-'}, max {float(max(r[3] for r in late)) if late else '-'}")
    print(f"  late events by subject's speed rank: {sorted(Counter(r[1] for r in late).items())}; by swept runner: {sorted(Counter(r[0] for r in late).items())}")
    print(f"  R overall max {float(max(r[2] for r in res)):.4f}; events with R in (7, 9): {sum(1 for r in res if 7 < r[2] < 9)}")
    print(f"  R <= 7 whenever S <= 7 (R1): {all(r[2] <= 7 for r in res if r[3] <= 7)}")
    bins = Counter(min(int(r[3]), 30) for r in late)
    print(f"  late events by floor(S): {sorted(bins.items())}")
