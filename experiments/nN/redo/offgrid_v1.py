"""Owner: map how the cascade moves the grid's isolation points when the speeds are moved off the grid, as E69 did from
the progression.  For a target V (eight positive whole-number speeds), the NEAREST GRID G: each speed moved by at most 4,
order kept, residues mod 8 all different (minimising the largest move, then the total).  Path v(s) = (1-s)G + sV (every
speed positive, order kept).  For every runner k: the cascade isolation R_k(s) = 8 d_min t on 300 steps, jumps located
by bisection to 2^-40; each jump classed forward (pinch) or back (birth); at s = 0 whether the isolation is a phi(8)
instant a/(8g) of the grid; at s = 1 whether V's isolation descends from the grid's by carried motion only (no jump).
Exact (Fraction)."""
import random, itertools
from fractions import Fraction as F
from math import gcd
from functools import reduce
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import readings, cascade

def nearest_grid(V):
    best = None
    for delta in range(0, 5):
        # DP over runners: choose shifts in [-delta, delta] with distinct residues, increasing speeds
        states = {(frozenset(), None): (0, [])}
        for v in V:
            new = {}
            for (used, last), (cost, path) in states.items():
                for sh in range(-delta, delta + 1):
                    w = v + sh
                    if w <= 0 or (last is not None and w <= last) or (w % 8) in used: continue
                    key = (used | {w % 8}, w); c2 = cost + abs(sh)
                    if key not in new or new[key][0] > c2: new[key] = (c2, path + [w])
            states = new
        if states:
            c, G = min(states.values(), key=lambda x: x[0])
            return G, delta
    return None, None

def iso(v, k):
    ds = readings(v, k); t, mv = cascade(ds); return 8 * min(ds) * t, t

def run(V):
    G, delta = nearest_grid(V)
    if G is None: return None
    g = reduce(gcd, [b - a for a in G for b in G if b > a])
    at = lambda s: [a + s * (b - a) for a, b in zip(map(F, G), map(F, V))]
    out = []
    for k in range(8):
        R0, t0 = iso(G, k)
        phi0 = any(t0 == F(a, 8 * g) for a in (1, 3, 5, 7))
        N = 300; prev = None; fwd = back = 0
        for q in range(0, N + 1):
            s = F(q, N); R, t = iso(at(s), k)
            if prev is not None and abs(R - prev) > F(1, 50):
                if R > prev: fwd += 1
                else: back += 1
            prev = R
        out.append((k, float(R0), phi0, fwd, back, float(prev)))
    return V, G, delta, g, out

if __name__ == '__main__':
    rnd = random.Random(41)
    Vs = [sorted(rnd.sample(range(1, 200), 8)) for _ in range(60)]
    with Pool() as pool: res = [r for r in pool.map(run, Vs) if r]
    rows = [(V, G, d, g) + o for V, G, d, g, out in res for o in out]
    n = len(rows)
    print(f"targets {len(res)}; largest speed move to the nearest grid: {sorted(Counter(r[2] for r in res).items())}")
    print(f"subjects {n}: grid isolation (cascade) at a phi(8) instant: {sum(r[6] for r in rows)}")
    print(f"  relocations along the path (forward pinch, back birth) per subject: {sorted(Counter((r[7], r[8]) for r in rows).items())[:24]}")
    print(f"  carried the whole way (no relocation): {sum(1 for r in rows if r[7] + r[8] == 0)}")
    print(f"  R at the grid: max {max(r[5] for r in rows):.3f}; R at the target: max {max(r[9] for r in rows):.3f}")
    for V, G, d, g, out in res[:3]:
        print(f"  V {V} <- grid {G} (moves <= {d}, g = {g}): " + "; ".join(f"runner {k}: R {a:.3f}{' phi' if p else ''} -> {b:.3f} ({f}f,{bk}b)" for k, a, p, f, bk, b in out))
