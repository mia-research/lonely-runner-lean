"""Owner: isolation is proved globally at the progression (scale free, residues mod 8); any arrangement deforms the circle
geometry and relocates it; the cascade + BSM give exactly where every runner is at any runner's isolation point.  Use it.
Path v(s) = (1 - s) v_AP + s V from the progression v_AP (same slowest speed and spread as V; positive speeds, order
kept) to V.  For EVERY runner k as subject, at every step: the cascade isolation instant t_k(s) from k's bound, and the
position of every other runner j on k's circle, p_j = frac((v_j - v_k) t_k), in eighths of a lap.  Exact (Fraction).
At each relocation (t_k jumps; bisected to 2^-40) record the geometry just before and just after: every runner's position,
which runner held the isolation (sitting exactly at 1/8 or 7/8, the pinner), and which runner's arrival displaced it."""
import sys, random
from fractions import Fraction as F
from math import floor
from arrangement_lib import nd

def iso(v, k):
    ds = [v[j] - v[k] for j in range(8) if j != k]
    others = [j for j in range(8) if j != k]
    dm = min(abs(d) for d in ds); t = F(1, 8) / dm; setter = None
    while True:
        way = [i for i, d in enumerate(ds) if nd(d * t) < F(1, 8)]
        if not way: break
        cand = {i: (F(floor(abs(ds[i]) * t - F(1, 8)) + 1) + F(1, 8)) / abs(ds[i]) for i in way}
        i = max(cand, key=lambda x: cand[x]); t = cand[i]; setter = others[i]
    pos = {others[i]: (ds[i] * t) % 1 for i in range(7)}
    return t, pos, setter, dm

def geom(pos):
    return ' '.join(f"{j}:{float(8 * p):.2f}" for j, p in sorted(pos.items(), key=lambda x: x[1]))

def path(V, k, N=400):
    W = V[-1] - V[0]; AP = [V[0] + F(W * i, 7) for i in range(8)]
    at = lambda s: [a + s * (b - a) for a, b in zip(AP, V)]
    rows = []; prev = None
    for q in range(1, N + 1):
        s = F(q, N); t, pos, setter, dm = iso(at(s), k); R = 8 * dm * t
        if prev is not None and abs(R - prev[1]) > F(1, 50):
            lo, hi = prev[0], s
            for _ in range(40):
                mid = (lo + hi) / 2; Rm = 8 * iso(at(mid), k)[3] * iso(at(mid), k)[0]
                if abs(Rm - prev[1]) <= F(1, 50) * (1 + 0): lo = mid; prev = (mid, Rm)
                else: hi = mid
            tb, pb, sb, db = iso(at(lo), k); ta, pa, sa, da = iso(at(hi), k)
            rows.append((float(lo), float(8 * db * tb), sb, geom(pb), float(8 * da * ta), sa, geom(pa)))
        prev = (s, R)
    return rows, iso(at(F(1)), k)

if __name__ == '__main__':
    rnd = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    V = sorted(rnd.sample(range(1, 200), 8))
    print(f"target V {V}; progression with the same slowest speed and spread")
    for k in range(8):
        W = V[-1] - V[0]; AP = [V[0] + F(W * i, 7) for i in range(8)]
        t0, p0, s0, d0 = iso([a + F(1, 10**6) * (b - a) for a, b in zip(AP, V)], k)
        rows, (t1, p1, s1, d1) = path(V, k)
        print(f"\n== subject {k}: just off the progression R {float(8*d0*t0):.3f} pinned by {s0}; geometry (runner:eighths) {geom(p0)}")
        for r in rows:
            print(f"   s {r[0]:.5f}: R {r[1]:.3f} pinned by {r[2]} [{r[3]}]  ->  R {r[4]:.3f} pinned by {r[5]} [{r[6]}]")
        print(f"   at V: R {float(8*d1*t1):.3f} pinned by {s1}; geometry {geom(p1)}")
