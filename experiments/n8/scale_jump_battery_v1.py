"""Scale-jump battery.  All times: least lattice L on the runner's own d_min (u = d_min*t = p/(8L), p odd,
every lap in one period) at which it is lonely.  Dead lattice (own frame): L dead iff some reading
s = e/d_min is an integer multiple of 8L.  Predicted scale = least L that is not dead."""
import sys, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from itertools import combinations
from collections import Counter
from multiprocessing import Pool
E = F(1, 8)
def fr(x): return x - floor(x)
def dist(x): x = fr(x); return min(x, 1 - x)
def least_L(V, i, Lmax=20):
    ds = [abs(V[j] - V[i]) for j in range(len(V)) if j != i]; m = min(ds)
    den = reduce(lambda a, b: a * b // gcd(a, b), [F(d).denominator for d in ds])
    g = F(reduce(gcd, [int(d * den) for d in ds]), den)
    laps = int(m / g) + 1
    for L in range(1, Lmax + 1):
        for p in range(1, 8 * L * laps, 2):
            if all(dist(d * F(p, 8 * L) / m) >= E for d in ds):
                return L, F(p, 8 * L), m
    return None, None, m
def predicted_L(V, i):
    ds = [abs(V[j] - V[i]) for j in range(len(V)) if j != i]; m = min(ds)
    s = [F(d) / m for d in ds]
    return next(L for L in range(1, 1000) if not any(x.denominator == 1 and x.numerator % (8 * L) == 0 for x in s))
def sides(V, i, t):
    rel = {j: fr((V[j] - V[i]) * t) for j in range(len(V)) if j != i}
    lo, hi = min(rel.values()), max(rel.values())
    return frozenset(j for j in rel if rel[j] == hi), frozenset(j for j in rel if rel[j] == lo)
def ap_expected(i, a):
    c = 1 if a % 8 in (1, 7) else 3
    return {(i - c) % 8, (i + c) % 8}
def one(V):
    out = []
    for i in range(len(V)):
        L, u, m = least_L(V, i); P = predicted_L(V, i)
        out.append((i, L, u, m, P))
    return V, out

def T1():
    print("T1  r8 moved from the AP; neighbours at each runner's time (labels = AP index, cyclic).")
    print("    ok = the AP event's neighbours for that instant (+-1 at phase 1,7; +-3 at 3,5); L=2 rows show raw sides")
    c = Counter(); rows = []
    for s in [F(8)] + [F(x, 100) for x in (850, 890, 899, 900, 901, 910, 950)] + [F(x, 2) for x in range(20, 34)]:
        V = [F(j + 1) for j in range(7)] + [s]
        cells = []
        for i in range(8):
            L, u, m = least_L(V, i); t = u / m; b, a = sides(V, i, t)
            txt = "/".join(f"r{j+1}" for j in sorted(b)) + "|" + "/".join(f"r{j+1}" for j in sorted(a))
            if L == 1 and m == 1:
                ok = {min(b), min(a)} == ap_expected(i, int(8 * u)) and len(a) == len(b) == 1
                c[("scale 1, d_min 1", ok)] += 1; txt += "" if ok else "*"
            else:
                c[(f"scale {L}, d_min {m}", "raw")] += 1
            cells.append(f"L{L} {txt}")
        rows.append(f"   r8={float(s):>5.2f}: " + "  ".join(cells))
    print("\n".join(rows)); print("   tally:", dict(c), "  (* = not the AP event's neighbours)")

def T2():
    print("\nT2  two runners on r1's slot at once: speeds (1,2,3,4,5,6, 1+8a, 1+8b); r1's scale vs dead-lattice prediction")
    for a, b in [(1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (2, 6), (3, 6), (4, 6), (4, 8), (6, 10), (6, 12), (12, 30)]:
        V = [F(v) for v in (1, 2, 3, 4, 5, 6, 1 + 8 * a, 1 + 8 * b)]
        L, u, m = least_L(V, 0); P = predicted_L(V, 0)
        print(f"   a={a:>2} b={b:>2}: dead {[s for s in range(1, 40) if a % s == 0 or b % s == 0][:10]}  predicted {P}  actual L={L} u={u}  {'AGREE' if L == P else 'DIFFERENT'}")
    print("   different subjects at once: r8 on r1's slot (9) and r7 on r2's slot (10) -> speeds (1,2,3,4,5,6,10,9) sorted")
    V = sorted([F(v) for v in (1, 2, 3, 4, 5, 6, 10, 9)])
    for i, L, u, m, P in one(V)[1]:
        print(f"     runner {V[i]}: predicted {P} actual L={L} u={u}")

def T3():
    print("\nT3  integer battery: every runner, predicted scale (first not-dead) vs actual least lonely scale")
    rng = random.Random(16)
    fams = [("all 8-subsets of [1,16], gcd 1", [tuple(F(v) for v in c) for c in combinations(range(1, 17), 8) if reduce(gcd, c) == 1]),
            ("random [1,100]", [tuple(F(v) for v in sorted(rng.sample(range(1, 101), 8))) for _ in range(1500)]),
            ("random [1,1000]", [tuple(F(v) for v in sorted(rng.sample(range(1, 1001), 8))) for _ in range(400)]),
            ("AP (1..8) with two runners pushed onto slots: (1..6, k1+8a, k2+8b)",
             [tuple(sorted({F(v) for v in (1, 2, 3, 4, 5, 6, k1 + 8 * a, k2 + 8 * b)})) for k1 in range(1, 9) for k2 in range(1, 9)
              for a in range(1, 5) for b in range(1, 5)])]
    with Pool(8) as pool:
        for name, arrs in fams:
            arrs = [V for V in arrs if len(V) == 8]
            res = pool.map(one, arrs, chunksize=16)
            c = Counter(); diff = Counter(); ex = []
            for V, out in res:
                for i, L, u, m, P in out:
                    c["runners"] += 1
                    if L is None: c["no scale <= 20"] += 1; continue
                    c["scale 1"] += L == 1
                    c["predicted == actual"] += L == P
                    if L != P:
                        diff[L - P] += 1
                        if len(ex) < 4: ex.append(([int(v) for v in V], int(V[i]), f"pred {P} actual {L} u={u} d_min={m}"))
            print(f"   {name}: {dict(c)}; actual minus predicted where different: {dict(sorted(diff.items()))}")
            for e in ex: print("      e.g.", e)
            sys.stdout.flush()

if __name__ == "__main__":
    T1(); T2(); T3()
