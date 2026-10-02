# Two-runner deformations of many arrangements.  R = 8*d_min*t ; reading rho (speed minus the subject's).  Exact Fractions.
# At each s on a path where TWO readings (the movers) move linearly and the others are frozen:
#   L(V(s)) = L(frozen) ∩ L(movers)  (checked), the landing (first lonely R) lies in a component of L(frozen) (checked),
#   and the landing is labelled by the nearest component of the base arrangement's own lonely set L(V(0)).
import sys, random
from fractions import Fraction as F
exec(open('four_instants_track_v1.py').read().split('AP = ')[0])
def comp_index(L, R):
    for i, (lo, hi) in enumerate(L):
        if lo <= R <= hi: return i
    return None
def label(base, R):
    best = None
    for k, (lo, hi) in enumerate(base):
        d = 0 if lo <= R <= hi else min(abs(R - lo), abs(R - hi))
        if best is None or d < best[0]: best = (d, k)
    return best
def run(base_rho, movers, target, steps=40):
    n = len(base_rho); frozen = [i for i in range(n) if i not in movers]
    L0 = lonely(base_rho)
    rows = []
    for st in range(steps + 1):
        s = F(st, steps)
        rho = list(base_rho)
        for i in movers: rho[i] = base_rho[i] + (target[i] - base_rho[i]) * s
        L = lonely(rho)
        Lf = lonely([rho[i] for i in frozen]); Lm = [windows(rho[i]) for i in movers]
        # L(V) = L(frozen) ∩ clear(movers)
        X = Lf
        for W in Lm: X = inter(X, W)
        X2 = []
        for lo, hi in sorted(X):
            if X2 and lo <= X2[-1][1]: X2[-1] = (X2[-1][0], max(X2[-1][1], hi))
            else: X2.append((lo, hi))
        assert X2 == L, "L != L(frozen) ∩ L(movers)"
        if L:
            land = L[0][0]; ci = comp_index(Lf, land); assert ci is not None, "landing outside L(frozen)"
            d, k = label(L0, land)
            rows.append((s, land, k, d, ci))
        else: rows.append((s, None, None, None, None))
    return L0, rows
def rle(rows, L0):
    out = []; cur = None
    for s, land, k, d, ci in rows:
        if land is None: tag = ("none",)
        elif d <= F(1, 2): tag = ("base event %d" % k,)
        else: tag = ("between",)
        if cur and cur[0] == tag: cur[2] = s; cur[3].append(land)
        else:
            if cur: out.append(cur)
            cur = [tag, s, s, [land] if land is not None else []]
    out.append(cur); return out
def describe(L0): return "[" + ", ".join(("%.3f" % float(lo)) if lo == hi else ("%.3f-%.3f" % (float(lo), float(hi))) for lo, hi in L0) + "]"
if __name__ == "__main__":
    rnd = random.Random(308)
    bases = [("AP 1..7 (speeds s+1..s+7)", [F(k) for k in range(1, 8)]),
             ("grid 1,2,3,4,5,6,15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]),
             ("grid 1,2,3,4,5,7,14", [F(x) for x in (1, 2, 3, 4, 5, 7, 14)]),
             ("grid 9,2,3,4,5,6,7 -> d_min 2", [F(x, 2) for x in (2, 3, 4, 5, 6, 7, 9)]),
             ("3*AP", [F(3 * k) for k in range(1, 8)])]
    from collections import Counter
    summary = Counter(); nruns = 0; log = []
    for name, base in bases:
        L0 = lonely(base)
        print("=" * 100); print(name, " base lonely components in (0,9.5]:", describe(L0))
        pairs = [(i, j) for i in range(7) for j in range(i + 1, 7)]
        for (i, j) in (pairs if name.startswith("AP") else rnd.sample(pairs, 6)):
            for rep in range(2 if name.startswith("AP") else 2):
                target = list(base)
                for m in (i, j):
                    target[m] = max(F(3, 10), base[m] + F(rnd.randint(-120, 120), 100) * (base[m] if base[m] < 3 else F(1)) / (F(1) if base[m] < 3 else F(1)))
                L0_, rows = run(base, (i, j), target)
                r = rle(rows, L0_); nruns += 1
                desc = " ; ".join("s%.2f-%.2f %s" % (float(a[1]), float(a[2]), a[0][0]) for a in r)
                print("  movers %s -> %s : %s" % ((i + 1, j + 1), [round(float(target[m]), 2) for m in (i, j)], desc))
                kinds = set(a[0][0].split(" ")[0] + (" event" if a[0][0].startswith("base") else "") for a in r)
                summary[tuple(sorted(a[0][0] for a in r))] += 1
    print("\nruns:", nruns, "; all asserted: L = L(frozen) ∩ L(movers), landing inside a component of L(frozen).")
