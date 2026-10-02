# Three- and four-runner deformations, tracked as a MAP: the frozen runners' lonely set L(frozen) is fixed; each of its components
# (in order of R) is either the place the isolation lands or is blocked, and by which mover's zone(s) Z(rho, j) = ((8j-1)/rho, (8j+1)/rho).
# Exact Fractions.  R = 8*d_min*t with d_min the base's smallest reading.
import sys, random
from fractions import Fraction as F
from collections import Counter
exec(open('two_mover_track_v1.py').read().split('if __name__')[0])
def zones(rho):
    out = []; j = 0
    while (8 * j - 1) / rho < RMAX:
        out.append(((8 * j - 1) / rho, (8 * j + 1) / rho, j)); j += 1
    return out
def blockers(comp, movers_rho):
    lo, hi = comp; out = []
    for m, rho in movers_rho:
        for zl, zh, j in zones(rho):
            if zl < hi and zh > lo or (lo == hi and zl < lo < zh): out.append((m, j))
    return out
def step_map(base, movers, target, s):
    n = len(base); frozen = [i for i in range(n) if i not in movers]
    rho = list(base)
    for i in movers: rho[i] = base[i] + (target[i] - base[i]) * s
    Lf = lonely([rho[i] for i in frozen])
    M = windows(rho[movers[0]])
    for m in movers[1:]: M = inter(M, windows(rho[m]))
    L = []
    for lo, hi in sorted(inter(Lf, M)):
        if L and lo <= L[-1][1]: L[-1] = (L[-1][0], max(L[-1][1], hi))
        else: L.append((lo, hi))
    assert L == lonely(rho)
    if not L: return Lf, None, []
    land = L[0][0]; ci = comp_index(Lf, land); assert ci is not None
    skipped = []
    for k in range(ci):
        skipped.append((k, blockers(Lf[k], [(m, rho[m]) for m in movers])))
    return Lf, ci, skipped
def run(base, movers, target, steps=30):
    seq = []; Lf0 = None
    for st in range(steps + 1):
        s = F(st, steps); Lf, ci, sk = step_map(base, movers, target, s)
        Lf0 = Lf0 or Lf; assert Lf == Lf0, "frozen set changed"
        seq.append((s, ci, tuple((k, tuple(sorted(set(b)))) for k, b in sk)))
    return Lf0, seq
def rle(seq):
    out = []
    for s, ci, sk in seq:
        key = (ci, sk)
        if out and out[-1][0] == key: out[-1][2] = s
        else: out.append([key, s, s])
    return out
if __name__ == "__main__":
    k = int(sys.argv[1]); nrun = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 309
    rnd = random.Random(seed + k)
    bases = [("AP s+1..s+7", [F(x) for x in range(1, 8)]), ("grid 1,2,3,4,5,6,15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]),
             ("grid 1,2,3,4,5,7,14", [F(x) for x in (1, 2, 3, 4, 5, 7, 14)]), ("3*AP", [F(3 * x) for x in range(1, 8)])]
    first_blockers = Counter(); nsteps = 0; hops = Counter(); shown = 0
    for name, base in bases:
        runs = nrun if name.startswith("AP") else max(4, nrun // 3)
        print("=" * 110); print(name, "  %d movers, %d runs" % (k, runs))
        for r in range(runs):
            movers = tuple(sorted(rnd.sample(range(7), k)))
            target = list(base)
            for m in movers:
                span = base[m] if base[m] < 6 else F(6)
                target[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-110, 110), 100) * span / 4)
            Lf, seq = run(base, movers, target)
            rr = rle(seq)
            for s, ci, sk in seq:
                nsteps += 1
                if sk and sk[0][0] == 0:
                    for m in {mm for mm, _ in sk[0][1]}: first_blockers[(name.split()[0], movers.index(m) >= 0 and m + 1)] += 1
            hop = tuple(x[0][0] for x in rr); hops[(name.split()[0], len(set(hop)))] += 1
            if shown < 14 or name.startswith("AP") and r < 8:
                shown += 1
                print(" movers (readings #%s) %s -> %s" % (",".join(str(m + 1) for m in movers), [round(float(base[m]), 2) for m in movers], [round(float(target[m]), 2) for m in movers]))
                print("   frozen lonely set (fixed):", describe(Lf))
                for (ci, sk), a, b in rr:
                    bl = "; ".join("C%d blocked by %s" % (kk, ",".join("#%dL%d" % (m + 1, j) for m, j in bs) or "no zone?") for kk, bs in sk)
                    print("   s %.2f-%.2f: lands in C%s%s" % (float(a), float(b), ci, (" ; " + bl) if bl else ""))
    print("\nsteps examined:", nsteps, " (every step asserted: frozen set unchanged, landing inside a frozen component, L = L(frozen) ∩ L(movers))")
    print("first frozen component C0 blocked, by mover (base reading index #) -- counts of (run, step):", sorted(first_blockers.items()))
    print("distinct frozen components the landing visits along a run (base, number): ", sorted(hops.items()))
