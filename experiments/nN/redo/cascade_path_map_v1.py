# The cascade's own path, step by step, under deformation of k runners (the others frozen).  R = 8*d_min*t in the unit of the smallest
# reading of the arrangement at that s; readings rho (speed minus the subject's).  Exact Fractions.
# State R: reading rho sits at p = R*rho mod 8 eighths; it blocks iff p in (-1, 1) mod 8, j = round(R*rho/8) is its lap, its exit is (8j+1)/rho.
# Move: R -> the largest exit among blockers.  For every move record: setter, jump, and for each blocker at the NEW state how it got there:
#   'carried' = clear at the old state (clear position p0 and shift rho*dR), 'returned' = a blocker at the old state that left and re-entered.
import sys, random
from fractions import Fraction as F
from collections import Counter, defaultdict
def pos(R, rho): return (R * rho) % 8
def blocks(R, rho): p = pos(R, rho); return min(p, 8 - p) < 1
def path(rhos):
    rm = min(rhos); R = 1 / rm; steps = []
    while True:
        bl = [i for i, r in enumerate(rhos) if blocks(R, r)]
        if not bl: return steps, R
        ex = [((8 * round(R * rhos[i] / 8) + 1) / rhos[i], i, round(R * rhos[i] / 8)) for i in bl]
        R2, setter, lap = max(ex)
        new = [i for i, r in enumerate(rhos) if blocks(R2, r)]
        info = []
        for i in new:
            p0 = pos(R, rhos[i]); sh = rhos[i] * (R2 - R)
            info.append((i, "returned" if i in bl else "carried", p0, sh))
        steps.append(dict(R=R, blockers=bl, setter=setter, lap=lap, R2=R2, new=info))
        R = R2
def role(i, movers): return "mover" if i in movers else "frozen"
if __name__ == "__main__":
    k = int(sys.argv[1]); nrun = int(sys.argv[2]); rnd = random.Random(310 + k)
    bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]),
             ("g14", [F(x) for x in (1, 2, 3, 4, 5, 7, 14)]), ("3AP", [F(3 * x) for x in range(1, 8)])]
    agg = Counter(); shifts = defaultdict(list); movesN = Counter(); lens = Counter(); printed = 0
    for name, base in bases:
        for r in range(nrun if name == "AP" else max(4, nrun // 3)):
            movers = tuple(sorted(rnd.sample(range(7), k))); target = list(base)
            for m in movers:
                target[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-150, 250), 100))
            for st in range(0, 31):
                s = F(st, 30); rhos = [base[i] + ((target[i] - base[i]) * s if i in movers else 0) for i in range(7)]
                steps, Rend = path(rhos); lens[len(steps)] += 1
                for n, mv in enumerate(steps):
                    key = min(n + 1, 4)
                    movesN[key] += 1
                    agg[("setter", key, role(mv["setter"], movers))] += 1
                    for i, how, p0, sh in mv["new"]:
                        c = "shift<1" if sh < 1 else ("shift 1-3" if sh < 3 else "shift>=3")
                        agg[("new blocker", key, how, c)] += 1
                        shifts[(key, how)].append(float(sh))
                if len(steps) >= 2 and printed < 9 and name == "AP" and st % 6 == 0:
                    printed += 1
                    print("AP movers #%s %s s=%.2f  rho=%s" % (",".join(str(m + 1) for m in movers), "->" , float(s), [round(float(x), 3) for x in rhos]))
                    for n, mv in enumerate(steps):
                        print("   move %d: R=%.4f  blockers %s  setter #%d lap %d -> R=%.4f ; blockers after: %s" % (n + 1, float(mv["R"]), ["#%d" % (i + 1) for i in mv["blockers"]], mv["setter"] + 1, mv["lap"], float(mv["R2"]),
                              ", ".join("#%d %s (p0=%.2f, shift=%.2f)" % (i + 1, how, float(p0), float(sh)) for i, how, p0, sh in mv["new"]) or "none (lonely)"))
                    print("   lonely at R=%.4f" % float(Rend))
    print("\nruns x steps with %d movers; number of cascade moves per path:" % k, sorted(lens.items()))
    print("moves by index (1,2,3,4+):", sorted(movesN.items()))
    for key in (1, 2, 3, 4):
        tot = movesN[key]
        if not tot: continue
        print(" move index %s%s: setter frozen %d, setter mover %d" % (key, "+" if key == 4 else "", agg[("setter", key, "frozen")], agg[("setter", key, "mover")]))
        for how in ("carried", "returned"):
            row = [(c, agg[("new blocker", key, how, c)]) for c in ("shift<1", "shift 1-3", "shift>=3")]
            print("     new blockers %-9s: %s" % (how, ", ".join("%s %d" % x for x in row)))
