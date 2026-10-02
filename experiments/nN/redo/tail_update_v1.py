# After an effective crossing at state i, what does the TAIL do?  Compare the path just before (s*-eps) and just after (s*+eps):
#   same landing flank (setter, lap) and R* continuous ("continuous"), new path rejoins the old one at a later common state ("rejoins"),
#   or a different landing: forward hop (R* larger) / backward hop (R* smaller), with the size of the hop.
import sys, random
sys.argv = [sys.argv[0]]
exec(open('effective_crossings_v1.py').read().split('\nif __name__ ==')[0])
from collections import Counter, defaultdict
rnd = random.Random(317)
EPS = F(1, 10**9)
def classify(p, q, s, i):
    ra = rho_at(p, q, s - EPS); rb = rho_at(p, q, s + EPS)
    sa, Ra = path(ra); sb, Rb = path(rb)
    Sa = [mv["R2"] for mv in sa]; Sb = [mv["R2"] for mv in sb]
    la = (sa[-1]["setter"], sa[-1]["lap"]) if sa else None; lb = (sb[-1]["setter"], sb[-1]["lap"]) if sb else None
    dR = float(Rb - Ra)
    if abs(dR) < 1e-6: kind = "continuous (same landing R)"
    else: kind = "forward hop" if dR > 0 else "backward hop"
    ta = {round(float(x), 5) for x in Sa[i:]}; tb = {round(float(x), 5) for x in Sb[i:]}
    rejoin = bool(ta & tb)
    return kind, dR, rejoin, len(sa), len(sb), la, lb, float(Ra), float(Rb)
bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]), ("wide", [F(1), F(2), F(5), F(11), F(23), F(47), F(95)]),
         ("clump", [F(1), F(30), F(31), F(33), F(36), F(40), F(45)])]
for i in range(6): bases.append(("rand%d" % i, [F(x) for x in sorted(rnd.sample(range(10, 400), 7))]))
bases = [(n, [F(x) / b[0] for x in b]) for n, b in bases]
tab = Counter(); jumps = defaultdict(list); rej = Counter(); examples = []
nev = 0
for name, base in bases:
    for r in range(30):
        k = rnd.choice((1, 2, 3, 4)); movers = tuple(sorted(rnd.sample(range(7), k)))
        p = list(base); q = [F(0)] * 7
        for m in movers:
            span = max(F(1), base[m] / 3); q[m] = max(F(3, 10) * base[0], base[m] + F(rnd.randint(-150, 300), 100) * span) - base[m]
        s0 = F(1, 1000)
        for _ in range(12):
            pred, steps = predicted_next(p, q, s0)
            if pred is None or pred[0] >= 1: break
            s, i, edge = pred
            kind, dR, rejoin, na, nb, la, lb, Ra, Rb = classify(p, q, s, i)
            typ = ("start" if edge[1] == -1 else "end")
            tab[(typ, kind)] += 1; nev += 1
            if kind != "continuous (same landing R)": jumps[kind].append(abs(dR))
            rej[(kind, rejoin)] += 1
            if kind != "continuous (same landing R)" and len(examples) < 14 and abs(dR) > 0.5: examples.append((name, movers, round(float(s), 5), i, round(Ra, 4), round(Rb, 4), na, nb))
            s0 = s + F(1, 10**6)
print("effective crossings examined:", nev)
for k, v in sorted(tab.items()): print("  crossing %-5s -> %-28s %d" % (k[0], k[1], v))
for kind, v in jumps.items():
    v.sort(); print("  %s: n=%d, median |jump| %.3f, 90th pct %.3f, max %.3f, jumps > 1: %d" % (kind, len(v), v[len(v)//2], v[int(len(v)*0.9)], v[-1], sum(1 for x in v if x > 1)))
print("  rejoin (new path shares a state with the old tail) by outcome:", sorted(rej.items(), key=str))
for e in examples: print("   hop example:", e)
