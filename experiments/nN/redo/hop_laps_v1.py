# At a hop (birth or death of the first lonely component) the component is a tangency: its left end is the END of a zone (A, j) and its right end the
# START of a zone (B, j').  Tabulate the laps (j, j') and the relative order of A and B (A slower / faster than B), for deaths and births.
import sys, random
sys.argv = [sys.argv[0]]
exec(open('hop_is_gap_event_v1.py').read().split('\nif __name__ ==')[0].split("sys.argv = [sys.argv[0]]\n")[-1]) if False else None
exec(open('effective_crossings_v1.py').read().split('\nif __name__ ==')[0])
src = open('hop_is_gap_event_v1.py').read()
body = src.split("from collections import Counter")[0].split("sys.argv = [sys.argv[0]]\n", 1)[1]
body = body.replace("exec(open('effective_crossings_v1.py').read().split('\\nif __name__ ==')[0])\n", "")
exec(body)
from collections import Counter
rnd = random.Random(325); EPS = F(1, 10**9); TINY = F(1, 10**6)
def ident(rho, val, kind):
    out = []
    for y, r in enumerate(rho):
        j = (val * r - (1 if kind == "end" else -1)) / 8
        if abs(j - round(j)) < F(1, 10**5) and round(j) >= 0: out.append((y, int(round(j))))
    return out
bases = [("AP", [F(x) for x in range(1, 8)]), ("g15", [F(x) for x in (1, 2, 3, 4, 5, 6, 15)]), ("wide", [F(1), F(2), F(5), F(11), F(23), F(47), F(95)])]
for i in range(5): bases.append(("rand%d" % i, [F(x) for x in sorted(rnd.sample(range(10, 400), 7))]))
bases = [(n, [F(x) / b[0] for x in b]) for n, b in bases]
death = Counter(); birth = Counter(); unident = 0; tot = 0
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
            s = pred[0]; ra = rho_at(p, q, s - EPS); rb = rho_at(p, q, s + EPS)
            La = lonely_set(ra); Lb = lonely_set(rb)
            if La and Lb and abs(Lb[0][0] - La[0][0]) >= TINY:
                tot += 1
                if Lb[0][0] > La[0][0]: comp, rho, D = La[0], ra, death
                else: comp, rho, D = Lb[0], rb, birth
                A = ident(rho, comp[0], "end"); Bz = ident(rho, comp[1], "start")
                if not A or not Bz: unident += 1; s0 = s + F(1, 10**6); continue
                (ya, ja), (yb, jb) = A[0], Bz[0]
                rel = "A slower" if rho[ya] < rho[yb] else ("A faster" if rho[ya] > rho[yb] else "equal")
                D[(("lap %d" % ja, "lap %d" % jb), rel)] += 1
            s0 = s + F(1, 10**6)
print("hops examined:", tot, "; endpoints not identified:", unident)
for nm, D in (("DEATH of the first component (forward hop)", death), ("BIRTH of an earlier component (backward hop)", birth)):
    print(nm); 
    for k, v in D.most_common(14): print("   zone end (A, %s) meets zone start (B, %s) ; %s : %d" % (k[0][0], k[0][1], k[1], v))
