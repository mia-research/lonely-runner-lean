# Lap of d_min in which the first isolation lands: M = floor(T * r_min), T in [(M+1/8)/r_min, (M+7/8)/r_min].  Exact Fractions.
# (1) random vectors, histogram of M by ratio bucket; (2) adversarial hill climb maximising T*r_min under a ratio cap;
# (3) perturbed tight vectors (1..7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13) scaled and perturbed.
import math, random, sys
from fractions import Fraction as F
from collections import Counter, defaultdict
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
def casc(r):
    t = F(1, 8 * min(r))
    while True:
        way = [d for d in r if dist(d * t) < E]
        if not way: return t
        t = max((F(round(d * t)) + E) / d for d in way)
def lap(r): return math.floor(casc(r) * min(r))
mode = sys.argv[1]; seed = int(sys.argv[2]); rnd = random.Random(seed)
buckets = [(1, 7), (7, 8), (8, 10), (10, 15), (15, 30), (30, 100), (100, 10**6)]
def bk(rat):
    for i, (a, b) in enumerate(buckets):
        if a <= rat <= b: return i
if mode == 'random':
    N = int(sys.argv[3]); H = defaultdict(Counter); worst = {}
    for _ in range(N):
        kind = rnd.choice(['unif', 'log', 'int'])
        if kind == 'unif': r = sorted({F(rnd.randint(48, 48 * rnd.choice([8, 12, 30])), 48) for _ in range(7)})
        elif kind == 'log': r = sorted({F(round(48 * 10 ** rnd.uniform(0, 2)), 48) for _ in range(7)})
        else: r = sorted({F(rnd.randint(1, 60)) for _ in range(7)})
        if len(r) < 7: continue
        b = bk(r[-1] / r[0]); M = lap(r); H[b][M] += 1
        if M >= worst.get(b, (-1,))[0]: worst[b] = (M, [str(x) for x in r])
    for b in sorted(H): print(f"ratio {buckets[b]}: n={sum(H[b].values())}  laps {dict(sorted(H[b].items()))}  deepest example {worst[b]}")
elif mode == 'climb':
    rho = F(sys.argv[3]); Q = int(sys.argv[4]); starts = int(sys.argv[5]); lo, hi = Q, int(rho * Q)
    def val(j):
        if len(set(j)) < 7 or min(j) < lo or max(j) > hi: return None
        r = [F(a, Q) for a in j]; T = casc(r); return T * min(r)
    best = (F(0), None)
    for _ in range(starts):
        j = [rnd.randint(lo, hi) for _ in range(7)]; cur = val(j)
        if cur is None: continue
        imp = True
        while imp:
            imp = False
            for i in range(7):
                for st in (-1, 1, -3, 3, -9, 9, -31, 31, -97, 97):
                    j2 = list(j); j2[i] += st; w = val(j2)
                    if w is not None and w > cur: j, cur, imp = j2, w, True
        if cur > best[0]: best = (cur, sorted(j))
    print(f"climb rho={rho} Q={Q}: max T*r_min = {float(best[0]):.4f} (lap {math.floor(best[0])})  vector {[str(F(a,Q)) for a in best[1]]}")
else:
    tights = {'AP': [1,2,3,4,5,6,7], 'T2': [1,2,3,4,5,7,12], 'T3': [1,4,5,6,7,11,13]}; Qp = int(sys.argv[3]); worst = {}
    for name, base in tights.items():
        mx = 0; arg = None
        for _ in range(int(sys.argv[4])):
            s = F(rnd.randint(Qp, 3 * Qp), Qp); eps = F(rnd.choice([1, 3, 10, 30, 100]), 10**4)
            r = sorted({s * a + eps * F(rnd.randint(-100, 100), 100) for a in base})
            if len(r) < 7 or min(r) <= 0: continue
            M = lap(r)
            if M >= mx: mx, arg = M, [str(x) for x in r]
        print(f"perturbed {name}: deepest lap {mx}  example {arg}")
