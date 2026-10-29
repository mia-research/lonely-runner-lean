# WindowBound probe.  Readings r_1..r_7 distinct positive in [1, rho] (c = 1).  W(rho) = sup T*8 where T = first isolation instant (cascade from 1/(8 r_min)).
# Random starts + exact hill climb (maximise T) on a grid of denominator Q.  Exact Fractions; cap 100000 moves (reported if hit).
import math, random, sys
from fractions import Fraction as F
E = F(1, 8)
def dist(x): f = x - math.floor(x); return min(f, 1 - f)
def casc(r, cap=100000):
    t = F(1, 8 * min(r)); mv = 0
    while mv < cap:
        way = [d for d in r if dist(d * t) < E]
        if not way: return t, mv
        t = max((F(round(d * t)) + E) / d for d in way); mv += 1
    return None, mv
rho = F(sys.argv[1]); Q = int(sys.argv[2]); starts = int(sys.argv[3]); seed = int(sys.argv[4])
rnd = random.Random(seed); best = (F(0), None, 0); evals = 0; capped = 0
lo, hi = Q, int(rho * Q)
def val(j):
    global evals, capped
    if len(set(j)) < 7: return None
    evals += 1
    T, mv = casc([F(a, Q) for a in j])
    if T is None: capped += 1; return None
    return T, mv
for s in range(starts):
    j = [rnd.randint(lo, hi) for _ in range(7)]
    v = val(j)
    if v is None: continue
    cur = v[0]; mvs = v[1]
    improved = True
    while improved:
        improved = False
        for i in range(7):
            for step in (-7, -3, -1, 1, 3, 7, 31, -31):
                j2 = list(j); j2[i] = min(hi, max(lo, j2[i] + step))
                w = val(j2)
                if w and w[0] > cur: j, cur, mvs, improved = j2, w[0], w[1], True
    if cur > best[0]: best = (cur, list(j), mvs)
T, j, mv = best
print(f"rho={rho} Q={Q} starts={starts} evals={evals} capped={capped}  max T*8c = {float(T*8):.4f}  (T={float(T):.4f}, moves={mv})  readings={[str(F(a,Q)) for a in sorted(j)]}")
