"""Does the return correction accumulate toward the cap, or plateau?

Lemma C needs a bound on how much words LONGER than the lap-1 ladder can add to R. Exhaustive
enumeration is infeasible (7.25e26 words), but the MAXIMUM does not need the full tree: a beam search
keeping the top-R words at each depth tracks the frontier at bounded cost.

This is a LOWER bound on sup R at each depth (a beam can miss the true maximum), so:
  * if best R plateaus well below the cap, that is evidence the correction is bounded;
  * if best R climbs past the cap, that REFUTES the ladder bound outright.
Either way the run is bounded: beam x children x depth LPs.
"""
import os, sys, time
from fractions import Fraction as F
src = open(os.path.join(os.path.dirname(__file__), 'order_n_certificate_v1.py')).read().split("if __name__ ==")[0]
g = {'__name__': 'beam'}
exec(src, g)
constraints = g['constraints']; opt = g['opt']; NV = g['NV']; n = g['n']
S = int(sys.argv[1]) if len(sys.argv) > 1 else 8
BEAM = int(sys.argv[2]) if len(sys.argv) > 2 else 500
DEPTH = int(sys.argv[3]) if len(sys.argv) > 3 else 20
L = ((n - 1) * S - 1) // n
CAP = n - 1
print(f"order {n}, ratio bound S = {S}, lap bound L = {L}, cap R < {CAP}", flush=True)
print(f"beam width {BEAM}, max depth {DEPTH}; ladder value ((n+1)/(n-1))^(n-2) = "
      f"{float(F(n+1,n-1)**(n-2)):.4f}\n", flush=True)
def score(word):
    cons = constraints(word)
    tau = opt(cons, NV, 'max', S, True)
    if tau is None or tau <= 0: return None
    x, Q = word[-1]
    m = opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    if m is None or m <= 0: return F(0)
    return F(n * Q + 1) / m
level = []
for x in range(1, NV + 1):
    for q in range(1, L + 1):
        r = score([(x, q)])
        if r is not None: level.append((r, [(x, q)]))
overall = max((r for r, _ in level), default=F(0)); argmax = None
t0 = time.time()
for d in range(1, DEPTH + 1):
    if not level: print(f"  depth {d}: no realisable words left -- frontier EXHAUSTED", flush=True); break
    level.sort(key=lambda z: -z[0])
    level = level[:BEAM]
    best = level[0]
    if best[0] > overall: overall, argmax = best[0], best[1]
    print(f"  depth {d:2}  frontier {len(level):5}  best R at this depth {float(best[0]):7.4f}"
          f"   running max {float(overall):7.4f}   ({time.time()-t0:5.0f}s)"
          f"{'   *** EXCEEDS CAP ***' if overall >= CAP else ''}", flush=True)
    nxt = []
    for r, w in level:
        used = {xx: qq for xx, qq in w}
        for nx in range(1, NV + 1):
            for nq in range(used.get(nx, 0) + 1, L + 1):
                w2 = w + [(nx, nq)]
                s = score(w2)
                if s is not None: nxt.append((s, w2))
    level = nxt
print(f"\n  max R found: {overall} = {float(overall):.4f}   cap {CAP}")
print(f"  ladder ((n+1)/(n-1))^(n-2) = {float(F(n+1,n-1)**(n-2)):.4f}")
print(f"  return correction factor = {float(overall / (F(n+1,n-1)**(n-2))):.4f}")
print(f"  available before the cap  = {float(F(CAP) / (F(n+1,n-1)**(n-2))):.4f}")
if argmax: print(f"  attained by {argmax}")
