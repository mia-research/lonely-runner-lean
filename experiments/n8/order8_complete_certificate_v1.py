"""The COMPLETE order-8 certificate at a given ratio bound: exhaustive, exact, no beam, no budget.

Breadth-first over words, keeping every realisable one (max tau > 0) and recording sup R at each
length. Runs until no realisable word can be extended -- the frontier exhausts -- at which point the
maximum is exact for that ratio bound, and 'sup R < n-1' is PROVED for it.

Streams one line per level: realisable count, best R at that length, running maximum, elapsed.
"""
import os, sys, time
from fractions import Fraction as F
src = open(os.path.join(os.path.dirname(__file__), 'order_n_certificate_v1.py')).read().split("if __name__ ==")[0]
g = {'__name__': 'complete'}
exec(src, g)
constraints = g['constraints']; opt = g['opt']; NV = g['NV']; n = g['n']
S = int(sys.argv[1]) if len(sys.argv) > 1 else 8
L = ((n - 1) * S - 1) // n
CAP = n - 1
print(f"order {n} COMPLETE certificate: ratio bound S = {S}, lap bound L = {L}, "
      f"max length {NV*L}, cap R < {CAP}", flush=True)
print(f"ladder ((n+1)/(n-1))^(n-2) = {float(F(n+1,n-1)**(n-2)):.4f}\n", flush=True)
def score(word):
    cons = constraints(word)
    tau = opt(cons, NV, 'max', S, True)
    if tau is None or tau <= 0: return None, None
    x, Q = word[-1]
    m = opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    R = F(n * Q + 1) / m if (m is not None and m > 0) else F(0)
    return R, tau
level = []
for x in range(1, NV + 1):
    for q in range(1, L + 1):
        R, tau = score([(x, q)])
        if R is not None: level.append(([(x, q)], R))
best = F(0); argbest = None; t0 = time.time(); total = 0
d = 1
while level:
    bd = max(r for _, r in level)
    if bd > best:
        best = bd; argbest = next(w for w, r in level if r == bd)
    total += len(level)
    print(f"  length {d:2}: realisable {len(level):8}   best R here {float(bd):7.4f}"
          f"   running max {float(best):7.4f}   ({time.time()-t0:6.0f}s)"
          f"{'   *** CAP EXCEEDED ***' if best >= CAP else ''}", flush=True)
    nxt = []
    for w, _ in level:
        used = {xx: qq for xx, qq in w}
        for nx in range(1, NV + 1):
            for nq in range(used.get(nx, 0) + 1, L + 1):
                w2 = w + [(nx, nq)]
                R, tau = score(w2)
                if R is not None: nxt.append((w2, R))
    level = nxt; d += 1
print(f"\n  FRONTIER EXHAUSTED at length {d}. Enumeration complete.", flush=True)
print(f"  words examined (realisable): {total}", flush=True)
print(f"  sup R = {best} = {float(best):.6f}   cap {CAP}", flush=True)
print(f"  attained by {argbest}", flush=True)
print(f"  return correction factor {float(best / (F(n+1,n-1)**(n-2))):.4f} "
      f"(available before cap: {float(F(CAP)/(F(n+1,n-1)**(n-2))):.4f})", flush=True)
print(f"\n  target sup R < {CAP}  ->  "
      f"{'PROVED for ratio S <= ' + str(S) if best < CAP else 'NOT PROVED'}", flush=True)
