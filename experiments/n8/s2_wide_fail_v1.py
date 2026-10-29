# Observation (exact): for each frozen set, the largest min(d1, d2) on the grid (step 1/4, up to 40) for which the first WIDE
# frozen piece holds NO common clear point of the two movers, against the proved threshold D0 = ceil(7/(4 L)).
import importlib.util, math
from fractions import Fraction as F
spec = importlib.util.spec_from_file_location("p", "s2_freeze_probe_v1.py"); p = importlib.util.module_from_spec(spec); spec.loader.exec_module(p)
lf = p.lf
step = F(1, 4); top = 40
out = []
for S in sorted(p.frozen_sets(), key=lambda S: (len(S), S)):
    Fm = [F(i) for i in S]
    P = lf.pieces(Fm, F(3))
    h = next(k for k, (l, r) in enumerate(P) if r > l)
    lw, rw = P[h]
    D0 = math.ceil(F(7, 4) / (rw - lw))
    worst = None; cnt = 0; tot = 0
    d1 = F(S[0]) + step
    while d1 <= top:
        d2 = d1
        while d2 <= top:
            if all(d1 != f and d2 != f for f in Fm):
                t, n = p.cascade_from([d1, d2], lw)
                tot += 1
                if t > rw:
                    cnt += 1
                    if worst is None or min(d1, d2) > worst[0]: worst = (min(d1, d2), d1, d2)
            d2 += step
        d1 += step
    out.append((S, D0, worst, cnt, tot))
    print("".join(map(str, S)).ljust(6), "D0 =", D0, " wide piece fails at %d of %d grid pairs; largest min(d) with failure:" % (cnt, tot), (str(worst[0]) if worst else "none"), flush=True)
