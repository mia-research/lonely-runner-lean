"""The block rule derived from the synchronised-block reduction, tested against the cascade.

For a separated runner (arrangements, every runner): core C = readings below the largest ratio gap
(>= 9), block F above.  The block is split into synchronised clusters (consecutive block readings
within relative spread 1/9 of the cluster's least).  Each cluster's common phase is free (sync_block);
it imposes only that its offsets {f - min(cluster)} leave a cyclic gap > 1/4 + 2E/N (E = the cluster's
spread, N = its least reading).  Clusters of <= 3 always leave a gap >= 1/3.
PREDICTION: the earliest t >= tau_C (the core's own isolation event) at which the core is clear and
every cluster's offsets are so gapped.  Compared with the cascade's event t* for the runner: the
cascade should land within one block turn (1/min cluster) after the prediction.  The prediction is
located on the exact grid tau_C + j/(64 * max(core, largest offset)), j >= 0 (a diagnostic grid;
all values exact fractions).
"""
import random
from fractions import Fraction as F
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
import separation_arrangements_v1 as SA
def clusters(block):
    out = [[block[0]]]
    for b in block[1:]:
        if b - out[-1][0] <= F(out[-1][0], 9): out[-1].append(b)
        else: out.append([b])
    return out
def max_gap(pts):
    p = sorted(set(x % 1 for x in pts)); g = [p[i + 1] - p[i] for i in range(len(p) - 1)] + [1 - p[-1] + p[0]]
    return max(g)
def predict(core, block, tC, limit):
    cl = clusters(block)
    scale = max([max(core)] + [c[-1] - c[0] for c in cl] + [1])
    step = F(1, 64 * scale); t = tC
    while t < limit:
        if all(nd(c * t) >= F(1, 8) for c in core) and \
           all(max_gap([(x - c[0]) * t for x in c]) > F(1, 4) + F(2 * (c[-1] - c[0]), c[0]) for c in cl if len(c) >= 4):
            return t, cl
        t += step
    return None, cl
if __name__ == "__main__":
    rnd = random.Random(55); SA.rnd = rnd
    n = agree = 0; big = 0; fails = []
    from collections import Counter
    sizes = Counter()
    for name in ("uniform", "clustered", "slow-plus-fast"):
        for _ in range(300):
            V = sorted(set(SA.family(name)))
            if len(V) < 8: continue
            for k in range(8):
                ds = readings(V, k)
                rs = [(F(ds[i + 1], ds[i]), i) for i in range(len(ds) - 1)]
                r, i = max(rs)
                if r < 9: continue
                core, block = ds[:i + 1], ds[i + 1:]
                if len(block) < 3: continue
                n += 1
                tC, _ = cascade_cap(core); t, _ = cascade_cap(ds)
                p, cl = predict(core, block, tC, 2 * tC)
                sizes[max(len(c) for c in cl)] += 1
                if any(len(c) >= 4 for c in cl): big += 1
                if p is not None and p - F(1, 64 * max(core)) <= t <= p + F(1, min(c[0] for c in cl)) + F(1, 64 * max(core)): agree += 1
                elif len(fails) < 6: fails.append((V[k], core, [c for c in cl], float(tC), None if p is None else float(p), float(t)))
    print(f"{n} separated runners (block 3-6): the derived prediction agrees with the cascade's event {agree}/{n}")
    print(f"   runners with a synchronised cluster of >= 4 (the only kind that can move the event): {big};  largest cluster sizes {dict(sorted(sizes.items()))}")
    for s, core, cl, tC, p, t in fails:
        print(f"   disagreement: runner {s}, core {core}, clusters {cl}: tau_C = {tC:.7f}, predicted {p}, cascade {t:.7f}")
