"""E164 v2: the random wide sets not covered with m <= 12 in m_vs_spread_v1 (same seeds): their least m up to 64."""
import random
from math import exp, log
from multiprocessing import Pool
from casec_gridclass_v1 import least_m
def p2(seed):
    rng = random.Random(1000 + seed); out = []
    for _ in range(1500):
        dmin = rng.randrange(1, 60); S = rng.uniform(7.01, 2000)
        xs = sorted({max(dmin + 1, int(round(dmin * exp(rng.uniform(0, log(S)))))) for _ in range(5)} | {dmin, int(dmin * S)})
        if len(xs) != 7 or xs[-1] <= 7 * xs[0]: continue
        if least_m(tuple(xs), 12) is None: out.append((tuple(xs), least_m(tuple(xs), 64)))
    return out
if __name__ == '__main__':
    with Pool(8) as p:
        for r in p.imap_unordered(p2, range(16)):
            for T, m in r: print(T, "spread %.0f" % (T[-1] / T[0]), "least m (<= 64):", m, flush=True)
