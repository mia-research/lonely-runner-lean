"""WP3 item 2, part 2: the movers.  For each top block's longest stretch: split the block at scale d1 into the core
(readings within 0.1 of a whole multiple of d1) and movers (the rest), with each mover's deviation eps and its nearest
small-denominator fraction p/q (q <= 4).  Per d1-band in the stretch: which movers the relay uses (patches) and each
mover's phase at the band's d1-opening.  Exact."""
from fractions import Fraction as F
from math import floor
from arrangement_lib import nd
from block_extremal_v1 import comps
from block_drift_v1 import relay
def near_frac(x, Q=4):
    best = None
    for q in range(1, Q + 1):
        p = round(x * q); err = abs(x - F(p, q))
        if best is None or err < best[0]: best = (err, F(p, q))
    return best
for B in ([165, 166, 337, 494, 505, 772], [355, 357, 373, 524, 561, 784], [232, 233, 361, 365, 680, 742]):
    cs = comps(B); L, a, b = max(((q - p, p, q) for p, q in cs if p > 0)); d1 = min(B)
    eps = {d: F(d, d1) - round(F(d, d1)) for d in B}
    movers = [d for d in B if abs(eps[d]) > F(1, 10)]
    print(f"\n=== {B}: core {[d for d in B if d not in movers]}, movers "
          + ", ".join(f"{d} (eps {float(eps[d]):+.3f} ~ {near_frac(eps[d])[1]} +/- {float(near_frac(eps[d])[0]):.3f})" for d in movers))
    mv = relay(B, a + F(1, 8 * d1), b)
    used = {}
    for (t, d, M, tn, slack) in mv:
        used.setdefault(floor(tn * d1), set()).add(d)
    for band in sorted(used):
        t_open = (band + F(1, 8)) / d1
        ph = ", ".join(f"{d}:{float((d * t_open) % 1):.3f}{'*' if d in used[band] else ''}" for d in movers)
        print(f"  band {band}: movers used {sorted(used[band] & set(movers))}; mover phases at the band's opening (* = patches): {ph}")
