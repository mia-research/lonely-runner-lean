# E640: for the 37 frozen sets of E557 (labels as in TwoMoverLarge2_<set>.lean), the pair threshold of the exact window: two movers a <= b, both real, are covered when a >= 1/(2 w) with w the core's widest exact clear window
# (cluster_transfer_window + pair_gap_half); compared with E557's D0 (old) read from s2_wide_fail_v1.out.  Exact Fractions.
import re, math
from fractions import Fraction as F
from core_lib_v1 import *
d0 = {}
for l in open('s2_wide_fail_v1.out'):
    m = re.match(r'^(\d+)\s+D0 = (\d+)', l)
    if m: d0[m.group(1)] = int(m.group(2))
import os
labels = sorted(f[len('TwoMoverLarge2_'):-5] for f in os.listdir('../../LonelyRunnerFresh/Fresh') if f.startswith('TwoMoverLarge2_'))
print('set  E557 D0(old)  widest window w   our pair threshold 1/(2w)')
for lab in labels:
    S = [int(c) for c in lab]
    lo, hi = widest_window(S); w = hi - lo
    thr = 1 / (2 * w) if w > 0 else None
    print(lab, d0.get(lab), w, thr, '(%.1f)' % float(thr) if thr else '')
