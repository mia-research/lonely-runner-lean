"""E410 (2026-10-06), block_three_check_v1: the block of three against a core of four, at ratio above 25.
Exact (integers and Fractions).
Derived (by hand): core C of four readings, block F of three with every f >= T*max(C), T > 25.  Order five gives
t0 with every ||c t0|| >= 1/5 (a lower-order input), so C is clear at 1/8 on I = [t0 - d, t0 + d], d = 3/(40 max C).
If F had no joint clear point in I, the open zones of F would cover I.  Reading f meets I in at most
(|I| f + 5/4) zones of length 1/(4f), so the cover's total length is at most 3|I|/4 + (5/16)(sum 1/f), which is
below |I| once T > 25 [PROVISIONAL: covering; supports: a block-clear point in I].  So S = C u F is lonely in I.
Checked here, per set: an exact t0 with the core at >= 1/5 (the least such instant, by an exact sweep of the core's
clear set at 1/5), the interval I, and an exact block-clear point in I (an exact sweep of F's clear set on I);
then the whole set at that point.  Sets: core drawn from [1, CMAX], block drawn with f in [T*max C, R*T*max C].
"""
import sys, random, math
from fractions import Fraction as F
def cd(x): x = x - math.floor(x); return min(x, 1 - x)
def clear_points(R, thr, lo, hi):
    """least point of [lo, hi] at which every r in R has ||r t|| >= thr, exact; None if none.
    Candidate points: lo and every zone exit (N + thr)/r in [lo, hi]."""
    cands = {lo}
    for r in R:
        n0 = math.floor(r * lo) - 1
        n = n0
        while True:
            p = (n + thr) / r
            if p > hi: break
            if p >= lo: cands.add(p)
            n += 1
    for p in sorted(cands):
        if all(cd(r * p) >= thr for r in R): return p
    return None
if __name__ == '__main__':
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    CMAX = 40; T = 26; rnd = random.Random(410); fails = []; done = 0
    for _ in range(trials):
        C = sorted(rnd.sample(range(1, CMAX + 1), 4)); cm = C[-1]
        Fb = sorted(rnd.sample(range(T * cm, 4 * T * cm), 3))
        t0 = clear_points(C, F(1, 5), F(0), F(1) + F(1, 2))   # core at 1/5 in its first period
        if t0 is None or t0 == 0: fails.append(('no t0', C, Fb)); continue
        d = F(3, 40 * cm); lo, hi = t0 - d, t0 + d
        assert all(cd(c * lo) >= F(1, 8) and cd(c * hi) >= F(1, 8) for c in C)
        p = clear_points(Fb, F(1, 8), lo, hi)
        if p is None or not all(cd(x * p) >= F(1, 8) for x in C + Fb): fails.append((C, Fb, t0)); continue
        done += 1
    msg = "trials %d, block-clear point found in I and the whole set lonely there: %d; failures %d %s" % (trials, done, len(fails), fails[:3])
    out = open('block_three_check_v1.out', 'w'); out.write(__doc__ + "\n" + msg + "\n"); out.close(); print(msg)
