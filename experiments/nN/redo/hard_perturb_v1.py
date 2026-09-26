"""Step 2 of E80: perturb the hardest cases (hard_cases_v1) through the cascade.  For each of the top 15: every speed
moved by -8..+8 in units of 1/8 of a whole speed (speeds scaled x8), one speed at a time, exactly.  Record the event's R,
the relay length, the relay word's prefix, whether the relay still reaches the nearest runner's zone (7, 9) (rank 0 sets),
and how many moves keep a late event (R > 7).  Also the staircase: for each pair of consecutive readings, whether their
first-lap zones (7/rho, 9/rho) overlap (ratio < 9/7)."""
import re
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from hard_cases_v1 import relay

def job(V):
    base = [8 * v for v in V]
    w0, R0, ds = relay(base)
    rho = [F(d, ds[0]) for d in ds]
    stair = [rho[i + 1] / rho[i] < F(9, 7) for i in range(6)]
    rows = []
    for i in range(8):
        for sh in range(-8, 9):
            if sh == 0: continue
            W = list(base); W[i] += sh; W = sorted(W)
            if len(set(W)) < 8 or W[0] < 1: continue
            w, R, _ = relay(W)
            rows.append((i, sh, float(R), len(w), 0 in w))
    return V, float(R0), len(w0), stair, rows

if __name__ == '__main__':
    Vs = []
    for line in open('hard_cases_v1.out'):
        m = re.search(r'V (\[[^\]]*\])', line)
        if m: Vs.append(eval(m.group(1)))
    with Pool() as pool: res = pool.map(job, Vs[:15])
    allrows = [r for *_, rows in res for r in rows]
    late = [r for r in allrows if r[2] > 7]
    print(f"hard cases 15; one-speed moves of 1/8 .. 1 speed unit: {len(allrows)}")
    print(f"  still late (R > 7): {len(late)}; still passing the nearest runner's zone (rank 0 sets): {sum(r[4] for r in allrows)}")
    print(f"  R after the move: {sorted(Counter(min(int(r[2]), 12) for r in allrows).items())}")
    print(f"  late by moved speed rank (0 = subject): {sorted(Counter(r[0] for r in late).items())}; by step: {sorted(Counter(r[1] for r in late).items())}")
    for V, R0, n0, stair, rows in res[:6]:
        keep = [(i, sh) for i, sh, R, n, z in rows if R > 7]
        print(f"  V {V}: R {R0:.3f}, {n0} moves; first-lap staircase links (ratio < 9/7) {stair}; late survives at moves {keep[:12]}")
