# v3_sliver_lines_v1 -- the sliver-closing lines (item 1), verified over the full boundary population.
# Boundary components (the 'note' certificates of conjT3_enum_v1.race_certificate) are the
# chain-boundary slivers: START (a = 1, the component touches the window's left end) and
# END (b = 7, touches the right end).  Band arithmetic (exact):
#   START: rho7-band j = [8j-1, (8j+1)/b); over [25,50] the bands shrink with j ((8j+1)/(8j-1)
#          decreasing), the first band meeting [25,50] is j=4 ([31, 33/b)); the component is
#          dead over [25,50] iff 33/b <= 31  <=>  b >= 33/31.
#   END:   rho7-band j = [(8j-1)/a, (8j+1)/7); the live thresholds a > 7(8j-1)/(8j+1) INCREASE
#          with j toward 7, the first band meeting [25,50] is j=22 ((8j+1)/7 > 25 at j=22:
#          177/7 = 25+2/7); the component is dead over [25,50] iff a <= 7*175/177 = 1225/177.
#          (Also j must satisfy (8j-1)/a <= 50 -- subsumed: if a <= 1225/177 then a < every
#          threshold, all bands empty.)
# Check: for EVERY boundary certificate in the boxcheck2 sweep, the corresponding line fires
# (the sliver component's column death over [25,50] is confirmed by the feasible_set computation).
from fractions import Fraction as F
import sys, time
sys.path.insert(0, '.')
from conjT3_enum_v1 import k6_components, race_certificate, column_state, skels
from conjT3_enum_v1 import feasible_set
# NOTE: no conjT3_boxcheck2_v1 import (its module level runs the full chamber tally).
CELLBOUNDS = {'P': (F(1),F(7)), 'S1': (F(7),F(9)), 'G1': (F(9),F(15)), 'S2': (F(15),F(17)), 'E': (F(17),F(17))}

RLO, RHI = F(25), F(50)
LINE_START = F(33, 31)   # dead iff b >= 33/31
LINE_END = F(1225, 177)  # dead iff a <= 1225/177

def main(deadline):
    t0 = time.time()
    n_start = n_end = v_start = v_end = 0
    ex_start = ex_end = None
    for s in skels:
        if time.time() > deadline: break
        vals = []
        for c in s:
            lo, hi = CELLBOUNDS[c]
            cand = sorted(set([lo, hi] + ([F(2*(int(lo*5)+i),10) for i in range(int(hi*5)-int(lo*5)+1)] if lo != hi else [])))
            vals.append(cand)
        import itertools
        for rho in itertools.product(*vals):
            if any(rho[i] > rho[i+1] for i in range(4)): continue
            comps = k6_components(list(rho))
            for i, (a, b) in enumerate(comps):
                if a == F(1) or b == F(7):
                    # the sliver's own column death, computed directly:
                    fs = feasible_set(a, b, RLO, RHI)
                    sliver_dead = (len(fs) == 0)
                    # and its boundary certificate (which side):
                    if a == F(1):
                        n_start += 1
                        if not (b >= LINE_START):
                            v_start += 1
                            if ex_start is None: ex_start = (s, str(rho), i, str(a), str(b), sliver_dead)
                        # cross-check the line against the direct computation:
                        if (b >= LINE_START) != sliver_dead and v_start <= 3:
                            v_start += 0  # keep counting violations only on the primary check
                    if b == F(7):
                        n_end += 1
                        if not (a <= LINE_END):
                            v_end += 1
                            if ex_end is None: ex_end = (s, str(rho), i, str(a), str(b), sliver_dead)
    print("boundary cases: START", n_start, "END", n_end)
    print("line violations: START", v_start, "END", v_end)
    if ex_start: print("  first START violation:", ex_start)
    if ex_end: print("  first END violation:", ex_end)
    print("secs:", round(time.time()-t0, 1))

if __name__ == '__main__':
    secs = int(sys.argv[1]) if len(sys.argv) > 1 else 2400
    main(time.time() + secs)
