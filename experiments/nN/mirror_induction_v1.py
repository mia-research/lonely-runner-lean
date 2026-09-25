"""Case B as an induction on order through the mirror merge -- and whether slack is needed.

At t = m/Q, Q = e + d_max, the largest reads exactly minus e: ||d_max t|| = ||e t||.  The merge is
exact, so no slack is spent on it.  Slack would only be spent ROUNDING an order-7 instant of the
other six (lonely at 1/7) onto the lattice m/Q: readings move by up to d/(2Q), which needs
Q >= 28 d_6 (d_6 the second largest) to stay within 1/7 - 1/8 = 1/56.
Tests on the hard sets (largest 41..60), no rounding anywhere:
  round   -- how many have Q >= 28 d_6 for some e (the slack route is possible at all);
  M(th)   -- some e in S \ {d_max} and m with every disparity at >= th at m/(e + d_max), for
             th = 1/8 (the mirror certificate with d_max as one side) and th = 1/7 (order seven's
             threshold, on the mirror lattice).
  Also M(1/8) with e_R = d_max forced vs the cell's own pair, and the non-hard control.
"""
import json, os, random
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def M(S, num, den):                     # threshold num/den: den*min(r, Q - r) >= num*Q
    b = max(S); out = []
    for e in S:
        if e == b: continue
        Q = e + b
        for m in range(1, Q):
            if all(den * min(d * m % Q, Q - d * m % Q) >= num * Q for d in S): out.append(e); break
    return out
def study(sets, label):
    rnd = sum(any(e + max(S) >= 28 * sorted(S)[-2] for e in S if e != max(S)) for S in sets)
    m8 = Counter(bool(M(S, 1, 8)) for S in sets); m7 = Counter(bool(M(S, 1, 7)) for S in sets)
    miss8 = [S for S in sets if not M(S, 1, 8)][:5]; miss7 = [S for S in sets if not M(S, 1, 7)][:5]
    print(f"{label} ({len(sets)}): rounding possible (Q >= 28 d_6) {rnd}; "
          f"mirror with d_max at 1/8: {m8[True]} (misses {miss8}); at 1/7: {m7[True]} (misses {miss7})")
study(H, "hard sets, largest 41..60")
random.seed(9); easy = []
while len(easy) < 2000:
    S = tuple(sorted(random.sample(range(1, 61), 7)))
    if eight_residual(S) and any(rule(S, q, free_exact) for q in range(2, 9)): easy.append(S)
study(easy, "non-hard residual sets of [1,60]")

# Control (as mirror_control_v1): the same test at Q +- 1, same size, no mirror pairing.
def Mshift(S, num, den, s):
    b = max(S)
    for e in S:
        if e == b: continue
        Q = e + b + s
        for m in range(1, Q):
            if all(den * min(d * m % Q, Q - d * m % Q) >= num * Q for d in S): return True
    return False
def dens(S, num, den, s):
    b = max(S); tot = hit = 0
    for e in S:
        if e == b: continue
        Q = e + b + s
        for m in range(1, Q):
            tot += 1; hit += all(den * min(d * m % Q, Q - d * m % Q) >= num * Q for d in S)
    return hit / tot
for s in (0, -1, 1):
    ok = sum(Mshift(S, 1, 7, s) for S in H); dn = sum(dens(S, 1, 7, s) for S in H) / len(H)
    print(f"hard sets at 1/7, Q = e + d_max {s:+d}: some lonely point {ok} of {len(H)}; mean share of lattice points lonely {100*dn:.2f}%")
