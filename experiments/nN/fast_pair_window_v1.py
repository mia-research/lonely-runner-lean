"""Two-runner window lemma at 1/8, and the fast-pair rule with PROVED constants.

Lemma (claimed): for integers 0 < a <= b, every closed window of length 3/(4a) contains t with
||a t|| >= 1/8 and ||b t|| >= 1/8.  Check exactly: the longest open run with no common clear point
(over one period of the pair, BSM-style: blocked zones open, their union's components) times a,
maximised over 1 <= a <= b <= 80.
Rule: core C (5 runners) lonely at 1/6 (order six) gives a C-clear window of length
2(1/6 - 1/8)/max C = 1/(12 max C) around its instant; if min(F) >= 9 max C for the pair F, the
lemma puts a common clear point of F inside it.  Applied, with exact construction and band-test
verification, to the members of residual_members_v2 (no large common factor, block split silent).
"""
from fractions import Fraction as Fr
from math import gcd
def longest_joint_blocked(a, b):
    g = gcd(a, b); P = Fr(1, g)                    # period of the pair
    z = sorted([(Fr(k, a) - Fr(1, 8 * a), Fr(k, a) + Fr(1, 8 * a)) for k in range(0, a // g + 2)] +
               [(Fr(k, b) - Fr(1, 8 * b), Fr(k, b) + Fr(1, 8 * b)) for k in range(0, b // g + 2)])
    # a common clear point is any point outside the union of the open zones; the union's components
    # are the maximal runs with no common clear point (touching open zones leave their shared end clear)
    best = Fr(0); lo, hi = z[0]
    for s, e in z[1:]:
        if s < hi: hi = max(hi, e)
        else: best = max(best, hi - lo); lo, hi = s, e
    return max(best, hi - lo)
worst = max((longest_joint_blocked(a, b) * a, a, b) for a in range(1, 81) for b in range(a, 81))
print(f"max over 1 <= a <= b <= 80 of (longest run with no common clear point) * a = {worst[0]} "
      f"(= {float(worst[0]):.4f}) at a={worst[1]}, b={worst[2]};  claimed bound 3/4: {'holds' if worst[0] <= Fr(3, 4) else 'FAILS'}")

exec(open('residual_members_v2.py').read().split("print(f\"constructed")[0])
def nd(x): x = x % 1; return min(x, 1 - x)
def lonely_opening(D, thr):
    best = None
    for e in D:
        for j in range(e):
            t = (j + thr) / e
            if all(nd(d * t) >= thr for d in D) and (best is None or t < best): best = t; break
    return best
ok = 0; fails = []
for S in members:
    C = [x for x in S if x < 10**6]; F = sorted(x for x in S if x >= 10**6); a, b = F
    assert a >= 9 * max(C)
    tau = lonely_opening(C, Fr(1, 6)); delta = (Fr(1, 6) - Fr(1, 8)) / max(C)
    # inside [tau - delta, tau + delta]: find a common clear point of (a, b) by scanning a's clear bands
    lo = tau - delta; hi = tau + delta; found = None
    k = (lo * a).__floor__()
    while found is None and Fr(k, a) <= hi:
        band_lo = max(lo, Fr(8 * k + 1, 8 * a)); band_hi = min(hi, Fr(8 * k + 7, 8 * a))
        if band_lo <= band_hi:
            m = (band_lo * b).__floor__()
            for cand in (band_lo, band_hi, Fr(8 * m + 1, 8 * b), Fr(8 * m + 9, 8 * b), Fr(8 * m + 7, 8 * b)):
                if band_lo <= cand <= band_hi and all(8 * nd(d * cand) >= 1 for d in S): found = cand; break
        k += 1
    if found is not None: ok += 1
    else: fails.append(S)
print(f"residual members without a large common factor: {len(members)};  fast-pair rule (min F >= 9 max C) "
      f"gives an exactly verified lonely instant: {ok}/{len(members)}")
