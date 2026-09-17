"""Who can block the subject at its own bound, and how local is the obligation?

Owner, 2026-09-17: "I don't think all seven speeds do need a common d_min, only 3 at a
time... There can be conflict between the scales, they just can't be within three
consecutive runners or two gaps."

d_min(i) for sorted speeds is min(v_i - v_{i-1}, v_{i+1} - v_i): three consecutive runners,
two gaps. Theorem 4.8 says every difference with d_min <= |d| <= 7*d_min is CLEAR at the
subject's bound t = 1/(8*d_min). So the only possible blockers at the bound are differences
ABOVE 7*d_min -- runners far in speed, never the immediate neighbours that set d_min.

Measured here: at each subject's own bound, who is in the way, and how far are they.
"""
import random, math
from fractions import Fraction as F

def dist8(x):
    y = x - 8 * math.floor(x / 8)
    return min(y, 8 - y)

rng = random.Random(20260917)
AP = [F(k) for k in range(1, 9)]
arrs = []
for qq in (3, 5, 7, 10, 16):
    n = 0
    while n < 400:
        V = [AP[j] + F(rng.randint(-(45*qq)//100, (45*qq)//100), qq) for j in range(8)]
        if all(V[j] < V[j+1] for j in range(7)) and V[0] > 0:
            arrs.append(V); n += 1
for _ in range(600):
    arrs.append([F(v) for v in sorted(rng.sample(range(1, 200), 8))])

tot = 0; clear_at_bound = 0
blockers_are_far = 0; any_blockers = 0
dmin_is_adjacent = 0
sep_hist = {}
for V in arrs:
    for i in range(8):
        ds = [(abs(V[j]-V[i]), abs(j-i)) for j in range(8) if j != i]
        m = min(d for d, _ in ds)
        tot += 1
        # is d_min set by an immediate neighbour (separation 1)?
        if min(sep for d, sep in ds if d == m) == 1:
            dmin_is_adjacent += 1
        S = [(d/m, sep) for d, sep in ds]
        # at the subject's own bound, u = 1/8 in its own reading: runner l sits at s_l/8 laps
        blocked = [(s, sep) for s, sep in S if dist8(s) < 1]
        if not blocked:
            clear_at_bound += 1
        else:
            any_blockers += 1
            if all(s > 7 for s, _ in blocked):
                blockers_are_far += 1
            for s, sep in blocked:
                sep_hist[sep] = sep_hist.get(sep, 0) + 1

print(f"(runner, arrangement) pairs                       : {tot}")
print(f"d_min set by an IMMEDIATE neighbour (separation 1) : {dmin_is_adjacent}  "
      f"({100*dmin_is_adjacent/tot:.1f}%)")
print()
print(f"subject already lonely at its own bound            : {clear_at_bound}  "
      f"({100*clear_at_bound/tot:.1f}%)")
print(f"subject has at least one blocker at its bound      : {any_blockers}")
print(f"  ...and EVERY blocker has reading > 7 (Thm 4.8)   : {blockers_are_far}  "
      f"({100*blockers_are_far/max(any_blockers,1):.1f}%)")
print()
print(f"blockers by speed-separation |j - i| from the subject:")
for k in sorted(sep_hist):
    print(f"   separation {k}: {sep_hist[k]}")

# ---------------------------------------------------------------------------
# The separation-1 blockers are the interesting ones: a runner's OWN immediate
# neighbour blocking it. That can only happen when d_min was set by the other side,
# so the two adjacent gaps differ by more than 7x. Purely local -- 3 consecutive
# runners, 2 gaps -- which is the owner's claim. Test it.
print()
print("=" * 66)
print("THE LOCAL CONDITION: when does a subject's OWN neighbour block it?")
both = 0; neigh_blocks = 0; ratio_gt7_and_blocks = 0; ratio_le7_and_blocks = 0
ratio_gt7 = 0
for V in arrs:
    for i in range(8):
        lo = V[i] - V[i-1] if i > 0 else None
        hi = V[i+1] - V[i] if i < 7 else None
        if lo is None or hi is None:
            continue                               # endpoints have one adjacent gap
        both += 1
        r = max(lo, hi) / min(lo, hi)
        m = min(abs(V[j]-V[i]) for j in range(8) if j != i)
        nb = [abs(V[j]-V[i])/m for j in (i-1, i+1)]
        blocked = any(dist8(s) < 1 for s in nb)
        if r > 7: ratio_gt7 += 1
        if blocked:
            neigh_blocks += 1
            if r > 7: ratio_gt7_and_blocks += 1
            else: ratio_le7_and_blocks += 1
print(f"  interior subjects (two adjacent gaps)            : {both}")
print(f"  adjacent-gap ratio > 7                           : {ratio_gt7}")
print(f"  an immediate neighbour blocks at the bound       : {neigh_blocks}")
print(f"    of those, adjacent-gap ratio > 7               : {ratio_gt7_and_blocks}")
print(f"    of those, adjacent-gap ratio <= 7              : {ratio_le7_and_blocks}")
print()
if ratio_le7_and_blocks == 0:
    print("  => a neighbour NEVER blocks when the two adjacent gaps are within 7x.")
    print("     The subject's own neighbourhood can only obstruct it through the RATIO")
    print("     of its two gaps, which is a 3-consecutive-runner quantity. Everything")
    print("     else that blocks sits at speed-separation >= 2.")
else:
    print(f"  => counterexamples exist: {ratio_le7_and_blocks} neighbours block with ratio <= 7.")
