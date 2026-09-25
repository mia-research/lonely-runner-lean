"""Are there EightResidual sets at all, once no_small_resolution (D <= 64) is in?  Every finite window
tested is empty (eight_residual_count_v6).  Construct candidates: five small runners C (random from
[1,100]) and two runners F = {L*u, L*u'} with L = 8*lcm(1..64), 1 <= u < u' <= 7u (so R8 does not
apply), and test the full residual predicate (v5's fields, verbatim, plus no clearing resolution
D <= 64 and no common factor).  Exact integer arithmetic throughout.
"""
import random, math
from math import gcd, lcm
from functools import reduce
src = open('eight_residual_count_v5.py').read()
exec(src[:src.index("t0 = time.time()")].replace("N = int(sys.argv[1]) if len(sys.argv) > 1 else 30", ""))
def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)
def small_resolution(S, cap=64): return any(clears(S, D, 8 * j + 1) for D in range(1, cap + 1) for j in range(D))
def residual(S):
    if len(set(S)) != 7 or reduce(gcd, S) > 1: return False
    if not any(d % 2 for d in S): return False
    if not all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8)): return False
    if not max(S) > 7 * min(S): return False
    if sum(4 if d % 8 == 4 else 2 for d in S if d % 8) < 8: return False
    if any(free_flank8(S, e) for e in S if e % 8 == 0): return False
    if shifted(S): return False
    srt = sorted(S)
    if srt[-1] > 7 * srt[-2]: return False
    if first_lap(S) or minus_seven(S): return False
    if has_rational_opening(S) or has_thirds(S) or has_fifths(S): return False
    if has_N(S, 6) or has_N(S, 7) or has_N(S, 9): return False
    if small_resolution(S): return False
    return True
L = 8 * lcm(*range(1, 65)); rnd = random.Random(30)
members = []; tried = 0
while tried < 3000:
    C = rnd.sample(range(1, 101), 5); u = rnd.randrange(1, 50); u2 = rnd.randrange(u + 1, 7 * u + 1)
    S = tuple(sorted(C + [L * u, L * u2])); tried += 1
    if residual(S): members.append(S)
print(f"L = 8*lcm(1..64) has {len(str(L))} digits")
print(f"constructed {tried}: in EightResidual (with D <= 64): {len(members)}")
for S in members[:5]:
    C = [d for d in S if d < L]; F = [d // L for d in S if d >= L]
    print(f"  core {C}, fast pair L*{F}")
