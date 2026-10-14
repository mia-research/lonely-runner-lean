"""Branch B: is there always a witness A/(8 s*) with A = 1 mod 8?

Readings S = {1, s2..s7}, integers.  Branch A (no reading divisible by 8) is proved.
Branch B: some s* with 8 | s*.  Test whether W(S, s) is nonempty, where

    W(S,s) = { A : A = 1 mod 8, s <= A <= 7s, and for all s' in S,
               min(r, 8s-r) >= s   with r = (s'*A) mod 8s }

All integer arithmetic.  Control: the same test with s NOT divisible by 8.
"""
from itertools import combinations
import random

def W(S, s):
    """The witness set, as a list."""
    M = 8*s
    out = []
    A = s + ((1 - s) % 8)          # least A = 1 mod 8 with A >= s
    while A <= 7*s:
        ok = True
        for sp in S:
            r = (sp*A) % M
            if min(r, M-r) < s:
                ok = False; break
        if ok: out.append(A)
        A += 8
    return out

# --- sanity: the s'=s identity the spec flagged, for EVERY s ---
for s in (3, 8, 11, 24, 40):
    A = s + ((1-s) % 8)
    assert (s*A) % (8*s) == s, (s, A)
print("identity check: (s*A) mod 8s = s for every s when A = 1 mod 8  -- holds\n")

# --- exhaustive arm: 6 free readings from [2,30], at least one divisible by 8 ---
fails, tot, wcount1 = [], 0, 0
ctrl_fail, ctrl_tot = 0, 0
pool = list(range(2, 31))
for combo in combinations(pool, 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo
    tot += 1
    star = [x for x in combo if x % 8 == 0]
    # main: every multiple of 8 must work (STRICT)
    for sstar in star:
        w = W(S, sstar)
        if not w:
            fails.append((S, sstar)); break
        if len(w) == 1: wcount1 += 1
    # control: readings not divisible by 8
    for s0 in combo:
        if s0 % 8 == 0 or s0 < 2: continue
        ctrl_tot += 1
        if not W(S, s0): ctrl_fail += 1

print(f"EXHAUSTIVE, 6 free readings from [2,30] with a multiple of 8: {tot:,} profiles")
print(f"  MAIN  (s = s*, strict over all multiples of 8): failures = {len(fails):,}")
print(f"  CTRL  (s not divisible by 8):                   failures = {ctrl_fail:,} / {ctrl_tot:,}"
      f"  ({100*ctrl_fail/ctrl_tot:.2f}%)")
print(f"  profiles where the witness set had size exactly 1: {wcount1:,}")
if fails:
    for S, sstar in fails[:5]:
        print(f"    COUNTEREXAMPLE  S={S}  s*={sstar}")
