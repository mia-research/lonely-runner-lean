r"""
ok_slack_v1 -- the Slack Lemma, and how much of Case 2 it reaches.

Case 1's proof is t = a/8, a odd: then ||e t|| = ||rho*a/8|| >= 1/8 for every e with 8 not
dividing e.  It is TIGHT exactly when rho*a = +-1 mod 8, i.e. (units are self-inverse mod 8)
when rho = +-a.  So:

  SLACK LEMMA.  If a in {1,3,5,7} and NO non-divisible runner has e = +-a (mod 8), then at
  t0 = a/8 every non-divisible runner has ||e t0|| >= 1/4 -- a full 1/8 of slack -- so
  ||e(t0+d)|| >= 1/8 for every |d| <= 1/(8V), V = max non-divisible speed.

The residue pairs {+-a} are {1,7} and {3,5}.  So the lemma applies iff
      R_non misses BOTH 1 and 7,   or   R_non misses BOTH 3 and 5.
Unit-Complete means {1,3,5,7} subset R_non, so it ALWAYS fails the lemma -- which is exactly
why that branch is hard.  Tested below, plus the reach over all 3312 residue multisets.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from collections import Counter

def nrm(x): 
    r = x - int(x)
    if r < 0: r += 1
    return min(F(r), 1-F(r))

print("check the lemma's arithmetic: min over rho of ||rho*a/8|| for each a")
for a in (1,3,5,7):
    row=[]
    for rho in range(1,8):
        row.append((rho, nrm(F(rho*a,8))))
    tight=[rho for rho,v in row if v==F(1,8)]
    print(f"  a={a}: ||rho a/8|| = {[(r,str(v)) for r,v in row]}")
    print(f"        tight (=1/8) at rho = {tight}   -> lemma needs R_non to miss {tight}")

print("\nreach over all 3312 realisable residue multisets:")
UNITS={1,3,5,7}
tot=0; hit=0; byshape=Counter(); hitshape=Counter()
for ms in combinations_with_replacement(range(8),7):
    if not any(r%2 for r in ms): continue
    tot+=1
    Rnon={r for r in ms if r!=0}; Ediv=sum(1 for r in ms if r==0)
    uc = UNITS<=Rnon
    key=f"{'UC' if uc else 'DU'} |R_non|={len(Rnon)} |E_div|={Ediv}"
    byshape[key]+=1
    ok = (not (Rnon & {1,7})) or (not (Rnon & {3,5}))
    if ok: hit+=1; hitshape[key]+=1
print(f"  Slack Lemma applies to {hit} / {tot} multisets  ({100*hit/tot:.1f}%)")
print(f"  shapes FULLY covered by it: "
      f"{sum(1 for k in byshape if hitshape[k]==byshape[k])} of {len(byshape)}")
print(f"  Unit-Complete shapes covered: {sum(hitshape[k] for k in hitshape if k.startswith('UC'))}"
      f"  (must be 0)")
print("\n  the extremal tuple (2,6,7,8,10,13,14): R_non = {2,5,6,7}")
R={2,5,6,7}
print(f"    misses both 1,7 ? {not (R & {1,7})}    misses both 3,5 ? {not (R & {3,5})}"
      f"   -> lemma applies: {(not (R&{1,7})) or (not (R&{3,5}))}")
