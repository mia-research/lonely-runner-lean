"""Framework-native: does the GUARD structure pick the reading that carries the witness?

AP: the clear set is the odd integers (ap_clear_at_odd); the witness is u odd in {1,3,5,7}.
General profile: the witness is u = (8m+1)/s -- the AP's odd-integer isolation, deformed by s.
Guard relation (Guard_v1): reading s guards R iff s*R = 1 (mod 8); guards are the units.
R closed form: least R >= 1 with s_i*R mod 8 in [1,7] for every reading.
"""
from itertools import combinations
from collections import Counter

def R_of(S):
    R = 1
    while True:
        if all((s*R) % 8 for s in S): return R
        R += 1

def supplies(S, s):
    M = 8*s; A = s + ((1-s) % 8)
    while A <= 7*s:
        if all(min((sp*A) % M, M - (sp*A) % M) >= s for sp in S): return True
        A += 8
    return False

tot = 0
tab = Counter()          # (is guard of R, supplies) -> count
never_odd = Counter()
for combo in combinations(range(2, 26), 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo; tot += 1
    R = R_of(S)
    for s in S:
        if s == 1: continue
        g = ((s*R) % 8 == 1)             # s guards R
        w = supplies(S, s)
        tab[(g, w)] += 1
        never_odd[(s % 2, w)] += 1

print(f"Branch B profiles, readings [2,25]: {tot:,}\n")
gw, gn = tab[(True,True)], tab[(True,False)]
ngw, ngn = tab[(False,True)], tab[(False,False)]
print(f"  reading GUARDS R      : supplies a witness {gw:>8,}   does not {gn:>8,}"
      f"   ({100*gw/(gw+gn):5.1f}%)")
print(f"  reading does NOT guard: supplies a witness {ngw:>8,}   does not {ngn:>8,}"
      f"   ({100*ngw/(ngw+ngn):5.1f}%)")
print()
for par, lab in ((1,"ODD "), (0,"EVEN")):
    a, b = never_odd[(par,True)], never_odd[(par,False)]
    print(f"  reading {lab} : supplies {a:>8,}  does not {b:>8,}   ({100*a/(a+b):5.1f}%)")
