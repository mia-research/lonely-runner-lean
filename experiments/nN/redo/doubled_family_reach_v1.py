"""E162: how far the proved doubled-slot family reaches.  Case B arrangements (subject at 0, readings = the other seven
speeds, readings <= 24, scaled by d_min where d_min divides all): (a) in the dsZ family exactly at scale d_min (the eight
speeds are {0..7} minus one slot r, plus s + 8m: the AP with one runner lapped into another slot); (b) residue pattern
mod 8 has exactly one doubled slot and one empty slot, any laps (the general one-doubled grid); (c) complete residue
system (no doubled slot); (d) other patterns.  Also: whether the set is lonely at the bound.  Exact integers."""
import itertools
from collections import Counter
from fractions import Fraction as F
import sys; sys.path.insert(0, '../band_cert_v1'); from core import is_clear
C = Counter()
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 24 * T[0]): continue
    g = T[0]
    if any(d % g for d in T):
        C[('not on the d_min grid',)] += 1; continue
    sp = [0] + [d // g for d in T]
    res = Counter(v % 8 for v in sp)
    doubled = [r for r, c in res.items() if c == 2]; empty = [r for r in range(8) if res[r] == 0]
    lapped = [v for v in sp if v >= 8]
    if len(res) == 8: kind = 'complete residue system'
    elif len(doubled) == 1 and len(empty) == 1 and max(res.values()) == 2:
        kind = 'dsZ family (one runner lapped)' if len(lapped) == 1 and sorted(v for v in sp if v < 8) == sorted(set(range(8)) - set(empty) | {doubled[0]} - (set() if doubled[0] in [v for v in sp if v < 8] else set())) or (len(lapped) == 1) else 'one doubled slot, several runners lapped'
        if len(lapped) != 1: kind = 'one doubled slot, several runners lapped'
    else: kind = 'two or more doubled slots'
    C[(kind, 'bound clear' if is_clear(T, F(1, g)) else 'bound blocked')] += 1
for k, v in sorted(C.items(), key=lambda kv: -kv[1]): print("  %7d  %s" % (v, k))
