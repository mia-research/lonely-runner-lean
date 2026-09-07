#!/usr/bin/env python3
"""CONTROL P2 from PREREG_X3_SECTOR_v1: a PLANT that must fire.
Take a seeded 4-set V of non-coarse speeds, compute D(V) = classes it fully covers, and feed
M := D(V) to the unmodified search.  A completion exists BY CONSTRUCTION (V itself), so the
search must return one.  A miss means the pruning is unsound and the run would be void.
Integer/bitmask only, no float."""
import sys, random
sys.path.insert(0, "experiments/n8")
from x3_sector_pilot_v1 import B, noncoarse, p
import x3_sector_pilot_v2 as S

rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
odd = [v for v in noncoarse if v % 2 == 1]
fired = miss = skipped = 0
for trial in range(30):
    V = rng.sample(odd, 2) + rng.sample([v for v in noncoarse if v % 2 == 0], 2)
    D = (B[V[0]][0]|B[V[1]][0]|B[V[2]][0]|B[V[3]][0])
    for t in (1,2,3):
        D &= (B[V[0]][t]|B[V[1]][t]|B[V[2]][t]|B[V[3]][t])
    if bin(D).count("1") < 20: skipped += 1; continue     # need a non-trivial demand set
    S.nodes = 0
    got = S.search(D, [0,0,0,0], 0, [])
    if got: fired += 1
    else:
        miss += 1
        print(f"  MISS: planted V={sorted(V)}  |D|={bin(D).count('1')}  search returned None")
print(f"PLANT CONTROL: {fired} fired, {miss} MISSED, {skipped} skipped (|D| < 20).")
print("PASS -- search finds a completion whenever one exists by construction."
      if miss == 0 else "FAIL -- pruning is unsound; the sector run would be VOID.")
