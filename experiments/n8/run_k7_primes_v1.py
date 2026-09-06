#!/usr/bin/env python3
"""Rosenfeld's 27 primes for k=7, via the unit-scaling normalisation."""
import time, sys
from normalised_search_v1 import bad_cover_normalised
# Rosenfeld's S, transcribed from the source (arXiv:2509.14111v2, eq. after Lemma 4).
# 41 is ABSENT: section 7 says "for k = 7, it seems that any prime p at least 31
# other than 41 works".  Our own search finds the bad cover at 41 independently --
# T = {1,4,12,13,14,16,20}, which covers all 164 targets and passes the gcd
# condition.  An earlier version of this list wrongly included 41 (28 primes).
PRIMES = [31,37,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,
          127,131,137,139,149,151,157,163]
assert len(PRIMES) == 27
tot = 0.0
for p in PRIMES:
    t0 = time.time()
    b = bad_cover_normalised(7, p)
    dt = time.time() - t0
    tot += dt
    print(f"k=7 p={p:>4}  bad cover: {str(b):>5}  Lemma 7 {'FAILS' if b else 'applies'}   {dt:8.1f}s")
    sys.stdout.flush()
print(f"total {tot:.1f}s")
