# unit tests for zone engine and type constraints (positive + negative controls)
from zones import *
from core import block_ok, landing
from fractions import Fraction as F
import random
z=band_zone(); p=z.point(); print("band point", [str(v) for v in p])
assert not z.empty()
# empty control: s6 > 9 contradiction
z2=band_zone().add(0,6,F(1,9),True).close(); assert z2.empty(), "should be empty"
# type constraints must agree with block test on random points
rng=random.Random(1); bad=0; tested=0
for _ in range(3000):
    n6=rng.randint(7*2520+1,9*2520); ns=(2520,*sorted(rng.sample(range(2521,n6),5)),n6)
    vals=[F(n,2520) for n in ns]
    for e in range(7):
        for K in range(0,17):
            ok=block_ok(ns,e,K)
            laps=type_of(vals,e,K)
            inzone=all(contains(vals,c) for c in type_constraints(e,K,laps))
            tested+=1
            if ok and not inzone: bad+=1
            if ok!= inzone:
                # inzone with same laps but not ok would be a soundness hole
                if inzone and not ok: bad+=1
print("type/block agreement tested", tested, "disagreements", bad)
assert bad==0
