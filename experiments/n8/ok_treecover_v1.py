r"""
ok_treecover_v1 -- is the n=8 case tree EXHAUSTIVE?

Our three leaf theorems (STATUS_n8_ANALYTIC_v1 section 1) all carry |R_non| = 5:
  DROPPED_UNIT_THEOREM_v1:10  "|R_non| = 5 with at least one absent residue class a unit"
  PARITY_MECHANISM_v1:10-11   Unit-Complete = "the two residue classes of {1..7} absent
                               from R_non are both non-units", so R_non = {1,3,5,7} + one rho0
  SAFE_FIBRE_THEOREM_v1:56    "|E_non| = 5 and |E| = 7, so |E_div| = 2 always"

Classify every 7-subset E of [1..LIM] with gcd 1 into:
  L1            E_div empty                                  (Case 1, proved, one line)
  DU5           E_div nonempty, some unit not in R_non, |R_non| = 5     (dropped-unit leaf)
  UC5_div2      Unit-Complete, |R_non| = 5, |E_div| = 2                 (H' leaf)
  UC5_div1      Unit-Complete, |R_non| = 5, |E_div| = 1                 (twin leaf)
  UNCOVERED     anything else
and report the uncovered shapes with examples.
"""
from itertools import combinations
from functools import reduce
from math import gcd
from collections import Counter
import sys

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 24
UNITS = {1,3,5,7}
cnt = Counter(); examples = {}
tot = 0
for E in combinations(range(1, LIM+1), 7):
    if reduce(gcd, E) != 1: continue
    tot += 1
    res = [e % 8 for e in E]
    Ediv = [e for e, r in zip(E, res) if r == 0]
    Rnon = {r for r in res if r != 0}
    if not Ediv:
        key = "L1"
    else:
        uc = UNITS <= Rnon
        if not uc and len(Rnon) == 5:                       key = "DU5"
        elif uc and len(Rnon) == 5 and len(Ediv) == 2:      key = "UC5_div2"
        elif uc and len(Rnon) == 5 and len(Ediv) == 1:      key = "UC5_div1"
        else:
            kind = "UnitComplete" if uc else "droppedUnit"
            key = f"UNCOVERED  {kind}  |R_non|={len(Rnon)}  |E_div|={len(Ediv)}"
    cnt[key] += 1
    examples.setdefault(key, (E, sorted(Rnon), Ediv))

print(f"# all 7-subsets of [1..{LIM}] with gcd 1 : {tot}")
print(f"\n{'class':46} {'count':>9}  example")
for k in sorted(cnt, key=lambda k: (k.startswith("UNCOVERED"), -cnt[k])):
    E, R, D = examples[k]
    print(f"{k:46} {cnt[k]:9}  E={E} R_non={R} E_div={D}")
unc = sum(v for k, v in cnt.items() if k.startswith("UNCOVERED"))
print(f"\nCOVERED   : {tot-unc:9} ({100*(tot-unc)/tot:.2f}%)")
print(f"UNCOVERED : {unc:9} ({100*unc/tot:.2f}%)   distinct uncovered shapes: "
      f"{sum(1 for k in cnt if k.startswith('UNCOVERED'))}")
