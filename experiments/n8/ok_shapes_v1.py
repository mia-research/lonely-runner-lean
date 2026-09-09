r"""
ok_shapes_v1 -- BOX-FREE audit of the n=8 case tree.

A tuple's shape is fixed by its multiset of residues mod 8.  Enumerating multisets instead
of tuples removes the box artefact: ok_treecover_v1 ran over [1..26], which cannot contain
four multiples of 8, so it could not produce |E_div| >= 4 at all.

Realisability: any residue multiset of size 7 with at least one ODD residue is realised by
7 distinct positive integers of gcd 1 (all-even residues force gcd >= 2; with an odd residue
r present, use r and r+8, whose gcd divides 8 and is odd, hence 1).

Covered shapes (STATUS section 1), all of which carry |R_non| = 5:
   L1        |E_div| = 0
   DU5       some unit not in R_non, |R_non| = 5
   UC5_div2  units subset R_non, |R_non| = 5, |E_div| = 2
   UC5_div1  units subset R_non, |R_non| = 5, |E_div| = 1
"""
from itertools import combinations_with_replacement
from collections import Counter

UNITS = {1,3,5,7}
shapes = Counter(); ex = {}
for ms in combinations_with_replacement(range(8), 7):
    if not any(r % 2 for r in ms): continue          # gcd 1 needs an odd speed
    Ediv = sum(1 for r in ms if r == 0)
    Rnon = {r for r in ms if r != 0}
    uc = UNITS <= Rnon
    if Ediv == 0: key = "L1  [covered]"
    elif not uc and len(Rnon) == 5: key = "DU5  [covered]"
    elif uc and len(Rnon) == 5 and Ediv == 2: key = "UC5_div2  [covered, (H')]"
    elif uc and len(Rnon) == 5 and Ediv == 1: key = "UC5_div1  [covered, twin]"
    else: key = f"{'UC' if uc else 'DU'}  |R_non|={len(Rnon)}  |E_div|={Ediv}"
    shapes[key] += 1
    ex.setdefault(key, ms)

cov = {k: v for k, v in shapes.items() if "covered" in k}
unc = {k: v for k, v in shapes.items() if "covered" not in k}
print(f"realisable residue multisets: {sum(shapes.values())}")
print(f"  covered by a proved leaf : {sum(cov.values())}  ({len(cov)} shapes)")
print(f"  NOT covered              : {sum(unc.values())}  ({len(unc)} shapes)\n")

def kEdiv(k):
    return int(k.split("|E_div|=")[1]) if "|E_div|=" in k else -1
print("UNCOVERED shapes, grouped by |E_div|:")
for d in sorted({kEdiv(k) for k in unc}):
    ks = [k for k in unc if kEdiv(k) == d]
    tot = sum(unc[k] for k in ks)
    note = ""
    if d >= 4:
        note = "  <-- |E_non| <= 3 blocks <= 6 < 8 residues; LRC(d+1) places x.  ONE-LINE"
    print(f"\n |E_div| = {d}   ({len(ks)} shapes, {tot} multisets){note}")
    for k in sorted(ks, key=lambda k: -unc[k]):
        print(f"     {k:34} {unc[k]:5}   e.g. residues {ex[k]}")
print(f"\nmax |E_div| realisable = {max(kEdiv(k) for k in list(unc)+list(cov) if kEdiv(k)>=0)}")
