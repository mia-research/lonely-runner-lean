#!/usr/bin/env python3
"""Base sets for the mixed shape (four units + z = 7^w m, 1 <= w <= a-2), for seven_abstract_triples_v1.c.
P1 (w = 1): runner 1 = 1 (T 0, first Farey cell, rho 1); z has rho in {7..42}, any T, any open cell.
   Base set = mask(runner 1) & mask(z).  Need: no three unit masks cover it.
P2 (w >= 2): base chosen with theta_z in [1/7, 6/35], so z is in band at every strategy with c <= 5 (rho_z = 0);
   runner 1 then has T 0 (by a fold), any open cell, any unit rho.  Base set = mask(runner 1) & {c <= 5}.
Writes units.txt (all distinct unit masks, 5 words) and bases_P1.txt, bases_P2.txt."""
import sys
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", "CMAX = 6"))
out = sys.argv[1]
def words(m): return " ".join(str((m >> (64 * w)) & ((1 << 64) - 1)) for w in range(5))
units49 = [r for r in range(1, 49) if r % 7]
U = {mask(T, fl, rho) for T in range(49) for fl in FL for rho in units49}
open(f"{out}/units.txt", "w").write(f"{len(U)}\n" + "\n".join(words(m) for m in U) + "\n")
m1 = mask(0, FL[0], 1)
P1 = {m1 & mask(T, fl, rho) for T in range(49) for fl in FL for rho in [7, 14, 21, 28, 35, 42]}
c5 = sum(1 << b for b, (c, s) in enumerate(strategies) if c <= 5)
P2 = {mask(0, fl, rho) & c5 for fl in FL for rho in units49}
for name, B in (("P1", P1), ("P2", P2)):
    open(f"{out}/bases_{name}.txt", "w").write(f"{len(B)}\n" + "\n".join(words(m) for m in B) + "\n")
    print(name, "base sets", len(B), "popcounts", min(bin(m).count('1') for m in B), max(bin(m).count('1') for m in B))
print("unit masks", len(U))
