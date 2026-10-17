#!/usr/bin/env python3
"""Order-8 block identity (docs/n8/COLLAPSE_Z163_v2.md §1-2) transferred to the five-unit abstraction, exact.
Instants (c, s), s = s0 + 7 s1.  Classes C(c, s0) = {(c, s0 + 7 s1) : s1 in Z/7}: 42 classes of 7.
Claim: a unit state blocks exactly 2 members of every class, a pair {x, x - d} with d = (c rho)^{-1} mod 7
(the 'pair type'), and its position depends only on a block index.  Also: the non-unit states of AbsP1/AbsP2
(rho = 0 mod 7) block 0 or 7 members of a class (the collapse type)."""
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", "CMAX = 6"))
units49 = [r for r in range(1, 49) if r % 7]
def blocked(T, fl, rho, c, s): return not (7 <= (c * T + fl[c - 1] + s * c * rho) % 49 <= 41)
bad = 0; types = {}
for T in range(49):
    for fl in FL:
        for rho in units49:
            for c in range(1, 7):
                for s0 in range(7):
                    B = [s1 for s1 in range(7) if blocked(T, fl, rho, c, s0 + 7 * s1)]
                    d = pow(c * rho % 7, -1, 7)
                    ok = len(B) == 2 and ((B[0] - B[1]) % 7 in (d, (-d) % 7))
                    bad += not ok
nonunit = set()
for T in range(49):
    for fl in FL:
        for rho in [0, 7, 14, 21, 28, 35, 42]:
            for c in range(1, 7):
                for s0 in range(7):
                    nonunit.add((rho % 7 == 0 and rho == 0, sum(blocked(T, fl, rho, c, s0 + 7 * s1) for s1 in range(7))))
print("unit states x classes violating 'exactly a d-pair':", bad)
print("non-unit (rho = 0 / 7k) per-class block counts:", sorted(nonunit))
