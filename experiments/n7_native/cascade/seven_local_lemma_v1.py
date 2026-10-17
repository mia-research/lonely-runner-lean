#!/usr/bin/env python3
"""Local digit lemma (EXACT, complete).  Runner state (u0, u1, e, D): u0 = u mod 7 (unit), u1 = second digit of u,
e = digit 1 and D = digit 2 of (u k2 + C_u).  With k = k2 + 7 y + 49 s, the top digit (digit 2) of u k + C_u is
(D + u1 y + floor((e + u0 y)/7) + u0 s) mod 7; allowed iff in {1..5}.  Mask of a state = set of (y, s) in 7x7 allowed.
Question: do some 5 masks (repetition allowed) have empty intersection?  Computed by closing the set of distinct
intersections of j masks for j = 1..5.  If 0 never appears, then for every five units mod 343, every shift vector C and
every k2, some (y, s) works."""
masks = set()
for u0 in range(1, 7):
    for u1 in range(7):
        for e in range(7):
            for D in range(7):
                m = 0
                for y in range(7):
                    for s in range(7):
                        if 1 <= (D + u1 * y + (e + u0 * y) // 7 + u0 * s) % 7 <= 5:
                            m |= 1 << (7 * y + s)
                masks.add(m)
print(f"states 2058, distinct masks {len(masks)}")
level = set(masks)
for j in range(2, 6):
    nxt = set()
    for a in level:
        for b in masks:
            nxt.add(a & b)
    level = nxt
    print(f"  intersections of {j} masks: {len(level)} distinct; empty intersection occurs: {0 in level}; "
          f"min popcount {min(bin(x).count('1') for x in level)}")
