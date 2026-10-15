#!/usr/bin/env python3
"""CRT form of the flank criterion at a flank e with gcd(e, 6) = 1 (n = 6). Opening j has multiplier
m = 6j + 1 (mod 6e). For a difference d with s = d mod 6, put w = d*m mod e and
c = einv * (s - w) mod 6, einv the inverse of e mod 6 (a unit, 1 or 5). Then the residue is
r = d*m mod 6e = w + e*c  (CRT), and the claim tested is
    e <= r <= 5e   iff   c in {1,2,3,4}   or   (c = 5 and w = 0)    [r = 5e exactly]
                                         or   (c = 0 and w >= e) -- impossible since w < e.
Checked for every opening j < e, every d in [1, 4e], every e coprime to 6 up to EMAX."""
import sys
EMAX = int(sys.argv[1]); checked = mism = 0
for e in range(1, EMAX + 1):
    if e % 2 == 0 or e % 3 == 0: continue
    einv = 1 if e % 6 == 1 else 5
    for d in range(1, 4 * e + 1):
        s = d % 6
        for j in range(e):
            m = 6 * j + 1
            r = (d * m) % (6 * e)
            w = (d * m) % e
            c = (einv * (s - w)) % 6
            assert r == w + e * c, (e, d, j)
            direct = e <= r <= 5 * e
            cell = (1 <= c <= 4) or (c == 5 and w == 0)
            checked += 1
            if direct != cell: mism += 1
print(f"EMAX={EMAX}: openings checked={checked}, CRT identity r = w + e*c held throughout, criterion mismatches={mism}")
