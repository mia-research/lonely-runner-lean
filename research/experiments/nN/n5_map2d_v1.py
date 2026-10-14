"""Two-parameter map of the dominant residue case.

Dominant case: non-flank = {d1, d2, 5m}, flank e, 5 does not divide e.
With 5 not dividing e, CRT makes a determined by r = a mod e (one a per r), and
   the MULTIPLE's condition is  m*r mod e in [e/5, 4e/5]   -- depends only on r
   a NON-multiple's condition is d*a mod 5e in [e, 4e]     -- depends on r through a
The hard cases observed were (1, 4, 5m, 5m+2): the multiple adjacent to the flank.
Map #openings over (m, e) with the small pair fixed, and look for the rule.
"""
import math

def n_open(c):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

print("=== (1, 4, 5m, e) : #openings as e moves past 5m ===")
print(f"{'m':>3} {'5m':>4} | " + " ".join(f"e={5*0+d:>3}" for d in []) )
for m in range(3, 12):
    row = []
    for off in range(1, 11):
        e = 5*m + off
        c = (1, 4, 5*m, e)
        if not prim(c) or e % 5 == 0: row.append("  . "); continue
        row.append(f"{n_open(c):>4}")
    print(f"{m:>3} {5*m:>4} | offsets e-5m = 1..10: " + "".join(row))
print()
print("=== the minimum over offsets, and WHERE it occurs ===")
print(f"{'m':>3} {'min #open':>10} {'at offset':>10} {'e':>5} {'e mod 5':>8} {'m mod 5':>8}")
for m in range(3, 20):
    best = None
    for off in range(1, 16):
        e = 5*m + off
        c = (1, 4, 5*m, e)
        if not prim(c) or e % 5 == 0: continue
        w = n_open(c)
        if best is None or w < best[0]: best = (w, off, e)
    if best:
        w, off, e = best
        print(f"{m:>3} {w:>10} {off:>10} {e:>5} {e%5:>8} {m%5:>8}")
