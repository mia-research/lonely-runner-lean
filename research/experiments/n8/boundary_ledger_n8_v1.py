#!/usr/bin/env python3
"""BOUNDARY LEDGER at n = 8 -- the translation of Appendix A.1-A.8 of lrc_n11_ap_paper_v30.md.

Complete blocking in W_ref means every pacemaker slot is FULLY covered by runners 2..n-2.
A slot is covered only if BOTH its endpoints are covered.  So the real objects are the slot
BOUNDARIES and, for each, the list of runners that can reach it and over what range of a_j.

  slots     I_s = [(n s + 1)/(n(n-1)), (n s + n-1)/(n(n-1))],  s = 1..n-2
  chain     B_{j,k}(a) = [(n k + n-1)/(n a), (n k + n+1)/(n a)]
  B_{j,k} contains a boundary b  <=>  (nk+n-1)/(n b) <= a <= (nk+n+1)/(n b)
  sign range (Lemma 5.1)  a_j in (j-1, j+1)

Exact Fraction only, no float.  Run with n=11 to compare against Appendix A.
"""
import sys
from fractions import Fraction as F

def ledger(n, wide=False):
    S = {s: (F(n*s+1, n*(n-1)), F(n*s+n-1, n*(n-1))) for s in range(1, n-1)}
    rows = {}
    for s,(bl,br) in S.items():
        for side, b in (("L", bl), ("R", br)):
            fills = []
            for j in range(2, n-1):
                lo, hi = (F(0), F(n)) if wide else (F(j-1), F(j+1))
                for k in range(0, 4*n):
                    amin, amax = F(n*k+n-1, n)/b, F(n*k+n+1, n)/b
                    l, h = max(lo, amin), min(hi, amax)
                    if l < h: fills.append((j, k, l, h))
            rows[(s, side, b)] = fills
    return S, rows

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    S, rows = ledger(n)
    print(f"n = {n}.  slots I_1..I_{n-2}; fillers = runners 2..{n-2}, a_j in (j-1,j+1).")
    for (s, side, b), fills in sorted(rows.items()):
        js = sorted({j for j,_,_,_ in fills})
        print(f"  I_{s} {side}-boundary b = {b}:  runners able to reach it: {js}"
              f"   ({len(fills)} (j,k) windows)")
        if len(js) <= 2:
            for j,k,l,h in fills:
                print(f"        runner {j}, k={k}:  a_{j} in [{l}, {h}]"
                      f"   width {h-l}")
