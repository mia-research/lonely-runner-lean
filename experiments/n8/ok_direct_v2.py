r"""
ok_direct_v2 -- exact o via BREAKPOINT enumeration (no lcm grid).  Independent of ob_core.

o_x(e)     : x in [0,1),     a_rho = floor(e_rho*x/2) mod 4   -- breakpoints x = 2k/e_rho
o_torus(e) : theta in [0,1), a_rho = floor(4*e_rho*theta) mod 4 -- breakpoints k/(4 e_rho)

BSM: the cell list is the union of ALL breakpoints, so no breakpoint lies strictly inside a
cell; ENTRY value is then the value throughout.  audit() re-checks entry vs exit explicitly.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce
import sys

MUV = (0, 1, 2, 3)

def _cells(bps):
    p = sorted(bps | {F(0), F(1)})
    return [(p[i], p[i+1]) for i in range(len(p)-1) if p[i] < p[i+1]]

def o_x(e):
    bps = {F(2*k, ei) for ei in e for k in range(0, (ei+1)//2 + 2) if F(2*k, ei) < 1}
    tot = F(0)
    for lo, hi in _cells(bps):
        a = [int(ei*lo/2) % 4 for ei in e]
        nu = [a[i] ^ MUV[i] for i in range(4)]
        if len(set(nu)) == 4:
            tot += hi - lo
    return tot

def o_torus(e):
    bps = {F(k, 4*ei) for ei in e for k in range(0, 4*ei)}
    tot = F(0); hi_ok = F(0)
    for lo, hi in _cells(bps):
        a = [int(4*ei*lo) % 4 for ei in e]
        al = [v >> 1 for v in a]
        if al[0]+al[1] == al[2]+al[3]:
            hi_ok += hi - lo
        nu = [a[i] ^ MUV[i] for i in range(4)]
        if len(set(nu)) == 4:
            tot += hi - lo
    return tot, hi_ok

def audit_torus(e):
    """entry value == exit value on every cell (exit = value just below the right end)."""
    bps = {F(k, 4*ei) for ei in e for k in range(0, 4*ei)}
    bad = 0
    for lo, hi in _cells(bps):
        mid_exit = lo + (hi-lo)*F(999999,1000000)
        for ei in e:
            if int(4*ei*lo) % 4 != int(4*ei*mid_exit) % 4:
                bad += 1
    return bad

if __name__ == "__main__":
    LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    print(f"# primitive unit 4-tuples (e1,e3,e5,e7), e_rho = rho mod 8, all e_rho <= {LIM}")
    print("# boundary audit (entry vs exit) on (1,3,5,7),(3,11,5,7),(17,3,21,7):",
          [audit_torus(t) for t in [(1,3,5,7),(3,11,5,7),(17,3,21,7)]], "mismatches")
    res = []
    for e1 in range(1, LIM+1, 8):
        for e3 in range(3, LIM+1, 8):
            for e5 in range(5, LIM+1, 8):
                for e7 in range(7, LIM+1, 8):
                    e = (e1,e3,e5,e7)
                    if reduce(gcd, e) != 1: continue
                    ot, h = o_torus(e)
                    res.append((ot, h, e))
    res.sort(key=lambda r: (-r[0], r[2]))
    print(f"\n{len(res)} primitive tuples.  TOP 14 by o:")
    print(f"{'e':22} {'o':>14} {'~':>9}   {'H (hi-bit)':>10} {'~':>8}")
    for ot, h, e in res[:14]:
        print(f"{str(e):22} {str(ot):>14} {float(ot):9.6f}   {str(h):>10} {float(h):8.5f}")
    over = [r for r in res if r[0] > F(1,3)]
    print(f"\n  o > 1/3 : {len(over)} tuples -> {[r[2] for r in over]}")
    rest = [r for r in res if r[0] <= F(1,3)]
    print(f"  max o among the rest: {rest[0][0]} = {float(rest[0][0]):.6f} at {rest[0][2]}")
    print(f"  o <= H everywhere? {all(r[0] <= r[1] for r in res)}")
    print(f"  max H = {max(r[1] for r in res)} = {float(max(r[1] for r in res)):.6f}"
          f"   min H = {min(r[1] for r in res)}")
    # cross-check against o_x on a sample
    import random
    random.seed(1)
    samp = random.sample(res, min(40, len(res)))
    print(f"  o_x == o_torus on {sum(1 for r in samp if o_x(r[2])==r[0])}/{len(samp)} sampled tuples")
