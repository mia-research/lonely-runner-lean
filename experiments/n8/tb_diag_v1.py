r"""
tb_diag_v1 -- diagnostic: for a given tuple, the whole resonance ladder.

For e, and for each height R, prints  L_R(e) rank, the saturated lattice, and its
EXACT Haar limit o_inf.  The quantity that decides (H3u) asymptotically is

      Delta(e) := o_inf(M')  -  o_inf(M_3),      M' = sat L_R(e) for the largest R
                                                 with rank <= 2, M_3 = sat L_3(e),

because a deep member of the same rank-2 class has o -> o_inf(M') while its
o_inf(L_3^sat) stays at o_inf(M_3).  Delta > 1/12 on any realisable class REFUTES
(H3u); Delta <= 1/12 everywhere is what (H3u) needs asymptotically.

usage: python3 tb_diag_v1.py "25,11,77,7" [RMAX]
"""
import sys
from fractions import Fraction as F
import rt_limit_v2 as RL
from ob_fast_v1 import o_fast, audit


def low_res(e, R):
    out = []
    for n3 in range(-R, R + 1):
        for n5 in range(-R, R + 1):
            for n7 in range(-R, R + 1):
                s = n3 * e[1] + n5 * e[2] + n7 * e[3]
                if s % e[0]:
                    continue
                n1 = -s // e[0]
                if abs(n1) > R or (n1 == n3 == n5 == n7 == 0):
                    continue
                out.append((n1, n3, n5, n7))
    return out


def limit_of(res):
    if not res:
        return F(3, 32), 0, ()
    M = [list(v) for v in res]
    B, rk = RL.kernel_basis(M)
    if rk == 0:
        return F(3, 32), 0, ()
    if rk >= 3:
        return None, rk, ()
    key, _ = RL.lattice_key(M)
    rows = [list(r) for r in key]
    val = RL.rank1_limit(tuple(rows[0])) if rk == 1 else RL.rank2_limit(rows)
    return val, rk, key


if __name__ == "__main__":
    e = tuple(int(x) for x in sys.argv[1].split(","))
    RMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    o = o_fast(e)
    print(f"e = {e}   o = {o} = {float(o):.7f}   boundary audit {audit(e)}")
    prev = None
    for R in range(1, RMAX + 1):
        res = low_res(e, R)
        lim, rk, key = limit_of(res)
        if (rk, key) == prev:
            continue
        prev = (rk, key)
        ls = f"{lim} = {float(lim):.7f}" if lim is not None else "(rank 3 -- o itself)"
        print(f"  R = {R:2d}:  #res = {len(res):4d}  rank = {rk}  o_inf = {ls}")
        if key:
            for r in key:
                print(f"            {r}")
        if lim is not None:
            print(f"            o - o_inf = {float(o - lim):+.7f}")
