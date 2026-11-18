# v3_exact_chain_v1 -- V3 with ALL-lap zones of rho6 and rho7: exact chain-cover search over the REAL box
#   1 <= rho2 <= ... <= rho7 <= B, with rho6 > RHO6LO (strict) and rho7 >= RHO7LO.
# Variables u_i = 1/rho_i (u_0 = reading 1).  Uses chain_cover_v4.search (strict: open zones cover [1,7]).
# Every reading, rho6 and rho7 included, contributes zones at every lap j (zones_of in taillemma_lib_v1 does too).
# [PROVISIONAL: covering] cover <=> no clear point in W0.  [PROVISIONAL: counting tool] laps bounded by rho <= B.
import sys, time
from fractions import Fraction as F
sys.path.insert(0, '.')
import chain_cover_v4 as cc
from d0_points_only_k6_v2 import base_system as _bs

def run(B, rho6lo, rho7lo, node_cap, secs, nread=7, show=True):
    B = F(B)
    def bs(n, BB):
        s = _bs(n, BB)
        if rho6lo is not None and n >= 6:
            assert s.add(n-2, 0, 1/F(rho6lo), True)      # u_{n-2} < u_0/rho6lo  (rho_{n-1} > rho6lo)
        if rho7lo is not None:
            assert s.add(n-1, 0, 1/F(rho7lo), False)     # u_{n-1} <= u_0/rho7lo
        return s
    cc.base_system = bs
    t = time.time()
    res, covers, nodes = cc.search(nread, B, 1, [(1, 7)], True, node_cap, time.time() + secs)
    out = (res, nodes, round(time.time() - t, 1))
    wit = None
    if covers:
        wit = cc.witness(covers[0][1], nread, [(F(1), F(7))], F(1), True)
    return out, covers, wit

if __name__ == "__main__":
    B, r6, r7 = F(sys.argv[1]), (None if sys.argv[2] == 'None' else F(sys.argv[2])), (None if sys.argv[3] == 'None' else F(sys.argv[3]))
    cap, secs = int(sys.argv[4]), int(sys.argv[5])
    out, covers, wit = run(B, r6, r7, cap, secs)
    print("B=%s rho6>%s rho7>=%s : %s" % (B, r6, r7, out))
    if wit: print("  witness rho =", [str(x) for x in wit])
    if covers: print("  chain:", covers[0][0])
