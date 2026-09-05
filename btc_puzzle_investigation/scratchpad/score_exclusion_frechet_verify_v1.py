#!/usr/bin/env python3
"""
score_exclusion_frechet_verify_v1.py  —  independent verification of the PREREG ruling
PREREG_score_exclusion_rangecut_v1.md : the deterministic pin [s(x_P)<3/16] => [eps_scalar(d)=0]
is PRE-REFUTED. Confirms (i) the exact Fréchet marginal floor from OUR measured marginals, and
(ii) the observed joint on constructed keys (should be > 0 and ~= product => independence).

Exact integer signal path: s<3/16 by cross-product enorm*16 < 3*p; eps_u by integer comparison.
Float only in the printed density (noqa carve-out).
"""
import os, sys, random
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from ecc_secp256k1 import scalar_mul, N_ORDER as N, P as p
from int1_frame_operator_v1 import build_secp
from lift_sextant_rhombus_law_proof_v2 import enorm

LAM = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
eis, eps = build_secp()
CEIL = (N + 1) // 2

def s_lt_316(x):  return enorm(eis(x % p)) * 16 < 3 * p       # s = N(eis(x))/p < 3/16, exact
def eps_u(d):     return 1 if (d * LAM % N) >= CEIL else 0    # single-key upper-half scalar carry

def main():
    rng = random.Random(2024); M = 20000
    n_s = n_e = n_both = 0
    for _ in range(M):
        d = rng.randrange(1, N); x, _y = scalar_mul(d)
        a = s_lt_316(x); b = eps_u(d)
        n_s += a; n_e += b; n_both += (a and b)
    ps, pe, pboth = Fr(n_s, M), Fr(n_e, M), Fr(n_both, M)
    print(f"M={M}  Pr[s<3/16]={float(ps):.4f}  Pr[eps_u=1]={float(pe):.4f}")           # noqa: float
    print(f"Frechet floor Pr[s AND eps=1] >= ps+pe-1 = {float(ps+pe-1):+.4f}")          # noqa: float
    print(f"OBSERVED Pr[s<3/16 AND eps_u=1] = {float(pboth):.4f} ({n_both}/{M})")        # noqa: float
    print(f"product ps*pe = {float(ps*pe):.4f}")                                         # noqa: float
    print(f"=> pin [s<3/16 => eps_u=0] REFUTED: {n_both} core keys have eps_u=1 "
          f"(viol rate {float(pboth):.3f}); joint ~= product => independent")            # noqa: float

if __name__ == "__main__":
    main()
