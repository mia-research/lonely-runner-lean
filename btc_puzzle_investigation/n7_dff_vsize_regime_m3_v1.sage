#!/usr/bin/env sage
# THE DECISIVE TEST for lead 7: is the measured d_ff forced by a degenerate factor base?
#
# DERIVATION (all premises confirmed by the harness's own numbers, re-measured this session):
#   supp(S_{m+1}(x;tau)) = dense box [0,D]^m with D = 2^(m-1)  =>  UNIQUE top monomial x_1^D..x_m^D
#   macaulay_stats skips a generator until its own degree, and the field eqs alone are a regular
#   sequence (CAL_A = None, re-confirmed)  =>  NO fall is possible below deg(P) = m*D.
#   At deg(P) a fall is FORCED iff x_1^D..x_m^D in (x_1^N,..,x_m^N), i.e. iff D >= N, N = |V|.
#   The harness sets N = m, and 2^(m-1) >= m for all m>=1  =>  d_ff = m*2^(m-1) IDENTICALLY.
#   Confirmed: 4 (m=2, both p), 12 (m=3), zero variance over 24 draws. m=4 predicts 32, and
#   Dmax was 30 -- so "CENSORED >30" was arithmetically guaranteed, not a discovery.
#
# The REAL Semaev regime has |V| ~ p^(1/m) >> 2^(m-1), i.e. N > D: the top monomial does NOT reduce
# and the fall is NOT forced. That regime has never been sampled.
#
# TEST (m=2: D=2, deg(P)=4, TWO variables -- cheap): sweep N = |V| across the D >= N boundary.
#   PREDICT  N <= 2 -> d_ff = 4 (forced);  N >= 3 -> mechanism gone, d_ff must DEPART from 4.
#   FALSIFIER: d_ff stays 4 for every N -> the fall is not the leading-form reduction; I am wrong.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from semaev_elimination_v1 import summation_poly, macaulay_stats

def d_ff_of(F, gens, xs, Dmax):
    st = macaulay_stats(F, gens, xs, Dmax)
    for D in sorted(st):
        if st[D].get('fall', 0) > 0: return D
    return None

A = 0; B = 7; m = 3; p = 307; Dmax = 20
F = GF(p); G = EllipticCurve(F, [A, B]).gens()[0]; tau = int(G[0])
S, xs_big, t_big = summation_poly(F, A, B, m)
Rt = xs_big[0].parent()
Rx = PolynomialRing(F, ['x%d' % i for i in range(1, m + 1)], order='degrevlex')
phi = Rt.hom(list(Rx.gens()) + [F(tau)], Rx)
Sx = phi(S); xr = list(Rx.gens())
D = 2**(m - 1); degP = Sx.degree()
print(f"m={m} p={p}  support={len(Sx.monomials())}  D=2^(m-1)={D}  deg(P)={degP}  Dmax={Dmax}")
print(f"PREDICTED d_ff = max(D,N)+(m-1)*D\n{chr(78):>6} {'D>=N (forced?)':>15} {'CAL_A (regular, want None)':>27} {'d_ff':>7} {'= deg(P)?':>10}")
for N in range(3, 8):
    V = list(range(1, N + 1))
    feq = [prod([xi - F(v) for v in V]) for xi in xr]
    t0 = time.time()
    calA = d_ff_of(F, list(feq), xr, Dmax)
    dff = d_ff_of(F, [Sx] + list(feq), xr, Dmax)
    print(f"{N:>6} {str(D >= N):>15} {str(calA):>27} {str(dff):>7} {str(dff == degP):>10}"
          f"   [{time.time()-t0:.0f}s]", flush=True)
