#!/usr/bin/env sage
# d_ff support law — is the Semaev first-fall degree a THEOREM about the harness rather than a
# measurement about ECDLP?
#
# DERIVATION under test:
#  (a) support of S_{m+1}(x;tau) is the dense box [0,D]^m, D = 2^(m-1)  => the max-total-degree
#      monomial x_1^D...x_m^D is UNIQUE => every polynomial on that support has the same leading form.
#  (b) macaulay_stats skips a generator until its own degree ("if df > D: continue"), and the field
#      equations x_i^m + ... alone are a REGULAR sequence (harness calibration CAL_A must be None)
#      => NO fall is possible below deg(P) = m*2^(m-1).
#  (c) at D = deg(P) the leading form x_1^D...x_m^D lies in (x_1^m,...,x_m^m) iff D >= m
#      => a fall is FORCED there.
#  ==> d_ff = m*2^(m-1) exactly, for ANY polynomial on that support.
#
# PREDICTION: d_ff = 4 (m=2), 12 (m=3), 32 (m=4), 80 (m=5), 192 (m=6).
# Measured: 4, 12, CENSORED>30 (Dmax was 30 < 32 -- consistent).
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import semaev_elimination_v1 as se
import semaev_structure_firstfall_vs_m_v2 as rn

A = 0; B = 7
print(f"{'m':>2} {'|supp|':>7} {'box':>10} {'D=2^(m-1)':>10} {'top mon unique':>15} "
      f"{'D>=m':>6} {'deg(P)=m*2^(m-1)':>17}")
for m in (2, 3, 4):
    F = GF(307); G = EllipticCurve(F, [A, B]).gens()[0]; tau = int(G[0])
    V = [i for i in range(1, m + 1)]
    Rx, Sx, xr, feq = rn.build_pieces(F, A, B, m, tau, V)
    supp = list(Sx.monomials())
    degs = [sum(e) for mo in supp for e in [mo.exponents()[0]]]
    D = 2**(m - 1)
    top = [mo for mo in supp if sum(mo.exponents()[0]) == max(degs)]
    print(f"{m:>2} {len(supp):>7} {str((D+1))+'^'+str(m):>10} {D:>10} "
          f"{str(len(top) == 1)+' ('+str(top[0])+')':>15} {str(D >= m):>6} {m*D:>17}")
    assert len(supp) == (D + 1)**m, "support is not the dense box"
    assert max(degs) == m * D and len(top) == 1
    # field-equation leading forms are x_i^m ; does the top monomial reduce?
    assert all(e >= m for e in top[0].exponents()[0]), "top monomial not divisible by any x_i^m"

print("\nRe-measuring d_ff with the harness at m=2,3 (fast) to confirm the law:")
for (m, Dmax) in ((2, 12), (3, 22)):
    for p in (307, 2069):
        F = GF(p); G = EllipticCurve(F, [A, B]).gens()[0]; tau = int(G[0])
        V = [i for i in range(1, m + 1)]
        Rx, Sx, xr, feq = rn.build_pieces(F, A, B, m, tau, V)
        dff = rn.d_ff_of(F, [Sx] + list(feq), xr, Dmax)
        calA = rn.d_ff_of(F, list(feq), xr, Dmax)
        pred = m * 2**(m - 1)
        print(f"  m={m} p={p}: d_ff={dff}  predicted={pred}  "
              f"{'MATCH' if dff == pred else 'MISMATCH'} | CAL_A (field eqs alone, must be None)={calA}",
              flush=True)

print("\nPredicted d_ff = m*2^(m-1):",
      {m: m * 2**(m - 1) for m in range(2, 9)})
