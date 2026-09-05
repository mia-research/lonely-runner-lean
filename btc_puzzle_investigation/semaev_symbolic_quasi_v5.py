# semaev_symbolic_quasi_v5.py   --   run:  sage semaev_symbolic_quasi_v5.py
#
# PREREG v5, arms B-S1 / B-S2: exact symbolic verification of the candidate mu3
# quasi-homogeneity of the Semaev polynomials at A=0 (j=0 curves).
#
# B-S1: S_3(w*a, w*b, w*c) == w * S_3(a,b,c)   for A=0, w a formal cube root of unity,
#       checked against the FROZEN INSTRUMENT'S OWN S_3 construction (semaev3), with B symbolic.
# B-S2: the equivariance exponent k of S_4:  S_4(w*x1..w*x4) == w^k * S_4(x1..x4),
#       built the instrument's way (summation_poly, m=3 => S_4(x1,x2,x3,t)).
# B-S2b (delimiting, reported not verdict): S_4(w*x1,w*x2,w*x3, t) with FIXED t --
#       the H1-relevant case (random V, fixed target). Expected NOT proportional;
#       the exact obstruction is computed.
#
# All arithmetic in exact rings QQ(w)[...] -- no floats.

from sage.all import *

H = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/semaev_elimination_v1.py"
_g = {'__name__': 'harness_mod'}
exec(open(H).read(), _g)
semaev3       = _g['semaev3']
summation_poly = _g['summation_poly']

K = CyclotomicField(3, 'w')
w = K.gen()

print("=" * 78)
print("B-S1: quasi-homogeneity of the instrument's S_3 at A=0")
print("=" * 78)
# Ring with B symbolic: QQ(w)[B,a,b,c]
R = PolynomialRing(K, ['B', 'a', 'b', 'c'])
B, a, b, c = R.gens()
A0 = R(0)

S3 = semaev3(a, b, c, A0, B)          # the instrument's own 3-variable Semaev polynomial
S3_scaled = semaev3(w * a, w * b, w * c, A0, B)

diff1 = S3_scaled - w * S3
print("  S3(wa,wb,wc) - w*S3(a,b,c) =", diff1)
print("  identically zero:", diff1 == 0)
BS1 = (diff1 == 0)
print("  B-S1:", "PROVED" if BS1 else "REFUTED")

# Control: the same check at A != 0 must FAIL (the symmetry is A=0-specific).
R2 = PolynomialRing(K, ['A', 'B', 'a', 'b', 'c'])
A2, B2, a2, b2, c2 = R2.gens()
S3_A = semaev3(a2, b2, c2, A2, B2)
S3_A_scaled = semaev3(w * a2, w * b2, w * c2, A2, B2)
ctrl = (S3_A_scaled - w * S3_A == 0)
print("  control (A symbolic, must FAIL):", ctrl, "->", "OK (fails as expected)" if not ctrl else "*** UNEXPECTED ***")

print()
print("=" * 78)
print("B-S2: equivariance of S_4 (instrument construction, m=3)")
print("=" * 78)
# Replicate _build_summation's m=3 path EXACTLY (P(4,zs) = Res_X(S3(z1,z2,X), S3(z3,z4,X)))
# in a FLAT ring QQ(w)[Bs, z1..z4, X] -- avoids Sage's nested-ring coercion failure in Rt().
Rflat = PolynomialRing(K, ['Bs', 'z1', 'z2', 'z3', 'z4', 'X'])
Bs, z1, z2, z3, z4, X = Rflat.gens()
left  = semaev3(z1, z2, X, Rflat(0), Bs)
right = semaev3(z3, z4, X, Rflat(0), Bs)
S4 = left.resultant(right, X)
ok_build = True

if ok_build:
    subs_all = {z1: w * z1, z2: w * z2, z3: w * z3, z4: w * z4}
    S4_scaled = S4.subs(subs_all)
    # find k such that S4_scaled == w^k * S4  (w^3=1, so k in {0,1,2})
    found = None
    for k in range(3):
        if S4_scaled - K(w)**k * S4 == 0:
            found = k
            break
    print("  S4(w*x1,w*x2,w*x3,w*t) == w^k * S4(x1,x2,x3,t):", found if found is not None else "NO k WORKS")
    BS2 = found is not None
    print("  B-S2:", ("PROVED (k=%d)" % found) if BS2 else "REFUTED")

    # B-S2b: fixed target (H1-relevant case)
    subs_fixt = {z1: w * z1, z2: w * z2, z3: w * z3}
    S4_fixt = S4.subs(subs_fixt)
    prop = None
    for k in range(3):
        if S4_fixt - K(w)**k * S4 == 0:
            prop = k
            break
    if prop is None:
        d1 = S4_fixt - S4
        print("  B-S2b (fixed t): NOT proportional (as expected for the H1 case).")
        print("    |monomials(S4)| =", len(S4.monomials()),
              "  |monomials(S4(w*x,t)-S4(x,t))| =", len(d1.monomials()))
    else:
        print("  B-S2b (fixed t): proportional with k=%d (unexpected -- would imply orbit" % prop,
              "symmetry at fixed target)")

print()
print("=" * 78)
print("SUMMARY")
print("=" * 78)
print("  B-S1 (S3 quasi-homogeneous, A=0):", "PROVED" if BS1 else "REFUTED")
if ok_build:
    print("  B-S2 (S4 equivariant, all-scaled):", ("PROVED k=%d" % found) if BS2 else "REFUTED")
print("  [record in RESULT_semaev_cm_lever_capability_v5.md]")
