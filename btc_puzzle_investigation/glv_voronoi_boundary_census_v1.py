#!/usr/bin/env python3
"""glv_voronoi_boundary_census_v1.py -- how many GLV Voronoi fault lines are there, and does the
POINT know about them?

The proposal: the Babai coefficients c1, c2 tick over only every ~2^128 scalars, so a random
1000-width interval is a flatland; target the exact scalars where the fractional part crosses 1/2
("the fault lines") and look for a phase shift / variance collapse in chi_2(x) as the scalar
crosses from one Voronoi cell to the next.

TWO CHECKS, both exact integer arithmetic, both cheap:

  B1  CENSUS.  Count the c1- and c2-boundaries inside the puzzle's native range [2^127, 2^128),
      and inside other ranges.  #boundaries in [L,U) = c(U) - c(L) exactly.  If the count in the
      target range is O(1), "targeted boundary sampling" there has a sample size of O(1).

  B2  REPRESENTATIVE-INDEPENDENCE.  At a true boundary, exhibit the jump in (k1,k2) and check what
      the POINT does.  [d]G = [k1]G + [k2][lambda]G holds for EVERY valid (k1,k2) with
      k1 + k2*lambda = d (mod N).  So the point is a function of d alone; the Voronoi cell is a
      property of which representative the reduction ALGORITHM returned.  Verified by computing
      [d]G both ways across a boundary.
"""

N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
A, Bc = 0, 7
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
LAMBDA = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
BETA = 0x7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE

A1 = 0x3086D221A7D46BCDE86C90E49284EB15
B1 = -0xE4437ED6010E88286F547FA90ABFE4C3
A2 = 0x114CA50F7A8E2F3F657C1108D9D44CFD8
B2 = 0x3086D221A7D46BCDE86C90E49284EB15


def rnd_div(a, b):
    q, r = divmod(a, b)
    return q + 1 if 2*r >= b else q


def c1_of(d):
    return rnd_div(d*B2, N)


def c2_of(d):
    return rnd_div(-(d*B1), N)


def glv(d):
    c1, c2 = c1_of(d), c2_of(d)
    return d - c1*A1 - c2*A2, -c1*B1 - c2*B2


def padd(Pt, Q):
    if Pt is None:
        return Q
    if Q is None:
        return Pt
    x1, y1 = Pt
    x2, y2 = Q
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if Pt == Q:
        num, den = (3*x1*x1 + A) % P, (2*y1) % P
    else:
        num, den = (y2 - y1) % P, (x2 - x1) % P
    lm = num * pow(den, P - 2, P) % P
    x3 = (lm*lm - x1 - x2) % P
    return (x3, (lm*(x1 - x3) - y1) % P)


def pmul(d, Pt):
    if d == 0 or Pt is None:
        return None
    neg = d < 0
    d = abs(d)
    R = None
    Q = Pt
    while d:
        if d & 1:
            R = padd(R, Q)
        Q = padd(Q, Q)
        d >>= 1
    return R if not neg else (R[0], (-R[1]) % P)


print("=" * 92)
print("B1 -- CENSUS OF GLV VORONOI FAULT LINES")
print("=" * 92)
print("  #c1-boundaries in [L,U) = c1(U) - c1(L);  same for c2.  Exact integer counts.")
print()
print("  %-34s %14s %14s %14s" % ("range", "c1 boundaries", "c2 boundaries", "total"))
ranges = [
    ("puzzle native  [2^127, 2^128)", 2**127, 2**128),
    ("puzzle #64     [2^63, 2^64)", 2**63, 2**64),
    ("[2^128, 2^129)", 2**128, 2**129),
    ("[2^130, 2^131)", 2**130, 2**131),
    ("[2^140, 2^141)", 2**140, 2**141),
    ("[2^160, 2^161)", 2**160, 2**161),
    ("full group [1, N)", 1, N),
]
for (lab, L, U) in ranges:
    n1 = c1_of(U) - c1_of(L)
    n2 = c2_of(U) - c2_of(L)
    print("  %-34s %14d %14d %14d" % (lab, n1, n2, n1 + n2))
print()
print("  Spacing: a c1 boundary every ~N/B2 = 2^%d scalars; a c2 boundary every ~N/|B1| = 2^%d."
      % ((N//B2).bit_length(), (N//(-B1)).bit_length()))
print("  => the ENTIRE puzzle-scale range [2^127, 2^128) contains the number of fault lines")
print("     printed above.  Targeted boundary sampling there has that many samples.")

print()
print("=" * 92)
print("B2 -- DOES THE POINT KNOW ABOUT THE BOUNDARY?")
print("=" * 92)
# locate an exact c2 boundary by binary search in [2^127, 2^128)
lo, hi = 2**127, 2**128
base = c2_of(lo)
if c2_of(hi) == base:
    print("  no c2 boundary in [2^127,2^128) -- searching [2^128, 2^129)")
    lo, hi = 2**128, 2**129
    base = c2_of(lo)
while hi - lo > 1:
    mid = (lo + hi)//2
    if c2_of(mid) == base:
        lo = mid
    else:
        hi = mid
dstar = hi
print("  exact boundary scalar d* = %d" % dstar)
print("  d* bit length = %d" % dstar.bit_length())
k_before, k_after = glv(dstar - 1), glv(dstar)
print("  (k1,k2) at d*-1 : k1 has %d bits, k2 has %d bits"
      % (abs(k_before[0]).bit_length(), abs(k_before[1]).bit_length()))
print("  (k1,k2) at d*   : k1 has %d bits, k2 has %d bits"
      % (abs(k_after[0]).bit_length(), abs(k_after[1]).bit_length()))
jump = (k_after[0] - k_before[0], k_after[1] - k_before[1])
print("  JUMP in (k1,k2) across the boundary: (%d, %d)" % jump)
print("     -> |jump| ~ 2^%d, 2^%d  (a lattice vector, not a step of 1)"
      % (abs(jump[0]).bit_length(), abs(jump[1]).bit_length()))
for d in (dstar - 1, dstar):
    k1, k2 = glv(d)
    assert (k1 + k2*LAMBDA - d) % N == 0, "GLV relation broken"
print("  both decompositions satisfy k1 + k2*LAMBDA = d (mod N): True")

G = (Gx, Gy)
Gl = (BETA*Gx % P, Gy)
assert pmul(LAMBDA, G) == Gl, "beta/lambda mismatch"
print("  [LAMBDA]G == (BETA*Gx, Gy): True   (the endomorphism, verified)")

print()
print("  Now the point itself, computed TWO ways on each side of the boundary:")
for lab, d in (("d*-1", dstar - 1), ("d*  ", dstar)):
    k1, k2 = glv(d)
    direct = pmul(d % N, G)
    viaglv = padd(pmul(k1, G), pmul(k2, Gl))
    print("     %s : direct [d]G == [k1]G + [k2][lambda]G : %s" % (lab, direct == viaglv))
Pb = pmul((dstar - 1) % N, G)
Pa = pmul(dstar % N, G)
print("  [d*]G - [d*-1]G == G : %s" % (padd(Pa, (Pb[0], (-Pb[1]) % P)) == G))
print()
print("  => crossing a Voronoi boundary changes the REPRESENTATIVE by a lattice vector while the")
print("     POINT advances by exactly G.  [d]G depends on d alone, never on which (k1,k2) the")
print("     reduction returned.  A statistic computed from (x,y) cannot see the cell boundary,")
print("     for the same reason it cannot see which algorithm you used to compute the point.")
