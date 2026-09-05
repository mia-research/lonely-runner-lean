"""
lrc_n11_uit_enum_v1.py
======================
Universal Incompatibility Theorem (UIT) Enumeration.

For each of the 247 feasible sign classes sigma = (s_2,...,s_9) in {+1,-1}^8, attempts
to demonstrate incompatibility via the pair (2,9) argument.

PROVED RESULT (paper §10.16, Theorem 10.16.5 = Runner 2 Incompatibility):
For the ++------ sign class (sigma_2=+1, sigma_9=-1):
  - Primary obligation: runner 2 closes I_4 → a_2 ≥ 20/9
  - I_9 left gap [10/11, 261/275] (runner 9 locked at a_9=25/3 by cascade) → a_2 ≤ 575/261
  - Gap = 20/9 - 575/261 = 5/261 > 0. ⟹ GF > 0.

STRUCTURE OF THIS SCRIPT:
  Part 1: Reproduce the proved incompatibility for ++------ with exact arithmetic.
  Part 2: For each sign class with sigma_2=+1 (128 classes), show L_primary = 20/9
           is sign-class-INDEPENDENT. The bound R_I9 = 575/261 is conditional on
           the cascade giving a_9=25/3; this is proved for ++------ and conjectured
           for other sigma_2=+1 classes.
  Part 3: For sigma_2=-1 classes (128 classes), state the symmetric structure via
           runner 9 (cascade analysis pending per sign class).

KEY FORMULAS:
  Slot I_{m-1} = [(11m-10)/110, (11m-1)/110], m=2,...,10.
  Bad interval of runner j: B_{j,k} = [(11k+10)/(11*a_j), (11k+12)/(11*a_j)].
  Runner j closes LEFT  edge of slot I_{m-1} via B_{j,k}: a_j ≥ (11k+10)*110/(11*(11m-10))
  Runner j closes RIGHT edge of slot I_{m-1} via B_{j,k}: a_j ≤ (11k+12)*110/(11*(11m-1))

COMPLEMENTARY PAIRS (from Theorem 10.16.1):
  j  j^{-1} mod 11   m_j^+ = 10*j^{-1} mod 11   owns I_{m^+-1} (upper) and I_{m^--1} (lower)
  2       6                    5                    I_4 (upper, sigma_2=+1), I_5 (lower, sigma_2=-1)
  3       4                    7                    I_6 (upper), I_3 (lower)
  4       3                    8                    I_7 (upper), I_2 (lower)
  5       9                    2                    I_1 (upper), I_8 (lower)
  (pairs: (2,9), (3,8), (4,7), (5,6); I_9 is always unclaimed)
"""

from fractions import Fraction

# ────────────────────────────────────────────────────────────────────────────
# Slot and bad interval structure
# ────────────────────────────────────────────────────────────────────────────

def slot_bounds(m):
    """Slot I_{m-1} = [(11m-10)/110, (11m-1)/110], witness t_m = m/11."""
    return Fraction(11*m - 10, 110), Fraction(11*m - 1, 110)

def bad_interval_bounds(k, a_j):
    """B_{j,k} = [(11k+10)/(11*a_j), (11k+12)/(11*a_j)]."""
    return Fraction(11*k + 10, 1) / (11 * a_j), Fraction(11*k + 12, 1) / (11 * a_j)

def a_closes_left(m, k):
    """Minimum a_j so that B_{j,k} left end ≤ left edge of I_{m-1}."""
    # (11k+10)/(11*a_j) ≤ (11m-10)/110 → a_j ≥ 110*(11k+10) / (11*(11m-10))
    return Fraction(110 * (11*k + 10), 11 * (11*m - 10))

def a_closes_right(m, k):
    """Maximum a_j so that B_{j,k} right end ≥ right edge of I_{m-1}."""
    # (11k+12)/(11*a_j) ≥ (11m-1)/110 → a_j ≤ 110*(11k+12) / (11*(11m-1))
    return Fraction(110 * (11*k + 12), 11 * (11*m - 1))

# ────────────────────────────────────────────────────────────────────────────
# Part 1: Exact reproduction of Runner 2 Incompatibility for ++------
# ────────────────────────────────────────────────────────────────────────────

print("=" * 70)
print("Part 1: Runner 2 Incompatibility (++------ class) — PROVED")
print("=" * 70)

# Primary obligation: close I_4 (slot m=5) from the left via B_{2,0}
L_primary = a_closes_left(5, 0)
print(f"  L_primary = a_2 ≥ {L_primary} = {float(L_primary):.6f}")
print(f"  (minimum a_2 to close I_4 left edge via B_{{2,0}})")

# Cascade (++------ specific): runner 9 locked at a_9 = 25/3
a9_cascade = Fraction(25, 3)
print(f"\n  Cascade (++------): a_9 = {a9_cascade} = {float(a9_cascade):.6f}")

# Runner 9 bad interval B_{9,7} covers part of I_9
I9_lo, I9_hi = slot_bounds(10)   # = [100/110, 109/110]
k9 = 7
B9_lo, B9_hi = bad_interval_bounds(k9, a9_cascade)
print(f"  B_{{9,7}} = [{B9_lo} = {float(B9_lo):.6f}, {B9_hi} = {float(B9_hi):.6f}]")
print(f"  I_9     = [{I9_lo} = {float(I9_lo):.6f}, {I9_hi} = {float(I9_hi):.6f}]")
print(f"  Left gap of I_9: [{I9_lo}, {B9_lo}] = [{float(I9_lo):.6f}, {float(B9_lo):.6f}]")

# Runner 2 must cover the left gap [I9_lo, B9_lo] with B_{2,1}
# B_{2,1} right end = 23/(11*a_2) ≥ B9_lo = 261/275
# → a_2 ≤ 23/11 * (275/261) = 23*275/(11*261) = 6325/2871
R_I9 = Fraction(11*1 + 12, 1) / (11 * 1) * (B9_lo / 1)   # = 23/(11) * 1/a_2 ≥ B9_lo
# Correct formula: 23/(11*a_2) ≥ B9_lo → a_2 ≤ 23/(11*B9_lo)
R_I9 = Fraction(23, 1) / (11 * B9_lo)
print(f"\n  R_I9 = a_2 ≤ {R_I9} = {float(R_I9):.6f}")
print(f"  (maximum a_2 for B_{{2,1}} right end to reach left gap boundary)")

gap = L_primary - R_I9
print(f"\n  GAP = L_primary - R_I9 = {L_primary} - {R_I9} = {gap}")
print(f"      = {float(gap):.8f} > 0  ✓  PROVED: GF(++------) > 0")
print(f"\n  (gap = {gap} matches paper's 5/261 = {Fraction(5, 261)})")

# ────────────────────────────────────────────────────────────────────────────
# Part 2: Structure of incompatibility across sign classes
# ────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("Part 2: Sign-class analysis of pair (2,9) incompatibility")
print("=" * 70)
print("""
Complementary Pairs structure for runner 2:
  sigma_2 = +1: runner 2 upper-blocks t_5 (I_4). Primary: a_2 ≥ L_primary = 20/9.
  sigma_2 = -1: runner 2 lower-blocks t_6 (I_5). Primary: a_2 ≤ R_primary < 2.

For sigma_2=+1 classes (128 of 256):
  L_primary = 20/9 is SIGN-CLASS-INDEPENDENT — it depends only on the geometry
  of I_4 and B_{2,0}, which is fixed regardless of other runners' signs.

  R_I9 = 575/261 is CONDITIONAL on cascade giving a_9 = 25/3. This cascade is:
    * PROVED for ++------ (paper §10.16, Case C analysis).
    * CONJECTURED for all 128 sigma_2=+1 classes (requires per-class cascade).

  IF the cascade gives a_9 = 25/3 for all sigma_2=+1 classes → gap = 5/261 > 0
  for ALL 128 sigma_2=+1 sign classes.

For sigma_2=-1 classes (128 of 256):
  Runner 9 takes the primary obligation (I_4 or I_5 depending on sigma_9).
  Symmetric analysis gives an analogous gap (cascade analysis pending).
""")

# Show the L_primary is sign-class-independent
print(f"  L_primary = a_closes_left(5, 0) = {a_closes_left(5, 0)} (independent of sign class)")
print(f"  R_I9      = 23 / (11 * {B9_lo}) = {R_I9}")
print(f"  Gap       = {gap} = {float(gap):.8f} > 0")

# ────────────────────────────────────────────────────────────────────────────
# Part 3: Enumerate all 256 sign classes showing structural type
# ────────────────────────────────────────────────────────────────────────────

print("\n" + "=" * 70)
print("Part 3: All 256 sign classes — Runner 2 / Runner 9 analysis")
print("=" * 70)
print(f"{'Sign (s2..s9)':<20} {'Pair(2,9) type':<22} {'L_prim':>10} {'R_I9':>10} {'Gap':>10} {'Status'}")
print("-" * 80)

n_sigma2_pos = 0  # sigma_2 = +1 classes
n_sigma9_neg = 0  # sigma_9 = -1 (runner 9 active for sigma_2=-1 case)

inv11 = {j: pow(j, -1, 11) for j in range(2, 10)}
# m_j^+ (upper-blocking witness): 10*inv11[j] mod 11
m_upper = {j: (10 * inv11[j]) % 11 for j in range(2, 10)}
# m_j^- (lower-blocking witness): inv11[j]
m_lower = {j: inv11[j] for j in range(2, 10)}

for bits in range(256):
    sigma = {}
    for i, j in enumerate(range(2, 10)):
        sigma[j] = 1 if (bits >> i) & 1 else -1

    sign_str = ''.join('+' if sigma[j] == 1 else '-' for j in range(2, 10))

    if sigma[2] == 1:
        # Runner 2 active: primary obligation I_4 (upper-blocks t_5)
        pair_type = "r2-active (I_4)"
        L = a_closes_left(5, 0)   # = 20/9
        R = R_I9                   # = 575/261, conditional on cascade
        g = L - R
        status = f"gap={float(g):.5f} [COND]" if sign_str != "++------" else f"gap={float(g):.5f} [PROVED]"
        n_sigma2_pos += 1
    else:
        # Runner 2 with sigma_2=-1 → runner 9 analysis (cascade-dependent)
        if sigma[9] == 1:
            pair_type = "r9-active (I_5, upper)"
        else:
            pair_type = "r9-active (I_4, lower)"
        # Runner 9 primary: closes I_4 (t_5) from below when sigma_9=-1
        # or closes I_5 (t_6) from above when sigma_9=+1.
        # Full analysis requires per-class cascade. Placeholder:
        L = Fraction(0)  # unknown without cascade
        R = Fraction(0)  # unknown without cascade
        g = Fraction(0)
        status = "pending (cascade needed)"
        n_sigma9_neg += 1

    print(f"{sign_str:<20} {pair_type:<22} {str(L):>10} {str(R):>10} {str(g):>10}  {status}")

print("=" * 80)
print(f"\nSummary:")
print(f"  sigma_2=+1 classes (runner 2 active): {n_sigma2_pos}/256")
print(f"  → gap = {gap} = {float(gap):.6f} > 0  [PROVED: ++------, CONJECTURED: all 128]")
print(f"  sigma_2=-1 classes (runner 9 active): {n_sigma9_neg}/256")
print(f"  → gap analysis requires per-class cascade [OPEN]")
print(f"\nKey verified result: Runner 2 Incompatibility for ++------")
print(f"  L_primary = {L_primary} ≈ {float(L_primary):.4f}")
print(f"  R_I9      = {R_I9} ≈ {float(R_I9):.4f}")
print(f"  Gap       = {gap} = {float(gap):.8f} > 0")
