"""Covering conditions for spread in (9, 24].  Exact (Fraction) throughout.

Every condition is a function  cond(rd) -> R or None.  If it returns R, the
claim is: the set rd (sorted, rd[0] == 1) is lonely at R and R <= 15.  The
check (check.py) re-verifies that claim with core.lonely_at on every set on
which a condition fires (soundness), independently of the condition's logic.

Tiers (see derivation.md):
  D = derived: the firing test is a closed list of ratio inequalities (or a
      single evaluation at an explicitly defined point) whose truth implies
      loneliness by L2/L3 or elementary algebra, proved in derivation.md.
  X = exact-lap: the firing test is existential over a finite, explicitly
      bounded range of lap indices (a finite disjunction of inequality
      systems).  Sound by L2 + L3; it locates a lap choice but does not
      explain why one exists.
"""
from fractions import Fraction as F
from core import lonely_at, next_clear_start, largest_gap

ONE = F(1)
SEVEN = F(7)
BIG = F(10**9)


# ---------------------------------------------------------------- helpers
def band_lap(s):
    """If s is blocked at R = 1 (s in (8m-1, 8m+1), m >= 1) return m, else None."""
    k = s.numerator // (8 * s.denominator)
    r = s - 8 * k
    if r > 7:
        return k + 1
    if r < 1:
        return k
    return None


def clear_pieces(f, a, b):
    """Closed clear pieces [max(a,(8k+1)/f), min(b,(8k+7)/f)] of reading f
    inside [a, b] (a >= 0), with lap index k."""
    out = []
    x = f * a
    k = max(0, x.numerator // (8 * x.denominator) - 1)
    while True:
        lo = F(8 * k + 1) / f
        if lo > b:
            break
        hi = F(8 * k + 7) / f
        L = lo if lo > a else a
        H = hi if hi < b else b
        if L <= H:
            out.append((L, H, k))
        k += 1
    return out


def phi(lam):
    """Lemma W: every closed interval of scaled length lam >= 2 contains a
    closed clear piece of scaled length >= min(6, (lam-2)/2)."""
    if lam < 2:
        return None
    v = (lam - 2) / 2
    return v if v < 6 else F(6)


def nested_longest(readings, a, b):
    """Explicit construction: I_0=[a,b]; for readings ascending, I_t = the
    longest clear piece of reading t inside I_{t-1} (ties: leftmost)."""
    I = (a, b)
    for f in sorted(readings):
        ps = clear_pieces(f, I[0], I[1])
        if not ps:
            return None
        best = ps[0]
        for p in ps[1:]:
            if p[1] - p[0] > best[1] - best[0]:
                best = p
        I = (best[0], best[1])
    return I


def lacunary_worst(readings, a, b):
    """Lambda-recurrence (Lemma W): Lambda_1 = f_1 (b-a),
    Lambda_{t+1} = (f_{t+1}/f_t) phi(Lambda_t); holds iff every Lambda_t >= 2.
    Pure inequality test; implies nested_longest succeeds on [a,b]."""
    ell = b - a
    if ell < 0:
        return False
    fs = sorted(readings)
    for t, f in enumerate(fs):
        lam = f * ell
        if lam < 2:
            return False
        if t == len(fs) - 1:
            return True
        ell = phi(lam) / f
    return True


def stairs(rd, max_groups, max_step, first_laps=(0,)):
    """Stair blocks.  Consecutive groups G_0 < G_1 < ... (at most max_groups)
    covering rd[0..p], laps k_0 in first_laps, k_{u+1}-k_u in 1..max_step;
      J = [max_u (8k_u+1)/min G_u, min_u (8k_u+7)/max G_u].
    Yields (J_left, J_right, p, laps, cuts) for every nonempty J."""
    n = len(rd)

    def rec(start, lap_next_min, lo, hi, g, laps, cuts):
        if start > 0:
            yield (lo, hi, start - 1, laps, cuts)
        if g >= max_groups or start >= n:
            return
        if start == 0:
            cand = first_laps
        else:
            cand = range(lap_next_min, lap_next_min + max_step)
        for lap in cand:
            for end in range(start, n):
                nlo = max(lo, F(8 * lap + 1) / rd[start])
                nhi = min(hi, F(8 * lap + 7) / rd[end])
                if nlo > nhi:
                    break  # enlarging the group only shrinks the block
                yield from rec(end + 1, lap + 1, nlo, nhi, g + 1,
                               laps + (lap,), cuts + (end,))

    yield from rec(0, 0, F(0), BIG, 0, (), ())


def stair_condition(rd, max_groups, max_step):
    for lo, hi, p, laps, cuts in stairs(rd, max_groups, max_step):
        rest = rd[p + 1:]
        if not rest:
            return lo
        if lacunary_worst(rest, lo, hi):
            I = nested_longest(rest, lo, hi)
            assert I is not None, "Lemma W violated"  # mechanical check of W
            return I[0]
    return None


# ---------------------------------------------------------------- tier D
def C0_R1(rd):
    """C0: no reading in a band (7,9) U (15,17) U (23,25): lonely at R = 1."""
    return ONE if all(band_lap(s) is None for s in rd) else None


def escape_point(rd):
    """R1 = max over band readings s (s in (8m-1,8m+1)) of (8m+1)/s; 1 if none."""
    R1 = ONE
    for s in rd:
        m = band_lap(s)
        if m is not None:
            c = F(8 * m + 1) / s
            if c > R1:
                R1 = c
    return R1


def C1_escape(rd):
    """C1 (one escape move): lonely at R1 = escape_point(rd).  Lemma E gives
    the pairwise (conflict-pair) form of the firing test."""
    R1 = escape_point(rd)
    return R1 if lonely_at(rd, R1) else None


def C1p_no_conflict(rd):
    """C1' (Lemma E, pairwise form): with c_s, e_s the escape start / end of
    the first clear interval of s at or after 1, fires iff max c <= min e.
    Implies C1."""
    cs, es = [], []
    for s in rd:
        m = band_lap(s)
        if m is None:
            k = s.numerator // (8 * s.denominator)
            cs.append(ONE)
            es.append(F(8 * k + 7) / s)
        else:
            cs.append(F(8 * m + 1) / s)
            es.append(F(8 * m + 7) / s)
    R1 = max(cs)
    return R1 if R1 <= min(es) else None


def admissible_splits(rd):
    return [i for i in range(6) if rd[i] <= 7]


def C2_lacunary(rd):
    """C2: slow block [1, 7/s_i] (L2) + Lambda-recurrence over the fast
    readings; largest-gap split first, then the other admissible splits."""
    i0, _ = largest_gap(rd)
    order = [i0] + [i for i in admissible_splits(rd) if i != i0]
    for i in order:
        if rd[i] > 7:
            continue
        a, b = ONE, SEVEN / rd[i]
        fast = rd[i + 1:]
        if lacunary_worst(fast, a, b):
            I = nested_longest(fast, a, b)
            assert I is not None, "Lemma W violated"
            return I[0]
    return None


def C3_stair3(rd):
    """C3: stair block with at most 3 groups, laps 0,1,2 (consecutive), plus
    Lambda-recurrence over the readings above the stair."""
    return stair_condition(rd, 3, 1)


def C4_single_fast(rd):
    """C4 (Lemma S): largest gap on top (one fast reading f = s6), s5 <= 7.
    f is clear somewhere on [1, 7/s5] iff NOT (f in (8m-1,8m+1) and
    7f/s5 < 8m+1).  R = 1 if f clear at 1, else (8m+1)/f."""
    i, _ = largest_gap(rd)
    if i != 5 or rd[5] > 7:
        return None
    f = rd[6]
    m = band_lap(f)
    if m is None:
        return ONE
    if SEVEN * f / rd[5] >= 8 * m + 1:
        return F(8 * m + 1) / f
    return None


def C5_grid_nudge(rd):
    """C5 (L6): whole-number readings (units of s0), s6 the only one = 0 mod 8,
    the others with residues in 1..6 mod 8: lonely at R = 1 + 1/s6."""
    if any(s.denominator != 1 for s in rd):
        return None
    top = rd[-1].numerator
    if top % 8 != 0:
        return None
    for s in rd[:-1]:
        if not (1 <= s.numerator % 8 <= 6):
            return None
    return ONE + F(1, top)


# ---------------------------------------------------------------- tier X
def X0_stair5(rd):
    """X0: stair with at most 5 groups, lap steps 1..3, + Lambda on the rest."""
    return stair_condition(rd, 5, 3)


def block_exact(rd, i):
    """Exact lap criterion for the slow block of split i (L2 + L3): exists laps
    m_f with max(1, max_f (8m_f+1)/f) <= min(7/s_i, min_f (8m_f+7)/f).
    Branching nested construction; returns the least such R or None."""
    Is = [(ONE, SEVEN / rd[i])]
    for f in rd[i + 1:]:
        new = []
        for I in Is:
            new += [(p[0], p[1]) for p in clear_pieces(f, I[0], I[1])]
        Is = new
        if not Is:
            return None
    return min(I[0] for I in Is)


def X1_block_largest_gap(rd):
    i, _ = largest_gap(rd)
    if rd[i] > 7:
        return None
    return block_exact(rd, i)


def X2_greedy3(rd):
    """Forced delay: the escape iteration R <- max_s next_clear_start(s, R)
    from R = 1 reaches a lonely point within 3 moves."""
    R = ONE
    for _ in range(4):
        nxt = max(next_clear_start(s, R) for s in rd)
        if nxt == R:
            return R if R <= 15 else None
        R = nxt
    return None


def X3_block_any_split(rd):
    """Exact block criterion over every admissible split (split 0 has block
    [1, 7], so this is: lonely somewhere in [1, 7])."""
    for i in admissible_splits(rd):
        R = block_exact(rd, i)
        if R is not None:
            return R
    return None


DERIVED = [("C0_R1", C0_R1), ("C1_escape", C1_escape),
           ("C1p_no_conflict", C1p_no_conflict),
           ("C2_lacunary", C2_lacunary), ("C3_stair3", C3_stair3),
           ("C4_single_fast", C4_single_fast), ("C5_grid_nudge", C5_grid_nudge)]
EXACT = [("X0_stair5", X0_stair5), ("X1_block_largest_gap", X1_block_largest_gap),
         ("X2_greedy3", X2_greedy3), ("X3_block_any_split", X3_block_any_split)]


# ---------------------------------------------------------------- negative controls
def NEG_block_ignore_fast(rd):
    """WRONG: lonely at the right end 7/s_top of the largest-gap slow block,
    ignoring the fast readings."""
    i, _ = largest_gap(rd)
    if rd[i] > 7:
        return None
    return SEVEN / rd[i]


def NEG_escape_no_check(rd):
    """WRONG: claims lonely at R1 = escape_point without any test."""
    return escape_point(rd)


def NEG_phi_generous(rd):
    """WRONG version of Lemma W: phi(lam) = lam - 1 with threshold lam >= 1
    (pretends the blocked gap never splits the interval); names the LEFT end
    of the construction it would license (the block's left end when the
    first reading is clear there)."""
    i, _ = largest_gap(rd)
    if rd[i] > 7:
        return None
    a, b = ONE, SEVEN / rd[i]
    ell = b - a
    for f in rd[i + 1:]:
        lam = f * ell
        if lam < 1:
            return None
        ell = (lam - 1) / f
    return a


NEGATIVE = [("NEG_block_ignore_fast", NEG_block_ignore_fast),
            ("NEG_escape_no_check", NEG_escape_no_check),
            ("NEG_phi_generous", NEG_phi_generous)]
