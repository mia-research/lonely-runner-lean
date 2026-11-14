# The n = 8 framework, compiled from the record (v1, 2026-10-05, DRAFT)

Compiled at the owner's request from the owner's account of the framework (message of 2026-10-05) and the record: `PAPER_v9_1.md` (cited as P§), `GATE_LEMMAS_v1.md` (GL), `MECHANISM_MAP_v5.md` (MM), `GRAND_RETURN_v1.md`, `ISOLATION_COUNT_v1.md`, `EXACT_PHI_N_AP_v1.md`, the Lean tree. Further owner additions go in as v2, v3.

Grades: [P] proved by hand in the cited source. [L] a Lean theorem exists at the named path (axioms not rechecked in this compilation). [OBS] observed, not derived. [OWED] not done. Exact arithmetic throughout; no floats appear in any statement below. Every runner has a positive speed; readings are differences from a subject of speed s > 0.

---

## 0. Ground rules (owner, 2026-10-05)

1. No runner is made stationary. Isolation of runner k is a statement about the differences v_j − v_k.
2. No approximation of an isolation. The isolation is located by the boundary set method (P§2.1) or the cascade (P§7).
3. Exact only; no floating point.
4. Orders 3 to 7 are not used. Where needed they are re-proved in this framework.
5. No clock, density or coverage unless it arises natively. (None is used below. Two counting steps are tagged where they occur.)
6. The cycle is one full rotation of the slowest speed.

Constraints on an arrangement: speeds are ordered, positive and pairwise distinct. Runner 2 cannot pass runner 3 without becoming runner 3; no speed is 0; no two speeds are equal. Ordering is a relabelling, so every arrangement is an affine rescaling of one ordered shape with six free values [L] `Spec/ArrangementShapeN.lean` (`reduction_iff`).

## 1. Isolation, and why it is rigid

Let ‖x‖ be the distance from x to the nearest integer. The subject is **lonely at t** when ‖d·t‖ ≥ 1/8 for every disparity d (closed condition) [P, P§2].

- **Theorem 1** [P§2]: a runner is lonely iff both gaps flanking it are ≥ 1/8.
- **Theorem 2** [P§2]: all eight are lonely at once iff every gap is exactly 1/8 (the regular octagon). Proof: the gaps sum to 1, the slacks g_j − 1/8 are non-negative and sum to 0.
- **Corollary 3** [P§2]: the number of simultaneously lonely runners is never exactly 7. Isolation cannot be taken from one runner while the others keep theirs.

Theorem 2 and Corollary 3: zero slack; loss of simultaneous isolation is all at once.

**Boundary set method** [P§2.1]. The obstruction of disparity d is the union of open zones ((N − 1/8)/d, (N + 1/8)/d). Endpoints are clear. A status changes only at zone endpoints; between consecutive endpoints the status is constant, and a cell is decided by an interior point. Open cells and boundary points are evaluated separately; touching zones are never merged.

## 2. Global isolation at the AP

**Theorem 4 (the φ(n) law)** [P§3; Palelei 2026a Thm 3.1; exact re-run `EXACT_PHI_N_AP_v1.md`, n = 3..12]. For speeds v₀, v₀ + d, …, v₀ + 7d, all eight are lonely exactly at

    t = a/(8d),   gcd(a, 8) = 1,

and at no other instant. In each period of 1/d there are φ(8) = 4 such instants, at t·d = 1/8, 3/8, 5/8, 7/8.

- **Scale invariance**: d enters only as the factor 1/d on t. The AP (10⁻⁶ … 8·10⁻⁶), (1 … 8), (π … 8π), (1 m … 8 m) have the same instants in u = d·t.
- **Four before the grand return** [P]: the relative positions are {i·u mod 1}; at u = a/8 with a a unit of ℤ/8 they are the eight vertices. There are four units (1, 3, 5, 7), and the instants u = 2/8, 4/8, 6/8 and the grand return u = 1 are not global isolations.
- **Grand return** (`GRAND_RETURN_v1.md` §1) [VERIFIED exact]: u ∈ ℤ, all runners at the start together, maximum crowding, no runner lonely. Isolation (four instants) and grand return are the two extremes of one cycle. For integer speeds with gcd 1 a grand return exists, so the cycle repeats with nothing new.
- **Lonely set at the AP** [P, exact]: on (0, 2] it is exactly 1/8, 3/8, …, 15/8, eight points, measure zero. The method therefore has no neighbourhood to act on (P§2.2).
- **Individual form** [P, one line, `EXACT_PHI_N_AP_v1.md` §2]: for any integer disparity set with 8 ∤ d for every d, and any odd r, ‖d·r/8‖ = |dr mod 8|/8 ≥ 1/8. A subject with no disparity divisible by 8 is lonely at all four instants r/8. This is not special to the AP; what is special to the AP is that nothing else is lonely.
- **Isolation events per period at the AP** [VERIFIED exact, `ISOLATION_COUNT_v1.md` §1]: runners 1..8 have 4, 8, 8, 6, 6, 8, 8, 4 events; the extremal runners have φ(8) = 4.

## 3. Grid (residue) global isolation, and D_max

**Theorem 5** [P§3]. Write speeds v_k = v₀ + k d + e_k. At t = a/(8d), gcd(a, 8) = 1, runner k sits at

    v₀a/(8d) + ka/8 + (e_k a/d)·(1/8).

The first term is a common rotation. The second is the AP vertex ka/8. The third is a displacement of exactly e_k·a/d of an eighth.

**Theorem 6** [P§3; L: `ConstructionN/Reference.lean` `survives_of`, `ConstructionN/Integrality.lean` `int_of_pairwise_sep`, `not_dvd_of_sep`]. The global instant survives the deviation iff every e_k·a/d is an integer and k ↦ ka + e_k a/d is a bijection of ℤ/8.

Consequences, in the owner's terms:

- **Grid arrangement**: integer speeds, in units of d, whose residues mod 8 are a complete system (each of 0..7 once). Every such arrangement is globally isolated at t = a/(8d) for the same four a. The AP is one grid; others exist (`ISOLATION_COUNT_v1.md` §3: (1,…,7,x) is complete mod 8 iff x ≡ 0).
- **D_max (the owner's grid direction)**: replacing a speed v by v + 8m·d leaves its residue, so its vertex at every global instant, unchanged. The family is unbounded in m, so a speed may be arbitrarily large and still isolate globally with the others. In the cascade this is the shift of a fast reading by +8m (MM, E326): the state sequence is kept when the reading and its image are both clear at every visited state (21,781 of 21,781 exact tests) [TESTED]; it is not unconditional, since the rank-labelled path and the closer change under +8m.
- **Naming clash to resolve**: P§4 Theorem 8 and rule R1 use d_max for the largest disparity of a subject. The owner's D_max is the grid direction above. v2 of this document should use one name for each.

**Proposition 4.1** (Palelei 2026a, restated P§3.1): the global instant has zero stability radius. A real or non-integral deviation destroys it; a rational one destroys it when two runners are sent to one vertex.

## 4. D_min: the deformation

The owner's reading: from an AP or grid speed to the next AP or grid speed, an individual isolation is displaced, not destroyed. Statements in the record that carry this:

- **Normalisation** [P§4]. For a subject, d_min is its smallest disparity; u = d_min·t; each disparity d has ratio s = d/d_min ≥ 1 and reading s·u.
- **Theorem 7** [P§4]: a lonely instant satisfies t ≥ 1/(8·d_min), i.e. u ≥ 1/8. This is the bound, where the cascade starts.
- **Theorem 8** [P§4]: if d_max(subject) ≤ 7·d_min the subject is lonely at t = 1/(8 d_min).
- **Cascade coordinate** (MM; GL): R = 8·d_min·t, readings ρ_y = disparity_y/d_min, 1 = ρ₁ < ρ₂ < … < ρ₇. Zone Z(y, j) = ((8j − 1)/ρ_y, (8j + 1)/ρ_y); a point R is **clear** for reading y iff R·ρ_y mod 8 ∈ [1, 7]. The landing R* is the least point ≥ 1 clear for all seven.
- **Pair law, grid through a reading** (MM line 187) [L: `Spec/GridPairLawN.lean` `grid_class_clear`]: at a grid through the arrangement's own reading, for one class and under small-deviation conditions, every runner is clear except those in the subject's slot.
- **Junction split** (MM, E208) [algebra]: J = s_b(8k+1) − s_a(8l−1) splits exactly into a grid part (a whole number) and a deviation part.

**Not established here:** that a deformation from one grid to the next always displaces the isolation to a landing, for every arrangement. That statement is the owed one (§7).

## 5. Individual isolation: localisation and the certificate

The conjecture asks for an isolation of each runner at some positive instant, not the first.

- **Opening** of the flank e at lap j: t = (j + 1/8)/e. The runner e stands at exactly 1/8, clear.
- **Theorem 9 (Localisation)** [P§5]: the subject is lonely at some positive instant iff some flank has a lonely opening. A lonely t yields a lonely opening T = max_e (⌊e t⌋ + 1/8)/e ≤ t.
- **Theorem 10 (certificate)** [P§6]: for integer disparities, opening j of flank e is lonely iff d·(8j + 1) mod 8e ∈ [e, 7e] for every d. Periodic in j with period e, so e checks decide it. Every opening index 8j + 1 is a unit of ℤ/8.
- **Certificate** = a pair (e, j) with a lonely opening. In the cascade: R = 8·(j + 1/8)·d_min/e.

## 6. The cascade, and why it is the oracle

**Definition** [P§7]. A runner d is in the way at t when ‖d·t‖ < 1/8. The **move** sends t to the largest next opening among those in the way, and fixes t if none is. The **cascade** starts at the bound 1/(8·d_min).

Recursion on the scale: D₀ = d_min, D_{j+1} = D_j·min{ s/(8N+1) : |s − 8N| < 1 }, instant 1/(8·D_final), where s = d/D_j.

**Theorem 11 (Construction)** [P§7.2]: a fixed step T is lonely, is the first lonely instant, ends a run of zones each containing the end of the one before, and carries a runner at exactly 1/8.

**Theorem 12 (Cascade localisation)** [P§7.2]: every lonely s satisfies s ≥ bound, every step ≤ s, and the cascade reaches a fixed point.

**Theorem 13** [P§7.2]: for every injective arrangement and subject, with no other hypothesis, these are equivalent: lonely at some positive instant; the cascade fixes; the cascade's instants are bounded; some flank has a lonely opening; each runner is in the way finitely often. Lean: `Spec/Doors.lean` and `Spec/DoorsN.lean`, `doors_agree`.

Theorem 13 makes the cascade equivalent to loneliness at the arrangement; that it always fixes is the conjecture [OWED].

**Worked example** [P§7.1]: speeds 1,2,3,4,5,6,8,9, subject at speed 1, d = {1,2,3,4,5,7,8}. Step 0 t = 1/8 (runner 8 in the way), step 1 t = 9/64 (runner 7), step 2 t = 9/56 fixed; certificate (e, j) = (7, 1).

**Structural rules** (each proved at general n, P§10; a rule fires on a condition, and its instant is lonely):

| rule | condition (disparity set) | instant |
|---|---|---|
| R1 | d_max ≤ 7·d_min | 1/(8·d_min) |
| R2 | all in one band [(8L+1)e/(8j+1), (8L+7)e/(8j+1)] | opening j of e |
| R3 | gcd(e, 8) = 1, no disparity divisible by 8 | a = e·(e⁻¹ mod 8) |
| R4 | 8 \| e, e largest, no other divisible by 8, fewer than φ(8) = 4 coprime to 8 | a = k·e + 1, k a unit **[PROVISIONAL: counting tool]** (pigeonhole over the units) |
| R5 | all but at most one disparity divisible by 8 | reduces to the quotient set, same threshold |
| R6 | for some q ≤ 8, no disparity divisible by q | t = 1/q |
| R7 | one disparity off the lattice of the rest, rest ≤ 3 | inherited |

R6 fails exactly when the disparities cover every modulus in [2, 8] by divisibility. At n = 8 the difficulty is 2³: φ(8)/8 = 1/2 (P§10.7).

## 7. Gate lemmas in cascade coordinates (GL)

Reading 1's zones are (7, 9), (15, 17), …; R ∈ [1, 7] is never blocked by reading 1. Carving: K₁ = [1, 7], K_k = K_{k−1} minus the zones of reading k; K₇ is the set of lonely windows in [1, 7].

- **L1(a)–(c)** [P]: R* > 7 ⇔ K₇ = ∅; no landing in (7, 9); the first state above 7 lies in (7, 9). **L1(d)** [OBS]: the move from it lands exactly at 9 (7,946 of 7,947 tree regions; the other lands at exactly 7).
- **L2** [P]: a zone of reading k holds at most one window of K_{k−1}.
- **L3** [P] **[PROVISIONAL: covering]** (window-against-zone statement; supports the description of gate crossers, not an existence claim): if K₇ = ∅, each window of K₆ lies in exactly one zone of reading 7, in distinct zones, each a move of the path.
- **L4** [P]: the opener's own reading is the closer only if it is reading 7.
- **L5** [P]: each move multiplies the state by at most 9/7; consecutive setters differ; if the first k+1 setters are distinct, ρ_{7−k} > 7·(7/9)^k.
- **L6** [L: `ZoneLinkN`]: after a move to the exit of (s, j), a slower reading blocks only at lap ≤ j, a faster one at lap ≥ j+1.
- **L7** [P]: the crossing arrangements form an open set whose boundary consists of touches (exit of one zone = entry of another).
- **Window for a mirror** (MM E342) [exact identity]: p_y(R + 8) = p_y(R) + 8·frac(ρ_y).
- **Observed bound** [OBS, tree to ρ₇ ≤ 25, exact members, LP not certified]: R* < 12 for every arrangement; sup 26433/2209 at a closure vertex.

## 8. What the record says is and is not done

Graded [P] or [L] in the sources: Theorems 1–13 (sections 1 to 6), L1(a)–(c), L2–L7. Sections 3 and 4 also carry [TESTED], [algebra] and [OWED] items, tagged where they occur; this is a PARTIAL account.

Owed (each is a statement the record marks open):
1. **That the displacement is forced**: for every arrangement an unblocked R exists. In cascade form, K₇ ≠ ∅ or the second carving is non-empty. The statement is a complement statement **[PROVISIONAL: covering]** (the zones of readings 2..7 do not cover every window); it is the target, not a result.
2. L1(d).
3. Closure of the crossing family for all ρ₇, and the scale reduction of a cluster of fast readings to a smaller arrangement (`N8_PROOF_ARCHITECTURE_v1.md` §3–4).
4. Exact certificates for the pruned branches of the tree.
5. Why R* < 12.

Not used because the record shows they do not carry the argument: window floors (E359 refutes L ≥ 2/(7ρ₆)), reach percentages, analytic or measure routes (the AP clear set has measure zero).

---

## Points for the owner to confirm (placed from the casual account, not asserted)

- **"Cycle = one full rotation of the slowest speed"** versus `GRAND_RETURN_v1.md` §5: for speeds (3, 5) the grand return is at t = 1 and the isolation period is 1/2. For the AP with relative speeds d, 2d, …, 7d the two coincide at t = 1/d. A definition of the cycle for a general arrangement is needed before the "four events before the grand return" statement can be made outside grids.
- **"Any arrangement refers to an AP and/or grid"**: Theorems 5 and 6 give the grid of the AP vertices and the displacement of each runner from them. Theorem 6 is an iff for global isolation at the AP's instants only. A chosen reference grid for an arbitrary arrangement (which grid, which divisor) is the cascade's conversion; its selection rule is not stated as a theorem in the record (MM, E295 withdrawal, E297 open).
- **Grid to grid**: Theorem 6 gives the surviving grids. The step "D_min also works between two grid speeds" has the pair law as its Lean content (§4); the general statement is not in the record.
