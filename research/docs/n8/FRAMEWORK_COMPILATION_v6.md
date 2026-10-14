# The n = 8 framework, compiled from the record (v6, 2026-10-05, DRAFT; v1 to v5 kept)

Compiled at the owner's request from the owner's account of the framework (message of 2026-10-05) and the record: `PAPER_v9_1.md` (cited as P§), `GATE_LEMMAS_v1.md` (GL), `MECHANISM_MAP_v5.md` (MM), `GRAND_RETURN_v1.md`, `ISOLATION_COUNT_v1.md`, `EXACT_PHI_N_AP_v1.md`, the Lean tree. Further owner additions go in as v2, v3.

Grades: [P] proved by hand in the cited source. [L] a Lean theorem exists at the named path (axioms not rechecked in this compilation). [OBS] observed, not derived. [OWED] not done. Exact arithmetic throughout; no floats appear in any statement below. Every runner has a positive speed; readings are differences from a subject of speed s > 0.

---

## 0. Ground rules (owner, 2026-10-05)

1. No runner is made stationary. Isolation of runner k is a statement about the differences v_j − v_k.
2. No approximation of an isolation. The isolation is located by the boundary set method (P§2.1) or the cascade (P§7).
3. Exact only; no floating point.
4. Orders 3 to 7 are not used. Where needed they are re-proved in this framework.
5. No clock, density or coverage unless it arises natively. (None is used below. Two counting steps are tagged where they occur.)
6. The cycle is one full rotation of the slowest speed. This is **not** the period of the pattern repeating (§2, two cycles).

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
- **Two cycles, kept apart** (owner, 2026-10-05):
  - *Slowest-runner cycle*: one full rotation of the slowest speed, t = 1/v_min. The unit in which the cascade's bound and openings are measured.
  - *Pattern cycle (grand return)*: the least t > 0 at which every runner is back at the start together (`GRAND_RETURN_v1.md` §1) [VERIFIED exact]. All integer patterns have one; after it the pattern repeats with no new outcome. For integer speeds with gcd g it is t = 1/g.
  - At the AP (1,…,8) both are t = 1. They separate elsewhere: speeds (3, 5) have slowest-runner cycle 1/3, grand return 1, isolation period 1/2 (`GRAND_RETURN_v1.md` §5). Isolation depends on disparities only, so the pattern cycle relevant to a subject is that of its disparities.
  - At the grand return no runner is lonely (maximum crowding); the four AP isolation instants lie inside the one cycle, between two grand returns.
- **Lonely set at the AP** [P, exact]: on (0, 2] it is exactly 1/8, 3/8, …, 15/8, eight points, measure zero. The method therefore has no neighbourhood to act on (P§2.2).
- **Individual form** [P, one line, `EXACT_PHI_N_AP_v1.md` §2]: for any integer disparity set with 8 ∤ d for every d, and any odd r, ‖d·r/8‖ = |dr mod 8|/8 ≥ 1/8. A subject with no disparity divisible by 8 is lonely at all four instants r/8. This is not special to the AP; what is special to the AP is that nothing else is lonely.
- **Two inverted patterns** [P, P§14.4; Palelei 2026b §14D–E, theorems cited not rechecked here]: the clear set is symmetric under x ↦ 8 − x (time reversal), obstructed only at residues 0 and 1 mod 8. Candidate endpoints form two patterns, s·x ≡ +1 and s·x ≡ −1 (mod 8), each the inversion of the other. The AP's four events are where the two coincide (u·u ≡ 1 and u·(8−u) ≡ −1; four units mod 8). Off the AP the coincidence does not transfer; each pattern still supplies a witness, generally at two different points.
- **Isolation events per period at the AP** [VERIFIED exact, `ISOLATION_COUNT_v1.md` §1]: runners 1..8 have 4, 8, 8, 6, 6, 8, 8, 4 events; the extremal runners have φ(8) = 4.

## 3. Grid (residue) global isolation, and D_max

**Theorem 5** [P§3]. Write speeds v_k = v₀ + k d + e_k. At t = a/(8d), gcd(a, 8) = 1, runner k sits at

    v₀a/(8d) + ka/8 + (e_k a/d)·(1/8).

The first term is a common rotation. The second is the AP vertex ka/8. The third is a displacement of exactly e_k·a/d of an eighth.

**Theorem 6** [P§3; L: `ConstructionN/Reference.lean` `survives_of`, `ConstructionN/Integrality.lean` `int_of_pairwise_sep`, `not_dvd_of_sep`]. The global instant survives the deviation iff every e_k·a/d is an integer and k ↦ ka + e_k a/d is a bijection of ℤ/8.

Consequences, in the owner's terms:

- **Grid arrangement**: integer speeds, in units of d, whose residues mod 8 are a complete system (each of 0..7 once). Every such arrangement is globally isolated at t = a/(8d) for the same four a. The AP is one grid; mixed ones exist, e.g. (1,…,7,16): an AP part (1..7) and one runner shifted by 8d. Theorem 6 covers it directly (e₈ = 8d, residue 0 kept), so global isolation at a/(8d) holds with no reference-grid selection needed [P by Thm 6; also exact cascade, below]. Others exist (`ISOLATION_COUNT_v1.md` §3: (1,…,7,x) is complete mod 8 iff x ≡ 0).
- **D_max (the owner's grid direction)**: replacing a speed v by v + 8m·d leaves its residue, so its vertex at every global instant, unchanged. The family is unbounded in m, so a speed may be arbitrarily large and still isolate globally with the others. In the cascade this is the shift of a fast reading by +8m (MM, E326): the state sequence is kept when the reading and its image are both clear at every visited state (21,781 of 21,781 exact tests) [TESTED]; it is not unconditional, since the rank-labelled path and the closer change under +8m.
- **Naming clash to resolve**: P§4 Theorem 8 and rule R1 use d_max for the largest disparity of a subject. The owner's D_max is the grid direction above. v2 of this document should use one name for each.

**Worked deformation, (1,…,7,15)** [exact Fractions, `experiments/n8/compile_ex_1to7_15_v1.py`]. 15 is the grid speed 16 displaced by e = −d, one grid unit, a whole eighth for every a. Residue 15 ≡ 7 collides with runner 7, so the bijection in Theorem 6 fails and the global instants are lost. Cascade, first lonely instant per runner: runners 1–6 at 1/8 with no move (unchanged); runner 7 at 9/64 after one move (displaced from 1/8, the pair-law collision partner); runner 8 (speed 15, d_min 8) at 1/64 with no move. For (1,…,7,16) every runner is lonely at 1/8 (runner 8 also at 1/72 as its own first). Only the colliding runner's isolation moved; the others kept theirs (consistent with rule 3 of RULES_n8_v4).

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
- **"Any arrangement refers to an AP and/or grid"**: for arrangements that are AP plus multiples of 8d (e.g. (1,…,7,16)) Theorem 6 is the statement. For an arbitrary arrangement the choice of reference grid (which grid, which divisor) is the cascade's conversion; its selection rule is not stated as a theorem in the record (MM, E295 withdrawal, E297 open) [OWED].
- **Grid to grid / d_min step**: (1,…,7,15) as a one-unit displacement of (1,…,7,16) is worked above for one case. The general statement (any displacement between two grid speeds relocates the isolation, never removes it) is not in the record beyond the pair law (§4) [OWED].


---
---

# ADDENDUM A. Other proofs, other attempts, and empirical hints (v6)

**Scope.** Read: `PAPER_v9_1.md` §§9–18, `MECHANISM_MAP_v5.md` §§5–9, 11, `CASCADE_FINDINGS_INDEX_v5.md`, `GATE_LEMMAS_v1.md`, `N8_PROOF_ARCHITECTURE_v1.md`, `CASCADE_MECHANISM_v1.md`, docstrings of about 25 `Spec/` modules, titles of all 164. Not read: `MANUSCRIPT_v21`/`_v22`, the older maps, handovers, log before E269, Palelei 2026b, Lean proof bodies. `compile-diff` against these is [OWED]. Grep finds no `sorry` token in `Spec/`; axioms not rechecked.

**Split (owner, 2026-10-05).** Part I holds what adheres to the current rules, including steps that carry the rule 7 tags. Part II holds what does not, kept on purpose: the rules were not in place when these were tried, and the record of what was tried is the reason the rules exist. The split is my classification from the sources and is unconfirmed by the owner; borderline rows are named in each part.

**Marks.** [PROVISIONAL: …] = the rule 7 tag, written in full at the step. LOW = uses orders 3–7 (ground rule 4: not used in the n = 8 proof). R7 = rule 7 shape (covering, cap, move budget, uniform formula, slack). F# = failure class in `MECHANISM_MAP_v5.md` §6.

---

# PART I. Adheres to the current rules

## I-1. Proved, native, bearing directly on "deformation relocates the isolation"

| item | statement (one line) | grade | vs rules |
|---|---|---|---|
| `ProgressionPairN` (E69) | AP readings j·c; deform to d_j with \|d_j − jc\| ≤ c/20. Instant a survives as the interval [a²/(8 d_a), a(8−a)/(8 d_{8−a})]. Instants form two pairs (1,7) and (3,5); one of each pair always holds (`pair_law`): displaced within its pair, never destroyed | [L] | OK |
| `TwoPinnerN` | an isolated instant pinned by neighbours d₊ (on +1/8) and d₋ (on −1/8) survives deformation at itself or at its mirror 1 − t*; scale invariant | [L] | OK |
| `PinchOpenN` | a simple pinch keeps the subject lonely under every small change of speeds, at the leaving runner's own opening, or at the mirror for common-period readings | [L] | OK |
| `DeformationN` | openness (`lonelyAt_of_close`: margin ε survives 2η\|t\| ≤ ε) and closedness (`lonelyAt_of_limit`) of loneliness along a path; the owner's argument as theorems with `hopen` explicit | [L] | OK; `hopen` carried as a hypothesis (multi-pinches, bounded time [OWED]) |
| `APNeighbourhoodN` | AP with every speed deviated by ≤ 1/32 of the gap: every runner lonely at a named instant (interior: 1/(8d), d the nearer neighbour gap; end runner: 1/(8 r₁) if r₇ ≤ 7 r₁, else class-7 instant 49/(8 r₇)) | [L] | OK |
| `GridNeighbourhoodN`, `GridClassN`, `GridPairLawN`, `GridPairN` | every complete grid (residues mod 8 all different): deviations ≤ ρ relocate each runner's isolation between the class-1 instant and its mirror class 7, named from the two circle neighbours A, B with D_A ≡ 1, D_B ≡ 7 (mod 8); any class p with mirror q | [L] | OK; under small-deviation conditions only |
| `GridNudgeN`, `SeparationN` | a captured runner in the subject's slot: the isolation waits for separation at t₁ = t₀ + 1/(8c); one cascade move as a rule on residues and margins | [L] | OK; repeated separations are the cascade itself |
| `ClassDeviationN` (E307) | a class instant a sees a reading only through its deviation scaled by the class; blocked by a lapped fastest reading iff \|a(ρ₇ − 8)\| < 1 | [L] | OK |
| `IntegerGridN`, `IntegerDisplacementN` | grid through D = 1 of an integer arrangement; displacement of the isolation in slot residue and shift (`lonely_of_displacement`) | [L] | OK; D = 1 is the cascade's start only when d_min = 1 (E301) |
| `CascadeGridN`, `CascadeTransportN`, `ZoneLinkN`, `SweepBridgeN` | grid certificates bound the actual cascade; exact transport including failed separation steps; link rule (L6); three move types (sweep down, bridge up, bridge down), `sweep_ratio` ρ_k = (8k+1)/(8k−1) | [L] | OK |
| `MirrorCentreN` | every lonely cell contains the mirror meeting of its opener and closer; at the AP the cell has width zero and the mirror meeting is the global instant | [L] | OK |
| `GrandReturnN` (E100) | whole-number readings: period 1 (`lonely_add_int`), mirror symmetry (`lonely_mirror`), lonely at some instant iff lonely in (0, 1/2] (`exists_lonely_iff_half`) | [L] | OK. The pattern cycle, as distinct from the slowest-runner cycle |
| `LogTimeN` | lonely iff some translate of {log d} lies inside G_n = ∪ [log(M + 1/n), log(M + 1 − 1/n)]; scale invariance is translation invariance; the first tooth has length log(n − 1) = R1 | [L] | OK |
| `Doors`, `DoorsN` | the four doors are equivalent to `LonelyForSubject`, at order 8 and at every n ≥ 2 | [L] | OK |
| `lonelyRunnerAt8_iff_residual`, `existenceAt8_iff_residual` | the conjecture at 8 is equivalent to every `EightResidual` set being lonely at 1/8 (both directions) | [L] | OK; an equivalent form, not a step (MM §5, C1) |
| `RealEightN` | real speeds reduce to whole numbers at order 8 | [L] | OK |
| `lonely_of_off_lattice` (E60), `OffLatticeN`, `OneFreeN`, `OneFreeEightN` | a reading off the lattice of the others closes the configuration | [L] | OK |


## I-2. Rules and reductions proved formally that extend section 6 (rule 7 tags at the step)

| item | statement | grade | vs rules |
|---|---|---|---|
| `DescentN`, `DescentMultiN`, `ShiftedTotientN`, `SelfSimilarN`, `LiftN` | the self-similar end of the trichotomy discharged by descent; several non-multiples: shift budget φ(n) | [L] | [PROVISIONAL: counting tool] at the shift budget φ(n), supporting the descent step |
| `DivisibleFlankN`, `NamedFlankN`, `OverlapFlankN`, `OtherFlankN` | R4 without the largest-flank hypothesis; the lonely point named from the arithmetic; the construction at a flank that need not be the largest | [L] | [PROVISIONAL: counting tool] at the unit count, supporting the named flank |
| `FlankFiniteN` | at most four disparities: the largest disparity hosts a lonely opening at every n ≥ 5 (exhaustive); clearance law k blockers need least order 5, 8, 11, 13 for k = 3..6; rank one holds iff n ≥ f(n−2) | [L] decidable layer; remainder [OWED] | [PROVISIONAL: counting tool] (exhaustive blocker count), supporting the flank-door claim |
| `BandCover*N` (core, trees 2, 3, 4, 17, 18, 19), `BandRouteN` | the band theorem: every real shape with 7m < W ≤ 9m is lonely (`lonely8_of_band`), proved by a tree of root cuts | [L] | **R7 (covering by a tree of cuts)**; [PROVISIONAL: covering] (supports: the 7m < W ≤ 9m case). The route needs `WideStep8` for W > 9m, OWED |
| `TwoBlockN`, `SlowBlockN` | the AP at one scale read on two laps of the grid; the slow group's first block (the d_max regime reduced to the fast group) | [L] | OK |
| `DoubledSlotN`, `DoubledNbhd*N` | two runners in one slot: the doubled-slot family exhibited, every runner lonely at a named instant under deviation | [L] | OK |

Borderline: the band-cover trees are covering admitted under the relaxation, and the route needs `WideStep8` (Part II).

## I-3. Flanks

Rule marks are at the step; unmarked lines are OK or cited only.

- **Flank = a disparity used as the denominator of a candidate** (P§19). Theorem 9 allows *any* flank; the largest-flank form is a narrower strengthening (P§14.7). [P]
- **Flank door**: at 4 or fewer disparities the largest hosts a lonely opening for every n ≥ 5 (`FlankFiniteN`, exhaustive) [PROVISIONAL: counting tool] (supports: the flank-door claim); at more it fails as a rule (clearance law above). [L]
- **Flanks and candidates are one language** (P§14.7; Palelei 2026b §15D Thm 15.15). [OBS: cited, not rechecked]
- **Candidate geometry** (P§14): the covering question is exact over ℤ (14.1) [PROVISIONAL: covering] (supports: decidability of the unblocked-point question over ℤ); candidates (8m+1)/s_k are the spine rescaled by s_k, and a reading s_j = c·s_k blocks them iff 8 | c (14.2) [OK, divisibility]; blocker count ≤ n−3 in the first band (14.3) [PROVISIONAL: counting tool] (supports: the candidate family is not wholly blocked); reflection x ↦ 8 − x obstructed only at residues 0 and 1 (14.4); the edge witness (14.5); the window as a cyclic ball covering a full period of any proper divisor (14.6) [PROVISIONAL: covering] (supports: a clear window contains a full residue cycle). Cited from Palelei 2026b as machine-checked; **no result in §14 discharges a case** (P§14 header).
- **Shadowing every opening requires the gcd-weighted count to reach e** (P§15; Palelei 2026b §15H). A counting statement: [PROVISIONAL: counting tool].


## I-4. Crossing

- **L1–L7** (section 7 above): the d_min gate. Landing > 7 iff K₇ = ∅ iff reading 1 sets a move from a state in (7, 9) [P (a)–(c); OBS (d)].
- **Crossing criterion** (E354, E366): an arrangement crosses the gate iff every component of K₆ lies in one open zone of reading 7; each such zone is a move of the path [P; T 0/12,078 and T 0/319,807].
- **The crossing family is open, bounded by touches** (L7; 28,511 of 28,511 observed losses are touches) [P / OBS].
- **Crossing family alphabet** (E376–E377): 47/51/52 distinct zones and 252/281/294 links at ρ₇ ≤ 9/17/25; the chain is a ladder of alternations of readings 3 and 2 (19 rank sequences, 28 chains with laps), constant over ρ₇ ≤ 9, 17, 25 [TREE]. Closedness for all ρ₇ **[OWED]**.
- **J = 3 tree run to its stop regions** (E368), PARTIAL: 1,878,060 regions; gate-crossing regions 7,855/7,940/7,947 at J = 1, 2, 3; 14 outcome classes [TREE: float-LP, exact members, no certificates].
- **Extremal cell** (E344): six tight "exit = entry" equalities along readings 3-5-7-6-4-2; R* ≤ 26433/2209 inside the cell [OBS: exact Farkas certificates, not re-read]; the vertex is tangent to d_min's second window edges 9 and 15. Why R* < 12 for every arrangement **[OWED]**.
- **Effective-crossing rule** (E312): five crossing types of an isolation across an edge [T 0 violations of 598; 2 unobservable]; the Lean statements of the five types **[OWED]**. A hop is the birth or death of a lonely window (E313) [T 0/1,716].
- **Exact gate crossers**: X24 with ρ₇ above 24 (E354, exact value in the log); 59 J = 2 members land above 7 with ρ₇ above 9 (E330, exact values in the log). [OBS: exact members]
- **Staircase** (L5): if the first k+1 setters are distinct, ρ_{7−k} > 7(7/9)^k [P]; infima 735/289, 3381/2125, … over members are float-LP upper bounds [TREE].


## I-5. Empirical hints (kept as hints; none is a proof)

- The AP has exactly four lonely instants per period, all isolated (R = 1, 3, 5, 7) (E306) [OBS: exact]; complete grids with laps < 4 are lonely at the four in 16,384 of 16,384.
- E308 found each AP event is a tangency of two zones, and the first event is not always kept (thresholds near 51/7 and 54/7).
- The frozen runners' lonely set is unchanged when others move; the landing lies in a component of it (E309, 90 runs); with three or four movers no step has an empty lonely set in (0, 9.5] (0 of 4,898, E310).
- No-move paths 1,577 of 1,860 under one deformed runner; at moves 2 and 3 every setter is frozen (210 of 210) (E311).
- Link data: never rank up with lap ≤ 0, never the same rank, never rank down with a higher lap (E315, 2,717 links); setter = largest exit [T 0/152,170] (E326).
- State sequence preserved when a reading and its image are both clear at every visited state (E327, 21,781 of 21,781); +8m and "inert component" moves (47,391 of 47,391); the closer and rank labels are not preserved.
- Phase rotation p(R+8) = p(R) + 8·frac(ρ) [OBS: exact identity, not re-read]; mirror symmetry about 4m when mρ_y ∈ ℤ [T 0/12,000]; integer arrangements: none of 66,000 lands above 7 (E342, exact maximum in its output).
- The complete grid's named instant stays lonely at q beyond 61, against a proved radius q ≤ 1/2 (E285–E286, 0 failures in 12,000).
- Lattices s = 1, 2, 3 over a₇ ≤ 40, 44, 45: 37 pairs, max landing 49/13, 33/7, 17/3, none above 7 (E357).
- Two non-AP tuples with the AP's minimal lonely set: n = 5 {1,3,4,7}; n = 8 {1,2,3,4,5,7,12} (`EXACT_PHI_N_AP_v1.md` §3). The rigid class is not characterised [OWED]. Existence witnesses, not rates.
- Literature (E276): a computer-assisted proof for eight runners exists (Rosenfeld, arXiv:2509.14111; Trakulthongchai for nine, ten); recorded as data, not imported (rule 6, ground rule 4).


---

# PART II. Why the rules exist: attempts that broke what are now the rules

## II-1. Formally proved or built, but outside the current rules

| item | statement | grade | vs rules |
|---|---|---|---|
| R8 `FastRunnerN` | one fast disparity V > (n−1)·s for all slow s: if the slow set is lonely at 1/(n−1) at τ, the whole set is lonely, since V cannot block a cell of half-width δ = 1/(n(n−1)s_max) | [L] | OK as a rule; **uses order n−1 = 7**, so LOW |
| `FastPairEightN`, `BlockSplitEightN`, `SplitChainN` | fast pair on order six; common-factor block split; nested windows needT(a :: L) = 2·needT L + 1/(4a) | [L] | R7 shape (windows and nesting as a bound); LOW. `SplitChainN` is the classical nested-intervals method, its nativeness the owner's call (E251) |
| `TrainCollapseN`, `SyncBlockN`, `SyncGridN`, `SyncPeriodN` | a fast train N + e collapses to an order-seven object; the event lies in [2τ, 2τ + 1/N), τ chosen before N; a train cannot carry the isolation past its period points | [L] | LOW (order seven); R7 (bound independent of N) |
| `RungBudgetEightN`, `RungR1N` | rung budget and link lemma, proved for every N; ladder rung plus the deviation forced by its multiples' own d_min | [L] | R7 (budget) |
| `MergeN`, `MergeFiveN`, `MergeSixN`, `MirrorN`, `RankTwoN`, `ManyDirectionsN`, `TwoGroupsN`, `IrrationalN`, `RationalN`, `ResonanceN` | merge rules (a runner sitting with another costs nothing), exact merges for five and six rows, mirror merge, real speeds on independent directions, incommensurable groups, instants not indexed by the arrangement | [L] titles read | mixed; the order 5 and 6 items are LOW |
| `OrdersThreeFourN`, `OrderFiveN`, `OrderFiveResidualN`, `OrderSix*N`, `OrderSeven*N`, `OrderSixSevenN` | orders 3–7 inside the framework; order 7 follows Barajas–Serra, order 6 follows BHK | [L] | LOW: not used in the n = 8 proof (owner, ground rule 4) |
| `OrderEightCasesN`, `EndRunnerN`, `SlowestSkeletonN`, `Order8SkeletonN` | at most six disparities by order seven; a common factor g divides out (τ gives τ/g); the slowest runner of every arrangement of eight is enough; split on W/g₁: Case A (W ≤ 7g₁, R1) proved, `CaseB8 T` and `CaseC8 T` OWED | [L] | LOW for the card ≤ 6 step; the skeleton is a case split with owed holes |
| `RegimeSkeletonN`, `Cover8` | `lonelyRunnerAt8_of_cover8 M : Cover8 M → LonelyRunnerAt8`: every set is lonely at the bound or at a relocated grid-class instant of a grid through one of its readings with step ≥ m/M | [L] statement; `Cover8 M` OWED | **R7 (cap M, covering)**; the cap is not native (MM C13) |
| `WideStep8` (E211–E217) | the native content is the lap structure of every `GridStep8` certificate; a uniform M bounds the time | [OBS: derived by hand, not checked] | R7 (cap); F15 |
| `GlobalIsolationTwoN` | two-dimensional form of the unit-orbit mechanism: the orbit k ↦ ({c₃k/n}, {c₁k/n}) meets every box | [L] | LOW (order 6 origin); "meets every box" is a covering form, [PROVISIONAL: covering] if used |

Why: LOW rows use order 7 or 6 (ground rule 4); R7 rows are window, budget, cap or covering shapes (rule 7).

## II-2. Flank-reading and empirical items refuted or outside rule 6

- **E259–E268, flank reading of the C1-shape**: "fastest flank free or twin chain free, 547 of 547" (E260) and "rank 1 or rank 2 free" (E264/E268) were **refuted** (F17). The account of persistent shadows and hand-offs (C22) stands as derived; mixed joint covers are open.
- `ISOLATION_COUNT_v1.md` found event rates per period lower off the AP, interior minimum exactly 2, binding runner the mover [T 24 sample points per transit, exact; mover claim OWED]. Rates are rule 5 items (F2); observation only.
- A displaced runner "harvests" the unmoved pack's reunions (`GRAND_RETURN_v1.md` §§2–3): the seven unmoved runners return to 0 at every integer t; the mover is lonely at the reunions when ‖εt‖ ≥ 1/8. The shares 1/2, 7/10, 3/4 are a density statement (F2), kept as observation.

## II-3. Attempts that did not comply with the rules, were refuted, or were withdrawn

One line per class; entries in `MECHANISM_MAP_v5.md` §6.

- **F1 imported shape ("that" or "when" it stops):** quantity tests (E170), waves "at most seven moves" (E171–E172), Props 6.10–6.11 (withdrawn), `DoorFirstLap` (`d_min·t ≤ 1`, **[REFUTED]** at the 28-move case τ = 2401/1872), `WideStep8 1` as a first-lap cap, `Cover8 M` at a uniform M.
- **F2 a rate as the answer:** coverage, shares of instants, reach percentages (one rule scores differently on three schemes, `reach_scheme_dependence_v1.out`), top-pair mirror meetings.
- **F3 a majority rule stated as a law:** "the same word repeats" (E64), block law 13/4 (E57), "every runner sets at most twice" (E66), "the unsettled are captured readings" (E129–E130), "no block reading set a move in a gap" (0 of 41, E233).
- **F4 a restatement taken for a step:** "every arrangement has a type" (E145), "the separations come to rest" (E159), (B) at the target (E187).
- **F5 a forced fact found after the data:** E136, E143, E150, E152, E176's 320/320, E188's "never later", E214's "R ≥ 9 after closure".
- **F6 unrestricted parameter:** E176, E188's q_c, E190's free model instant.
- **F7 the record not read:** E172, E184, E187, E209, E217, E219, E225–E230, E252, E256.
- **F8 a false `def … : Prop`:** `DoorFirstLap`; `Cover8` without the card bound (fixed `3ea9feb`). A `def : Prop` is type-checked, never proved; no gate sees a false one.
- **F9 frame error:** a runner held fixed (E75, `region_lonely`, E186); pre-registration language on LRC (E172); `SplitChainN` nested intervals (flag E251).
- **F12 range-forced:** "the slowest runner never leaves its first block" (O7, E151, E153).
- **F13 consequence not drawn:** `band_lonely` proved (E169) and imported by nothing until E212; `lonelyRunnerAt8_iff_residual` unpropagated for 5 days.
- **F14 an instant family the cascade does not use:** order seven's multipliers at 8·2^V (E193–E195); the 2t, 3t, 5t candidates (E196).
- **F15 a proved by-product promoted to the object:** `WideStep8 1`'s window (E211–E214) passed the place test via a by-product of M = 1.
- **F16 a proxy count for the object:** the "cover" substring count (E215), the gate-count 4,749 for 4,748, E264's "the landing is at rank 1 or 2".
- **F17 a constructed sample's regularity stated as a law:** E260 547 of 547, refuted by 6 in 5,431 (E264); E264's own statement refuted by 287 constructed members (E268).
- **F18 the obligation replaced by a stricter one:** a fourth rule (D, a), a uniform theorem, a named instant, a bound (E229–E230).
- **Specific retractions:** L ≥ 2/(7ρ₆) for K₆ (E359; counterexample (1, 6559/2279, 26236/6779, 231/47, 26236/4115, 7), L = 135/3748); the uncovered-length floor 53/462 (v12); the "reach ceiling" (E352–E354); sampler-reach claims "rank 1 inert" and "longest path 12" (E326); "hops land on frozen edges only" (E311/E313); E278's dichotomy and evenness branch; E286's comparison columns; E346's "8 leaf members form one family" (E347); leaf-only tree statistics (E347); the E328 taxonomy (E348); window-floor statistics tied to ρ₇ ≥ 7 storage (E359).


## II-4. Which failure produced which rule

PARTIAL mapping from `MECHANISM_MAP_v5.md` §6 to `RULES_n8_v4.md` (F11 is not mapped); the rules cite owner messages (M-numbers), and this mapping is **[mine]**, unconfirmed by the owner.

| failure class (II-3) | rule it motivated |
|---|---|
| F1 "that"/"when" it stops; F15 by-product promoted; F18 stricter obligation; `Cover8 M`, `WideStep8` caps; Props 6.10–6.11; band-cover trees | 7 (banned shapes: supply against demand, termination, move budgets, caps, uniform formula, slack) and its 2026-10-05 relaxation for covering and counting tools |
| F2 rates, shares, reach percentages | 6 (no imported density or coverage) |
| F9 a runner held fixed (E75, `region_lonely`, E186) | 5 (no runner is ever stationary) |
| F7 the record not read | 13 (full record, reuse before rebuilding) |
| F4 restatements, F16 proxy counts, F14 instant families the cascade does not use | 8 (check proxy against cascade), 9 (the next test is what the cascade does that is not understood) |
| F3 majority rule as a law, F17 constructed-sample regularity, F5 forced facts, F12 range-forced | 11 (theory is adjusted to the cascade's results), 10 (test new arrangements, not restatements) |
| F8 false `def … : Prop`, "full mechanism" on a partial result | 18 (do not claim what is not done; grades) |
| float tree cells, float-LP witnesses (E331, E337, E338) | 15 (exact only) |
| sampler-reach claims (E326), half sets and leaf-only statistics (E347) | 14 (full data sets) |
| F6 unrestricted parameter; F10 continuation asserted (F10 is in `MECHANISM_MAP_v5.md` §6, not listed in II-3) | 12 (search clever, perturb to explain), 18 |
| stationary-runner frame and pre-registration language on LRC (E172) | 5; CLAUDE.md §3 (checks stay, pre-registration is ECC only) |
| F13 consequence not drawn | map rule M7 (`Consequence:` line), not a numbered rule in v4 |


---

## Unclassified: statement not read

Grade [L] is from the module's docstring; the statement was not read, so no rule classification is made. [OWED] reading.

| item | statement (one line) | grade | vs rules |
|---|---|---|---|
| `SegmentWindowN`, `WindowPinchN`, `SymbolicWindow*N`, `PinchTransportN`, `PinchReflectionN`, `PartialReflectionN` | exact lap windows along a one-mover segment and at the first pinch of an AP deformation; period reflection picks replacement labels at a one-sided pinch | [L] titles read; statements not re-read | not classified |
| `FlankSumN` | the flank sum criterion for rational movers at order 8 | [L] title read | not classified |
| `HalfPairParityN`, `HandoffDriftN`, `HandoffResonanceN`, `LapDeadlineN`, `CoreWindow*N`, `MovingCore*N`, `IncomingWindowN`, `FiniteWindowContinuationN`, `DeadlineRelabelN`, `BidirectionalReplacementN`, `VariableCoreReplacementN`, `DoubleBacktrackN`, `MixedLapOverlapN` | the hand-off machinery: parity of a half-integer walker, drift of a repeated captured pair, lap deadlines carried through forward moves, core windows forcing named zones in the run, replacement labels | [L] titles read; statements not re-read | not classified |

---

## Owed (carried from the record)

1. [OWED] The displacement is forced: an unblocked R exists for every arrangement **[PROVISIONAL: covering]** (target).
2. L1(d); R* < 12; closure of the crossing family for all ρ₇; the touch alphabet finite (L7).
3. The scale reduction of a cluster of fast readings (`N8_PROOF_ARCHITECTURE_v1.md` §4).
4. Exact certificates for pruned LP branches and cells thinner than the slack.
5. The reference-grid selection rule, and the grid-to-grid statement in general.
6. Statement (T) (E280): tight arrangements have only simple pinches; multi-pinches and bounded time (`hopen`).
7. `compile-diff` of this addendum against the sources listed under Scope.
