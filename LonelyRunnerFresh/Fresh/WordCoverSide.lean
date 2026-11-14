import Fresh.JoinFamComposed
import Fresh.ComposedFamData
import Fresh.OneSidedGlue

/-!
# The word-cover side: direction (b) of the OneSided spine, at the level of the pieces

Written 2026-11-13.  New file; nothing existing is edited.  This formalizes the census
word-cover side of the OneSided spine — `Fresh.SpineTotalData` §5's direction (b), "no `W₁`
clear point ⟹ some family word demand is realized on `g`" — in the `ChainReal` /
`ComposedEdge` vocabulary of `Fresh.JoinFamComposed`, so that `Fresh.OneSidedGlue`'s named
OWED direction (b) composes to it.

The mathematics (census word-cover, [T]-verified in `j2_cycle_v6/v12` and dump v2's
word-class hops): a `W₁` word is a monotone zone chain covering `[9,15]` — zones
`(8j±1)/ρ` of the readings.  Its edges demand ratios: consecutive zones `u → x` (levels
`ju < jx`) whose zones overlap inside `[9,15]` share a point `R` with
`R < (8ju+1)/ρu` and `R > (8jx−1)/ρx`, whence `(8jx−1)·ρu < (8ju+1)·ρx`, i.e. the seam
demand `ρx/ρu > (8jx−1)/(8ju+1)`; transposed into the `ComposedEdge` demand convention
(`ρ_{e.x}/ρ_{e.y} < A/B`, chain from `e.y` to `e.x`), the word edge is
`(e.x, e.y, A, B) = (u, x, 8ju+1, 8jx−1)`: `ρu/ρx < (8ju+1)/(8jx−1)` — the demand's
numerator side is the FIRST (earlier-level) zone's reading.  (Census check: box
(1,2,3,4,5,6,8)'s `ρ₂/ρ₆ < 25/63` — reading 2 at zone level 3 first, reading 6 at level
8 second, `8·3+1 = 25`, `8·8−1 = 63`.)  A single zone cannot cover both endpoints `9` and
`15` (readings positive, levels `≥ 1` force `48j < 24` — contradiction), so a realized
word always HAS an edge, and every realized edge's demand is realized on `g`.

Contents (all PROVED; every theorem closed):
* `inZone` / `HasAdj` / `WordRealized` — the `W₁`-word realization (zone form matching
  `CarvesOneSeven`'s `(8j±1)/ρ` zones; adjacency; coverage of `[9,15]`; level monotonicity
  and overlap of consecutive zones inside the window);
* `WordEdgeOf` / `SameEdge` — the word-edge shape `(x, y, P, Q)` (`P = 8ju+1`,
  `Q = 8jx−1`) and the family-record match;
* `wordEdge_demand` — THE SEAM-DEMAND REALIZATION LEMMA: a realized word's edge forces the
  demand `ρx/ρy < P/Q` on `g` (positivity included) — the covering argument's engine;
* `wordRealized_has_edge` — a realized word has an edge (the two-endpoint argument above);
* `wordCover_realizes` — direction (b)'s conclusion shape: word realized + the
  W₀-chain-conditional bridge (`capChainsRealized`, direction (a)'s hypothesis form) +
  family exhaustiveness (`hFam`, the dump's per-box word-edge totality, `no-raw-kill
  pairs 0` / [T 73/73] form) ⟹ some family record is fully realized on `g`;
* `wordCover_demands` — the kill form: the same hypotheses + the banked datum ⟹ False
  (through `composedFamRefutes` / `composedCap_conflict`);
* `NoClearPointWordRealized`, `FamilyCoversWordEdges` — the two named OWED data-side
  directions this file does NOT assume (the finite closed-interval covering refinement,
  and the per-box family exhaustiveness instantiation of the dump);
* `composedTotal_of_wordCover` / `oneSidedSound_of_wordCover` — the glue: these two OWED
  discharge `Fresh.OneSidedGlue.ComposedTotalOneSided` for a covered box, and hence
  complete the glue's OWED direction (b) inside `oneSidedSound_of_composedData`.

Signature note (recorded divergence): the requested shape
`WordRealized g w → (∀ e ∈ f.edges, ¬ ChainReal g e.y e.caps e.x) → False` is NOT
provable: the word side forces DEMANDS only (the seam lemma); the chain side is the
independent W₀-conditional (a realization of `W₁`'s zones carries no information about the
J-side caps — direction (a)'s content), and `demand-realized + chain-unrealized + datum`
is consistent (e.g. `ρx/ρy` small with the cap violated).  The chain side therefore enters
as `capChainsRealized g f` — exactly the hypothesis every OneSided totality datum of the
spine carries (`Fresh.SpineSound.SpineTotalOneSided`,
`Fresh.OneSidedGlue.ComposedTotalOneSided`); under it the literal `∀ e, ¬ ChainReal ...`
hypothesis is vacuous (it contradicts the bridge outright), so the content statement is
`wordCover_realizes` and the kill `wordCover_demands` is its corollary.

All arithmetic is exact (`norm_num`/`linarith` on integers/rationals; floats nowhere).
Every theorem carries `#print axioms`; the accepted profile is the standard three
(propext, Classical.choice, Quot.sound) — `sorryAx` is failure.
-/

namespace Fresh.WordCoverSide

open Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
open Fresh.FilterAssembly Fresh.FrontierFamilyCap

/-! ## 1. The zone vocabulary and the W₁ word -/

/-- A reading `ρ = g u` at comb level `j` covers `R` when `8j−1 < ρR < 8j+1` — the zone
form of `Fresh.FrontierFamilyCap.CarvesOneSeven` (with `j : ℕ`; `W₁` zones have `j ≥ 1`). -/
-- STANDING: DEFINITION
def inZone (g : Fin 7 → ℝ) (u : Fin 7) (j : ℕ) (R : ℝ) : Prop :=
  ((j : ℝ) * 8 - 1 < g u * R ∧ g u * R < (j : ℝ) * 8 + 1)

/-- Two entries are ADJACENT in the word: consecutive members of the list
(`w = l₁ ++ p :: q :: l₂`). -/
-- STANDING: DEFINITION
def HasAdj (w : List (Fin 7 × ℕ)) (p q : Fin 7 × ℕ) : Prop :=
  ∃ l₁ l₂ : List (Fin 7 × ℕ), w = l₁ ++ p :: q :: l₂

/-- **A `W₁` word realized on `g`**: a monotone zone chain of `g`'s readings covering
`[9,15]` — (i) the word's readings are positive and its levels `≥ 1` (the `W₁` window's
comb levels), (ii) every `R ∈ [9,15]` lies in some zone of the chain, (iii) consecutive
zones have strictly increasing levels and OVERLAP inside `[9,15]` (the chain is connected:
the word's zone edges cover the carved window without a gap). -/
-- STANDING: DEFINITION
def WordRealized (g : Fin 7 → ℝ) (w : List (Fin 7 × ℕ)) : Prop :=
  (∀ p ∈ w, 0 < g p.1 ∧ 1 ≤ p.2) ∧
  (∀ R : ℝ, 9 ≤ R → R ≤ 15 → ∃ p ∈ w, inZone g p.1 p.2 R) ∧
  (∀ p q : Fin 7 × ℕ, HasAdj w p q → p.2 < q.2 ∧
    ∃ R : ℝ, 9 ≤ R ∧ R ≤ 15 ∧ inZone g p.1 p.2 R ∧ inZone g q.1 q.2 R)

/-- A word edge `(x, y, P, Q)`: the word has consecutive zones `(x, jx) → (y, jy)` — the
`x`-zone FIRST (lower level), the `y`-zone second — with `P = 8jx+1`, `Q = 8jy−1`.  The
realized demand is then `g x / g y < P/Q` (`wordEdge_demand`): in the `ComposedEdge`
convention the record is `(e.x, e.y, A, B) = (x, y, P, Q)` (demand numerator side = first
zone's reading; chain from `e.y`, the second zone's reading, to `e.x` — cf. the banked
`ρ₆/ρ₂ ≤ 17/7` cap of `fam12568`'s `ρ₂/ρ₆ < 25/63` demand).  This is the structural
(word-side) predicate; the demand's realization on `g` is derived, not assumed. -/
-- STANDING: DEFINITION
def WordEdgeOf (g : Fin 7 → ℝ) (w : List (Fin 7 × ℕ)) (x y : Fin 7) (P Q : ℤ) : Prop :=
  ∃ jx jy : ℕ, HasAdj w (x, jx) (y, jy) ∧
    P = ((jx : ℤ) * 8 + 1) ∧ Q = ((jy : ℤ) * 8 - 1)

/-- A composed record `e` matches the word edge `(x, y, P, Q)`: same demand edge, same
data (`e.x = x`, `e.y = y`, `e.A = P`, `e.B = Q`). -/
-- STANDING: DEFINITION
def SameEdge (e : ComposedEdge) (x y : Fin 7) (P Q : ℤ) : Prop :=
  e.x = x ∧ e.y = y ∧ e.A = P ∧ e.B = Q

/-! ## 2. The seam-demand realization lemma and the edge-existence lemma -/

/-- **THE SEAM-DEMAND REALIZATION LEMMA** (direction (b)'s engine): consecutive zones
`(x, jx) → (y, jy)` of a realized word (`jx < jy`, the `x`-zone first) overlap inside
`[9,15]`, so their readings share a point `R` with `g x·R < 8jx+1` (first zone's upper
side) and `g y·R > 8jy−1` (second zone's lower side); cross-multiplying
`(8jy−1)/(g y) < R < (8jx+1)/(g x)` forces `(8jy−1)·g x < (8jx+1)·g y`, i.e. the word
edge's demand `g x / g y < P/Q` realized on `g`, with the positivity the composed engine
needs. -/
theorem wordEdge_demand {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hw : WordRealized g w) {x y : Fin 7} {P Q : ℤ} (hedge : WordEdgeOf g w x y P Q) :
    0 < g x ∧ 0 < g y ∧ g x / g y < (P : ℝ) / (Q : ℝ) := by
  obtain ⟨hpos, hcov, hlink⟩ := hw
  obtain ⟨jx, jy, hadj, hP, hQ⟩ := hedge
  obtain ⟨l₁, l₂, hweq⟩ := hadj
  have hxm : (x, jx) ∈ w := by rw [hweq]; simp
  have hym : (y, jy) ∈ w := by rw [hweq]; simp
  have hxpos : 0 < g x := (hpos (x, jx) hxm).1
  have hypos : 0 < g y := (hpos (y, jy) hym).1
  have hx1 : 1 ≤ jx := (hpos (x, jx) hxm).2
  obtain ⟨hmono, R, hR1, hR2, hxz, hyz⟩ := hlink (x, jx) (y, jy) ⟨l₁, l₂, hweq⟩
  obtain ⟨_, hxa⟩ := hxz   -- g x * R < (jx : ℝ) * 8 + 1   (first zone's upper side)
  obtain ⟨hya, _⟩ := hyz   -- (jy : ℝ) * 8 - 1 < g y * R   (second zone's lower side)
  have hjy2 : (2 : ℝ) ≤ (jy : ℝ) := by
    have h2 : (2 : ℕ) ≤ jy := by omega
    exact_mod_cast h2
  have eP : (P : ℝ) = (jx : ℝ) * 8 + 1 := by exact_mod_cast hP
  have eQ : (Q : ℝ) = (jy : ℝ) * 8 - 1 := by exact_mod_cast hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := by rw [eQ]; linarith
  have hxa' : g x * R < (P : ℝ) := by linarith
  have hya' : (Q : ℝ) < g y * R := by linarith
  -- the shared point: (8jy−1)/g y < R < (8jx+1)/g x  ⟹  Q·g x < g y·R·g x < P·g y
  have m1 : (Q : ℝ) * g x < g y * R * g x := mul_lt_mul_of_pos_right hya' hxpos
  have m2 : g x * R * g y < (P : ℝ) * g y := mul_lt_mul_of_pos_right hxa' hypos
  have k3 : g x * (Q : ℝ) < (P : ℝ) * g y := by linarith
  exact ⟨hxpos, hypos, (div_lt_div_iff₀ hypos hQpos).mpr k3⟩

#print axioms wordEdge_demand

/-- **A realized word has an edge**: a single zone (reading positive, level `≥ 1`) cannot
cover both window endpoints — covering `9` gives `8j−1 < 9ρ`, covering `15` gives
`15ρ < 8j+1`, whence `ρ < 1/3` and `8j < 4`, contradicting `j ≥ 1`.  So the chain has at
least two zones, and its first two form an edge. -/
theorem wordRealized_has_edge {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}
    (hw : WordRealized g w) :
    ∃ x y : Fin 7, ∃ P Q : ℤ, WordEdgeOf g w x y P Q := by
  obtain ⟨hpos, hcov, hlink⟩ := hw
  obtain ⟨p, hp, h9⟩ := hcov 9 (by norm_num) (by norm_num)
  cases w with
  | nil => exact absurd hp (by simp)
  | cons u rest =>
    cases rest with
    | nil =>
      obtain ⟨q, hq, h15⟩ := hcov 15 (by norm_num) (by norm_num)
      simp only [List.mem_singleton] at hp hq
      rw [hp] at h9
      rw [hq] at h15
      obtain ⟨h91, _⟩ := h9
      obtain ⟨_, h152⟩ := h15
      have hgu : (0 : ℝ) < g u.1 := (hpos u (by simp)).1
      have hr1 : (1 : ℝ) ≤ ((u.2 : ℕ) : ℝ) := by exact_mod_cast (hpos u (by simp)).2
      have hlt : ((u.2 : ℕ) : ℝ) < 1 := by linarith
      exact absurd hlt (not_lt.mpr hr1)
    | cons v rest' =>
      exact ⟨u.1, v.1, ((u.2 : ℤ) * 8 + 1), ((v.2 : ℤ) * 8 - 1),
        u.2, v.2, ⟨[], rest', rfl⟩, rfl, rfl⟩

#print axioms wordRealized_has_edge

/-! ## 3. Direction (b): the word-cover realization and the kill -/

/-- **Direction (b)'s conclusion shape**: a `W₁` word realized on `g`, the
W₀-chain-conditional bridge (direction (a)'s hypothesis form: the family's composed cap
chains realized on `g`), and family exhaustiveness (every realized word edge of the word
maps into the family) ⟹ some family record is FULLY realized on `g` — demand (from the
seam lemma) and chain (from the bridge), i.e. `ComposedEdgeRealized`. -/
theorem wordCover_realizes {g : Fin 7 → ℝ} {f : ComposedFam}
    (hchains : capChainsRealized g f)
    {w : List (Fin 7 × ℕ)} (hw : WordRealized g w)
    (hFam : ∀ (x y : Fin 7) (P Q : ℤ), WordEdgeOf g w x y P Q →
      ∃ e ∈ f.edges, SameEdge e x y P Q) :
    ∃ e ∈ f.edges, ComposedEdgeRealized g e := by
  obtain ⟨x, y, P, Q, hedge⟩ := wordRealized_has_edge hw
  obtain ⟨hxpos, hypos, hdem⟩ := wordEdge_demand hw hedge
  obtain ⟨e, he, hsame⟩ := hFam x y P Q hedge
  refine ⟨e, he, ?_, ?_, ?_, hchains e he⟩
  · rw [hsame.1]; exact hxpos
  · rw [hsame.2.1]; exact hypos
  · rw [hsame.1, hsame.2.1, hsame.2.2.1, hsame.2.2.2]; exact hdem

#print axioms wordCover_realizes

/-- **THE WORD-COVER KILL** (`wordCover_demands`): a `W₁` word realized on `g` + the
W₀-chain-conditional bridge + family exhaustiveness + the banked composed datum ⟹ False —
the realized record dies through `composedFamRefutes` (whose engine is
`composedCap_conflict`: the demand `ρx/ρy < A/B`, the telescoped chain cap
`ρy/ρx ≤ ∏caps`, the datum `A·∏caps ≤ B`).  This is the one-sided kill shape "IF `g`
carves `W₁` (word realized) and the join side is realized (bridge), the arrangement cannot
exist".  See the module docstring for the recorded divergence from the literal
`∀ e ∈ f.edges, ¬ ChainReal g e.y e.caps e.x` hypothesis shape. -/
theorem wordCover_demands {g : Fin 7 → ℝ} {f : ComposedFam}
    (hdata : ComposedFamData f) (hchains : capChainsRealized g f)
    {w : List (Fin 7 × ℕ)} (hw : WordRealized g w)
    (hFam : ∀ (x y : Fin 7) (P Q : ℤ), WordEdgeOf g w x y P Q →
      ∃ e ∈ f.edges, SameEdge e x y P Q) :
    False :=
  composedFamRefutes hdata (wordCover_realizes hchains hw hFam)

#print axioms wordCover_demands

/-! ## 4. The two OWED data-side directions and the glue to `OneSidedGlue` -/

/-- **OWED — the `W₁`-word covering direction** (the finite closed-interval covering
argument recorded as missing in `Fresh.FrontierFamilyCap.FrontierCarveCap`'s docstring):
if `g` admits no `W₁` clear point, then the zones of `g`'s readings cover `[9,15]`
(`distInt (g i * (s/8)) < 1/8` at some reading `i` is exactly the zone condition
`8k−1 < g i·s < 8k+1`), and that cover refines to a monotone connected zone chain — a
realized word.  Not proved here; nothing assumes it. -/
-- STANDING: OWED
def NoClearPointWordRealized (g : Fin 7 → ℝ) : Prop :=
  ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
    ∃ w : List (Fin 7 × ℕ), WordRealized g w

/-- **OWED — family exhaustiveness** (the dump's per-box word-edge totality, the [T
73/73] `join_domination_all_chains`-style law of dump v2 / `no-raw-kill pairs 0` of
`j2_cycle_v6`): for an arrangement in the box, EVERY word edge `(x, y, P, Q)` of every
realized `W₁` word is carried by the box's family — the family enumerates all word-edge
demands of the box.  Data-side: the per-box instantiation for `compFamOf b` is the dump's
exhaustiveness, not proved here. -/
-- STANDING: OWED
def FamilyCoversWordEdges (b : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ (g : Fin 7 → ℝ) (w : List (Fin 7 × ℕ)),
    (∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i) → WordRealized g w →
    ∀ (x y : Fin 7) (P Q : ℤ), WordEdgeOf g w x y P Q →
      ∃ e ∈ f.edges, SameEdge e x y P Q

/-- **THE GLUE — direction (b) discharged**: for a covered box `b`, the two OWED
data-side directions (the `W₁`-word covering direction, and the family exhaustiveness
datum) give `Fresh.OneSidedGlue.ComposedTotalOneSided b (compFamOf b)` — the composed
one-sided totality whose consumption by `oneSidedSound_of_composedData` completes the
spine.  Proof: no clear point gives a realized word (`NoClearPointWordRealized`); the
word's edges map into the family (`FamilyCoversWordEdges`); `wordCover_realizes` realizes
a record (the bridge `hchains` is a hypothesis of the totality datum itself). -/
theorem composedTotal_of_wordCover (b : Fin 7 → ℤ) (_hb : b ∈ coveredSet)
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b)) :
    ComposedTotalOneSided b (compFamOf b) := by
  intro g hface hchains hcarve hnoc
  obtain ⟨w, hw⟩ := hword g hnoc
  obtain ⟨e, he, hxpos, hypos, hdem, _⟩ :=
    wordCover_realizes hchains hw (hexh g w hface hw)
  exact ⟨e, he, hxpos, hypos, hdem⟩

#print axioms composedTotal_of_wordCover

/-- **The OneSided conclusion through the word-cover side**: the glue
`Fresh.OneSidedGlue.oneSidedSound_of_composedData` with its OWED direction (b) discharged
by `composedTotal_of_wordCover` — an arrangement in a covered box whose chains are
realized (the W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its
faces. -/
theorem oneSidedSound_of_wordCover (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)
    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)
    (hexh : FamilyCoversWordEdges b (compFamOf b))
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)
    (hchains : capChainsRealized g (compFamOf b))
    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=
  oneSidedSound_of_composedData b hb (composedTotal_of_wordCover b hb hword hexh)
    g hface hchains hcarve

#print axioms oneSidedSound_of_wordCover

end Fresh.WordCoverSide
