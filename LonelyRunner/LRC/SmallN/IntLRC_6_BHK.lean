import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.SmallN.IntLRC_5_Bienia

/-!
# Bohman–Holzman–Kleitman 2001 (`Six Lonely Runners`) — Lean port

Goal: prove the Hard Case of `intLRC 6`. Concretely, for any five positive
integers `v_1 < v_2 < v_3 < v_4 < v_5` with `gcd = 1`, there exists `t : ℝ`
with `circDist (v_i * t) ≥ 1 / 6` for every `i`.

Source: T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*,
Electronic Journal of Combinatorics **8** (2001) R3.

## Architecture

BHK's argument operates on reciprocal lengths `x_i := 1 / v_i` and proves the
contrapositive: the union `⋃_i x_i · B` is not all of `ℝ⁺`, where
`B = ⋃_{k ∈ ℤ} (k − 1/6, k + 1/6)` is the unsafe set near integers. In their
notation, **i-blocks** are maximal closed intervals contained in `x_i · B`, and
**S-gaps** are maximal open intervals contained in the complement. The crux is
that a sufficiently long S-gap exists.

After scaling, BHK normalise `x_3 = 1` (real speeds; their §4 Lemma 8 reduces
real to rational). For our **integer** formulation we cannot normalise, but
the structural arguments (B-blocks, S-gaps, the Main Lemma on torus
subgroups) are scale-invariant and so carry over directly.

## File map (sub-theorems mirror BHK sections)

| Sub-theorem | BHK reference | Description |
|---|---|---|
| `bhk_lemma_4` | Lemma 4 | A 45-block has length `< 2 · x_4 / 3`. |
| `bhk_corollary_5` | Corollary 5 | A 3-gap that is also a 123-gap ⇒ `B ≠ ℝ⁺`. |
| `bhk_main_lemma` | Main Lemma | Cyclic subgroup `G` of the 2-torus `T` of order `n` intersects every `α × β` rectangle with `αβ ≥ 1/n`, modulo two exceptional configurations. |
| `bhk_corollary_6` | Corollary 6 | Applied form: either `G` hits every rectangle or contains a small lattice vector. |
| `bhk_case_v1_large` | §8 | `v_1` (smallest) at least `v_3 / 3` — ad hoc. |
| `bhk_case_v1_small_generic` | §7 | `v_3 / 4 < v_1 < v_3 / 3`, with `{t_0} ≠ 0` and `{v_1 t_0} ≠ 0`. |
| `bhk_case_t0_zero` | §6 | `{t_0} = 0`. |
| `bhk_case_v1t0_zero` | §5 | `{v_1 t_0} = 0`. |
| `intLRC_six_hard` | Theorem 2 | The integer-speed five-mover statement (combines the cases). |

Each sub-theorem is currently `sorry`-stubbed. The plan is to discharge them
in subsequent sessions in roughly the order above (Lemma 4 / Corollary 5 are
elementary; the Main Lemma and the four §5–§8 case branches contain the bulk
of the work).

**Sorry budget:** 9 (one per stubbed sub-theorem; `intLRC_six_hard` is
*not* `sorry`-stubbed at the body but rather uses the stubbed lemmas, so
the budget reflects the actual mathematical content remaining).
-/

open MeasureTheory Set

namespace BHK

/-! ## §2 Setup: B-blocks, S-gaps, and the 45-block lemma -/

/-- BHK's `B`: the open unsafe set near integers,
    `B = {x : ℝ | ∃ k : ℤ, |x − k| < 1/6}`.

    A runner with speed `v` is *not* lonely at time `t` (for the `1/6` gap)
    iff `t ∈ (1/v) · B`. -/
def bhkB : Set ℝ := { x : ℝ | ∃ k : ℤ, |x - (k : ℝ)| < 1 / 6 }

/-- BHK's union `𝓑 = ⋃_i x_i · B`. The conjecture for five integer speeds
    is the statement `𝓑 ≠ ℝ⁺`. -/
noncomputable def bhkBunion (speeds : Fin 5 → ℕ) : Set ℝ :=
  ⋃ i, { t : ℝ | (speeds i : ℝ) * t ∈ bhkB }

/-- The set of times where runner `i` is "near the origin" (within `1/6`)
    on the circle. Equivalently, `t ∈ unsafeOf speeds i` ↔ `(v_i · t) ∈ bhkB`.
    A maximal closed sub-interval of `⋃_{i∈S} unsafeOf speeds i` is an
    `S`-block. -/
def unsafeOf (speeds : Fin 5 → ℕ) (i : Fin 5) : Set ℝ :=
  { t : ℝ | (speeds i : ℝ) * t ∈ bhkB }

/-- Bridge between BHK's interval formulation and our `circDist` formulation:
    `x ∈ bhkB` iff `circDist x < 1/6`. Proved via `circDist_eq_infDist` for
    the forward direction and via the `min(fract, 1-fract)` form for the
    reverse direction. -/
theorem mem_bhkB_iff (x : ℝ) : x ∈ bhkB ↔ circDist x < 1 / 6 := by
  constructor
  · rintro ⟨k, hk⟩
    -- dist x k < 1/6, and circDist x ≤ dist x k via infDist characterization.
    have hmem : (k : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) := ⟨k, rfl⟩
    rw [circDist_eq_infDist]
    calc Metric.infDist x (Set.range (Int.cast : ℤ → ℝ))
        ≤ dist x (k : ℝ) := Metric.infDist_le_dist_of_mem hmem
      _ = |x - (k : ℝ)| := Real.dist_eq _ _
      _ < 1 / 6 := hk
  · intro hcd
    unfold circDist at hcd
    rcases min_lt_iff.mp hcd with hL | hR
    · -- fract x < 1/6 ⇒ k = ⌊x⌋
      refine ⟨⌊x⌋, ?_⟩
      have hfl_le : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      have hfract : x - (⌊x⌋ : ℝ) = Int.fract x := by
        unfold Int.fract; ring
      rw [abs_of_nonneg (by linarith), hfract]; exact hL
    · -- 1 - fract x < 1/6 ⇒ k = ⌊x⌋ + 1
      refine ⟨⌊x⌋ + 1, ?_⟩
      have hlt : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
      have hfract_lt_one : Int.fract x < 1 := Int.fract_lt_one x
      have hcast : ((⌊x⌋ + 1 : ℤ) : ℝ) = (⌊x⌋ : ℝ) + 1 := by push_cast; ring
      have hdiff : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = -(1 - Int.fract x) := by
        rw [hcast]; unfold Int.fract; ring
      rw [hdiff, abs_neg, abs_of_nonneg (by linarith)]; exact hR

/-- Translated bridge: `t ∈ unsafeOf speeds i` iff
    `circDist (v_i · t) < 1/6`. -/
theorem mem_unsafeOf_iff (speeds : Fin 5 → ℕ) (i : Fin 5) (t : ℝ) :
    t ∈ unsafeOf speeds i ↔ circDist ((speeds i : ℝ) * t) < 1 / 6 := by
  unfold unsafeOf; exact mem_bhkB_iff _

/-- **BHK Lemma 4.** Any closed interval `[a, b]` contained in the union of
    runner 4's and runner 5's unsafe sets has length strictly less than
    `2 / (3 · v_4)`. BHK's "45-block" specialises this to maximal such
    intervals; the bound holds vacuously for sub-intervals as well. The proof
    splits on the number of 5-blocks `k` contained in the interval; for
    `k ≤ 1` direct, for `k ≥ 2` via a containment of any 4-gap. -/
theorem bhk_lemma_4 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (hI : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩) :
    b - a < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
  sorry

/-- **BHK Corollary 5.** If a closed interval is contained in the *complement*
    of `unsafeOf 0 ∪ unsafeOf 1 ∪ unsafeOf 2` (a 123-gap) and has length at
    least `2 / (3 · v_3)`, then it cannot lie inside a 45-block (Lemma 4
    bounds those by `< 2 / (3 · v_4) < 2 / (3 · v_3)`). Hence the interval
    contains a time that is lonely for *all* five runners — proving
    `bhkBunion speeds ≠ ℝ`. (Proved modulo Lemma 4.) -/
theorem bhk_corollary_5 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (a b : ℝ) (hab : a ≤ b)
    (h123gap : Set.Icc a b ⊆ (unsafeOf speeds ⟨0, by omega⟩ ∪
                              unsafeOf speeds ⟨1, by omega⟩ ∪
                              unsafeOf speeds ⟨2, by omega⟩)ᶜ)
    (h3len : 2 / (3 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ b - a) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  -- Contradiction: assume no lonely time in [a, b].
  by_contra hne
  push_neg at hne
  -- Every t ∈ [a, b] has some unsafe runner; by h123gap that runner ∈ {3, 4}.
  have hcover : Set.Icc a b ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪
                              unsafeOf speeds ⟨4, by omega⟩ := by
    intro t ht
    obtain ⟨i, hi⟩ := hne t
    have h123 : t ∉ unsafeOf speeds ⟨0, by omega⟩ ∪
                    unsafeOf speeds ⟨1, by omega⟩ ∪
                    unsafeOf speeds ⟨2, by omega⟩ := h123gap ht
    -- hi : circDist (v_i * t) < 1/6  ⇒  t ∈ unsafeOf i.
    have ht_unsafe : t ∈ unsafeOf speeds i := (mem_unsafeOf_iff speeds i t).mpr hi
    -- i ∉ {0,1,2} because h123 excludes those.
    fin_cases i
    · exact absurd (Or.inl (Or.inl ht_unsafe)) h123
    · exact absurd (Or.inl (Or.inr ht_unsafe)) h123
    · exact absurd (Or.inr ht_unsafe) h123
    · exact Or.inl ht_unsafe
    · exact Or.inr ht_unsafe
  -- Apply Lemma 4 to conclude b - a < 2 / (3 v_4).
  have hbnd : b - a < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    bhk_lemma_4 speeds hmono hpos a b hab hcover
  -- But v_3 < v_4 ⇒ 2 / (3 v_4) < 2 / (3 v_3) ≤ b - a.  Contradiction.
  have hv3pos : (0 : ℝ) < speeds ⟨2, by omega⟩ := by exact_mod_cast hpos _
  have hv4pos : (0 : ℝ) < speeds ⟨3, by omega⟩ := by exact_mod_cast hpos _
  have hlt : (speeds ⟨2, by omega⟩ : ℝ) < speeds ⟨3, by omega⟩ := by
    have : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ :=
      hmono (show (⟨2, by omega⟩ : Fin 5) < ⟨3, by omega⟩ by decide)
    exact_mod_cast this
  have hcmp : 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) <
              2 / (3 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  linarith

/-! ## §3 Main Lemma (torus subgroup vs rectangles) -/

/-- The 2-dimensional torus `T = [0,1)²` as a set of `ℝ × ℝ`. The Main Lemma
    quantifies over **finite cyclic subgroups** `G ⊆ T`; we encode this as a
    subset of `ℝ × ℝ` with the relevant finiteness and group-closure
    hypotheses passed in as arguments to the lemma. -/
def bhkRectangle (x₁ x₂ α β : ℝ) : Set (ℝ × ℝ) :=
  { p | 0 ≤ Int.fract (p.1 - x₁) ∧ Int.fract (p.1 - x₁) ≤ α ∧
        0 ≤ Int.fract (p.2 - x₂) ∧ Int.fract (p.2 - x₂) ≤ β }

/-- **BHK Main Lemma.** Let `G ⊆ ℝ²` be a finite cyclic subgroup mod 1 in
    each coordinate, of order `n > 1`, and let `0 < α, β < 1` with
    `α · β ≥ 1 / n`. Then `G` intersects every rectangle of width `α` and
    height `β`, modulo the two exceptional configurations described in
    BHK §3 (a small `(i, j) ∈ ℤ² \ {(0,0)}` in the appropriate box).

    *Statement is approximate;* the exact `n ≥ 2 / (αβ)` vs.
    `1/n ≤ αβ < 2/n` split from BHK is left implicit here and unfolded
    where used. -/
theorem bhk_main_lemma
    (G : Set (ℝ × ℝ)) (hG_fin : G.Finite) (n : ℕ) (hn : 1 < n)
    (hG_card : G.ncard = n)
    (α β : ℝ) (hα : 0 < α) (hα' : α < 1) (hβ : 0 < β) (hβ' : β < 1)
    (hαβ : α * β ≥ 1 / (n : ℝ)) :
    (∀ x₁ x₂, (G ∩ bhkRectangle x₁ x₂ α β).Nonempty) ∨
    (∃ ij : ℤ × ℤ, ij ≠ (0, 0) ∧
      ((ij.1 : ℝ) / n, (ij.2 : ℝ) / n) ∈ G ∧
      β * |(ij.1 : ℝ)| + α * |(ij.2 : ℝ)| - 2 / n * |(ij.1 : ℝ)| * |(ij.2 : ℝ)| < 1) := by
  sorry

/-- **BHK Corollary 6.** Applied form of the Main Lemma: either every
    `α × β` rectangle is hit, or there is a small lattice point `(i, j)`
    with `(i/n, j/n) ∈ G`. -/
theorem bhk_corollary_6
    (G : Set (ℝ × ℝ)) (hG_fin : G.Finite) (n : ℕ) (hn : 1 < n)
    (hG_card : G.ncard = n)
    (α β : ℝ) (hα : 0 < α) (hα' : α < 1) (hβ : 0 < β) (hβ' : β < 1) :
    (∀ x₁ x₂, (G ∩ bhkRectangle x₁ x₂ α β).Nonempty) ∨
    (∃ ij : ℤ × ℤ, ij ≠ (0, 0) ∧
      ((ij.1 : ℝ) / n, (ij.2 : ℝ) / n) ∈ G ∧
      0 ≤ ij.1 ∧ (ij.1 : ℝ) < 1 / β ∧
      -1 / α - β / α * ij.1 < (ij.2 : ℝ) ∧
      (ij.2 : ℝ) < 1 / α + β / α * ij.1) := by
  sorry

/-! ## §§5–8 Case branches of BHK -/

/-- **BHK §5.** Case `{v_1 t_0} = 0` under "small `v_1`" (`3 v_1 < v_3`), where
    `t_0 = 1 / (v_3 - v_2)` is the elementary period of runner 3 passing
    runner 2. Handled via specialised Main Lemma application. -/
theorem bhk_case_v1t0_zero (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK §6.** Case `{t_0} = 0` under "small `v_1`" (`3 v_1 < v_3`). -/
theorem bhk_case_t0_zero (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((1 : ℝ) / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩)) = 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK §7.** Case "small `v_1`" (`3 v_1 < v_3`) with both `{t_0} ≠ 0` and
    `{v_1 t_0} ≠ 0`. Handled by direct Main Lemma application to the standard
    `2/3 × 1/3` rectangle inside `P`. -/
theorem bhk_case_v1_small_generic (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (ht0 : Int.fract ((1 : ℝ) / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩)) ≠ 0)
    (hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) *
              (1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩))) ≠ 0) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-- **BHK §8.** Case `v_1 ≥ v_3 / 3` (in normalised terms), i.e. the smallest
    speed is comparable with `v_3`. Handled by ad hoc argument. -/
theorem bhk_case_v1_large (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

/-! ## Main theorem: combine the cases -/

/-- **BHK Theorem 2** (Six Lonely Runners), integer-speed five-mover form.
    For any `v_1 < … < v_5` positive integers with `gcd = 1`, there exists a
    real `t` with all five at circle-distance `≥ 1/6` from the origin.

    The proof dispatches on the BHK case split:
    * `v_3 ≤ 3 v_1` → `bhk_case_v1_large` (§8);
    * `3 v_1 < v_3 ≤ 4 v_1` → §7 or §5/6 depending on `{t_0}`, `{v_1 t_0}`;
    * `4 v_1 < v_3` → §5 or §6 depending on `{t_0}`, `{v_1 t_0}`. -/
theorem bhk_theorem_2 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  by_cases hlarge : speeds ⟨2, by omega⟩ ≤ 3 * speeds ⟨0, by omega⟩
  · exact bhk_case_v1_large speeds hmono hpos hgcd hlarge
  · push_neg at hlarge
    -- 3 v_1 < v_3.  Now split on {t_0}, {v_1 t_0}.
    set t₀ : ℝ := 1 / ((speeds ⟨2, by omega⟩ : ℝ) - speeds ⟨1, by omega⟩) with ht₀_def
    by_cases hv1t0 : Int.fract ((speeds ⟨0, by omega⟩ : ℝ) * t₀) = 0
    · exact bhk_case_v1t0_zero speeds hmono hpos hgcd hlarge hv1t0
    · by_cases ht0 : Int.fract t₀ = 0
      · exact bhk_case_t0_zero speeds hmono hpos hgcd hlarge ht0
      · exact bhk_case_v1_small_generic speeds hmono hpos hgcd hlarge ht0 hv1t0

end BHK

/-- Exported alias: the integer-speed n=6 Hard Case theorem.
    Cited from `IntLRC_6.lean`.  -/
theorem intLRC_six_hard (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 :=
  BHK.bhk_theorem_2 speeds hmono hpos hgcd
