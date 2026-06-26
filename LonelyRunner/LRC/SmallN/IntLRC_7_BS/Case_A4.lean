import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Defs
import Mathlib.Algebra.Field.ZMod

/-!
# n = 7 (Barajas–Serra) — §5, the case `|A| = 4`

Source: `sources_barajas_serra_2008.txt`, lines 267–363.

The core combinatorial engine: for any 4 elements at level 0, there exist
multiplier coefficients placing all q-values outside `{0, 6}` in `ZMod 7`.

## Strategy

The argument has two phases:
1. **Compression**: show that at some Λ-multiplier step, the q-values fit in
   a consecutive arc of length ≤ 5 in `ZMod 7` (i.e., `ℓ ≤ 5`).
2. **Phase 2 (shifting)**: any set fitting in a window of 5 can be shifted
   (via a Λ₀ multiplier) to avoid `{0, 6}`.

Phase 1 uses the carry lemma (`qz_add_carry`): `q(x+y) ∈ {q(x)+q(y), q(x)+q(y)+1}`.
Applied step by step, this tracks possible q-values through multiplier applications.
The paper's three cases (|A_s| ∈ {4, 3, 2}) each show compression holds within
5 steps, by a finite case chase over `ZMod 7`.
-/

open Finset

namespace IntLRC7BS

/-! ### Phase 2: shifting a compressed set to avoid {0, 6} -/

/-- A value `a ∈ ZMod 7` **avoids** the forbidden set `{0, 6}`. -/
def avoids06 (a : ZMod 7) : Prop := a ≠ 0 ∧ a ≠ 6

instance : DecidablePred avoids06 :=
  fun a => inferInstanceAs (Decidable (a ≠ 0 ∧ a ≠ 6))

/-- **Phase 2 (window-shift lemma).** If a set of `ZMod 7` values is contained in
a consecutive window of length 5 (i.e., `{a, a+1, a+2, a+3, a+4}` for some `a`),
then shifting by `1 - a` maps the window to `{1, 2, 3, 4, 5}`, which avoids `{0, 6}`.

Concretely: `∀ x, (x - a).val ≤ 4 → avoids06 (x + (1 - a))`. -/
theorem phase2_shift (a x : ZMod 7) (hx : (x - a).val ≤ 4) :
    avoids06 (x + (1 - a)) := by
  have h1 : x + (1 - a) = (x - a) + 1 := by ring
  rw [h1]
  -- Reduce to a finite decidable check over the value `d = x - a`.
  have key : ∀ d : ZMod 7, d.val ≤ 4 → avoids06 (d + 1) := by decide
  exact key (x - a) hx

/-- **Phase 2 corollary.** For a `Finset` of `ZMod 7` values fitting in a window of 5,
there exists a shift `t` such that all elements avoid `{0, 6}`. -/
theorem phase2 (S : Finset (ZMod 7))
    (hwin : ∃ a : ZMod 7, ∀ x ∈ S, (x - a).val ≤ 4) :
    ∃ t : ZMod 7, ∀ x ∈ S, avoids06 (x + t) := by
  obtain ⟨a, ha⟩ := hwin
  exact ⟨1 - a, fun x hx => phase2_shift a x (ha x hx)⟩

/-! ### Compression predicate: `ℓ(S) ≤ 5` -/

/-- `S` fits in a consecutive arc of length 5 in `ZMod 7` (i.e. `ℓ(S) ≤ 5`):
some `a` has every element within `{a, a+1, a+2, a+3, a+4}`. Decidable. -/
def fitsWindow5 (S : Finset (ZMod 7)) : Prop :=
  ∃ a : ZMod 7, ∀ x ∈ S, (x - a).val ≤ 4

instance (S : Finset (ZMod 7)) : Decidable (fitsWindow5 S) := by
  unfold fitsWindow5; infer_instance

/-- **Phase 2 in window form.** A 4-tuple whose value set fits in a window of 5
admits a shift `t` placing every coordinate outside `{0, 6}`. Bridges the
compression conclusion (`fitsWindow5`) to the avoidance goal. -/
theorem avoidance_of_fitsWindow5 (q : Fin 4 → ZMod 7)
    (h : fitsWindow5 (Finset.image q Finset.univ)) :
    ∃ t : ZMod 7, ∀ i : Fin 4, avoids06 (q i + t) := by
  obtain ⟨t, ht⟩ := phase2 (Finset.image q Finset.univ)
    (by obtain ⟨a, ha⟩ := h; exact ⟨a, ha⟩)
  exact ⟨t, fun i => ht (q i) (Finset.mem_image_of_mem q (Finset.mem_univ i))⟩

/-- Tuple form of `fitsWindow5` (no `Finset`, so kernel-`decide`-friendly): the
four coordinates `q i` lie in a common window of 5. -/
def fits4 (q : Fin 4 → ZMod 7) : Prop := ∃ a : ZMod 7, ∀ i, (q i - a).val ≤ 4

instance : DecidablePred fits4 := fun q => by unfold fits4; infer_instance

/-- `fits4` agrees with `fitsWindow5` on the image of a 4-tuple. -/
theorem fits4_iff (q : Fin 4 → ZMod 7) :
    fits4 q ↔ fitsWindow5 (Finset.image q Finset.univ) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun x hx => ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ha i
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i => ha (q i) (Finset.mem_image_of_mem q (Finset.mem_univ i))⟩

/-- **Translation invariance.** Shifting every coordinate by a constant `c`
preserves `fits4` (the window center moves by `c`). -/
theorem fits4_translate (q : Fin 4 → ZMod 7) (c : ZMod 7) :
    fits4 (fun i => q i + c) ↔ fits4 q := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a - c, fun i => ?_⟩
    have h := ha i
    rw [show q i - (a - c) = q i + c - a by ring]
    exact h
  · rintro ⟨a, ha⟩
    refine ⟨a + c, fun i => ?_⟩
    have h := ha i
    show ((q i + c) - (a + c)).val ≤ 4
    rw [show q i + c - (a + c) = q i - a by ring]
    exact h

-- `decide` over the 343 × 256 representatives needs a raised heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- **Case 1 finite core (translation representative).** With the base normalized
to `a 0 = 0` (so `a = ![0, x, y, z]`), one of steps 1, 2, 3 compresses to a window
of 5, for every choice of carry bits. Proved by `decide` over the `7³ × 2⁴ × 2⁴`
representatives (the full `7⁴` space is recovered by `fits4_translate`). -/
theorem case1_decide (x y z : ZMod 7) (b2 b3 : Fin 4 → Bool) :
    fits4 ![0, x, y, z] ∨
    fits4 (fun i => 2 * (![0, x, y, z] : Fin 4 → ZMod 7) i + (if b2 i then 1 else 0)) ∨
    fits4 (fun i => 3 * (![0, x, y, z] : Fin 4 → ZMod 7) i
      + (if b2 i then 1 else 0) + (if b3 i then 1 else 0)) := by
  revert x y z b2 b3
  decide

/-! ### Case 1: |A_s| = 4 (all same residue `s`)

`q(λ'_j · d_i)` evolves by the correlated carry recurrence (Barajas–Serra eq (9),
formalized by `qz_add_carry`): since `λ'_{j+1}·d = λ'_j·d + λ'_1·d`,
`q(λ'_{j+1}·d_i) ∈ {q(λ'_j·d_i) + a_i, q(λ'_j·d_i) + a_i + 1}` where `a_i = q(λ'_1·d_i)`.

**Claim (compression):** for any base `a` and any carry-consistent sequence `Q`,
some step `j ∈ {1,…,5}` has `fitsWindow5 {Q j i}`. Then `avoidance_of_fitsWindow5`
+ the `k·s` shift (eq (10), `s` a unit) finishes.

Verified computationally (`scratchpad/verify_case1_v2.py`): for every ℓ=6 initial
set (the 7 translates of `{0,2,4,6}`, all orderings), every carry path reaches
`fitsWindow5` by step 3. The reduction to `{0,2,4,6}` is justified by
translation-invariance of the recurrence: replacing `a` by `a - t` and `Q j` by
`Q j - j·t` preserves both the recurrence and `fitsWindow5` (translation-invariant).
-/

/-- One deterministic carry step: `Q' i = Q i + a i + (carry bit)`. -/
def carryStep (a : Fin 4 → ZMod 7) (b : Fin 4 → Bool) (Q : Fin 4 → ZMod 7) :
    Fin 4 → ZMod 7 :=
  fun i => Q i + a i + (if b i then 1 else 0)

/-- **Case 1 compression (the §5 combinatorial core).** For the same-residue base
`a` and any correlated carry sequence `Q` (`Q 1 = a`, each next step adds `a i`
plus a 0/1 carry per coordinate), some step `j ∈ {1,…,5}` compresses to a window
of 5. Computationally verified; proof via the translation reduction to `{0,2,4,6}`
then a finite check over the 24 orderings × 16² carry choices. -/
theorem case1_compresses (a : Fin 4 → ZMod 7)
    (Q : ℕ → Fin 4 → ZMod 7) (hQ1 : Q 1 = a)
    (hstep : ∀ j, 1 ≤ j → ∃ b : Fin 4 → Bool, Q (j + 1) = carryStep a b (Q j)) :
    ∃ j, 1 ≤ j ∧ j ≤ 5 ∧ fitsWindow5 (Finset.image (Q j) Finset.univ) := by
  classical
  obtain ⟨b2, hb2⟩ := hstep 1 le_rfl
  obtain ⟨b3, hb3⟩ := hstep 2 (by norm_num)
  -- translation constant normalizing `a 0` to `0`
  set c : ZMod 7 := - a 0 with hc
  have ha0 : a 0 + c = 0 := by rw [hc]; ring
  -- representative: `(fun i => a i + c) = ![0, a 1 + c, a 2 + c, a 3 + c]`
  have hrep : ∀ i, (![0, a 1 + c, a 2 + c, a 3 + c] : Fin 4 → ZMod 7) i = a i + c := by
    intro i; fin_cases i <;> simp [ha0]
  -- explicit values at steps 2 and 3 (carry recurrence)
  have hQ2 : Q 2 = fun i => a i + a i + (if b2 i then (1 : ZMod 7) else 0) := by
    rw [hb2, hQ1]; funext i; simp [carryStep]
  have hQ3 : Q 3 = fun i =>
      a i + a i + (if b2 i then (1 : ZMod 7) else 0) + a i
        + (if b3 i then (1 : ZMod 7) else 0) := by
    rw [hb3, hQ2]; funext i; simp [carryStep]
  -- the finite compression fact for the representative
  rcases case1_decide (a 1 + c) (a 2 + c) (a 3 + c) b2 b3 with h1 | h2 | h3
  · -- step 1
    refine ⟨1, le_rfl, by norm_num, ?_⟩
    rw [← fits4_iff, hQ1, ← fits4_translate a c]
    have : (fun i => a i + c) = (![0, a 1 + c, a 2 + c, a 3 + c] : Fin 4 → ZMod 7) := by
      funext i; rw [hrep]
    rw [this]; exact h1
  · -- step 2
    refine ⟨2, by norm_num, by norm_num, ?_⟩
    rw [← fits4_iff, hQ2]
    have hfun : (fun i => 2 * (![0, a 1 + c, a 2 + c, a 3 + c] : Fin 4 → ZMod 7) i
          + (if b2 i then (1 : ZMod 7) else 0))
        = (fun i => (a i + a i + (if b2 i then (1 : ZMod 7) else 0)) + 2 * c) := by
      funext i; rw [hrep]; ring
    rw [hfun] at h2
    exact (fits4_translate _ (2 * c)).mp h2
  · -- step 3
    refine ⟨3, by norm_num, by norm_num, ?_⟩
    rw [← fits4_iff, hQ3]
    have hfun : (fun i => 3 * (![0, a 1 + c, a 2 + c, a 3 + c] : Fin 4 → ZMod 7) i
          + (if b2 i then (1 : ZMod 7) else 0) + (if b3 i then (1 : ZMod 7) else 0))
        = (fun i => (a i + a i + (if b2 i then (1 : ZMod 7) else 0) + a i
            + (if b3 i then (1 : ZMod 7) else 0)) + 3 * c) := by
      funext i; rw [hrep]; ring
    rw [hfun] at h3
    exact (fits4_translate _ (3 * c)).mp h3

end IntLRC7BS
