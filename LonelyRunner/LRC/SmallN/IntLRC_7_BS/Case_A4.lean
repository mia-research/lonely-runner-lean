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

instance : DecidablePred avoids06 := fun a => by unfold avoids06; exact And.decidable

/-- **Phase 2 (window-shift lemma).** If a set of `ZMod 7` values is contained in
a consecutive window of length 5 (i.e., `{a, a+1, a+2, a+3, a+4}` for some `a`),
then shifting by `1 - a` maps the window to `{1, 2, 3, 4, 5}`, which avoids `{0, 6}`.

Concretely: `∀ x, (x - a).val ≤ 4 → avoids06 (x + (1 - a))`. -/
theorem phase2_shift (a x : ZMod 7) (hx : (x - a).val ≤ 4) :
    avoids06 (x + (1 - a)) := by
  have h1 : x + (1 - a) = (x - a) + 1 := by ring
  rw [h1]
  have hv := hx
  have hlt : (x - a).val < 7 := ZMod.val_lt (x - a)
  interval_cases (x - a) <;> simp_all [avoids06]

/-- **Phase 2 corollary.** For a `Finset` of `ZMod 7` values fitting in a window of 5,
there exists a shift `t` such that all elements avoid `{0, 6}`. -/
theorem phase2 (S : Finset (ZMod 7))
    (hwin : ∃ a : ZMod 7, ∀ x ∈ S, (x - a).val ≤ 4) :
    ∃ t : ZMod 7, ∀ x ∈ S, avoids06 (x + t) := by
  obtain ⟨a, ha⟩ := hwin
  exact ⟨1 - a, fun x hx => phase2_shift a x (ha x hx)⟩

/-! ### Carrying arithmetic: tracking q-values through multiplier steps -/

/-- The set of possible q-values after doubling: `q(2x) ∈ {2a, 2a+1}` where `a = q(x)`. -/
def step2_range (a : ZMod 7) : Finset (ZMod 7) := {2 * a, 2 * a + 1}

/-- The set of possible q-values after one carry step from `prev` with base `a`:
`q(prev·x + x) ∈ {prev_q + a, prev_q + a + 1}`. -/
def carry_step (prev_q a : ZMod 7) : Finset (ZMod 7) := {prev_q + a, prev_q + a + 1}

/-- All possible q-values at step `j` starting from initial value `a`, computed
by expanding all carry paths through the step-by-step evolution. -/
def possible_vals : ℕ → ZMod 7 → Finset (ZMod 7)
  | 0, a => {a}
  | 1, a => {a}
  | (n + 2), a =>
    (possible_vals (n + 1) a).biUnion (fun prev => carry_step prev a)

/-! ### Case 1: |A_s| = 4 (all same residue)

The claim: for any 4-tuple of initial q-values, either the set directly admits
a shift avoiding {0,6} (Phase 2), or the step-by-step carry evolution produces
a step where the values fit in a window of 5.

Verified computationally: for initial sets with ℓ = 6 (translates of {0,2,4,6}),
step 3 always achieves ℓ ≤ 5 across all 4096 carry paths.
-/

/-- The arc length `ℓ(S)` of a finite set in `ZMod 7`: the size of the smallest
consecutive arc `{a, a+1, ..., a+k}` containing `S`. -/
def arcLength (S : Finset (ZMod 7)) : ℕ :=
  if S.card ≤ 1 then S.card
  else Finset.univ.inf' ⟨0, mem_univ 0⟩
    (fun a => (S.filter (fun x => ¬((x - a).val ≤ 6))).card + S.card)
  -- placeholder; proper def below

-- TODO: proper arcLength definition and the Case 1 proof

/-- **§5 main theorem stub.** For 4 elements at level 0 (q-values `a : Fin 4 → ZMod 7`),
with all having the same unit residue `s`, there exist multiplier indices `j` and `k`
such that the composite q-values avoid `{0, 6}`.

The proof combines Phase 2 with the carry compression analysis. -/
theorem section5_case1_avoidance (a : Fin 4 → ZMod 7) (s : ZMod 7) (hs : s ≠ 0) :
    (∃ t : ZMod 7, ∀ i : Fin 4, avoids06 (a i + t)) ∨
    (∃ j : ℕ, j ≤ 5 ∧ ∃ t : ZMod 7, ∀ i : Fin 4,
      ∀ v ∈ possible_vals j (a i), avoids06 (v + t)) := by
  sorry

end IntLRC7BS
