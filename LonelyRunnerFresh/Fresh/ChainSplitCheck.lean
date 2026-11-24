import Mathlib
import Fresh.M4SplitAssembly

/-!
# `ChainBoxSoundPinned` from a two-window self-splitting checker (2026-11-22)

New file; nothing existing is edited.

As `Fresh.M4SplitCheck`, with the leaf's clear instant `R` allowed in `[1,7]` (the `W₀` window,
`NoCarve`) or in `[9,15]` (the `W₁` window, the second disjunct of `ChainBoxSoundPinned` with
`s = R`).  Candidates: `1`, `9`, and the exit edges `(8j+1)·2^e/a`; complete, because the least
point of a nonempty piece of the feasible set in either window is one of them.  The sub-boxes
cover the box [PROVISIONAL: covering -- supports "a clear instant for every reading vector in
the box"].
-/

namespace Fresh.ChainSplitCheck

open Fresh Fresh.Certs Fresh.M4SplitCheck Fresh.M4SplitAssembly Fresh.FilterAssembly
open Fresh.FilterAssemblyPerBox Fresh.FilterAssemblyPerBoxV2

/-- `p/q` lies in `[1,7] ∪ [9,15]`. -/
def inWin (p q : ℕ) : Bool :=
  (decide (q ≤ p) && decide (p ≤ 7 * q)) || (decide (9 * q ≤ p) && decide (p ≤ 15 * q))

def leafAt2 (p q e : ℕ) (box : List (ℕ × ℕ)) : Bool :=
  decide (0 < q) && inWin p q && box.all (fun ab => gapOK p ab.1 ab.2 (q * 2 ^ e))

def leafOK2 (e : ℕ) (box : List (ℕ × ℕ)) : Bool :=
  leafAt2 1 1 e box || leafAt2 9 1 e box ||
    box.any (fun ab => (List.range 34).any (fun j => leafAt2 ((8 * j + 1) * 2 ^ e) ab.1 e box))

def check2 : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | 0, e, box => leafOK2 e box
  | f + 1, e, box =>
      leafOK2 e box ||
        (check2 f (e + 1) (splitL (widest box) box) && check2 f (e + 1) (splitR (widest box) box))

/-- `R` is a clear instant in `[1,7] ∪ [9,15]` for every reading. -/
-- STANDING: DEFINITION
def GoodR2 (g : Fin 7 → ℝ) (R : ℝ) : Prop :=
  ((1 ≤ R ∧ R ≤ 7) ∨ (9 ≤ R ∧ R ≤ 15)) ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (R / 8))

theorem leafAt2_sound {p q e : ℕ} {box : List (ℕ × ℕ)} {g : Fin 7 → ℝ}
    (h : leafAt2 p q e box = true) (hg : InBox e box g) : GoodR2 g ((p : ℝ) / q) := by
  simp only [leafAt2, inWin, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨hq, hwin⟩, hall⟩ := h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨?_, ?_⟩
  · rcases hwin with ⟨h1, h7⟩ | ⟨h9, h15⟩
    · left
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hqpos]; simpa using (Nat.cast_le (α := ℝ)).mpr h1
      · rw [div_le_iff₀ hqpos]
        have := (Nat.cast_le (α := ℝ)).mpr h7; push_cast at this; linarith
    · right
      refine ⟨?_, ?_⟩
      · rw [le_div_iff₀ hqpos]
        have := (Nat.cast_le (α := ℝ)).mpr h9; push_cast at this; linarith
      · rw [div_le_iff₀ hqpos]
        have := (Nat.cast_le (α := ℝ)).mpr h15; push_cast at this; linarith
  · intro i
    obtain ⟨hlen, hin⟩ := hg
    have hi : (i : ℕ) < box.length := lt_of_lt_of_le i.isLt hlen
    have hmem : box.getD i (0, 0) ∈ box := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    obtain ⟨j, hj⟩ := gap_sound hq (hall _ hmem) (hin i).1 (hin i).2
    exact (clearAt_R_iff (g i) ((p : ℝ) / q)).mpr ⟨j, hj⟩

#print axioms leafAt2_sound

theorem leafOK2_sound {e : ℕ} {box : List (ℕ × ℕ)} {g : Fin 7 → ℝ}
    (h : leafOK2 e box = true) (hg : InBox e box g) : ∃ R, GoodR2 g R := by
  simp only [leafOK2, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with (h | h) | ⟨ab, -, j, -, hj⟩
  · exact ⟨_, leafAt2_sound h hg⟩
  · exact ⟨_, leafAt2_sound h hg⟩
  · exact ⟨_, leafAt2_sound hj hg⟩

theorem check2_sound (f e : ℕ) (box : List (ℕ × ℕ)) (h : check2 f e box = true)
    (g : Fin 7 → ℝ) (hg : InBox e box g) : ∃ R, GoodR2 g R := by
  induction f generalizing e box with
  | zero => exact leafOK2_sound h hg
  | succ f ih =>
    simp only [check2, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hL, hR⟩
    · exact leafOK2_sound h hg
    · rcases inBox_split (widest box) hg with hg' | hg'
      · exact ih (e + 1) _ hL hg'
      · exact ih (e + 1) _ hR hg'

#print axioms check2_sound

/-- The chain boxes are sorted lists beginning with `1`. -/
theorem chainBoxes_sorted : ∀ t ∈ chainBoxes, ((1 : ℤ) :: t).Pairwise (· ≤ ·) ∧ ∀ x ∈ t, 1 ≤ x := by
  decide +kernel

/-- **`ChainBoxSoundPinned` from the per-box verdicts.** -/
theorem chainPinned_of_check
    (H : ∀ t ∈ chainBoxes, check2 64 1 (boxOfL (((1 : ℤ) :: t).map Int.toNat) 0) = true) :
    ChainBoxSoundPinned := by
  intro n hr hc g hf ⟨i0, hi0⟩
  obtain ⟨t, ht, hms⟩ := hc
  set σ := Tuple.sort n with hσ
  set n' : Fin 7 → ℤ := n ∘ σ with hn'
  have hmono : Monotone n' := Tuple.monotone_sort n
  have hpos : ∀ i, 1 ≤ n i := fun i => (hr i).1
  have hms' : boxMS n = (List.ofFn n' : Multiset ℤ) := by
    unfold boxMS
    rw [← Fin.univ_val_map]
    rw [hn', ← Multiset.map_map, Multiset.map_univ_val_equiv]
  have hperm : List.Perm (List.ofFn n') (1 :: t) := by
    rw [← Multiset.coe_eq_coe, ← hms', hms]
  have hofFn : List.ofFn n' = 1 :: t := by
    refine List.Perm.eq_of_pairwise' ?_ (chainBoxes_sorted t ht).1 hperm
    rw [List.pairwise_ofFn]; intro i j hij; exact hmono hij.le
  set l : List ℕ := (((1 : ℤ) :: t).map Int.toNat) with hlDef
  have hlen : l.length = 7 := by
    rw [hlDef, List.length_map, ← hofFn, List.length_ofFn]
  have hget : ∀ i : Fin 7, l.getD i 0 = (n' i).toNat := by
    intro i
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
    simp only [hlDef, List.getElem_map, ← hofFn, List.getElem_ofFn]
  have hn0 : n i0 = 1 := by
    have h1 := (hf i0).1
    rw [hi0] at h1
    unfold FaceLo at h1
    have h2 : ((max (2 * n i0 - 1) 2 : ℤ) : ℝ) ≤ 2 := by linarith
    have h3 : max (2 * n i0 - 1) 2 ≤ 2 := by exact_mod_cast h2
    have := hpos i0
    omega
  set j0 : Fin 7 := σ.symm i0 with hj0
  have hσj0 : σ j0 = i0 := by simp [hj0]
  have hj0v : n' j0 = 1 := by simp [hn', Function.comp, hσj0, hn0]
  have h00 : n' 0 = 1 := by
    have := hmono (Fin.zero_le j0); have := hpos (σ 0)
    simp only [hn', Function.comp] at *; omega
  set τ : Equiv.Perm (Fin 7) := Equiv.swap 0 j0 with hτ
  have hnτ : ∀ i, n' (τ i) = n' i := by
    intro i
    rcases eq_or_ne i 0 with rfl | h0
    · simp [hτ, Equiv.swap_apply_left, hj0v, h00]
    rcases eq_or_ne i j0 with rfl | h1
    · simp [hτ, Equiv.swap_apply_right, hj0v, h00]
    · simp [hτ, Equiv.swap_apply_of_ne_of_ne h0 h1]
  set g' : Fin 7 → ℝ := fun i => g (σ (τ i)) with hg'
  have hbox : InBox 1 (boxOfL l 0) g' := by
    refine ⟨by rw [boxOfL_length, hlen], fun i => ?_⟩
    rw [boxOfL_getD l 0 i (by rw [hlen]; exact i.isLt)]
    by_cases hij : (i : ℕ) = 0
    · have hii : i = 0 := Fin.ext hij
      rw [if_pos hij]
      have : g' i = 1 := by
        rw [hii]; simp only [hg', hτ, Equiv.swap_apply_left, hσj0, hi0]
      rw [this]; norm_num
    · rw [if_neg hij, hget i, ← hnτ i]
      have hfc := face_cast (n' (τ i))
        (by have := hpos (σ (τ i)); simp only [hn', Function.comp]; omega)
      rw [hfc.1, hfc.2]
      exact hf (σ (τ i))
  obtain ⟨R, hwin, hRc⟩ := check2_sound 64 1 _ (H t ht) g' hbox
  have hclear : ∀ j, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
    intro j
    have := hRc (τ (σ.symm j))
    simpa [hg', hτ, Equiv.swap_apply_self] using this
  rcases hwin with ⟨h1, h7⟩ | ⟨h9, h15⟩
  · exact Or.inl (noCarve_of_goodR ⟨h1, h7, hclear⟩)
  · exact Or.inr ⟨R, h9, h15, hclear⟩

#print axioms chainPinned_of_check

end Fresh.ChainSplitCheck
