import Mathlib
import Fresh.M4SplitCheck
import Fresh.FilterAssemblyPerBoxV2

/-!
# `M4BoxNoCarvePinned` from the self-splitting checker (2026-11-22)

New file; nothing existing is edited.

`checkT l` (for a sorted 7-tuple `l` of box indices) is `true` when `l` is one of the 73 chain
boxes, or when for every coordinate `p` with `l_p = 1` the pinned box (`g_p = 1`) passes
`check 64 1`.  `m4Pinned_of_checkT` proves `M4BoxNoCarvePinned` from `checkT` on every sorted
tuple of `[1,17]^7` containing `1`; `gen_complete` reduces that to the generator `gen`, which
the chunk files decide by kernel evaluation.  The hypothesis `¬ M1Cond n` is not used: the
checker covers the M1 boxes too.
-/

namespace Fresh.M4SplitAssembly

open Fresh Fresh.Certs Fresh.M4SplitCheck Fresh.FilterAssembly Fresh.FilterAssemblyPerBox
open Fresh.FilterAssemblyPerBoxV2

/-! ## Tuples, the generator, the initial boxes -/

/-- Nondecreasing lists of length `k` with entries in `[lo, 17]`. -/
def gen : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | k + 1, lo => (List.range' lo (18 - lo)).flatMap (fun v => (gen k v).map (fun t => v :: t))

theorem gen_complete (l : List ℕ) (lo : ℕ) (hs : l.Pairwise (· ≤ ·))
    (hr : ∀ x ∈ l, lo ≤ x ∧ x ≤ 17) : l ∈ gen l.length lo := by
  induction l generalizing lo with
  | nil => simp [gen]
  | cons v t ih =>
    rw [List.pairwise_cons] at hs
    have hv := hr v (by simp)
    have ht : t ∈ gen t.length v :=
      ih v hs.2 (fun x hx => ⟨hs.1 x hx, (hr x (by simp [hx])).2⟩)
    simp only [List.length_cons, gen, List.mem_flatMap, List.mem_map, List.mem_range'_1]
    exact ⟨v, ⟨hv.1, by omega⟩, t, ht, rfl⟩

/-- The face of box index `v`: `[max(2v−1,2), 2v+1]` over `2`. -/
def faceOf (v : ℕ) : ℕ × ℕ := (max (2 * v - 1) 2, 2 * v + 1)

/-- The box of tuple `l` with coordinate `p` pinned to `[2,2]/2 = {1}`. -/
def boxOfL : List ℕ → ℕ → List (ℕ × ℕ)
  | [], _ => []
  | _ :: t, 0 => (2, 2) :: t.map faceOf
  | v :: t, p + 1 => faceOf v :: boxOfL t p

theorem boxOfL_length (l : List ℕ) (p : ℕ) : (boxOfL l p).length = l.length := by
  induction l generalizing p with
  | nil => cases p <;> rfl
  | cons v t ih => cases p <;> simp [boxOfL, ih]

theorem boxOfL_getD (l : List ℕ) (p i : ℕ) (hi : i < l.length) :
    (boxOfL l p).getD i (0, 0) = if i = p then (2, 2) else faceOf (l.getD i 0) := by
  induction l generalizing p i with
  | nil => simp at hi
  | cons v t ih =>
    cases p with
    | zero =>
      cases i with
      | zero => simp only [boxOfL, List.getD_cons_zero, if_true]
      | succ i =>
        simp only [List.length_cons] at hi
        simp only [boxOfL, List.getD_cons_succ]
        rw [if_neg (Nat.succ_ne_zero i)]
        rw [List.getD_eq_getElem _ _ (by simpa using (show i < t.length by omega)),
          List.getD_eq_getElem _ _ (show i < t.length by omega), List.getElem_map]
    | succ p =>
      cases i with
      | zero =>
        simp only [boxOfL, List.getD_cons_zero]; rw [if_neg (Nat.zero_ne_add_one p)]
      | succ i =>
        simp only [List.length_cons] at hi
        simp only [boxOfL, List.getD_cons_succ]
        rw [ih p i (by omega)]
        by_cases h : i = p
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]

/-- `l` (with its leading `1`) is one of the 73 chain boxes. -/
def isChainL (l : List ℕ) : Bool :=
  chainBoxes.any (fun t => decide (l.map (fun x : ℕ => (x : ℤ)) = (1 : ℤ) :: t))

/-- The boxes (sorted 7-tuples of box indices) on which the self-splitting checker does not
terminate: a point of the box where every clear instant is pinched (log E925).  Filled from
`experiments/n8/m4_fixedpoint_split_v1_retry3.jsonl` (status STALL). -/
def stallBoxes : List (List ℕ) := []

/-- **OWED — the stall boxes.**  `M4BoxNoCarvePinned` restricted to the boxes of `stallBoxes`. -/
-- STANDING: OWED
def StallBoxesNoCarvePinned : Prop :=
  ∀ n : Fin 7 → ℤ, InRange17 n → (∃ t ∈ stallBoxes, boxMS n = ((t.map (fun x : ℕ => (x : ℤ))) : Multiset ℤ)) →
    ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) → (∃ i, g i = 1) → NoCarve g

/-- The per-tuple verdict.  Only the pin at coordinate `0` is checked: in a sorted tuple every
coordinate with index value `1` has the same face, so the proof swaps the pinned coordinate
into position `0`. -/
def checkT (l : List ℕ) : Bool :=
  isChainL l || decide (l ∈ stallBoxes) || check 64 1 (boxOfL l 0)

/-! ## From `checkT` on sorted tuples to the OWED prop -/

theorem face_cast (m : ℤ) (hm : 1 ≤ m) :
    (((faceOf m.toNat).1 : ℕ) : ℝ) / 2 ^ 1 = ((max (2 * m - 1) 2 : ℤ) : ℝ) / 2 ∧
    (((faceOf m.toNat).2 : ℕ) : ℝ) / 2 ^ 1 = ((2 * m + 1 : ℤ) : ℝ) / 2 := by
  have ht : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
  have h1 : (((max (2 * m.toNat - 1) 2 : ℕ)) : ℤ) = max (2 * m - 1) 2 := by
    rw [Nat.cast_max]; push_cast [Nat.cast_sub (show 1 ≤ 2 * m.toNat by omega)]; rw [ht]
  have h2 : (((2 * m.toNat + 1 : ℕ)) : ℤ) = 2 * m + 1 := by push_cast; rw [ht]
  refine ⟨?_, ?_⟩
  · simp only [faceOf, pow_one]
    rw [← Int.cast_natCast, h1]
  · simp only [faceOf, pow_one]
    rw [← Int.cast_natCast, h2]

/-- **`M4BoxNoCarvePinned` from the per-tuple verdicts.** -/
theorem m4Pinned_of_checkT (hstall : StallBoxesNoCarvePinned)
    (hall : ∀ l : List ℕ, l.length = 7 → l.Pairwise (· ≤ ·) → (∀ x ∈ l, 1 ≤ x ∧ x ≤ 17) →
      1 ∈ l → checkT l = true) :
    M4BoxNoCarvePinned := by
  intro n hr hl _hm hc g hf ⟨i0, hi0⟩
  set σ := Tuple.sort n with hσ
  set n' : Fin 7 → ℤ := n ∘ σ with hn'
  have hmono : Monotone n' := Tuple.monotone_sort n
  set l : List ℕ := List.ofFn (fun i => (n' i).toNat) with hlDef
  have hlen : l.length = 7 := by simp [hlDef]
  have hget : ∀ i : Fin 7, l.getD i 0 = (n' i).toNat := by
    intro i
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact i.isLt)]
    simp only [hlDef, List.getElem_ofFn]
  have hpos : ∀ i, 1 ≤ n i := fun i => (hr i).1
  -- the tuple's properties
  have hsorted : l.Pairwise (· ≤ ·) := by
    rw [hlDef, List.pairwise_ofFn]
    intro i j hij
    exact Int.toNat_le_toNat (hmono hij.le)
  have hrange : ∀ x ∈ l, 1 ≤ x ∧ x ≤ 17 := by
    intro x hx
    rw [hlDef, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hr (σ i); simp only [hn', Function.comp]; omega
  -- the pinned coordinate has index value 1
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
  have hl1 : 1 ∈ l := by
    rw [hlDef, List.mem_ofFn]; exact ⟨j0, by simp [hn', Function.comp, hσj0, hn0]⟩
  have hchk := hall l hlen hsorted hrange hl1
  simp only [checkT, Bool.or_eq_true, decide_eq_true_eq] at hchk
  have hmapl : l.map (fun x : ℕ => (x : ℤ)) = List.ofFn n' := by
    rw [hlDef, List.map_ofFn]
    congr 1; funext i
    simp only [Function.comp]
    exact Int.toNat_of_nonneg (by have := hpos (σ i); simp only [hn', Function.comp]; omega)
  have hms : boxMS n = (List.ofFn n' : Multiset ℤ) := by
    unfold boxMS
    rw [← Fin.univ_val_map]
    rw [hn', ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rcases hchk with (hch | hst) | hp
  · -- a chain box: contradicts `¬ IsChainBox n`
    exfalso; apply hc
    simp only [isChainL, List.any_eq_true, decide_eq_true_eq] at hch
    obtain ⟨t, ht, heq⟩ := hch
    exact ⟨t, ht, by rw [hms, ← hmapl, heq]⟩
  · -- a stall box: the OWED residue
    exact hstall n hr ⟨l, hst, by rw [hms, ← hmapl]⟩ g hf ⟨i0, hi0⟩
  · -- the box pinned at coordinate 0 passes the checker; move the pin there
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
    obtain ⟨R, hR1, hR7, hRc⟩ := check_sound 64 1 _ hp g' hbox
    refine noCarve_of_goodR (R := R) ⟨hR1, hR7, fun j => ?_⟩
    have := hRc (τ (σ.symm j))
    simpa [hg', hτ, Equiv.swap_apply_self] using this

#print axioms m4Pinned_of_checkT

/-- The sorted tuples containing `1` are `1 :: v :: w :: t` with `t ∈ gen 4 w`. -/
theorem all_of_chunks
    (hch : ∀ v w : ℕ, 1 ≤ v → v ≤ w → w ≤ 17 → ∀ t ∈ gen 4 w, checkT (1 :: v :: w :: t) = true) :
    ∀ l : List ℕ, l.length = 7 → l.Pairwise (· ≤ ·) → (∀ x ∈ l, 1 ≤ x ∧ x ≤ 17) →
      1 ∈ l → checkT l = true := by
  intro l hlen hs hr h1
  match l, hlen with
  | a :: v :: w :: t, hlen =>
    have hlt : t.length = 4 := by simp at hlen; omega
    have hs' := hs
    simp only [List.pairwise_cons, List.mem_cons] at hs'
    have ha : a = 1 := by
      have ha1 := (hr a (by simp)).1
      rcases List.mem_cons.mp h1 with h | h
      · omega
      · have := hs'.1 1 (by simp only [List.mem_cons] at h; exact h)
        omega
    subst ha
    have hvw : v ≤ w := hs'.2.1 w (Or.inl rfl)
    have hv := hr v (by simp)
    have hw := hr w (by simp)
    have htg : t ∈ gen 4 w := by
      have := gen_complete t w (by simpa using hs'.2.2.2)
        (fun x hx => ⟨hs'.2.2.1 x hx, (hr x (by simp [hx])).2⟩)
      rwa [hlt] at this
    exact hch v w hv.1 hvw hw.2 t htg

#print axioms all_of_chunks

end Fresh.M4SplitAssembly
