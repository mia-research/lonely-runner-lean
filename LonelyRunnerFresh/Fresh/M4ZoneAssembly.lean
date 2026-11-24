import Mathlib
import Fresh.ZoneCover
import Fresh.M4SplitAssembly
import Fresh.ChainSplitCheck

/-!
# `M4BoxNoCarvePinned` and `ChainBoxSoundPinned` from gap-pattern zone certificates (2026-11-22)

New file; nothing existing is edited.

The per-tuple verdict `zverdict l c` is `true` when `l` is a chain box, or when the zone
certificate `c` covers the box of `l` pinned at coordinate `0` (`Fresh.ZoneCover.zc` with
`w = 0`: a clear instant `R ∈ [1,7]`).  `m4Pinned_of_zone` proves `M4BoxNoCarvePinned` from a
verdict on every sorted tuple of `[1,17]^7` containing `1`, by the same sort-and-swap argument
as `Fresh.M4SplitAssembly.m4Pinned_of_checkT`.  There is no stall residue: the zone checker cuts
along the ratio hyperplanes `g_s/g_r = c` on which the fixed-instant checker stalled.

`chainPinned_of_zone`: the same with `w = 1` (reading `0` in the gap of index `0` or `1`, i.e.
`R ∈ [1,7]` or `R ∈ [9,15]`) on the 73 chain boxes.

`zchunk v w x cs`: the verdicts on the tuples `1 :: v :: w :: x :: t`, `t ∈ gen 3 x`, against
the certificate list `cs` in the same order.
-/

namespace Fresh.M4ZoneAssembly

open Fresh Fresh.Certs Fresh.M4SplitCheck Fresh.M4SplitAssembly Fresh.FilterAssembly
open Fresh.FilterAssemblyPerBox Fresh.FilterAssemblyPerBoxV2 Fresh.ZoneCover

/-- The per-tuple verdict. -/
def zverdict (l : List ℕ) (c : ZT) : Bool := isChainL l || zc 0 c (rootZ (boxOfL l 0))

theorem faceLo_pos (n : Fin 7 → ℤ) (i : Fin 7) : 0 < FaceLo n i := by
  unfold FaceLo
  have : (2 : ℝ) ≤ ((max (2 * n i - 1) 2 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
  linarith

/-- **`M4BoxNoCarvePinned` from the per-tuple zone verdicts.** -/
theorem m4Pinned_of_zone
    (hall : ∀ l : List ℕ, l.length = 7 → l.Pairwise (· ≤ ·) → (∀ x ∈ l, 1 ≤ x ∧ x ≤ 17) →
      1 ∈ l → ∃ c, zverdict l c = true) :
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
  have hsorted : l.Pairwise (· ≤ ·) := by
    rw [hlDef, List.pairwise_ofFn]
    intro i j hij
    exact Int.toNat_le_toNat (hmono hij.le)
  have hrange : ∀ x ∈ l, 1 ≤ x ∧ x ≤ 17 := by
    intro x hx
    rw [hlDef, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := hr (σ i); simp only [hn', Function.comp]; omega
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
  obtain ⟨c, hchk⟩ := hall l hlen hsorted hrange hl1
  simp only [zverdict, Bool.or_eq_true] at hchk
  have hmapl : l.map (fun x : ℕ => (x : ℤ)) = List.ofFn n' := by
    rw [hlDef, List.map_ofFn]
    congr 1; funext i
    simp only [Function.comp]
    exact Int.toNat_of_nonneg (by have := hpos (σ i); simp only [hn', Function.comp]; omega)
  have hms : boxMS n = (List.ofFn n' : Multiset ℤ) := by
    unfold boxMS
    rw [← Fin.univ_val_map]
    rw [hn', ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rcases hchk with hch | hp
  · exfalso; apply hc
    simp only [isChainL, List.any_eq_true, decide_eq_true_eq] at hch
    obtain ⟨t, ht, heq⟩ := hch
    exact ⟨t, ht, by rw [hms, ← hmapl, heq]⟩
  · have hj0v : n' j0 = 1 := by simp [hn', Function.comp, hσj0, hn0]
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
    have hg'0 : g' 0 = 1 := by simp only [hg', hτ, Equiv.swap_apply_left, hσj0, hi0]
    have hgpos : ∀ i, 0 < g' i := fun i => lt_of_lt_of_le (faceLo_pos n _) (hf (σ (τ i))).1
    have hbox : InBox 1 (boxOfL l 0) g' := by
      refine ⟨by rw [boxOfL_length, hlen], fun i => ?_⟩
      rw [boxOfL_getD l 0 i (by rw [hlen]; exact i.isLt)]
      by_cases hij : (i : ℕ) = 0
      · have hii : i = 0 := Fin.ext hij
        rw [if_pos hij, hii, hg'0]; norm_num
      · rw [if_neg hij, hget i, ← hnτ i]
        have hfc := face_cast (n' (τ i))
          (by have := hpos (σ (τ i)); simp only [hn', Function.comp]; omega)
        rw [hfc.1, hfc.2]
        exact hf (σ (τ i))
    obtain ⟨R, hR1, hR7, hRc⟩ := zc_goodR c _ hp g' hbox hgpos hg'0
    refine noCarve_of_goodR (R := R) ⟨hR1, hR7, fun j => ?_⟩
    have := hRc (τ (σ.symm j))
    simpa [hg', hτ, Equiv.swap_apply_self] using this

#print axioms m4Pinned_of_zone

/-! ## Chunks -/

/-- The verdicts on `1 :: v :: w :: x :: t`, `t ∈ gen 3 x`, against certificates in order. -/
def zchunk (v w x : ℕ) (cs : List ZT) : Bool :=
  decide ((gen 3 x).length = cs.length) &&
    (List.zip (gen 3 x) cs).all (fun p => zverdict (1 :: v :: w :: x :: p.1) p.2)

theorem zip_all {α β : Type} (P : α → β → Bool) :
    ∀ (L : List α) (C : List β), L.length = C.length →
      (List.zip L C).all (fun p => P p.1 p.2) = true → ∀ a ∈ L, ∃ b, P a b = true
  | [], _, _, _, a, ha => by simp at ha
  | a0 :: L, [], h, _, _, _ => by simp at h
  | a0 :: L, b0 :: C, h, hall, a, ha => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨b0, hall.1⟩
    · exact zip_all P L C (by simpa using h) hall.2 a ha'

/-- The 969 chunk indices `1 ≤ v ≤ w ≤ x ≤ 17`. -/
def trip : List (ℕ × ℕ × ℕ) :=
  (List.range' 1 17).flatMap (fun v => (List.range' v (18 - v)).flatMap
    (fun w => (List.range' w (18 - w)).map (fun x => (v, w, x))))

theorem mem_trip {v w x : ℕ} (h1 : 1 ≤ v) (h2 : v ≤ w) (h3 : w ≤ x) (h4 : x ≤ 17) :
    (v, w, x) ∈ trip := by
  simp only [trip, List.mem_flatMap, List.mem_map, List.mem_range'_1]
  exact ⟨v, ⟨h1, by omega⟩, w, ⟨h2, by omega⟩, x, ⟨h3, by omega⟩, rfl⟩

theorem mem_gen_succ {k lo : ℕ} {t : List ℕ} (h : t ∈ gen (k + 1) lo) :
    ∃ x t', lo ≤ x ∧ x ≤ 17 ∧ t' ∈ gen k x ∧ t = x :: t' := by
  simp only [gen, List.mem_flatMap, List.mem_map, List.mem_range'_1] at h
  obtain ⟨x, ⟨h1, h2⟩, t', ht', rfl⟩ := h
  exact ⟨x, t', h1, by omega, ht', rfl⟩

/-- Sorted tuples containing `1` are `1 :: v :: w :: t`, `t ∈ gen 4 w`. -/
theorem all_sorted_of (P : List ℕ → Prop)
    (hch : ∀ v w : ℕ, 1 ≤ v → v ≤ w → w ≤ 17 → ∀ t ∈ gen 4 w, P (1 :: v :: w :: t)) :
    ∀ l : List ℕ, l.length = 7 → l.Pairwise (· ≤ ·) → (∀ x ∈ l, 1 ≤ x ∧ x ≤ 17) →
      1 ∈ l → P l := by
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

/-- **`M4BoxNoCarvePinned` from the 969 chunk verdicts.** -/
theorem m4Pinned_of_zchunks (H : ∀ p ∈ trip, ∃ cs, zchunk p.1 p.2.1 p.2.2 cs = true) :
    M4BoxNoCarvePinned := by
  refine m4Pinned_of_zone (all_sorted_of _ ?_)
  intro v w hv hvw hw t ht
  obtain ⟨x, t', hwx, hx, ht', rfl⟩ := mem_gen_succ ht
  obtain ⟨cs, hcs⟩ := H (v, w, x) (mem_trip hv hvw hwx hx)
  simp only [zchunk, Bool.and_eq_true, decide_eq_true_eq] at hcs
  exact zip_all (fun t c => zverdict (1 :: v :: w :: x :: t) c) _ _ hcs.1 hcs.2 t' ht'

#print axioms m4Pinned_of_zchunks

/-! ## The chain boxes (`w = 1`) -/

theorem zc_goodR2 (t : ZT) (box : List (ℕ × ℕ)) (h : zc 1 t (rootZ box) = true)
    (g : Fin 7 → ℝ) (hb : InBox 1 box g) (hg : ∀ i, 0 < g i) (h0 : g 0 = 1) :
    ∃ R, Fresh.ChainSplitCheck.GoodR2 g R := by
  obtain ⟨R, hall, k, hk, h1, h7⟩ := zc_sound 1 t _ h g hg (rootZ_valid hb)
  rw [h0, one_mul] at h1 h7
  refine ⟨R, ?_, fun i => (clearAt_R_iff (g i) R).mpr (hall i)⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl | rfl
  · left; constructor <;> push_cast at h1 h7 <;> linarith
  · right; constructor <;> push_cast at h1 h7 <;> linarith

#print axioms zc_goodR2

/-- **`ChainBoxSoundPinned` from the per-box zone verdicts (`w = 1`).** -/
theorem chainPinned_of_zone
    (H : ∀ t ∈ chainBoxes, ∃ c, zc 1 c (rootZ (boxOfL (((1 : ℤ) :: t).map Int.toNat) 0)) = true) :
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
    refine List.Perm.eq_of_pairwise' ?_ (Fresh.ChainSplitCheck.chainBoxes_sorted t ht).1 hperm
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
  have hg'0 : g' 0 = 1 := by simp only [hg', hτ, Equiv.swap_apply_left, hσj0, hi0]
  have hgpos : ∀ i, 0 < g' i := fun i => lt_of_lt_of_le (faceLo_pos n _) (hf (σ (τ i))).1
  have hbox : InBox 1 (boxOfL l 0) g' := by
    refine ⟨by rw [boxOfL_length, hlen], fun i => ?_⟩
    rw [boxOfL_getD l 0 i (by rw [hlen]; exact i.isLt)]
    by_cases hij : (i : ℕ) = 0
    · have hii : i = 0 := Fin.ext hij
      rw [if_pos hij, hii, hg'0]; norm_num
    · rw [if_neg hij, hget i, ← hnτ i]
      have hfc := face_cast (n' (τ i))
        (by have := hpos (σ (τ i)); simp only [hn', Function.comp]; omega)
      rw [hfc.1, hfc.2]
      exact hf (σ (τ i))
  obtain ⟨c, hcert⟩ := H t ht
  obtain ⟨R, hwin, hRc⟩ := zc_goodR2 c _ hcert g' hbox hgpos hg'0
  have hclear : ∀ j, (1 / 8 : ℝ) ≤ distInt (g j * (R / 8)) := by
    intro j
    have := hRc (τ (σ.symm j))
    simpa [hg', hτ, Equiv.swap_apply_self] using this
  rcases hwin with ⟨h1, h7⟩ | ⟨h9, h15⟩
  · exact Or.inl (noCarve_of_goodR ⟨h1, h7, hclear⟩)
  · exact Or.inr ⟨R, h9, h15, hclear⟩

#print axioms chainPinned_of_zone

end Fresh.M4ZoneAssembly
