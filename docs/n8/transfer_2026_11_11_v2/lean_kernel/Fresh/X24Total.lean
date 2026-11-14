import Fresh.X24Sound
import Mathlib.Data.Fin.Tuple.Sort

namespace Fresh.X24Replay

private noncomputable def index (r : ℝ) : Nat :=
  min 25 ⌊r + 1/2⌋₊

private theorem index_mono : Monotone index := by
  intro a b hab
  exact min_le_min_left _ (Nat.floor_mono (by linarith))

private theorem index_bounds {r : ℝ} (hr : 1 ≤ r) : 1 ≤ index r ∧ index r ≤ 25 := by
  refine ⟨le_min (by decide) ((Nat.le_floor_iff' (by decide : (1 : Nat) ≠ 0)).2 ?_),
    min_le_left _ _⟩
  norm_num
  linarith

private theorem index_dist {r : ℝ} (hr : 1 ≤ r) (ht : r ≤ 51/2) :
    (index r : ℝ) - 1/2 ≤ r ∧ r ≤ (index r : ℝ) + 1/2 := by
  have hfloor := Nat.floor_le (show 0 ≤ r + 1/2 by linarith)
  have hlt := Nat.lt_floor_add_one (r+1/2)
  unfold index
  rcases le_total ⌊r+1/2⌋₊ 25 with h | h
  · rw [min_eq_right h]
    exact ⟨by linarith, by linarith⟩
  · rw [min_eq_left h]
    have hc : (25 : ℝ) ≤ (⌊r+1/2⌋₊ : ℝ) := by exact_mod_cast h
    exact ⟨by linarith, by linarith⟩

private theorem center_mem {r : ℝ} (hr : 1 ≤ r) (ht : r ≤ 51/2) :
    ((centerFace (index r)).1 : ℝ) ≤ scale*r ∧ scale*r ≤ (centerFace (index r)).2 := by
  obtain ⟨hl, hu⟩ := index_dist hr ht
  have hk := (index_bounds hr).1
  have eqLo : (((2*index r-1)*scale/2 : Nat) : ℝ) = (scale : ℝ)*((index r : ℝ)-1/2) := by
    rw [Nat.mul_div_assoc _ (by decide : 2 ∣ scale)]
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2*index r)]
    push_cast
    norm_num [scale]
    ring
  have eqHi : (((2*index r+1)*scale/2 : Nat) : ℝ) = (scale : ℝ)*((index r : ℝ)+1/2) := by
    rw [Nat.mul_div_assoc _ (by decide : 2 ∣ scale)]
    push_cast
    norm_num [scale]
    ring
  have sp : (0 : ℝ) ≤ scale := by positivity
  unfold centerFace
  dsimp only
  push_cast
  rw [eqLo, eqHi]
  refine ⟨max_le ?_ (mul_le_mul_of_nonneg_left hl sp),
    le_min ?_ (mul_le_mul_of_nonneg_left hu sp)⟩
  · simpa using mul_le_mul_of_nonneg_left hr sp
  · norm_num [maxTop,scale]
    linarith

private theorem roots_cover {g : Fin 7 → ℝ}
    (pin : g 0 = 1) (ordered : Monotone g) (hmax : g 5 ≤ 51/2) :
    ∃ a b c d e : Nat, 1 ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e ∧ e ≤ 25 ∧
      inBox (root a b c d e) g := by
  let k (i : Fin 5) := index (g (coordinate i))
  have hLow (i : Fin 5) : 1 ≤ g (coordinate i) := by
    rw [← pin]
    exact ordered (by omega)
  have hHigh (i : Fin 5) : g (coordinate i) ≤ 51/2 := (ordered (by decide +revert)).trans hmax
  have hmon : Monotone k := by
    intro i j hij
    exact index_mono (ordered (show coordinate i ≤ coordinate j by
      change i.val+1 ≤ j.val+1
      exact Nat.add_le_add_right hij 1))
  refine ⟨k 0, k 1, k 2, k 3, k 4, (index_bounds (hLow 0)).1,
    hmon (by decide), hmon (by decide), hmon (by decide), hmon (by decide),
    (index_bounds (hLow 4)).2, ?_⟩
  intro i
  have hh := center_mem (hLow i) (hHigh i)
  fin_cases i <;> exact hh

theorem cells_of_check (checked : (List.range' 1 25).all checkFirst = true)
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g)
    (hmax : g 5 ≤ 51/2) : CellPairFor g := by
  obtain ⟨a,b,c,d,e,ha,hab,hbc,hcd,hde,he,hbox⟩ := roots_cover pin ordered hmax
  have ha' : a ∈ List.range' 1 25 := List.mem_range'_1.mpr ⟨ha,by omega⟩
  have hb' : b ∈ List.range' a (26-a) := List.mem_range'_1.mpr ⟨hab,by omega⟩
  have hc' : c ∈ List.range' b (26-b) := List.mem_range'_1.mpr ⟨hbc,by omega⟩
  have hd' : d ∈ List.range' c (26-c) := List.mem_range'_1.mpr ⟨hcd,by omega⟩
  have he' : e ∈ List.range' d (26-d) := List.mem_range'_1.mpr ⟨hde,by omega⟩
  have ca := List.all_eq_true.mp checked a ha'
  simp only [checkFirst, List.all_eq_true] at ca
  exact cover_sound pin 32 (root a b c d e) (ca b hb' c hc' d hd' e he') hbox

theorem bandClearPoint_of_check (checked : (List.range' 1 25).all checkFirst = true)
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g)
    (hmin : 45/2 ≤ g 6) (hmax : g 6 ≤ 51/2) : Fresh.BandNoCarve.BandClearPoint g :=
  have ho := ordered (show (5 : Fin 7) ≤ 6 by decide)
  (cells_of_check checked g pin ordered (ho.trans hmax)).bandClearPoint ho hmin hmax

/-- The verified domain cover applies to normalized readings in any order. -/
theorem bandClearPoint_of_check_unsorted (checked : (List.range' 1 25).all checkFirst = true)
    (g : Fin 7 → ℝ) (bounds : ∀ i, 1 ≤ g i ∧ g i ≤ 51/2)
    (pin : ∃ i, g i = 1) (fast : ∃ i, 45/2 ≤ g i) :
    Fresh.BandNoCarve.BandClearPoint g := by
  let σ := Tuple.sort g
  let f := g ∘ σ
  have ordered : Monotone f := Tuple.monotone_sort g
  obtain ⟨i, hi⟩ := pin
  obtain ⟨j, hj⟩ := fast
  have hp : f 0 = 1 := by
    apply le_antisymm _ (bounds (σ 0)).1
    calc
      f 0 ≤ f (σ.symm i) := ordered (Fin.zero_le _)
      _ = 1 := by simpa [f] using hi
  have hf : 45/2 ≤ f 6 := by
    calc
      45/2 ≤ f (σ.symm j) := by simpa [f] using hj
      _ ≤ f 6 := ordered (by have := (σ.symm j).isLt; omega)
  obtain ⟨R, hL, hU, hW, hclear⟩ :=
    bandClearPoint_of_check checked f hp ordered hf (bounds (σ 6)).2
  exact ⟨R, hL, hU, hW, fun i => by simpa [f] using hclear (σ.symm i)⟩

#print axioms cells_of_check
#print axioms bandClearPoint_of_check
#print axioms bandClearPoint_of_check_unsorted

end Fresh.X24Replay
