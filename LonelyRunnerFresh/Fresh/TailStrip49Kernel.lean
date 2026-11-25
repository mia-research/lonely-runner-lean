import Fresh.TailStrip49Cert
import Fresh.Strip49.Slice01
import Fresh.Strip49.Slice02
import Fresh.Strip49.Slice03
import Fresh.Strip49.Slice04
import Fresh.Strip49.Slice05
import Fresh.Strip49.Slice06
import Fresh.Strip49.Slice07
import Fresh.Strip49.Slice08
import Fresh.Strip49.Slice09
import Fresh.Strip49.Slice10
import Fresh.Strip49.Slice11
import Fresh.Strip49.Slice12
import Fresh.Strip49.Slice13
import Fresh.Strip49.Slice14
import Fresh.Strip49.Slice15
import Fresh.Strip49.Slice16
import Fresh.Strip49.Slice17
import Fresh.Strip49.Slice18
import Fresh.Strip49.Slice19
import Fresh.Strip49.Slice20
import Fresh.Strip49.Slice21
import Fresh.Strip49.Slice22
import Fresh.Strip49.Slice23
import Fresh.Strip49.Slice24
import Fresh.Strip49.Slice25
import Fresh.Strip49.Slice26

/-!
# The 49–51 strip without `native_decide` (E929)

Written 2026-11-25.  New file; nothing existing is edited.  Owner (2026-11-25): *"Yes, scale up"*.

The 26 slice theorems `Strip49.sliceNN` (generated certificates, each data file checked by the kernel with
`decide +kernel`, assembled by `seg_of_codeChunk`, `seg_one`, `boxAt_split`, `seg_join`) replace
`TailStrip49Checked.stripCheck`.  The theorems below are `bandClearPoint_of_check`,
`bandClearPoint_of_check_unsorted`, `tailStrip49_clearPoint`, `tailStrip49_lands_of_check`, `tailStrip49_lands` and
`tailBelow17_of_above51`, with `cells_of_check stripCheck` replaced by `cells_kernel`; the proofs are those, copied.

Grades: [L; PROVISIONAL: covering], as for the originals.  The claim supported is the strip's clear point.
-/

namespace Fresh.TailStrip49Kernel

open Fresh Fresh.TailStrip49 Fresh.TailStrip49Cert Fresh.TailStrip49Cert.Strip49

theorem allSlices : ∀ a, 1 ≤ a → a ≤ 26 → ∀ t ∈ rootTuples a, BoxOK (rootOf t) := by
  intro a h1 h2
  interval_cases a
  exacts [slice01, slice02, slice03, slice04, slice05, slice06, slice07, slice08, slice09, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19, slice20, slice21, slice22, slice23, slice24, slice25, slice26]

/-- [L; PROVISIONAL: covering] The conclusion of `cells_of_check`, from kernel-checked certificates. -/
theorem cells_kernel (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g) (hmax : g 5 ≤ 51) :
    CellPairFor g :=
  cells_of_slices allSlices g pin ordered hmax

theorem bandClearPoint_kernel
    (g : Fin 7 → ℝ) (pin : g 0 = 1) (ordered : Monotone g)
    (hmin : 49 ≤ g 6) (hmax : g 6 ≤ 51) : Fresh.BandNoCarve.BandClearPoint g :=
  have ho := ordered (show (5 : Fin 7) ≤ 6 by decide)
  (cells_kernel g pin ordered (ho.trans hmax)).bandClearPoint ho hmin hmax

theorem bandClearPoint_kernel_unsorted
    (g : Fin 7 → ℝ) (bounds : ∀ i, 1 ≤ g i ∧ g i ≤ 51)
    (pin : ∃ i, g i = 1) (fast : ∃ i, 49 ≤ g i) :
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
  have hf : 49 ≤ f 6 := by
    calc
      49 ≤ f (σ.symm j) := by simpa [f] using hj
      _ ≤ f 6 := ordered (by have := (σ.symm j).isLt; omega)
  obtain ⟨R, hL, hU, hW, hclear⟩ :=
    bandClearPoint_kernel f hp ordered hf (bounds (σ 6)).2
  exact ⟨R, hL, hU, hW, fun i => by simpa [f] using hclear (σ.symm i)⟩

/-- [L; PROVISIONAL: covering] `TailStrip49Checked.tailStrip49_clearPoint` without `native_decide`. -/
theorem tailStrip49_clearPoint (g : Fin 7 → ℝ)
    (bounds : ∀ i, 1 ≤ g i ∧ g i ≤ 51) (pin : ∃ i, g i = 1)
    (fast : ∃ i, 49 ≤ g i) : Fresh.BandNoCarve.BandClearPoint g :=
  bandClearPoint_kernel_unsorted g bounds pin fast

open Fresh.FilterAssembly Fresh.FilterSkeleton in
/-- [L; PROVISIONAL: covering] `TailStrip49Checked.tailStrip49_lands` without `native_decide`. -/
theorem tailStrip49_lands {v : Fin 8 → ℝ} (hv : Fresh.IsArrangement v)
    {k : Fin 8} {m : ℝ} (hm : Fresh.IsDmin v k m)
    (fast : ∃ d ∈ disparitySet v k, 49 * m ≤ d)
    (bound : ∀ d ∈ disparitySet v k, d ≤ 51 * m) :
    CascadeLandsBelow17 (disparitySet v k) m := by
  let g (i : Fin 7) := |v (k.succAbove i) - v k| / m
  have hm0 : 0 < m := Fresh.Cascade.disparitySet_pos hv k m hm.1
  have hmem (i : Fin 7) : |v (k.succAbove i) - v k| ∈ disparitySet v k :=
    Finset.mem_image.mpr ⟨k.succAbove i, Finset.mem_erase.mpr
      ⟨Fin.succAbove_ne k i, Finset.mem_univ _⟩, rfl⟩
  have read (d : ℝ) (hd : d ∈ disparitySet v k) : ∃ i, g i = d/m := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
    exact ⟨i,rfl⟩
  have bounds (i : Fin 7) : 1 ≤ g i ∧ g i ≤ 51 := by
    refine ⟨(le_div_iff₀ hm0).2 ?_, (div_le_iff₀ hm0).2 (bound _ (hmem i))⟩
    simpa using hm.2 (hmem i)
  obtain ⟨i,hi⟩ := read m hm.1
  have pin : ∃ i, g i = 1 := ⟨i, hi.trans (div_self (ne_of_gt hm0))⟩
  obtain ⟨d,hd,hd49⟩ := fast
  obtain ⟨j,hj⟩ := read d hd
  have top : ∃ j, 49 ≤ g j := ⟨j, hj.symm ▸ (le_div_iff₀ hm0).2 hd49⟩
  obtain ⟨s,hs,hu,hw,hclear⟩ := bandClearPoint_kernel_unsorted g bounds pin top
  apply cascadeLandsBelow17_of_clearPoint hv hm s hs hu hw
  intro d hd
  obtain ⟨i,hi⟩ := read d hd
  simpa [hi] using hclear i

open Fresh.FilterAssembly in
/-- [L; PROVISIONAL: covering] `TailStrip49Checked.tailBelow17_of_above51` without `native_decide`. -/
theorem tailBelow17_of_above51
    (above : ∀ v : Fin 8 → ℝ, Fresh.IsArrangement v →
      ∀ (k : Fin 8) (m : ℝ), Fresh.IsDmin v k m →
      (∃ d ∈ disparitySet v k, 51 * m < d) →
      Fresh.FilterSkeleton.CascadeLandsBelow17 (disparitySet v k) m) :
    TailBelow17 := by
  intro v hv k m hm h49
  by_cases h51 : ∃ d ∈ disparitySet v k, 51 * m < d
  · exact above v hv k m hm h51
  · obtain ⟨d,hd,h⟩ := h49
    exact tailStrip49_lands hv hm ⟨d,hd,h.le⟩
      (fun e he => le_of_not_gt (fun h => h51 ⟨e,he,h⟩))

#print axioms cells_kernel
#print axioms tailStrip49_clearPoint
#print axioms tailStrip49_lands
#print axioms tailBelow17_of_above51

end Fresh.TailStrip49Kernel
