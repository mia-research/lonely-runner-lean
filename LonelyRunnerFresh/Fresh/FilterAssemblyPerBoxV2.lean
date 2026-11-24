import Mathlib
import Fresh.FilterAssemblyPerBox

/-!
# Per-box assembly with the d_min pin (2026-11-08)

New file; `Fresh.FilterAssemblyPerBox` is not edited.

**Defect in `FilterAssemblyPerBox.M4BoxNoCarve` [T, `experiments/n8/m4_negcycle_v1_boxes.jsonl`].**
The prop lets every coordinate range over its face.  The least coordinate (`n i = 1`) has face
`[1, 3/2]`, so the d_min reading may leave `1`.  With it free, the negative-cycle search finds
carves of `[1,7]` with exact verified witnesses, for example box `(1,2,3,3,4,5,7)` with least
reading `302526/221983`.  So `M4BoxNoCarve` as stated is not the record's statement; the record
pins the least reading (E832: `lo 0 = hi 0 = 1`).

**The pin.**  In the assembly the readings are `d / m` with `m` the least disparity, so `1` is a
reading (`pin_of_cover`).  The pinned props add the hypothesis `∃ i, g i = 1`.  With the pin,
`experiments/n8/m4_negcycle_v2.out` decides all 12,540 M4 boxes "no carve"
[T 12,540/12,540; PROVISIONAL: covering, open cover ⇔ carve; PROVISIONAL: counting tool, finitely
many chains].  Both pinned props are weaker than the unpinned ones (`m4_pinned_of_unpinned`,
`chain_pinned_of_unpinned`), and they suffice for the same assembly
(`filterAssemblyPerBoxPinned`).
-/

open Classical

namespace Fresh.FilterAssemblyPerBoxV2

open Fresh Fresh.Cascade Fresh.KTaxonomy Fresh.Certs Fresh.FilterSkeleton
open Fresh.FrontierFamilyCap Fresh.FilterAssembly Fresh.FilterAssemblyPerBox

/-- **OWED — the M4 boxes, pinned.**  As `M4BoxNoCarve`, with the least reading at `1`. -/
-- STANDING: OWED
def M4BoxNoCarvePinned : Prop :=
  ∀ n : Fin 7 → ℤ, InRange17 n → HasLeast n → ¬ M1Cond n → ¬ IsChainBox n →
    ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) → (∃ i, g i = 1) → NoCarve g

/-- **OWED — the 73 chain boxes, pinned.**  As `ChainBoxSound`, with the least reading at `1`. -/
-- STANDING: OWED
def ChainBoxSoundPinned : Prop :=
  ∀ n : Fin 7 → ℤ, InRange17 n → IsChainBox n →
    ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) → (∃ i, g i = 1) →
      NoCarve g ∨ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)))

theorem m4_pinned_of_unpinned (h : M4BoxNoCarve) : M4BoxNoCarvePinned :=
  fun n hr hl hm hc g hf _ => h n hr hl hm hc g hf

#print axioms m4_pinned_of_unpinned

theorem chain_pinned_of_unpinned (h : ChainBoxSound) : ChainBoxSoundPinned :=
  fun n hr hc g hf _ => h n hr hc g hf

#print axioms chain_pinned_of_unpinned

/-- The normalised readings of an arrangement include `1`: the least disparity over itself. -/
theorem pin_of_cover {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (hv : IsArrangement v)
    (hm : IsDmin v k m) {g : Fin 7 → ℝ}
    (himage : Finset.image g Finset.univ = Finset.image (fun d => d / m) (disparitySet v k)) :
    ∃ i, g i = 1 := by
  have hm0 : 0 < m := disparitySet_pos hv k m hm.1
  have h1 : (1 : ℝ) ∈ Finset.image g Finset.univ := by
    rw [himage]; exact Finset.mem_image.mpr ⟨m, hm.1, div_self hm0.ne'⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h1
  exact ⟨i, hi⟩

#print axioms pin_of_cover

/-- The J2 region from the two pinned per-box OWED props. -/
theorem allLandBelow17_perBoxPinned (hM4 : M4BoxNoCarvePinned) (hCh : ChainBoxSoundPinned)
    {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m)
    (hmax : ∀ d ∈ disparitySet v k, d ≤ 17 * m) :
    CascadeLandsBelow17 (disparitySet v k) m := by
  obtain ⟨g, n, hrange, hface, himage⟩ := coverTuple hv hm hmax
  have hpin := pin_of_cover hv hm himage
  have viaNoCarve : NoCarve g → CascadeLandsBelow17 (disparitySet v k) m := by
    intro hnc
    obtain ⟨t, ht1, ht2, hlon⟩ := (notCarve_witness g).mp hnc
    refine cascadeLandsBelow17_of_clearPoint hv hm (8 * t) ?_ ?_ (Or.inl ?_) ?_
    · linarith
    · linarith
    · linarith
    · intro d hd
      have hmem : d / m ∈ Finset.image g Finset.univ := by
        rw [himage]; exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
      rw [Finset.mem_image] at hmem
      obtain ⟨i, -, he⟩ := hmem
      rw [← he]
      have hdist := hlon (g i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      have he8 : (8 * t) / 8 = t := by field_simp
      rw [he8]
      exact hdist
  have viaW1 : (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) →
      CascadeLandsBelow17 (disparitySet v k) m := by
    rintro ⟨s, hs9, hs15, hcl⟩
    refine cascadeLandsBelow17_of_clearPoint hv hm s ?_ hs15 (Or.inr hs9) ?_
    · linarith
    · exact clear_of_image himage hcl
  by_cases hM1 : M1Cond n
  · obtain ⟨r, base, hc⟩ := hM1
    obtain ⟨s, hs1, hs2, hsw, hcl⟩ :=
      clearPointOfCert n 0 (certOfCond n r base 0 hc) (by omega) g hface
    exact cascadeLandsBelow17_of_clearPoint hv hm s hs1 hs2 hsw (clear_of_image himage hcl)
  · by_cases hC : IsChainBox n
    · rcases hCh n hrange hC g hface hpin with h | h
      · exact viaNoCarve h
      · exact viaW1 h
    · exact viaNoCarve
        (hM4 n hrange (hasLeast_of_cover hv hm hrange hface himage) hM1 hC g hface hpin)

#print axioms allLandBelow17_perBoxPinned

/-- **The pinned per-box assembly.** -/
theorem filterAssemblyPerBoxPinned (hM4 : M4BoxNoCarvePinned) (hCh : ChainBoxSoundPinned)
    (hOutside : OutsideBelow17) (hTail : TailBelow17) : LonelyRunnerEight := by
  apply lonelyRunnerEight_of_allLandBelow17
  intro v hv k m hm
  by_cases h17 : ∀ d ∈ disparitySet v k, d ≤ 17 * m
  · exact allLandBelow17_perBoxPinned hM4 hCh hv hm h17
  · push_neg at h17
    obtain ⟨d, hdmem, hd17⟩ := h17
    by_cases h49 : ∀ d' ∈ disparitySet v k, d' ≤ 49 * m
    · exact hOutside v hv k m hm ⟨d, hdmem, hd17⟩ h49
    · push_neg at h49
      obtain ⟨d', hd'mem, hd'49⟩ := h49
      exact hTail v hv k m hm ⟨d', hd'mem, hd'49⟩

#print axioms filterAssemblyPerBoxPinned

end Fresh.FilterAssemblyPerBoxV2
