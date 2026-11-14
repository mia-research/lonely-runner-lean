import Mathlib
import Fresh.FilterAssembly
import Fresh.SpineSound

/-!
# Per-box restatement of the J2 branch of `Fresh.FilterAssembly` (2026-11-08)

New file; nothing existing is edited.  It records two defects of the J2 hypotheses of
`Fresh.FilterAssembly.filterAssembly` and replaces them with per-box hypotheses whose box sets
are fixed by the artifacts.

**Defect 1 (vacuous family) [L, below].**  `JoinFam n fam` does not mention `n`, and the
empty family satisfies it.  So `CoverData` is provable with no data (`coverData_trivial`), and
`PairwiseSound` instantiated at the empty family is the J2-region statement for every box
(`pairwiseSound_iff_universal`).  Also, `famRefutes` makes every conflict edge unrealisable, so
the per-box totality datum `SpineTotalPairwise n fam` is the box conclusion itself
(`spineTotalPairwise_iff`).

**Defect 2 (M4 shape) [T 12,540/12,540, `experiments/n8/zoneclear_single_R_v1.out`].**
`M4Cond n` asks for ONE `W₀` clear point over the whole box.  Exact test with the
`ZoneClearCond` semantics: M1 62,000/62,000 have one, M4 0/12,540, CHAIN 0/73.  So `M4Cond` is
false on every M4 box, and the original `CoverData` held there only through Defect 1.  What the
M4 DFS certifies is box-wide no-carve, a clear point that depends on the reading vector.

**The restatement.**  The J2 tuple is split by excluded middle, with no data hypothesis:
(i) `M1Cond n` holds (decidable integer check; the bridge `clearPointOfCert` is proved);
(ii) `n` is one of the 73 chain boxes `chainBoxes` (from `j2_g1sweep_checkpoint.jsonl`,
`s1 = chain`): OWED `ChainBoxSound`, no carve or a `W₁` clear point over the box (68 one-sided
`j2_cycle_v6/v10`, 5 two-sided `j2_cycle_v12`);
(iii) otherwise (exactly the 12,540 M4 tuples [T]): OWED `M4BoxNoCarve`, box-wide no carve.
Both OWED props quantify over a FIXED box set; neither has a free family to instantiate.
-/

open Classical

namespace Fresh.FilterAssemblyPerBox

open Fresh Fresh.Cascade Fresh.KTaxonomy Fresh.Certs Fresh.FilterSkeleton
open Fresh.FrontierFamilyCap Fresh.FilterAssembly

/-! ## Defect 1, proved -/

theorem joinFam_empty (n : Fin 7 → ℤ) : JoinFam n ∅ := by
  intro e; exact absurd e.2 (Finset.notMem_empty _)

#print axioms joinFam_empty

/-- `CoverData` holds with no data: every tuple is "OneSided" through the empty family. -/
theorem coverData_trivial : CoverData :=
  fun n _ => Or.inr (Or.inr (Or.inl ⟨∅, joinFam_empty n⟩))

#print axioms coverData_trivial

/-- `PairwiseSound` is the unconditional J2-region statement over every box. -/
theorem pairwiseSound_iff_universal :
    PairwiseSound ↔ ∀ n : Fin 7 → ℤ, InRange17 n → ∀ g : Fin 7 → ℝ,
      (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      NoCarve g ∨ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) := by
  constructor
  · intro h n hr g hf; exact h n ∅ hr (joinFam_empty n) g hf
  · intro h n _ hr _ g hf; exact h n hr g hf

#print axioms pairwiseSound_iff_universal

/-- The per-box totality datum is the box conclusion itself. -/
theorem spineTotalPairwise_iff (n : Fin 7 → ℤ) (fam : Finset JoinEdge) (hfam : JoinFam n fam) :
    Fresh.SpineSound.SpineTotalPairwise n fam ↔
      ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
        CarvesOneSeven (Finset.image g Finset.univ) →
        (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) := by
  constructor
  · intro h g hf hc
    by_contra hno
    obtain ⟨e, he, hr⟩ := h g hf hc hno
    exact Fresh.SpineSound.famRefutes hfam ⟨e, he, hr⟩
  · intro h g hf hc hno; exact absurd (h g hf hc) hno

#print axioms spineTotalPairwise_iff

/-! ## The fixed box sets -/

/-- The multiset of a tuple's coordinates (faces are per coordinate, so the box is the multiset). -/
noncomputable def boxMS (n : Fin 7 → ℤ) : Multiset ℤ := Finset.univ.val.map n

/-- The 73 chain boxes of the J2 cover, as sorted six-tuples of the non-least readings
(`j2_g1sweep_checkpoint.jsonl`, `s1 = chain`; `j2_admit_cover_v1.out` CHAIN 73). -/
def chainBoxes : List (List ℤ) :=
[
  [2, 3, 4, 4, 5, 7], [2, 3, 4, 4, 6, 7], [2, 3, 4, 5, 5, 7], [2, 3, 4, 5, 6, 7], [2, 3, 4, 5, 6, 8], [2, 3, 4, 5, 7, 7],
  [2, 3, 4, 5, 7, 8], [2, 3, 4, 6, 6, 8], [2, 3, 4, 6, 7, 8], [2, 3, 5, 6, 6, 8], [2, 4, 4, 6, 6, 8], [2, 4, 5, 6, 6, 8],
  [3, 3, 4, 4, 5, 7], [3, 3, 4, 4, 6, 7], [3, 3, 4, 5, 5, 7], [3, 3, 4, 5, 6, 7], [3, 3, 4, 5, 6, 8], [3, 3, 4, 5, 7, 8],
  [3, 3, 4, 6, 6, 8], [3, 3, 4, 6, 7, 8], [3, 3, 5, 5, 6, 8], [3, 3, 5, 6, 6, 8], [3, 3, 5, 6, 7, 8], [3, 3, 5, 6, 8, 8],
  [3, 3, 5, 6, 8, 9], [3, 4, 4, 5, 5, 7], [3, 4, 4, 5, 6, 7], [3, 4, 4, 5, 6, 8], [3, 4, 4, 5, 7, 7], [3, 4, 4, 6, 6, 8],
  [3, 4, 4, 6, 6, 15], [3, 4, 5, 5, 5, 7], [3, 4, 5, 5, 6, 7], [3, 4, 5, 5, 6, 8], [3, 4, 5, 5, 7, 7], [3, 4, 5, 5, 7, 8],
  [3, 4, 5, 5, 7, 9], [3, 4, 5, 6, 6, 7], [3, 4, 5, 6, 6, 8], [3, 4, 5, 6, 6, 15], [3, 4, 5, 6, 7, 7], [3, 4, 5, 6, 7, 8],
  [3, 4, 5, 6, 7, 9], [3, 4, 5, 6, 7, 15], [3, 4, 5, 6, 7, 16], [3, 4, 5, 6, 8, 9], [3, 4, 5, 7, 7, 7], [3, 4, 5, 7, 7, 9],
  [3, 5, 5, 6, 6, 8], [3, 5, 5, 6, 7, 8], [3, 5, 6, 6, 7, 8], [3, 5, 6, 6, 8, 8], [3, 5, 6, 7, 7, 8], [3, 5, 6, 7, 8, 8],
  [4, 4, 5, 5, 6, 7], [4, 4, 5, 5, 6, 8], [4, 4, 5, 6, 6, 7], [4, 4, 5, 6, 6, 8], [4, 5, 5, 5, 6, 7], [4, 5, 5, 6, 6, 7],
  [4, 5, 5, 6, 6, 8], [4, 5, 5, 6, 7, 7], [4, 5, 5, 6, 7, 8], [4, 5, 5, 6, 7, 9], [4, 5, 6, 6, 7, 8], [4, 5, 6, 6, 7, 9],
  [4, 5, 6, 6, 7, 11], [4, 5, 6, 7, 8, 8], [4, 5, 6, 7, 8, 9], [5, 5, 5, 6, 7, 8], [5, 5, 6, 6, 7, 8], [5, 5, 6, 7, 7, 8],
  [5, 5, 6, 7, 8, 8]]

theorem chainBoxes_length : chainBoxes.length = 73 := by rfl

/-- `n` is a chain box: its coordinates are `1` plus one of the 73 six-tuples. -/
-- STANDING: DEFINITION
def IsChainBox (n : Fin 7 → ℤ) : Prop :=
  ∃ t ∈ chainBoxes, boxMS n = ((1 :: t : List ℤ) : Multiset ℤ)

/-- Some coordinate is the least reading's tuple value `1`. -/
-- STANDING: DEFINITION
def HasLeast (n : Fin 7 → ℤ) : Prop := ∃ i, n i = 1

/-- **OWED — the M4 boxes** (`j2_admit_cert2_checkpoint.jsonl`, 12,540 DFS verdicts): every
J2 tuple that is neither M1 nor a chain box has no carve of `[1,7]` anywhere in its box.  The
hypothesis set is exactly the 12,540 M4 tuples up to coordinate order
[T, `zoneclear_single_R_v1.out`]. -/
-- STANDING: OWED
def M4BoxNoCarve : Prop :=
  ∀ n : Fin 7 → ℤ, InRange17 n → HasLeast n → ¬ M1Cond n → ¬ IsChainBox n →
    ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) → NoCarve g

/-- **OWED — the 73 chain boxes** (68 one-sided `j2_cycle_v6/v10`, 5 two-sided
`j2_cycle_v12`): every reading vector in the box does not carve `[1,7]` or has a `W₁` clear
point.  For a two-sided box with a valid family this is `SpineTotalPairwise` by
`spineTotalPairwise_iff`. -/
-- STANDING: OWED
def ChainBoxSound : Prop :=
  ∀ n : Fin 7 → ℤ, InRange17 n → IsChainBox n →
    ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
      NoCarve g ∨ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)))

/-! ## The per-box assembly -/

/-- The tuple of an arrangement has a coordinate `1` (the least reading's face is `[1, 3/2]`). -/
theorem hasLeast_of_cover {v : Fin 8 → ℝ} {k : Fin 8} {m : ℝ} (hv : IsArrangement v)
    (hm : IsDmin v k m) {g : Fin 7 → ℝ} {n : Fin 7 → ℤ} (hrange : InRange17 n)
    (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (himage : Finset.image g Finset.univ = Finset.image (fun d => d / m) (disparitySet v k)) :
    HasLeast n := by
  have hm0 : 0 < m := disparitySet_pos hv k m hm.1
  have h1 : (1 : ℝ) ∈ Finset.image g Finset.univ := by
    rw [himage]; exact Finset.mem_image.mpr ⟨m, hm.1, div_self hm0.ne'⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h1
  refine ⟨i, ?_⟩
  have hlo := (hface i).1
  rw [hi] at hlo
  unfold FaceLo at hlo
  have h2 : ((max (2 * n i - 1) 2 : ℤ) : ℝ) ≤ 2 := by linarith
  have h3 : max (2 * n i - 1) 2 ≤ 2 := by exact_mod_cast h2
  have h4 := le_of_max_le_left h3
  have h5 := (hrange i).1
  omega

#print axioms hasLeast_of_cover

/-- The J2 region (all normalised readings at most 17) from the two per-box OWED props. -/
theorem allLandBelow17_perBox (hM4 : M4BoxNoCarve) (hCh : ChainBoxSound)
    {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m : ℝ} (hm : IsDmin v k m)
    (hmax : ∀ d ∈ disparitySet v k, d ≤ 17 * m) :
    CascadeLandsBelow17 (disparitySet v k) m := by
  obtain ⟨g, n, hrange, hface, himage⟩ := coverTuple hv hm hmax
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
    · rcases hCh n hrange hC g hface with h | h
      · exact viaNoCarve h
      · exact viaW1 h
    · exact viaNoCarve
        (hM4 n hrange (hasLeast_of_cover hv hm hrange hface himage) hM1 hC g hface)

#print axioms allLandBelow17_perBox

/-- **The per-box assembly**: the J2 region needs exactly `M4BoxNoCarve` (12,540 boxes) and
`ChainBoxSound` (73 boxes); the outside and tail are unchanged. -/
theorem filterAssemblyPerBox (hM4 : M4BoxNoCarve) (hCh : ChainBoxSound)
    (hOutside : OutsideBelow17) (hTail : TailBelow17) : LonelyRunnerEight := by
  apply lonelyRunnerEight_of_allLandBelow17
  intro v hv k m hm
  by_cases h17 : ∀ d ∈ disparitySet v k, d ≤ 17 * m
  · exact allLandBelow17_perBox hM4 hCh hv hm h17
  · push_neg at h17
    obtain ⟨d, hdmem, hd17⟩ := h17
    by_cases h49 : ∀ d' ∈ disparitySet v k, d' ≤ 49 * m
    · exact hOutside v hv k m hm ⟨d, hdmem, hd17⟩ h49
    · push_neg at h49
      obtain ⟨d', hd'mem, hd'49⟩ := h49
      exact hTail v hv k m hm ⟨d', hd'mem, hd'49⟩

#print axioms filterAssemblyPerBox

end Fresh.FilterAssemblyPerBox
