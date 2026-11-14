import Fresh.FilterAssembly
/-!
# Kernel probe (transfer package, 2026-11-11)

Two facts about the SHAPE of `Fresh.FilterAssembly.filterAssembly`'s hypotheses, checked by Lean.
They change what "the remaining work" is; see `N8_LEAN_KERNEL_AND_GAPS_v1.md` section 4.
-/
open Fresh Fresh.FilterAssembly

/-- `CoverData` is provable as stated (take the empty edge family): it carries none of the
74,613-box data.  The box data therefore lives nowhere in the Lean statement. -/
theorem probe_coverData : CoverData := by
  intro n _
  exact Or.inr (Or.inr (Or.inl ⟨∅, fun e => (Finset.notMem_empty e.1 e.2).elim⟩))
#print axioms probe_coverData

/-- `PairwiseSound`, as stated, already asserts the whole inside statement for EVERY box and
EVERY reading vector in it (again via the empty family): no carve of `[1,7]`, or a clear point
in `[9,15]`. -/
theorem probe_pairwise (h : PairwiseSound) (n : Fin 7 → ℤ) (hr : InRange17 n) (g : Fin 7 → ℝ)
    (hf : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    Fresh.Certs.NoCarve g ∨ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=
  h n ∅ hr (fun e => (Finset.notMem_empty e.1 e.2).elim) g hf
#print axioms probe_pairwise
