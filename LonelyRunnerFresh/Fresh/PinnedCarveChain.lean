import Fresh.M4CertSound

namespace Fresh.UClosure

open Fresh FilterAssembly

/-- Start the existing strict-seam walk at the opening of the pinned
reading. The starting table may be any table realized by the arrangement.
The returned suffix starts at a genuine numbered zone and has the
envelope required by the bounded replay. -/
theorem pinnedCarve_chain {n : Fin 7 → ℤ} (hn17 : ∀ i, n i ≤ 17)
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (hpin : g 0 = 1) {U : UTable} (hfine : UFine g U)
    (hnoc : ¬ ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :
    ∃ (i : Fin 7) (j : Fin 16) (V : UTable) (rest : List Step),
      uStep U 0 i 1 (zEntry j) (zExit j) = some V ∧ UFine g V ∧
      ChainRealized g U 0 1 (⟨i, zEntry j, zExit j⟩ :: rest) ∧
      ChainRealized g V i (zExit j) rest ∧ EnvChain i (zExit j) rest ∧
      rest.length ≤ 112 := by
  have hlo (i : Fin 7) := (faceLo_ge_one n i).trans (hface i).1
  have hhi (i : Fin 7) := (hface i).2.trans (faceHi_le n hn17 i)
  have hpos (i : Fin 7) := zero_lt_one.trans_le (hlo i)
  have hcov := cover_of_noClear n hn17 hface hnoc
  obtain ⟨i, hi, j, hz⟩ := hcov 1 le_rfl (by norm_num [hpin])
  have left : (zEntry j : ℝ) < g i := by simpa only [mul_one] using hz.1
  have right : g i < (zExit j : ℝ) := by simpa only [mul_one] using hz.2
  have hj : 0 < j.val := by
    by_contra h
    have hj0 : j = 0 := Fin.ext (by omega)
    subst j
    norm_num [zExit] at right
    linarith [hlo i]
  have hpA := zEntry_pos_of_val j hj
  have hpB := zExit_pos j
  have sat1 : BHolds true (g 0 / g i) (1 / zEntry j) := by
    rw [BHolds, Rat.cast_div, Rat.cast_one, hpin, div_lt_div_iff₀ (hpos i) (Rat.cast_pos.mpr hpA)]
    simpa using left
  have sat2 : BHolds true (g i / g 0) (zExit j / 1) := by
    simpa [BHolds, hpin] using right
  obtain ⟨V₁, hV₁⟩ := Option.ne_none_iff_exists.mp (uAdd_none_of_fine_sat hpos hfine sat1)
  have hf₁ := uAdd_fine_some hpos hfine sat1 hV₁.symm
  obtain ⟨V, hV⟩ := Option.ne_none_iff_exists.mp (uAdd_none_of_fine_sat hpos hf₁ sat2)
  have hfV := uAdd_fine_some hpos hf₁ sat2 hV.symm
  have hstep : uStep U 0 i 1 (zEntry j) (zExit j) = some V := by
    unfold uStep
    rw [uGt_pos U 0 i (by norm_num) hpA, hV₁.symm]
    change uGt V₁ (zExit j) i 1 0 = some V
    rw [uGt_pos V₁ i 0 hpB (by norm_num), hV.symm]
  obtain ⟨c, _, hB⟩ := envAB_of_tooth j hj (by omega)
  have hstart : 1 < (zExit j : ℝ) / g i := by
    exact (lt_div_iff₀ (hpos i)).mpr (by simpa using right)
  have continuation : ∃ rest : List Step, ChainRealized g V i (zExit j) rest ∧
      EnvChain i (zExit j) rest ∧ rest.length ≤ 112 := by
    by_cases h : (zExit j : ℝ) / g i ≤ 7 / g 0
    · have hcard : (zoneFront g ((zExit j : ℝ) / g i)).card ≤ 112 := by
        calc
          _ ≤ Fintype.card (Fin 7 × Fin 16) := Finset.card_le_univ _
          _ = 112 := by norm_num
      obtain ⟨rest, hreal, hlen, henv⟩ :=
        chainWalk hlo hhi hcov 112 i (zExit j) V hi hfV ⟨c, hB.symm⟩ hstart h hcard
      exact ⟨rest, hreal, henv, hlen⟩
    · refine ⟨[], ?_, ⟨hi, ⟨c, hB.symm⟩, by simp⟩, by simp⟩
      simp only [ChainRealized, BHolds, Rat.cast_div, Rat.cast_ofNat, hpin, div_one]
      have hend := (lt_div_iff₀ (hpos i)).mp (lt_of_not_ge h)
      rw [hpin, div_one] at hend
      exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 7)).mpr (by linarith)
  obtain ⟨rest, hr, he, hl⟩ := continuation
  exact ⟨i, j, V, rest, hstep, hfV, ⟨V, hstep, hpA, hpB, sat1, sat2, hr⟩, hr, he, hl⟩

#print axioms pinnedCarve_chain

end Fresh.UClosure

namespace Fresh.M4Cert

open Fresh FilterAssembly UClosure

/-- A covering forest whose roots are all genuine blocking readings
cannot satisfy the unrestricted root predicate. That predicate also
tests arbitrary starting numerators and the empty already-exited walk. -/
theorem not_dfsRootAdm_of_nonbase_roots {n : Fin 7 → ℤ} {T : List DfsCert}
    (hnonbase : ∀ t ∈ T, t.root.a ≠ 0) : ¬ DfsRootAdm n T := by
  intro hall
  let g : Fin 7 → ℝ := fun _ => 1
  let U : UTable := fun _ _ => none
  have hfine : UFine g U := fun _ _ => bhof_none
  have hexit : ChainRealized g U 0 8 [] := by norm_num [ChainRealized, BHolds, g]
  obtain ⟨t, ht, hrow, _, _, _⟩ := hall g U 0 8 [] (by simp [g]) hfine hexit
  exact hnonbase t ht hrow

/-- Replay a forest against a chain that actually starts at the pinned
window. Only roots reached in this way need the soft-admissibility proof. -/
theorem firstWindow_of_pinned_forest {n : Fin 7 → ℤ} (hn17 : ∀ i, n i ≤ 17)
    (T : List DfsCert) (hclosed : ∀ t ∈ T, DfsClosed t) (henum : ∀ t ∈ T, DfsEnum n t)
    (hprune : ∀ t ∈ T, DfsPruneDom t)
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) (hpin : g 0 = 1)
    (hadmit : ∀ (i : Fin 7) (j : Fin 16) (V : UTable) (rest : List Step),
      uStep (fun _ _ => none) 0 i 1 (zEntry j) (zExit j) = some V →
      ChainRealized g (fun _ _ => none) 0 1 (⟨i, zEntry j, zExit j⟩ :: rest) →
      EnvChain i (zExit j) rest →
      ∃ t ∈ T, t.root.a = i ∧ t.root.Aex = zExit j ∧ UFine g t.root.U ∧
        DfsSoftAdm n t.root rest) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by
  by_contra hnoc
  have hfine : UFine g (fun _ _ => none) := fun _ _ => bhof_none
  obtain ⟨i, j, V, rest, hs, hf, hw, hr, he, _⟩ :=
    pinnedCarve_chain hn17 hface hpin hfine hnoc
  have hp (k : Fin 7) : 0 < g k :=
    zero_lt_one.trans_le ((faceLo_ge_one n k).trans (hface k).1)
  exact noChain_of_forest n T hclosed henum hprune g V i (zExit j) rest
    hp hf hr (hadmit i j V rest hs hw he)

#print axioms not_dfsRootAdm_of_nonbase_roots
#print axioms firstWindow_of_pinned_forest

end Fresh.M4Cert
