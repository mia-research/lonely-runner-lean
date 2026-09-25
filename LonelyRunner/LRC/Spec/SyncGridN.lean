import LonelyRunner.LRC.Spec.SyncBlockN

/-!
# The synchronised block at the seventh: R by pigeonhole

2026-09-25.  `SyncBlockN` reduces a fast synchronised block `{N + e : e ∈ E}` to a question with no
`N` in it: is there a start `t₀`, clear for the core, where the offsets `{e·t₀}` leave room for a
point `y` at distance more than `1/8` from all of them?  At `t₀ = 1/7` the offsets sit on the grid
`(1/7)ℤ`.  **At most six offsets leave one of the seven slots empty** (`exists_empty_slot`), and the
empty slot `y = k/7` is at distance at least `1/7` from every offset (`circDist_seventh`).  A core
runner `c` not divisible by `7` reads `c/7`, also at distance at least `1/7` from the integers.
The margin `1/7 − 1/8 = 1/56` absorbs the drift over one turn once `N ≥ 56·max`.

So a core with no element divisible by `7`, and a block of at most six runners with offsets and core
below `N/56`, is lonely at a named instant (`lonely_of_sync_grid`): the empty slot's phase, reached
in the turn after `1/7`.  Verified before formalising: the grid criterion (at `q ∈ {2,3,6,7}`) settles
281,008 of 288,288 cases of the reduced question with speeds in `[1,16]`, with no error
(`experiments/nN/sync_R_grid_v1.out`).  Cores divisible by `7` are **not** covered here.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SyncGrid

open LRC.MirrorCentre

/-- **Pigeonhole on seven slots.**  At most six offsets leave a residue mod `7` unused. -/
theorem exists_empty_slot (E : Finset ℕ) (hE : E.card ≤ 6) : ∃ k < 7, ∀ e ∈ E, e % 7 ≠ k := by
  classical
  have hlt : (E.image (· % 7)).card < (Finset.range 7).card := by
    rw [Finset.card_range]; exact lt_of_le_of_lt Finset.card_image_le (by omega)
  obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨k, Finset.mem_range.mp hk, fun e he hek => hkn ?_⟩
  exact Finset.mem_image.mpr ⟨e, he, hek⟩

/-- An integer not divisible by `7`, divided by `7`, is at distance at least `1/7` from the integers. -/
theorem circDist_seventh {m : ℤ} (hm : m % 7 ≠ 0) : (7 : ℝ)⁻¹ ≤ circDist ((m : ℝ) / 7) := by
  have h1 : 1 ≤ m % 7 := by have := Int.emod_nonneg m (by norm_num : (7 : ℤ) ≠ 0); omega
  have h2 : m % 7 ≤ 6 := by have := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 7); omega
  have hdiv : (m : ℝ) = 7 * ((m / 7 : ℤ) : ℝ) + ((m % 7 : ℤ) : ℝ) := by
    have := Int.ediv_add_emod m 7; exact_mod_cast this.symm
  have h1' : (1 : ℝ) ≤ ((m % 7 : ℤ) : ℝ) := by exact_mod_cast h1
  have h2' : ((m % 7 : ℤ) : ℝ) ≤ 6 := by exact_mod_cast h2
  refine circDist_ge_of_window (m := m / 7) ?_ ?_ (by norm_num)
  · rw [hdiv]; linarith
  · rw [hdiv]; linarith

/-- **The synchronised block at the seventh.**  A core `C` with no element divisible by `7`; a block
`{N + e : e ∈ E}` of at most six runners; `56·c ≤ N` and `56·e ≤ N` throughout.  Then the core and
the block are clear at `1/8` together, at an instant in `[1/7, 1/7 + 1/N]`. -/
theorem lonely_of_sync_grid {C E : Finset ℕ} (hC7 : ∀ c ∈ C, ¬ 7 ∣ c) (hE : E.card ≤ 6)
    {N : ℕ} (hN : 0 < N) (hCN : ∀ c ∈ C, 56 * c ≤ N) (hEN : ∀ e ∈ E, 56 * e ≤ N) :
    ∃ t : ℝ, 0 < t ∧ (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * t)) ∧
      ∀ e ∈ E, (8 : ℝ)⁻¹ ≤ circDist (((N : ℝ) + e) * t) := by
  classical
  obtain ⟨k, hk7, hk⟩ := exists_empty_slot E hE
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set Emax : ℝ := (N : ℝ) / 56 with hEmax
  -- the empty slot is at distance ≥ 1/7 ≥ 1/8 + Emax/N from every offset at t₀ = 1/7
  have hy : ∀ e ∈ (E.image (fun e : ℕ => (e : ℝ))),
      (8 : ℝ)⁻¹ + Emax / N ≤ circDist ((k : ℝ) / 7 - e * (1 / 7)) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    have hm : ((k : ℤ) - (e : ℤ)) % 7 ≠ 0 := by
      intro h0
      have : (e : ℤ) % 7 = (k : ℤ) % 7 := by omega
      have hk' : (k : ℤ) % 7 = k := Int.emod_eq_of_lt (by omega) (by omega)
      exact hk e he (by omega)
    have h7 := circDist_seventh hm
    push_cast at h7
    have hval : (k : ℝ) / 7 - (e : ℝ) * (1 / 7) = ((k : ℝ) - (e : ℝ)) / 7 := by ring
    have hE56 : Emax / N = 1 / 56 := by rw [hEmax]; field_simp
    rw [hval, hE56]
    have h78 : (8 : ℝ)⁻¹ + 1 / 56 = 7⁻¹ := by norm_num
    linarith
  obtain ⟨t, ht1, ht2, hcore, hblock⟩ := LRC.SyncBlock.lonely_of_sync_block
    (C := C.image (fun c : ℕ => (c : ℝ))) (E := E.image (fun e : ℕ => (e : ℝ)))
    (N := N) (t₀ := 1 / 7) (y := (k : ℝ) / 7) (Emax := Emax) hNR (by norm_num)
    (by intro x hx; obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hx; positivity)
    (by
      intro x hx; obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      rw [hEmax, le_div_iff₀ (by norm_num)]
      have := hEN e he; have : ((56 * e : ℕ) : ℝ) ≤ N := by exact_mod_cast this
      push_cast at this; linarith)
    (by
      intro x hx s hs1 hs2
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
      have h7 : (7 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * (1 / 7)) := by
        have hm : (c : ℤ) % 7 ≠ 0 := by
          intro h0; exact hC7 c hc (by exact_mod_cast Int.dvd_of_emod_eq_zero h0)
        have := circDist_seventh hm
        rwa [show ((c : ℤ) : ℝ) / 7 = (c : ℝ) * (1 / 7) by push_cast; ring] at this
      have hcN : (56 : ℝ) * c ≤ N := by exact_mod_cast hCN c hc
      have hdrift : |(c : ℝ) * s - (c : ℝ) * (1 / 7)| ≤ 1 / 56 := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ c),
          abs_of_nonneg (by linarith)]
        calc (c : ℝ) * (s - 1 / 7) ≤ c * (1 / N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ 1 / 56 := by
            rw [mul_one_div, div_le_div_iff₀ hNR (by norm_num)]; linarith
      have hlip := circDist_lipschitz.dist_le_mul ((c : ℝ) * s) ((c : ℝ) * (1 / 7))
      simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
      have := (abs_sub_le_iff.mp hlip).2
      norm_num at h7 ⊢; linarith)
    (by exact hy)
  refine ⟨t, by linarith, fun c hc => hcore _ (Finset.mem_image_of_mem _ hc),
    fun e he => hblock _ (Finset.mem_image_of_mem _ he)⟩

end LRC.SyncGrid
