import LonelyRunner.LRC.Spec.RealSevenN

/-!
# One free reading at order eight, in whole numbers

2026-09-27.  Running record: `RUNNING_LOG_order8_v1.md` E117.

**`lonely_eight_of_one_free`.**  Seven positive whole-number readings; six of them share a factor `g ≥ 2` that the
seventh `x` lacks.  Then the subject is lonely at `1/8`:

* native order seven clears the six at `1/7` at some `t₇` (`OrderSevenN.existenceAtN_seven`);
* at `t₇ + k/g` the six have moved by whole laps (`g` divides each), while `x` has moved by `k·x/g`, a step whose
  fractional part `fract (x/g)` is not zero;
* one step cannot stay in the way (`Flanks.exists_clear_step`, the mover ladder's rung `m = 1`): some `k` puts `x`
  at least `1/8` from the subject.

It generalises halving (`g = 2`: six even readings and one odd).  It is the whole-number form of
`OneFreeN.lonely_of_one_free_eight` (one reading off the lattice of the other six), and a case of the order-eight
list (`OrderEightCasesN`, field `no_one_free`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.OneFreeEight

open ConstructionN

/-- **One free reading, whole numbers.** -/
theorem lonely_eight_of_one_free {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (hcard : S.card ≤ 7)
    {x g : ℕ} (hx : x ∈ S) (hg : 2 ≤ g) (hdiv : ∀ d ∈ S, d ≠ x → g ∣ d) (hnd : ¬ g ∣ x) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set ds : Finset ℝ := (S.erase x).image (fun d : ℕ => (d : ℝ)) with hds
  have hcard6 : ds.card ≤ 7 - 1 := by
    have h1 : ds.card ≤ (S.erase x).card := Finset.card_image_le
    have h2 := Finset.card_erase_of_mem hx
    omega
  have hdpos : ∀ y ∈ ds, 0 < y := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
    exact_mod_cast hpos d (Finset.mem_of_mem_erase hd)
  obtain ⟨t7, ht7, hl7⟩ := LRC.OrderSevenN.existenceAtN_seven ds hdpos hcard6
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  -- the step of `x` per `1/g`: its fractional part is not zero
  set f : ℝ := Int.fract ((x : ℝ) / g) with hf
  have hf1 : f < 1 := Int.fract_lt_one _
  have hf0 : 0 < f := by
    rcases (Int.fract_nonneg ((x : ℝ) / g)).lt_or_eq with h | h
    · exact h
    · exfalso; apply hnd
      obtain ⟨z, hz⟩ := Int.fract_eq_zero_iff.mp h.symm
      have hz0 : 0 ≤ z := by
        have : (0 : ℝ) ≤ (x : ℝ) / g := by positivity
        exact_mod_cast (hz ▸ this)
      refine ⟨z.toNat, ?_⟩
      have : (x : ℝ) = g * z := by field_simp at hz; linarith
      have hz' : ((z.toNat : ℕ) : ℝ) = z := by exact_mod_cast Int.toNat_of_nonneg hz0
      exact_mod_cast (by rw [this, hz'] : (x : ℝ) = g * (z.toNat : ℕ))
  obtain ⟨k, hk⟩ := Flanks.exists_clear_step (n := 8) (by norm_num) (c := (x : ℝ) * t7) hf0 hf1
  refine ⟨t7 + k / g, by positivity, fun d hd => ?_⟩
  by_cases hdx : d = x
  · subst hdx
    have e : (d : ℝ) * (t7 + k / g) = ((k : ℝ) * f + d * t7) + ((k * ⌊(d : ℝ) / g⌋ : ℤ) : ℝ) := by
      have : f = (d : ℝ) / g - ⌊(d : ℝ) / g⌋ := rfl
      rw [this]; push_cast; field_simp; ring
    rw [e, circDist_add_int]
    exact_mod_cast hk
  · obtain ⟨m, hm⟩ := hdiv d hd hdx
    have e : (d : ℝ) * (t7 + k / g) = (d : ℝ) * t7 + ((k * m : ℤ) : ℝ) := by
      rw [hm]; push_cast; field_simp
    rw [e, circDist_add_int]
    have hmem : (d : ℝ) ∈ ds := Finset.mem_image.mpr ⟨d, Finset.mem_erase.mpr ⟨hdx, hd⟩, rfl⟩
    have h7 := hl7 _ hmem
    have : ((7 : ℕ) : ℝ)⁻¹ ≥ (8 : ℝ)⁻¹ := by norm_num
    linarith

end LRC.OneFreeEight
