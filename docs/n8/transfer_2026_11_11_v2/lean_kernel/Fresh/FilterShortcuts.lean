import Fresh.BandNoCarve

namespace Fresh.FilterShortcuts

open Fresh.Cascade Fresh.Certs Fresh.FilterAssembly Fresh.FilterSkeleton Fresh.BandNoCarve
open Fresh.FilterAssemblyPerBoxV2

/-- Each step uses an open interval containing the current point and moves to its right end. -/
inductive ExitChain {ι : Type*} (zones : Finset ι) (entry exit : ι → ℝ) (b : ℝ) :
    ℝ → Prop
  | past {x} : b < x → ExitChain zones entry exit b x
  | step {x i} : i ∈ zones → entry i < x → x < exit i →
      ExitChain zones entry exit b (exit i) → ExitChain zones entry exit b x

theorem exitChain_of_cover {ι : Type*} (zones : Finset ι) (entry exit : ι → ℝ)
    (a b : ℝ)
    (hcover : ∀ x ∈ Set.Icc a b, ∃ i ∈ zones, entry i < x ∧ x < exit i) :
    ExitChain zones entry exit b a := by
  classical
  let count (x : ℝ) := (zones.filter fun i => x < exit i).card
  have aux (n : ℕ) : ∀ x : ℝ, a ≤ x → count x = n → ExitChain zones entry exit b x := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hax hx
      by_cases hxb : b < x
      · exact .past hxb
      obtain ⟨i, hi, hen, hex⟩ := hcover x ⟨hax, le_of_not_gt hxb⟩
      have hsub : (zones.filter fun j => exit i < exit j) ⊂
          (zones.filter fun j => x < exit j) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro j hj
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, hex.trans hj.2⟩
        · intro heq
          have hmem : i ∈ zones.filter (fun j => x < exit j) :=
            Finset.mem_filter.mpr ⟨hi, hex⟩
          rw [← heq] at hmem
          exact (lt_irrefl _) (Finset.mem_filter.mp hmem).2
      have hlt : count (exit i) < n := hx ▸ Finset.card_lt_card hsub
      exact .step hi hen hex (ih _ hlt _ (hax.trans hex.le) rfl)
  exact aux (count a) a le_rfl rfl

theorem cover_of_exitChain {ι : Type*} {zones : Finset ι} {entry exit : ι → ℝ}
    {a b : ℝ} (h : ExitChain zones entry exit b a) :
    ∀ x ∈ Set.Icc a b, ∃ i ∈ zones, entry i < x ∧ x < exit i := by
  induction h with
  | past h =>
    intro x hx
    exact ((h.trans_le hx.1).not_ge hx.2).elim
  | @step a i hi hen _ _ ih =>
    intro x hx
    by_cases hxi : x < exit i
    · exact ⟨i, hi, hen.trans_le hx.1, hxi⟩
    · exact ih x ⟨le_of_not_gt hxi, hx.2⟩

theorem exitChain_iff_cover {ι : Type*} (zones : Finset ι) (entry exit : ι → ℝ) (a b : ℝ) :
    ExitChain zones entry exit b a ↔
      ∀ x ∈ Set.Icc a b, ∃ i ∈ zones, entry i < x ∧ x < exit i :=
  ⟨cover_of_exitChain, exitChain_of_cover zones entry exit a b⟩

/-- The single interval tested by the two-window search. -/
def JointCarve (g : Fin 7 → ℝ) : Prop :=
  ∀ R ∈ Set.Icc (1 : ℝ) 15, ∃ i, InWay (g i) (R / 8)

theorem noJointCarve_iff_clear {g : Fin 7 → ℝ} (hpin : ∃ i, g i = 1) :
    ¬ JointCarve g ↔ BandClearPoint g := by
  classical
  constructor
  · intro h
    obtain ⟨R, hR, hclear⟩ : ∃ R ∈ Set.Icc (1 : ℝ) 15, ∀ i, ¬ InWay (g i) (R / 8) := by
      simpa only [JointCarve, not_forall, not_exists, exists_prop] using h
    obtain ⟨i, hi⟩ := hpin
    have hw : R ≤ 7 ∨ 9 ≤ R := by
      by_contra hn
      push Not at hn
      exact hclear i (inWay_of_zone (j := 1)
        (by simpa [hi] using hn.1) (by simpa [hi] using hn.2))
    exact ⟨R, hR.1, hR.2, hw, fun i => not_lt.mp (hclear i)⟩
  · rintro ⟨R, hl, hr, _, hc⟩ h
    obtain ⟨i, hi⟩ := h R ⟨hl, hr⟩
    exact (not_lt.mpr (hc i)) hi

/-- A safe finite lap list for the exact joint-window search. A tight bound can be
used by a certificate checker in place of the deliberately coarse bound here. -/
theorem jointCarve_iff_zoneChain (g : Fin 7 → ℝ) (N : ℤ)
    (hpos : ∀ i, 0 < g i) (hN : ∀ i, 15 * g i ≤ (N : ℝ)) :
    JointCarve g ↔
      ExitChain
        (Finset.univ.product (Finset.Icc (0 : ℤ) N) : Finset (Fin 7 × ℤ))
        (fun z => ((z.2 : ℝ) * 8 - 1) / g z.1)
        (fun z => ((z.2 : ℝ) * 8 + 1) / g z.1) 15 1 := by
  rw [exitChain_iff_cover]
  constructor
  · intro h R hR
    obtain ⟨i, hi⟩ := h R hR
    obtain ⟨j, hentry, hexit⟩ := inWay_zone_iff.mp hi
    have hprod : 0 < g i * R := mul_pos (hpos i) (by linarith [hR.1])
    have hjlo : (-1 : ℝ) < (j : ℝ) := by linarith
    have hjloZ : (-1 : ℤ) < j := by exact_mod_cast hjlo
    have hRmax : g i * R ≤ (N : ℝ) := by
      calc
        g i * R ≤ g i * 15 := mul_le_mul_of_nonneg_left hR.2 (hpos i).le
        _ ≤ _ := by simpa [mul_comm] using hN i
    have hn : (0 : ℝ) ≤ (N : ℝ) := (hprod.le.trans hRmax)
    have hjhi : (j : ℝ) < (N : ℝ) + 1 := by linarith
    have hjhiZ : j < N + 1 := by exact_mod_cast hjhi
    refine ⟨(i, j), Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_Icc.mpr ?_⟩,
      (div_lt_iff₀ (hpos i)).2 ?_, (lt_div_iff₀ (hpos i)).2 ?_⟩
    · omega
    · simpa [mul_comm] using hentry
    · simpa [mul_comm] using hexit
  · intro h R hR
    obtain ⟨⟨i, j⟩, _, hentry, hexit⟩ := h R hR
    refine ⟨i, inWay_zone_iff.mpr ⟨j, ?_, ?_⟩⟩
    · simpa [mul_comm] using (div_lt_iff₀ (hpos i)).mp hentry
    · simpa [mul_comm] using (lt_div_iff₀ (hpos i)).mp hexit

/-- The bounded and tail branches can return different kinds of witnesses. -/
theorem lonelyRunnerEight_of_jointExclusion
    (hInside : ∀ n : Fin 7 → ℤ, InRange17 n →
      ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
        (∃ i, g i = 1) → ¬ JointCarve g)
    (hBand : ∀ g : Fin 7 → ℝ, BandRange g → ¬ JointCarve g)
    (hTail : ∀ v : Fin 8 → ℝ, IsArrangement v → ∀ (k : Fin 8) (m : ℝ), IsDmin v k m →
      (∃ d ∈ disparitySet v k, 49 * m < d) → Isolation v k) :
    LonelyRunnerEight := by
  intro v hv k
  obtain ⟨m, hm⟩ := exists_dmin k
  by_cases h49 : ∃ d ∈ disparitySet v k, 49 * m < d
  · exact hTail v hv k m hm h49
  have hb49 : ∀ d ∈ disparitySet v k, d ≤ 49 * m := by
    intro d hd
    exact le_of_not_gt (fun h => h49 ⟨d, hd, h⟩)
  have finish (g : Fin 7 → ℝ)
      (himage : Finset.image g Finset.univ = Finset.image (fun d => d / m) (disparitySet v k))
      (h : ¬ JointCarve g) : Isolation v k := by
    obtain ⟨s, h1, h15, hw, hc⟩ :=
      (noJointCarve_iff_clear (pin_of_cover hv hm himage)).mp h
    exact isolation_of_cascadeLandsBelow17 hv hm
      (cascadeLandsBelow17_of_clearPoint hv hm s h1 h15 hw (clear_of_image himage hc))
  by_cases h17 : ∃ d ∈ disparitySet v k, 17 * m < d
  · obtain ⟨g, hr, himage⟩ := bandTuple hv hm h17 hb49
    exact finish g himage (hBand g hr)
  · have hb17 : ∀ d ∈ disparitySet v k, d ≤ 17 * m := by
      intro d hd
      exact le_of_not_gt (fun h => h17 ⟨d, hd, h⟩)
    obtain ⟨g, n, hr, hf, himage⟩ := coverTuple hv hm hb17
    exact finish g himage (hInside n hr g hf (pin_of_cover hv hm himage))

#print axioms exitChain_iff_cover
#print axioms noJointCarve_iff_clear
#print axioms jointCarve_iff_zoneChain
#print axioms lonelyRunnerEight_of_jointExclusion

end Fresh.FilterShortcuts
