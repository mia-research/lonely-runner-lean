import LonelyRunner.LRC.Spec.RegimeSkeletonN
import LonelyRunner.LRC.Spec.BandCoverN
import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# The band route: the conjecture at eight runners from the band theorem and one owed statement above spread 9

2026-10-01.  Running record: `RUNNING_LOG_order8_v1.md` E211 (design), E212 (build and check).

Seven readings, least `m`, greatest `W`:

| case | discharge |
|---|---|
| at most six readings | native order seven at `1/7` (`lonely_eight_of_card_le_six`) |
| `W ≤ 7m` | the bound `1/(8m)` (R1, `lonely_eight_of_spread`) |
| `7m < W ≤ 9m` | the band theorem `BandCover.band_lonely`, every real shape (`lonely8_of_band`) |
| `9m < W` | **`WideStep8 M`, OWED** (registered in `scripts/nN/spec_gate.sh`) |

**`lonelyRunnerAt8_of_wideStep8 M : WideStep8 M → LonelyRunnerAt8`**, for every `M`.  `WideStep8 M` is `Cover8 M`
restricted to seven readings of spread above 9 (`wideStep8_of_cover8`), so this route asks no more than
`lonelyRunnerAt8_of_cover8` at the same `M`.

**Measured** `[VERIFIED — these populations; not proved]`: `Cover8` needs `M = 2` only on band shapes (E210,
`experiments/nN/redo/cover8_check_v1.out`).  `WideStep8 1` holds as written on every population in
`experiments/nN/redo/wide_step_check_v1.out` and `wide_step_check_v2.out` (E212; v2 replaces v1's edge population,
which was bound-clear by construction).  An adversarial walk found no wide set without a lonely instant in the slowest
reading's first window (`wide_first_stretch_walk_v1.out`): a truth check of the by-product below, nothing more (E215).

**The place is the grid-class instant**: the largest left end of the assigned lap blocks, an opening of one of the
readings, on a grid through one of the arrangement's own readings.  `gridStep8_one_first_stretch` records a by-product at
`M = 1`: that instant falls in the slowest reading's first window, `1 ≤ 8·m·t ≤ 7`.  The framework does not require the
first window (object register v3 item 15), and through this by-product `WideStep8 1` is a first-lap cap on wide sets,
the shape of the refuted `Spec.DoorFirstLap` (E215).  The route holds for every `M`; `M = 1` is a reading of the data,
not the target.

Everything here is proved; no `sorry`, no `native_decide`.  `WideStep8` is a hypothesis, not a theorem.
-/

namespace LRC.BandRoute

open LRC.OrderEightN LRC.Order8Skeleton LRC.RegimeSkeleton

/-- **The band, on whole-number readings.**  Seven readings with least `m` and greatest in `(7m, 9m]` are lonely: list
them in order, divide by `m`, apply `band_lonely`, and rescale its instant by `1/m` (the AP is scale invariant). -/
theorem lonely8_of_band {S : Finset ℕ} (hS : S.card = 7) (hpos : ∀ d ∈ S, 0 < d) {m : ℕ} (hmS : m ∈ S)
    (hmin : ∀ d ∈ S, m ≤ d) (hlo : ∃ d ∈ S, 7 * m < d) (hhi : ∀ d ∈ S, d ≤ 9 * m) : Lonely8 S := by
  classical
  set a := S.orderEmbOfFin hS with ha
  have hmem : ∀ i, a i ∈ S := fun i => S.orderEmbOfFin_mem hS i
  have hsurj : ∀ d ∈ S, ∃ i, a i = d := by
    intro d hd
    have : d ∈ Set.range a := by rw [ha, Finset.range_orderEmbOfFin]; exact hd
    exact this
  have hmono : Monotone a := a.monotone
  have hm0 : 0 < m := hpos m hmS
  have ha0 : a 0 = m := by
    obtain ⟨i, hi⟩ := hsurj m hmS
    refine le_antisymm ?_ (hmin _ (hmem 0))
    rw [← hi]; exact hmono (Fin.zero_le i)
  have hmax : ∀ d ∈ S, d ≤ a 6 := by
    intro d hd
    obtain ⟨i, rfl⟩ := hsurj d hd
    exact hmono (by fin_cases i <;> decide)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  set x : Fin 7 → ℝ := fun i => (a i : ℝ) / m with hx
  have hxle : ∀ i j : Fin 7, i ≤ j → x i ≤ x j := fun i j hij =>
    (div_le_div_iff_of_pos_right hmR).mpr (by exact_mod_cast hmono hij)
  have hx1 : 1 ≤ x 1 := by
    simp only [hx]; rw [le_div_iff₀ hmR, one_mul]; exact_mod_cast hmin _ (hmem 1)
  obtain ⟨d, hdS, hd⟩ := hlo
  have h6lo : 7 ≤ x 6 := by
    have h := hmax d hdS
    simp only [hx]; rw [le_div_iff₀ hmR]; exact_mod_cast (by omega : 7 * m ≤ a 6)
  have h6hi : x 6 ≤ 9 := by
    simp only [hx]; rw [div_le_iff₀ hmR]; exact_mod_cast hhi _ (hmem 6)
  obtain ⟨t, ht, hl⟩ := LRC.BandCover.band_lonely (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) hx1
    (hxle _ _ (by decide)) (hxle _ _ (by decide)) (hxle _ _ (by decide)) (hxle _ _ (by decide))
    (hxle _ _ (by decide)) h6lo h6hi
  refine ⟨t / m, div_pos ht hmR, fun d hd => ?_⟩
  obtain ⟨i, rfl⟩ := hsurj d hd
  have hx0 : x 0 = 1 := by simp only [hx]; rw [ha0]; exact div_self hmR.ne'
  have key : LRC.BandCover.bandS (x 1 - 1) (x 2 - 1) (x 3 - 1) (x 4 - 1) (x 5 - 1) (x 6 - 1) i = x i := by
    fin_cases i <;> simp [LRC.BandCover.bandS, hx0]
  have heq : (a i : ℝ) * (t / m) = x i * t := by simp only [hx]; ring
  have hli := hl i
  rw [key] at hli
  rwa [heq]

/-- **OWED: the grid regime above spread 9.**  Every set of seven positive whole-number readings, least reading `m`, with
a reading above `9m`, is lonely at the bound or at a grid-class instant of a grid through one of its own readings with
step at least `m/M` (`GridStep8 S m M`). -/
def WideStep8 (M : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card = 7 → (∀ d ∈ S, 0 < d) →
    ∀ m ∈ S, (∀ d ∈ S, m ≤ d) → (∃ d ∈ S, 9 * m < d) → GridStep8 S m M

/-- `WideStep8 M` is `Cover8 M` on a smaller domain. -/
theorem wideStep8_of_cover8 {M : ℕ} (h : Cover8 M) : WideStep8 M :=
  fun S hS hpos m hmS hmin _ => h S hS.le hpos m hmS hmin

/-- **The conjecture at eight runners from the band theorem and `WideStep8 M`**, for any step bound `M`. -/
theorem lonelyRunnerAt8_of_wideStep8 (M : ℕ) (h : WideStep8 M) : LRC.Spec.LonelyRunnerAt8 := by
  refine LRC.Spec.lonelyRunnerAt8_of_existence (existenceAt8_of_nat fun S hpos hcard => ?_)
  classical
  by_cases h6 : S.card ≤ 6
  · exact lonely_eight_of_card_le_six hpos h6
  have hS : S.card = 7 := by omega
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hmS : S.min' hne ∈ S := Finset.min'_mem S hne
  have hmin : ∀ d ∈ S, S.min' hne ≤ d := fun d hd => Finset.min'_le S d hd
  have hm0 := hpos _ hmS
  by_cases h7 : ∀ d ∈ S, d ≤ 7 * S.min' hne
  · exact lonely_eight_of_spread hm0 hmin h7
  push Not at h7
  by_cases h9 : ∀ d ∈ S, d ≤ 9 * S.min' hne
  · exact lonely8_of_band hS hpos hmS hmin h7 h9
  push Not at h9
  exact lonely_of_gridStep8 hne hpos hm0 (h S hS hpos _ hmS hmin h9)

/-- **A by-product at `M = 1`, not the place.**  A grid with step at least the slowest reading `m` puts `m` at grid point
1, so on lap 0 at every class that is a unit mod 8; the 1-D Helly instant (the largest left end of the assigned clear
blocks) then falls in `m`'s first window.  At the bound, `8·m·t = 1`.  The place is the grid-class instant; the first
window is not a requirement of the framework (E215; object register v3 item 15). -/
theorem gridStep8_one_first_stretch {S : Finset ℕ} {m : ℕ} (hpos : ∀ d ∈ S, 0 < d) (hmS : m ∈ S)
    (h : GridStep8 S m 1) :
    ∃ t : ℝ, 0 < t ∧ 1 ≤ 8 * m * t ∧ 8 * m * t ≤ 7 ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have hm : (0 : ℝ) < m := by exact_mod_cast hpos m hmS
  rcases h with hb | ⟨e, heS, mm, c, -, hstep, hc, k, hgrid, hpair⟩
  · have h1 : 8 * (m : ℝ) * (1 / (8 * m)) = 1 := by field_simp
    exact ⟨1 / (8 * m), by positivity, by rw [h1], by rw [h1]; norm_num, hb⟩
  · -- the slowest reading is on lap 0
    have hk0 : k m = 0 := by
      obtain ⟨n, hn1, hn, -, hkm⟩ := hgrid m hmS
      have hn2 : n < 2 := by
        by_contra hcon
        push Not at hcon
        have : 2 * e ≤ n * e := Nat.mul_le_mul_right e hcon
        linarith
      obtain rfl : n = 1 := by omega
      rcases hc with rfl | rfl | rfl | rfl <;> omega
    -- the largest left end of the assigned blocks
    obtain ⟨f, hfS, hmax⟩ := S.exists_max_image (fun d : ℕ => ((8 * k d + 1 : ℕ) : ℚ) / d) ⟨m, hmS⟩
    have hf : (0 : ℝ) < f := by exact_mod_cast hpos f hfS
    set t : ℝ := (8 * (k f : ℝ) + 1) / (8 * f) with ht
    have hblock : ∀ d ∈ S, (8 * (k d : ℝ) + 1) ≤ 8 * d * t ∧ 8 * d * t ≤ 8 * k d + 7 := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hpos d hd
      have hq := hmax d hd
      have hd0q : (0 : ℚ) < d := by exact_mod_cast hpos d hd
      have hf0q : (0 : ℚ) < f := by exact_mod_cast hpos f hfS
      rw [div_le_div_iff₀ hd0q hf0q] at hq
      have h1 : (8 * (k d : ℝ) + 1) * f ≤ (8 * k f + 1) * d := by exact_mod_cast hq
      have h2 : (8 * (k f : ℝ) + 1) * d ≤ (8 * k d + 7) * f := by exact_mod_cast hpair f hfS d hd
      have hdt : 8 * (d : ℝ) * t = (8 * k f + 1) * d / f := by rw [ht]; field_simp
      rw [hdt]
      constructor
      · rw [le_div_iff₀ hf]; linarith
      · rw [div_le_iff₀ hf]; linarith
    refine ⟨t, by positivity, ?_, ?_, fun d hd => ?_⟩
    · have := (hblock m hmS).1; rw [hk0] at this; push_cast at this; linarith
    · have := (hblock m hmS).2; rw [hk0] at this; push_cast at this; linarith
    · obtain ⟨h1, h2⟩ := hblock d hd
      exact LRC.TwoPinner.clear_of_band (N := k d) (by push_cast; linarith) (by push_cast; linarith)

end LRC.BandRoute
