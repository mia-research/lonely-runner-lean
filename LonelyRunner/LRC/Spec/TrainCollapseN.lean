import LonelyRunner.LRC.Spec.SyncBlockN
import LonelyRunner.LRC.Spec.OrderSevenN
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# The train collapses to order seven: a bound on the handoff that does not depend on `N`

2026-09-25.  A runner's readings split into a core `C` and a fast train `{N + e : e ∈ E}`,
`|C| + |E| ≤ 7`.  Put the train's free phase at `y = (i + j)·τ` for two of its offsets `i < j` with no
offset at their midpoint.  The train's condition becomes `‖(2e − i − j)·τ‖`, and `i`, `j` give the same
reading `j − i`: the set `R = {2c} ∪ {|2e − i − j|}` has at most six readings, an order-seven object,
lonely at `1/7` at some `τ` (`OrderSevenN.lonely_seven_nat`).  At `t₀ = 2τ` the core is clear at `1/7` and
every train offset is `1/7` from `y`; within one turn `1/N` the fast phase reaches `y` (`sync_block`), and
the margin `1/7 − 1/8 = 1/56` absorbs the drift once `N ≥ 56·m`.

The instant `τ` is chosen **before** `N` (`lonely_of_train_collapse`): however far out the train is sent,
the event lies in `[2τ, 2τ + 1/N)`.  The fast train cannot carry the isolation event beyond a time fixed
by the core and the train's differences alone.

Checked before formalising on 780 arrangements, no violation of `t* ≤ 2τ₇ + 1/N`
(`experiments/nN/redo/train_collapse_bound_v1.out`).  Everything here is proved; no `sorry`, no
`native_decide`.
-/

namespace LRC.TrainCollapse

/-- `circDist` is even (local copy of `Flanks.circDist_neg`, to keep the import light). -/
theorem circDist_neg' (x : ℝ) : circDist (-x) = circDist x := by
  unfold circDist
  rcases eq_or_ne (Int.fract x) 0 with h | h
  · rw [h, Int.fract_neg_eq_zero.mpr h]
  · rw [Int.fract_neg h, min_comm]
    congr 1 <;> ring

/-- The collapsed reading of a train offset. -/
def collapse (i j e : ℕ) : ℕ := Int.natAbs (2 * (e : ℤ) - i - j)

/-- The two chosen offsets give the same collapsed reading, so the train loses one reading. -/
theorem card_collapse_le {E : Finset ℕ} {i j : ℕ} (hi : i ∈ E) (hj : j ∈ E) (hij : i < j) :
    (E.image (collapse i j)).card ≤ E.card - 1 := by
  have hsame : collapse i j j = collapse i j i := by
    unfold collapse; omega
  have heq : E.image (collapse i j) = (E.erase j).image (collapse i j) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨e, he, rfl⟩
      by_cases hej : e = j
      · subst hej; exact ⟨i, ⟨by omega, hi⟩, hsame.symm⟩
      · exact ⟨e, ⟨hej, he⟩, rfl⟩
    · rintro ⟨e, ⟨-, he⟩, rfl⟩
      exact ⟨e, he, rfl⟩
  rw [heq, ← Finset.card_erase_of_mem hj]
  exact Finset.card_image_le

/-- **The train collapse.**  Core `C` (positive, at most `m`), train offsets `E` (at most `m`),
`|C| + |E| ≤ 7`, and two train offsets `i < j` with no offset at their midpoint.  Then there is one
instant `τ > 0`, depending on `C`, `E`, `i`, `j` only, such that for every `N ≥ 56·m` the core and the
whole train `{N + e}` are clear at `1/8` at a named instant of `[2τ, 2τ + 1/N)`. -/
theorem lonely_of_train_collapse {C E : Finset ℕ} {i j m : ℕ} (hCpos : ∀ c ∈ C, 0 < c)
    (hCm : ∀ c ∈ C, c ≤ m) (hEm : ∀ e ∈ E, e ≤ m) (hi : i ∈ E) (hj : j ∈ E) (hij : i < j)
    (hmid : ∀ e ∈ E, 2 * e ≠ i + j) (hcard : C.card + E.card ≤ 7) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ N : ℕ, 0 < N → 56 * m ≤ N →
      ∃ t : ℝ, 2 * τ ≤ t ∧ t < 2 * τ + 1 / N ∧
        (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * t)) ∧
        ∀ e ∈ E, (8 : ℝ)⁻¹ ≤ circDist (((N : ℝ) + e) * t) := by
  classical
  set R : Finset ℕ := C.image (fun c => 2 * c) ∪ E.image (collapse i j) with hR
  have hRpos : ∀ r ∈ R, 0 < r := by
    intro r hr
    rcases Finset.mem_union.mp hr with h | h
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h; have := hCpos c hc; omega
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      have := hmid e he
      unfold collapse; omega
  have hRcard : R.card ≤ 6 := by
    have h1 : R.card ≤ (C.image (fun c => 2 * c)).card + (E.image (collapse i j)).card := by
      rw [hR]; exact Finset.card_union_le _ _
    have h2 : (C.image (fun c => 2 * c)).card ≤ C.card := Finset.card_image_le
    have h3 := card_collapse_le hi hj hij
    have h4 : 2 ≤ E.card := by
      have : ({i, j} : Finset ℕ) ⊆ E := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have := Finset.card_le_card this
      rw [Finset.card_pair (by omega)] at this; exact this
    omega
  obtain ⟨τ, hτ, hl⟩ := LRC.OrderSevenN.lonely_seven_nat R hRpos hRcard
  refine ⟨τ, hτ, fun N hN hNm => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmN : (m : ℝ) / N ≤ 1 / 56 := by
    rw [div_le_iff₀ hNR]; have : (56 * m : ℝ) ≤ N := by exact_mod_cast hNm
    linarith
  -- each train offset is 1/7 from the phase y = (i + j) τ at t₀ = 2τ
  have hoff : ∀ e ∈ E, (7 : ℝ)⁻¹ ≤ circDist (((i : ℝ) + j) * τ - (e : ℝ) * (2 * τ)) := by
    intro e he
    have hr : collapse i j e ∈ R := Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)
    have h7 := hl _ hr
    have hz : ((i : ℝ) + j) * τ - (e : ℝ) * (2 * τ) = -(((2 * (e : ℤ) - i - j : ℤ) : ℝ) * τ) := by
      push_cast; ring
    rw [hz, circDist_neg']
    unfold collapse at h7
    have hk := Int.natAbs_eq (2 * (e : ℤ) - i - j)
    generalize Int.natAbs (2 * (e : ℤ) - i - j) = k at h7 hk
    rcases hk with h | h
    · rw [h]; exact_mod_cast h7
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul, circDist_neg']
      exact h7
  have key := LRC.SyncBlock.sync_block (E := E.image (fun e : ℕ => (e : ℝ))) (N := (N : ℝ))
    (t₀ := 2 * τ) (y := ((i : ℝ) + j) * τ) (Emax := (m : ℝ)) hNR
    (by intro x hx; obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hx; positivity)
    (by intro x hx; obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx; exact_mod_cast hEm e he)
    (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
      have := hoff e he
      linarith)
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨_, h1, h2, fun c hc => ?_, fun e he => h3 _ (Finset.mem_image_of_mem _ he)⟩
  -- the core drifts by at most m/N ≤ 1/56 in one turn
  set t := 2 * τ + Int.fract (-(((i : ℝ) + j) * τ) - N * (2 * τ)) / N
  have hcR : (0 : ℝ) < c := by exact_mod_cast hCpos c hc
  have hcm : (c : ℝ) ≤ m := by exact_mod_cast hCm c hc
  have h2c : (2 * c : ℕ) ∈ R := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
  have h7 := hl _ h2c
  have h7' : (7 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * (2 * τ)) := by
    rw [show (c : ℝ) * (2 * τ) = ((2 * c : ℕ) : ℝ) * τ by push_cast; ring]; exact h7
  have hdist : |(c : ℝ) * t - (c : ℝ) * (2 * τ)| ≤ 1 / 56 := by
    rw [← mul_sub, abs_mul, abs_of_pos hcR]
    have hts : |t - 2 * τ| ≤ 1 / N := by
      rw [abs_le]; constructor <;> linarith
    calc (c : ℝ) * |t - 2 * τ| ≤ m * (1 / N) := mul_le_mul hcm hts (abs_nonneg _) (by positivity)
      _ = m / N := by ring
      _ ≤ 1 / 56 := hmN
  have hlip := circDist_lipschitz.dist_le_mul ((c : ℝ) * t) ((c : ℝ) * (2 * τ))
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
  have := (abs_sub_le_iff.mp hlip).2
  norm_num at h7' ⊢
  linarith

end LRC.TrainCollapse
