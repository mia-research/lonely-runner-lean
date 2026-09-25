import LonelyRunner.LRC.Spec.SteppingN

/-!
# Order five, real speeds on any number of independent directions

2026-09-24.  Write the disparities as `rᵢ₀ + Σⱼ rᵢ,ⱼ₊₁ βⱼ` with whole-number rows `rᵢ` and
`1, β₀, …, β_{d−1}` free of rational relations.  Two directions (`d = 1`) is `RankTwoN.lean`; this
file carries every `d ≥ 1`, so the class structure `1 + 1 + 1 + 1` is settled on three and four
directions as well.

* **The model.**  A whole-number direction `y` reads row `r` as `Σₖ rₖ yₖ`.  Project the rows to
  the plane along two whole-number directions `u, v` chosen so that the projected rows stay
  pairwise non-parallel (`exists_avoid`, by base-`N` digits); the plane's exact merge
  (`exists_merge_model`) then gives `y = p·u + q·v`, in which two runners coincide up to sign.
* **The order below.**  Three runners are lonely at `1/4` at an instant `τ`: a margin of `1/20`.
* **To a real time.**  `t = τ y₀ + K`; stepping (`Stepping.exists_step_near`) puts every `βⱼ t`
  within `η` of `τ yⱼ₊₁` (`lonely_of_model_many`, at every order `n`).

No density, no measure: pigeonhole returns, their span, and rounding down.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.OrderFiveN

open MomentIterationN LRC.SpecN ConstructionN LRC.Stepping

variable {d m : ℕ}

/-- The real speed of a whole-number row on the directions `1, β`. -/
noncomputable def speed (β : Fin d → ℝ) (r : Fin (d + 1) → ℤ) : ℝ :=
  (r 0 : ℝ) + ∑ j, (r j.succ : ℝ) * β j

/-- The reading of row `r` along the whole-number direction `y`. -/
def dotZ (y r : Fin m → ℤ) : ℤ := ∑ k, r k * y k

/-- Two rows are parallel when every `2 × 2` minor vanishes. -/
def Parallel (r s : Fin m → ℤ) : Prop := ∀ i k, r i * s k = r k * s i

/-! ## From a model instant to a real time, at every order and on any number of directions -/

/-- **The model carries to the reals.**  If along `y` every row's reading is clear at `1/(n − 1)`
at `τ`, the real speeds are lonely at `1/n`. -/
theorem lonely_of_model_many {n : ℕ} (hn : 2 ≤ n) {β : Fin d → ℝ} (hβ : NoRelation β)
    (j0 : Fin d) {R : Finset (Fin (d + 1) → ℤ)} (hR : R.Nonempty) (y : Fin (d + 1) → ℤ) {τ : ℝ}
    (hτ : ∀ r ∈ R, ((n : ℝ) - 1)⁻¹ ≤ circDist ((dotZ y r : ℝ) * τ)) :
    ∃ t : ℝ, 0 < t ∧ ∀ r ∈ R, (n : ℝ)⁻¹ ≤ circDist (speed β r * t) := by
  classical
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  set σ : ℝ := ((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹ with hσ
  have hσ0 : 0 < σ := by
    rw [hσ, sub_pos]; exact inv_strictAnti₀ hn1 (by linarith)
  set C : ℝ := ∑ r ∈ R, ∑ j : Fin d, |(r j.succ : ℝ)| + 1 with hC
  have hC0 : 0 < C := by
    have : 0 ≤ ∑ r ∈ R, ∑ j : Fin d, |(r j.succ : ℝ)| :=
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hrC : ∀ r ∈ R, ∑ j : Fin d, |(r j.succ : ℝ)| ≤ C := by
    intro r hr
    have := Finset.single_le_sum (f := fun r : Fin (d + 1) → ℤ => ∑ j : Fin d, |(r j.succ : ℝ)|)
      (fun r _ => Finset.sum_nonneg fun j _ => abs_nonneg _) hr
    linarith
  set η : ℝ := σ / C with hη
  have hη0 : 0 < η := by positivity
  -- step every irrational direction onto the model
  obtain ⟨K, P, hKP⟩ := exists_step_near hβ j0 (fun j : Fin d => τ * y j.succ - β j * (τ * y 0)) hη0
  set e : Fin d → ℝ := fun j : Fin d => (K : ℝ) * β j - P j - (τ * y j.succ - β j * (τ * y 0)) with he
  set t0 : ℝ := τ * y 0 + K with ht0
  have key : ∀ r, speed β r * t0 = ((dotZ y r : ℝ) * τ + ∑ j, (r j.succ : ℝ) * e j) +
      ((r 0 * K + ∑ j, r j.succ * P j : ℤ) : ℝ) := by
    intro r
    set Sβ : ℝ := ∑ j : Fin d, (r j.succ : ℝ) * β j with hSβ
    set SP : ℝ := ∑ j : Fin d, (r j.succ : ℝ) * (P j : ℝ) with hSP
    set Sy : ℝ := ∑ j : Fin d, (r j.succ : ℝ) * (y j.succ : ℝ) with hSy
    have hE : ∑ j, (r j.succ : ℝ) * e j = K * Sβ - SP - τ * Sy + τ * y 0 * Sβ := by
      simp only [he, hSβ, hSP, hSy, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hD : (dotZ y r : ℝ) = r 0 * y 0 + Sy := by
      simp only [dotZ, Fin.sum_univ_succ, hSy]; push_cast; rfl
    have hI : ((r 0 * K + ∑ j, r j.succ * P j : ℤ) : ℝ) = r 0 * K + SP := by
      simp only [hSP]; push_cast; rfl
    rw [hE, hD, hI, speed, ht0, ← hSβ]
    ring
  have hclear : ∀ r ∈ R, (n : ℝ)⁻¹ ≤ circDist (speed β r * t0) := by
    intro r hr
    rw [key r, circDist_add_int]
    have hlip := circDist_lipschitz.dist_le_mul ((dotZ y r : ℝ) * τ + ∑ j, (r j.succ : ℝ) * e j)
      ((dotZ y r : ℝ) * τ)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    have hbound : |(dotZ y r : ℝ) * τ + ∑ j, (r j.succ : ℝ) * e j - (dotZ y r : ℝ) * τ| ≤ σ := by
      rw [add_sub_cancel_left]
      calc |∑ j, (r j.succ : ℝ) * e j| ≤ ∑ j : Fin d, |(r j.succ : ℝ)| * η := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hKP j) (abs_nonneg _)
        _ = (∑ j : Fin d, |(r j.succ : ℝ)|) * η := by rw [Finset.sum_mul]
        _ ≤ C * η := mul_le_mul_of_nonneg_right (hrC r hr) hη0.le
        _ = σ := by rw [hη]; field_simp
    have h1 := hτ r hr
    have := abs_sub_le_iff.mp hlip
    linarith [this.2]
  obtain ⟨r0, hr0⟩ := hR
  have ht0ne : t0 ≠ 0 := by
    intro h0
    have := hclear r0 hr0
    rw [h0, mul_zero, show circDist 0 = 0 by simp [circDist]] at this
    have : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
    linarith
  refine ⟨|t0|, abs_pos.mpr ht0ne, fun r hr => ?_⟩
  rcases abs_choice t0 with h | h
  · rw [h]; exact hclear r hr
  · rw [h, mul_neg, circDist.symm_neg]; exact hclear r hr

/-! ## Avoiding finitely many hyperplanes, by base-`N` digits -/

/-- Digits smaller than `N` in absolute value, summing to zero in base `N`, are all zero. -/
theorem digits_eq_zero {N : ℕ} (hN : 0 < N) :
    ∀ {m : ℕ} (c : Fin m → ℤ), (∀ k, |c k| < N) → ∑ k, c k * (N : ℤ) ^ (k : ℕ) = 0 → c = 0 := by
  intro m
  induction m with
  | zero => intro c _ _; funext k; exact k.elim0
  | succ m ih =>
    intro c hc hsum
    rw [Fin.sum_univ_succ] at hsum
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ] at hsum
    have hsplit : ∑ x : Fin m, c x.succ * ((N : ℤ) ^ (x : ℕ) * N) =
        N * ∑ x : Fin m, c x.succ * (N : ℤ) ^ (x : ℕ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit] at hsum
    have hdvd : (N : ℤ) ∣ c 0 := ⟨-∑ x : Fin m, c x.succ * (N : ℤ) ^ (x : ℕ), by linarith⟩
    have h0 : c 0 = 0 := by
      obtain ⟨q, hq⟩ := hdvd
      have := hc 0
      rw [hq, abs_mul] at this
      have hNpos : (0 : ℤ) < N := by exact_mod_cast hN
      rw [abs_of_pos hNpos] at this
      have : |q| < 1 := by nlinarith [abs_nonneg q]
      have : q = 0 := by rw [abs_lt] at this; omega
      rw [hq, this, mul_zero]
    rw [h0, zero_add] at hsum
    have hrest : ∑ x : Fin m, c x.succ * (N : ℤ) ^ (x : ℕ) = 0 := by
      have hNne : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
      exact (mul_eq_zero.mp hsum).resolve_left hNne
    have := ih (fun k => c k.succ) (fun k => hc k.succ) hrest
    funext k
    refine Fin.cases h0 (fun j => ?_) k
    exact congrFun this j

/-- **Avoiding hyperplanes.**  For finitely many non-zero whole-number normals there is a
whole-number direction off all their hyperplanes: `y = (1, N, N², …)` with `N` above every
entry. -/
theorem exists_avoid (S : Finset (Fin m → ℤ)) (hS : ∀ s ∈ S, s ≠ 0) :
    ∃ y : Fin m → ℤ, ∀ s ∈ S, dotZ y s ≠ 0 := by
  classical
  set N : ℕ := ∑ s ∈ S, ∑ k, (s k).natAbs + 1 with hN
  have hNpos : 0 < N := by omega
  refine ⟨fun k => (N : ℤ) ^ (k : ℕ), fun s hs h0 => hS s hs ?_⟩
  refine digits_eq_zero hNpos s (fun k => ?_) h0
  have h1 : (s k).natAbs ≤ ∑ k, (s k).natAbs :=
    Finset.single_le_sum (f := fun k => (s k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have h2 : ∑ k, (s k).natAbs ≤ ∑ s ∈ S, ∑ k, (s k).natAbs :=
    Finset.single_le_sum (f := fun s : Fin m → ℤ => ∑ k, (s k).natAbs) (fun _ _ => Nat.zero_le _) hs
  have h3 : (s k).natAbs < N := by omega
  rw [Int.abs_eq_natAbs]; exact_mod_cast h3

/-! ## The exact merge on any number of directions -/

theorem dotZ_add_smul (p q : ℤ) (u v r : Fin m → ℤ) :
    dotZ (fun k => p * u k + q * v k) r = p * dotZ u r + q * dotZ v r := by
  simp only [dotZ, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The normal `(r · u) s − (s · u) r`: a direction `v` off its hyperplane keeps `r` and `s`
apart in the plane of `u, v`. -/
def gvec (u r s : Fin m → ℤ) : Fin m → ℤ := fun k => dotZ u r * s k - dotZ u s * r k

theorem dotZ_gvec (u v r s : Fin m → ℤ) :
    dotZ v (gvec u r s) = dotZ u r * dotZ v s - dotZ u s * dotZ v r := by
  unfold gvec
  generalize dotZ u r = A
  generalize dotZ u s = B
  simp only [dotZ, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The exact merge, any number of directions.**  Four pairwise non-parallel rows have a
whole-number direction whose readings are non-zero, with row `0` coinciding up to sign with row
`1` or row `2`. -/
theorem exists_merge_model_many (a : Fin 4 → Fin m → ℤ)
    (hpar : ∀ i j, i ≠ j → ¬ Parallel (a i) (a j)) :
    ∃ y : Fin m → ℤ, (∀ i, dotZ y (a i) ≠ 0) ∧
      ((dotZ y (a 0)).natAbs = (dotZ y (a 1)).natAbs ∨
        (dotZ y (a 0)).natAbs = (dotZ y (a 2)).natAbs) := by
  classical
  -- rows are non-zero
  have hnz : ∀ i, a i ≠ 0 := by
    intro i h
    obtain ⟨j, hj⟩ : ∃ j, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩
    exact hpar i j hj.symm (fun k l => by simp [h])
  -- `u`: every row reads non-zero
  obtain ⟨u, hu⟩ := exists_avoid (Finset.univ.image a) (by
    intro s hs; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs; exact hnz i)
  have hu' : ∀ i, dotZ u (a i) ≠ 0 := fun i => hu _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  -- `v`: off the hyperplanes of the normals `gvec u (a i) (a j)`
  have hgnz : ∀ i j, i ≠ j → gvec u (a i) (a j) ≠ 0 := by
    intro i j hij h0
    apply hpar i j hij
    intro k l
    have hk := congrFun h0 k
    have hl := congrFun h0 l
    simp only [gvec, Pi.zero_apply] at hk hl
    have : dotZ u (a i) * (a i k * a j l - a i l * a j k) = 0 := by
      linear_combination (a i k) * hl - (a i l) * hk
    have := (mul_eq_zero.mp this).resolve_left (hu' i)
    linarith
  obtain ⟨v, hv⟩ := exists_avoid
    ((Finset.univ.filter (fun ij : Fin 4 × Fin 4 => ij.1 ≠ ij.2)).image
      (fun ij => gvec u (a ij.1) (a ij.2)))
    (by
      intro s hs
      obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hs
      exact hgnz ij.1 ij.2 (Finset.mem_filter.mp hij).2)
  have hv' : ∀ i j, i ≠ j → dotZ v (gvec u (a i) (a j)) ≠ 0 := fun i j hij =>
    hv _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
  -- the projected rows in the plane, pairwise non-parallel
  set pr : Fin 4 → ℤ × ℤ := fun i => (dotZ u (a i), dotZ v (a i)) with hpr
  have hcross : ∀ i j, i ≠ j → cross (pr i) (pr j) ≠ 0 := by
    intro i j hij
    have e : cross (pr i) (pr j) = dotZ v (gvec u (a i) (a j)) := by
      rw [dotZ_gvec]; simp only [cross, hpr]; ring
    rw [e]; exact hv' i j hij
  obtain ⟨y2, n1, n2, n3, n4, hm⟩ := exists_merge_model (hcross 0 1 (by decide))
    (hcross 0 2 (by decide)) (hcross 0 3 (by decide)) (hcross 1 2 (by decide))
    (hcross 1 3 (by decide)) (hcross 2 3 (by decide))
  -- lift the plane's direction back
  have hlift : ∀ i, dotZ (fun k => y2.1 * u k + y2.2 * v k) (a i) = reading y2 (pr i) := by
    intro i; rw [dotZ_add_smul]; simp only [reading, hpr]; ring
  refine ⟨fun k => y2.1 * u k + y2.2 * v k, fun i => ?_, ?_⟩
  · rw [hlift]
    fin_cases i
    · exact n1
    · exact n2
    · exact n3
    · exact n4
  · rw [hlift, hlift, hlift]; exact hm

/-! ## Order five -/

/-- **Order five, real speeds on any number of independent directions.**  Four speeds
`rᵢ₀ + Σⱼ rᵢ,ⱼ₊₁ βⱼ` with `1, β` free of rational relations (at least one irrational direction)
and pairwise non-parallel whole-number rows are lonely at `1/5`. -/
theorem lonely_five_many {β : Fin d → ℝ} (hβ : NoRelation β) (j0 : Fin d)
    (a : Fin 4 → Fin (d + 1) → ℤ) (hpar : ∀ i j, i ≠ j → ¬ Parallel (a i) (a j)) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, (5 : ℝ)⁻¹ ≤ circDist (speed β (a i) * t) := by
  classical
  obtain ⟨y, hnz, hm⟩ := exists_merge_model_many a hpar
  set w : Fin 4 → ℝ := fun i => |((dotZ y (a i) : ℤ) : ℝ)| with hw
  have hwnat : ∀ i, w i = (((dotZ y (a i)).natAbs : ℕ) : ℝ) := fun i => by
    rw [hw]; simp only; rw [Nat.cast_natAbs, Int.cast_abs]
  set W : Finset ℝ := {w 0, w 1, w 2, w 3} with hW
  have hWpos : ∀ x ∈ W, 0 < x := by
    intro x hx
    simp only [hW, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact abs_pos.mpr (by exact_mod_cast hnz _)
  have hWcard : W.card ≤ 3 := by
    rcases hm with h | h
    · have : w 0 = w 1 := by rw [hwnat, hwnat, h]
      rw [hW, this, Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)]
      exact le_trans (Finset.card_insert_le _ _)
        (by have := Finset.card_insert_le (w 2) ({w 3} : Finset ℝ); simp at this ⊢; omega)
    · have : w 0 = w 2 := by rw [hwnat, hwnat, h]
      rw [hW, this, Finset.insert_eq_of_mem (by simp)]
      exact le_trans (Finset.card_insert_le _ _)
        (by have := Finset.card_insert_le (w 2) ({w 3} : Finset ℝ); simp at this ⊢; omega)
  obtain ⟨τ, -, hl⟩ := existenceAtN_four W hWpos (by simpa using hWcard)
  have hτ : ∀ r ∈ Finset.univ.image a, ((5 : ℕ) - 1 : ℝ)⁻¹ ≤ circDist ((dotZ y r : ℝ) * τ) := by
    intro r hr
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    have hwi : w i ∈ W := by
      simp only [hW, Finset.mem_insert, Finset.mem_singleton]
      fin_cases i <;> simp
    have := hl (w i) hwi
    rw [hw] at this; simp only at this
    rw [circDist_abs_mul] at this
    have h54 : ((5 : ℕ) - 1 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h54]; exact this
  obtain ⟨t, ht, hlt⟩ := lonely_of_model_many (n := 5) (by norm_num) hβ j0
    ⟨a 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩ y hτ
  exact ⟨t, ht, fun i => by simpa using hlt (a i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

end LRC.OrderFiveN
