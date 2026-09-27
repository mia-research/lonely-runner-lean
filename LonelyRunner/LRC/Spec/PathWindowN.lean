import LonelyRunner.LRC.Spec.PathRouteN
import LonelyRunner.LRC.Spec.EndRunnerN

/-!
# The conjecture at eight runners from the window

2026-09-27.  Plan: `docs/n8/PATH_ROUTE_LEAN_PLAN_v1.md`.  Running record: `RUNNING_LOG_order8_v1.md` E113–E115.

**`WindowBound`** is the owner's *"bounded by the speeds of the arrangement"* (E52): on every bounded set of
arrangements whose readings (of the subject) lie in `[c, C]`, `c > 0`, a lonely subject is lonely at some instant `≤ T`.
It is a hypothesis here, registered OWED; nothing here asserts it.

**`lonelyRunnerAt8_of_window`: `WindowBound → LonelyRunnerAt8`.**  The argument is the owner's deformation argument,
one runner at a time:
* start at the AP (readings `j/8`), lonely at `t = 1`;
* move the runners to their target speeds **one at a time** (`PathRouteN.segment_lonely`): the others stay put, so at a
  lonely instant only the moving runner changes; off an edge it stays clear, on an edge it moves inward for one sign
  and, at the mirror instant, for the other;
* each segment: openness from that, closedness from the window (`DeformationN.lonely_along_path`);
* after seven moves, the slowest runner of any whole-number arrangement is lonely, and `EndRunnerN` gives the rest.

No ordering of the moves is needed and no speed need stay distinct along the way: every lemma asks only that the
subject's readings stay positive.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.PathWindow

open Arrangement LRC.PathRoute LRC.Order8Skeleton

/-- **The window** (OWED): on every set of arrangements whose subject readings lie in `[c, C]`, `c > 0`, a lonely
subject is lonely at some instant `≤ T`, one `T` for the whole set. -/
def WindowBound : Prop :=
  ∀ c C : ℝ, 0 < c → ∃ T : ℝ, ∀ v : Fin 8 → ℝ, ∀ k : Fin 8,
    (∀ j : Fin 8, j ≠ k → c ≤ v j - v k ∧ v j - v k ≤ C) →
      LRC.Spec.LonelyForSubject v k → ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ LonelyAt v k t

theorem circDist_le_abs' (x : ℝ) : circDist x ≤ |x| := by
  simpa using ConstructionN.circDist_le_abs_sub_int x 0

/-- A lonely instant is at least `1/(8C)` when some reading is positive and at most `C`. -/
theorem lonely_ge {v : Fin 8 → ℝ} {k j : Fin 8} {C t : ℝ} (hjk : j ≠ k) (hd : 0 < v j - v k)
    (hC : v j - v k ≤ C) (ht : 0 < t) (hl : LonelyAt v k t) : 1 / (8 * C) ≤ t := by
  have h1 := hl j hjk
  rw [LRC.PathRoute.sep_eq] at h1
  have h2 := circDist_le_abs' (sep v k j t)
  rw [LRC.PathRoute.sep_eq, abs_of_pos (mul_pos hd ht)] at h2
  have hC0 : 0 < C := lt_of_lt_of_le hd hC
  rw [div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hC ht.le]

/-- The chain: runners `1 … n` at their target speeds `V`, the rest at the AP speeds `A`. -/
noncomputable def chain (A V : Fin 8 → ℝ) (n : ℕ) : Fin 8 → ℝ :=
  fun j => if 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ n then V j else A j

theorem chain_succ (A V : Fin 8 → ℝ) {n : ℕ} (hn : n + 1 < 8) :
    chain A V (n + 1) = chain A V n + (1 : ℝ) • (fun m : Fin 8 => if m = ⟨n + 1, hn⟩ then V m - A m else 0) := by
  ext j
  simp only [chain, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
  by_cases hj : j = ⟨n + 1, hn⟩
  · subst hj; simp
  · have hj' : (j : ℕ) ≠ n + 1 := fun h => hj (Fin.ext h)
    by_cases h1 : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ n
    · have h2 : 1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ n + 1 := ⟨h1.1, by omega⟩
      simp [h1, h2, hj]
    · have h2 : ¬ (1 ≤ (j : ℕ) ∧ (j : ℕ) ≤ n + 1) := by omega
      simp [h1, h2, hj]

/-- **The slowest runner of a whole-number arrangement, from the window.** -/
theorem slowest_of_window (hW : WindowBound) (v : Fin 8 → ℕ) (hv : Arr8 v) (hslow : ∀ i, v 0 ≤ v i) :
    Lonely8 (readingsOf v 0) := by
  classical
  set V : Fin 8 → ℝ := fun j => (v j : ℝ) with hV
  set A : Fin 8 → ℝ := fun j => (v 0 : ℝ) + (j : ℕ) / 8 with hA
  have hVpos : ∀ j : Fin 8, j ≠ 0 → (1 : ℝ) ≤ V j - V 0 := by
    intro j hj
    have hlt : v 0 < v j := lt_of_le_of_ne (hslow j) (fun h => hj (hv.2 h).symm)
    simp only [hV]; have : ((v 0 : ℕ) : ℝ) + 1 ≤ (v j : ℝ) := by exact_mod_cast hlt
    linarith
  -- the bounds of the readings along the whole chain
  set C : ℝ := 1 + ∑ j, (V j - V 0) with hC
  have hVC : ∀ j : Fin 8, j ≠ 0 → V j - V 0 ≤ C := by
    intro j hj
    have hnn : ∀ m ∈ (Finset.univ : Finset (Fin 8)), 0 ≤ V m - V 0 := by
      intro m _; by_cases hm : m = 0
      · subst hm; simp
      · linarith [hVpos m hm]
    have := Finset.single_le_sum hnn (Finset.mem_univ j)
    linarith
  have hAr : ∀ j : Fin 8, j ≠ 0 → (1 : ℝ) / 8 ≤ A j - V 0 ∧ A j - V 0 ≤ 7 / 8 := by
    intro j hj
    have h1 : (1 : ℕ) ≤ (j : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hj (Fin.ext h))
    have h2 : (j : ℕ) ≤ 7 := Nat.lt_succ_iff.mp j.2
    simp only [hA, hV]
    constructor
    · have : (1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast h1
      linarith
    · have : ((j : ℕ) : ℝ) ≤ 7 := by exact_mod_cast h2
      linarith
  have hC1 : (1 : ℝ) ≤ C := by
    have hnn : ∀ m ∈ (Finset.univ : Finset (Fin 8)), 0 ≤ V m - V 0 := by
      intro m _; by_cases hm : m = 0
      · subst hm; simp
      · linarith [hVpos m hm]
    have := Finset.sum_nonneg hnn
    linarith
  obtain ⟨T, hT⟩ := hW (1 / 8) C (by norm_num)
  -- every arrangement on the chain: subject speed V 0, readings in [1/8, C]
  have hchain0 : ∀ n : ℕ, chain A V n 0 = V 0 := by
    intro n; simp [chain, hA, hV]
  -- the AP is lonely at t = 1
  have hAP : LRC.Spec.LonelyForSubject (chain A V 0) 0 := by
    refine ⟨1, one_pos, fun j hj => ?_⟩
    have hc : chain A V 0 j = A j := by
      simp only [chain]; rw [if_neg]; omega
    rw [LRC.PathRoute.sep_eq, hc, hchain0, mul_one]
    obtain ⟨h1, h2⟩ := hAr j hj
    exact LRC.TwoPinner.clear_of_band (N := 0) (by push_cast; linarith) (by push_cast; linarith)
  -- one segment
  have hstep : ∀ n : ℕ, (hn : n + 1 < 8) → LRC.Spec.LonelyForSubject (chain A V n) 0 →
      LRC.Spec.LonelyForSubject (chain A V (n + 1)) 0 := by
    intro n hn hl
    set i : Fin 8 := ⟨n + 1, hn⟩ with hi
    set w : Fin 8 → ℝ := fun m => if m = i then V m - A m else 0 with hw
    have hki : (0 : Fin 8) ≠ i := by intro h; have := congrArg Fin.val h; simp [hi] at this
    have hwz : ∀ m : Fin 8, m ≠ i → w m = 0 := by intro m hm; simp [hw, hm]
    have hci : chain A V n i = A i := by
      simp only [chain, hi]; rw [if_neg]; omega
    -- the readings along the segment
    have hread : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j : Fin 8, j ≠ 0 →
        (1 : ℝ) / 8 ≤ (chain A V n + s • w) j - (chain A V n + s • w) 0 ∧
          (chain A V n + s • w) j - (chain A V n + s • w) 0 ≤ C := by
      intro s hs j hj
      have hw0 : w 0 = 0 := hwz 0 hki
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw0, mul_zero, add_zero, hchain0]
      by_cases hji : j = i
      · subst hji
        rw [hci]; simp only [hw, if_pos rfl]
        obtain ⟨a1, a2⟩ := hAr i hj
        have v1 := hVpos i hj
        have v2 := hVC i hj
        obtain ⟨s0, s1⟩ := hs
        constructor <;> nlinarith
      · rw [hwz j hji, mul_zero, add_zero]
        simp only [chain]
        split_ifs
        · exact ⟨by linarith [hVpos j hj], hVC j hj⟩
        · obtain ⟨a1, a2⟩ := hAr j hj; exact ⟨a1, by linarith⟩
    have hseg := segment_lonely (v := chain A V n) (w := w) (k := 0) (i := i) (c := 1 / (8 * C)) (T := T)
      (by positivity) hki hwz ?_ ?_ ?_ hl
    · rw [chain_succ A V hn, one_smul]; exact hseg
    · -- the fixed runners' readings are rational
      intro j _
      rw [hchain0]
      simp only [chain]
      split_ifs
      · exact ⟨(v j : ℚ) - v 0, by simp [hV]⟩
      · exact ⟨(j : ℕ) / 8, by simp [hA, hV]⟩
    · intro s hs j hj
      linarith [(hread s hs j hj).1]
    · intro s hs hl'
      obtain ⟨t, ht, htT, htl⟩ := hT _ 0 (hread s hs) hl'
      obtain ⟨j, hj⟩ : ∃ j : Fin 8, j ≠ 0 := ⟨1, by decide⟩
      have hr := hread s hs j hj
      exact ⟨t, ⟨lonely_ge hj (by linarith [hr.1]) hr.2 ht htl, htT⟩, htl⟩
  have hall : ∀ n : ℕ, n < 8 → LRC.Spec.LonelyForSubject (chain A V n) 0 := by
    intro n
    induction n with
    | zero => intro _; exact hAP
    | succ n ih => intro hn; exact hstep n hn (ih (by omega))
  obtain ⟨t, ht, hlt⟩ := hall 7 (by norm_num)
  have hc7 : chain A V 7 = V := by
    ext j; simp only [chain]
    by_cases hj : (j : ℕ) = 0
    · have : j = 0 := Fin.ext hj
      subst this; simp [hA, hV]
    · rw [if_pos]; exact ⟨Nat.one_le_iff_ne_zero.mpr hj, Nat.lt_succ_iff.mp j.2⟩
  rw [hc7] at hlt
  refine ⟨t, ht, fun d hd => ?_⟩
  simp only [readingsOf, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true] at hd
  obtain ⟨j, hj, rfl⟩ := hd
  have := hlt j hj
  rw [LRC.PathRoute.sep_eq] at this
  have hle : v 0 ≤ v j := hslow j
  have e : ((Nat.dist (v j) (v 0) : ℕ) : ℝ) = V j - V 0 := by
    simp only [hV]; rw [Nat.dist_eq_sub_of_le_right hle]; push_cast [hle]; ring
  rw [e]; exact this

/-- **The conjecture at eight runners from the window.** -/
theorem lonelyRunnerAt8_of_window (hW : WindowBound) : LRC.Spec.LonelyRunnerAt8 :=
  LRC.EndRunner.lonelyRunnerAt8_of_slowest (fun v hv hslow => slowest_of_window hW v hv hslow)

end LRC.PathWindow
