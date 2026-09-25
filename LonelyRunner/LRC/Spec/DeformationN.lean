import LonelyRunner.LRC.Spec.Doors

/-!
# The deformation step: isolation carried along a path of speeds

2026-09-26.  The owner's argument: the arithmetic progression is globally isolated (the φ(n) law), every
arrangement is a deformation of it, and a deformation moves each runner's isolation point without destroying it.
This file states that argument as theorems about arrangements (`Arrangement.LonelyAt`), with its two conditions
explicit.

* **Openness** (`lonelyAt_of_close`).  If the subject is lonely at `t` with margin `ε` (every other runner at circle
  distance at least `1/8 + ε`), it is lonely at the same `t` in every arrangement whose speeds are all within `η` of
  these, as long as `2η|t| ≤ ε`.  `circDist` is 1-Lipschitz.
* **Closedness** (`lonelyAt_of_limit`).  If arrangements `vs n` converge to `v0` and each has the subject lonely at an
  instant `ts n` in a fixed window `[c, T]`, then `v0` has the subject lonely at some instant of `[c, T]`.  A bounded
  sequence of instants has a convergent subsequence and loneliness is a closed condition.  This is where "the
  isolation cannot escape to infinity" is used, and it is the only place.
* **The deformation theorem** (`lonely_along_path`).  Along a continuous path of speeds `p : ℝ → (Fin 8 → ℝ)`,
  if the subject is lonely at `p 0`, loneliness is locally stable along the path, and whenever the subject is lonely
  some lonely instant lies in a fixed window `[c, T]` with `c > 0`, then the subject is lonely at `p 1`.  Real
  induction on `[0, 1]` (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`).

The two conditions of the deformation theorem are hypotheses here, stated as what they are.  Local stability holds
wherever the lonely set has interior (`lonelyAt_of_close`); the window is the owner's "bounded by the speeds of the
arrangement".

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.Deformation

open Arrangement Filter Topology

theorem sep_sub (v w : Fin 8 → ℝ) (k i : Fin 8) (t : ℝ) :
    sep w k i t - sep v k i t = ((w i - v i) - (w k - v k)) * t := by
  unfold sep; ring

/-- **Openness.**  Loneliness with a margin survives every small enough change of speeds, at the same instant. -/
theorem lonelyAt_of_close {v w : Fin 8 → ℝ} {k : Fin 8} {t ε η : ℝ}
    (hmargin : ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ + ε ≤ circDist (sep v k i t))
    (hclose : ∀ i : Fin 8, |w i - v i| ≤ η) (hsmall : 2 * η * |t| ≤ ε) : LonelyAt w k t := by
  intro i hi
  have hlip := circDist_lipschitz.dist_le_mul (sep w k i t) (sep v k i t)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
  have h1 : |(w i - v i) - (w k - v k)| ≤ 2 * η := by
    have a := abs_le.mp (hclose i); have b := abs_le.mp (hclose k)
    rw [abs_le]; constructor <;> linarith
  have hd : |sep w k i t - sep v k i t| ≤ ε := by
    rw [sep_sub, abs_mul]
    calc |(w i - v i) - (w k - v k)| * |t| ≤ 2 * η * |t| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ ε := hsmall
  have := (abs_sub_le_iff.mp hlip).2
  have := hmargin i hi
  linarith

/-- **Closedness.**  A limit of arrangements whose subject is lonely at instants of a fixed window `[c, T]` has the
subject lonely at an instant of `[c, T]`. -/
theorem lonelyAt_of_limit {vs : ℕ → Fin 8 → ℝ} {v0 : Fin 8 → ℝ} {ts : ℕ → ℝ} {k : Fin 8} {c T : ℝ}
    (hconv : Tendsto vs atTop (𝓝 v0)) (hts : ∀ n, ts n ∈ Set.Icc c T)
    (hl : ∀ n, LonelyAt (vs n) k (ts n)) : ∃ t0 ∈ Set.Icc c T, LonelyAt v0 k t0 := by
  obtain ⟨t0, ht0, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hts
  refine ⟨t0, ht0, fun i hi => ?_⟩
  have hsub : Tendsto (fun n => vs (φ n)) atTop (𝓝 v0) := hconv.comp hφ.tendsto_atTop
  have hvi : Tendsto (fun n => vs (φ n) i) atTop (𝓝 (v0 i)) :=
    ((continuous_apply i).tendsto v0).comp hsub
  have hvk : Tendsto (fun n => vs (φ n) k) atTop (𝓝 (v0 k)) :=
    ((continuous_apply k).tendsto v0).comp hsub
  have ht : Tendsto (fun n => ts (φ n)) atTop (𝓝 t0) := hlim
  have hsep : Tendsto (fun n => sep (vs (φ n)) k i (ts (φ n))) atTop (𝓝 (sep v0 k i t0)) := by
    unfold sep
    exact (hvi.mul ht).sub (hvk.mul ht)
  have hcd : Tendsto (fun n => circDist (sep (vs (φ n)) k i (ts (φ n)))) atTop
      (𝓝 (circDist (sep v0 k i t0))) :=
    (circDist_lipschitz.continuous.tendsto _).comp hsep
  exact ge_of_tendsto' hcd (fun n => hl (φ n) i hi)

/-- **The deformation theorem.**  Along a continuous path of speeds, isolation present at the start, locally stable,
and never escaping a fixed window of instants `[c, T]` (`c > 0`), is present at the end. -/
theorem lonely_along_path {p : ℝ → Fin 8 → ℝ} (hp : Continuous p) {k : Fin 8} {c T : ℝ} (hc : 0 < c)
    (h0 : LRC.Spec.LonelyForSubject (p 0) k)
    (hopen : ∀ s ∈ Set.Icc (0 : ℝ) 1, LRC.Spec.LonelyForSubject (p s) k → ∀ᶠ r in 𝓝 s, LRC.Spec.LonelyForSubject (p r) k)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, LRC.Spec.LonelyForSubject (p s) k →
      ∃ t ∈ Set.Icc c T, LonelyAt (p s) k t) :
    LRC.Spec.LonelyForSubject (p 1) k := by
  set Λ : Set ℝ := {s | LRC.Spec.LonelyForSubject (p s) k} with hΛ
  -- closed on [0, 1]: sequences
  have hclosed : IsClosed (Λ ∩ Set.Icc (0 : ℝ) 1) := by
    apply IsSeqClosed.isClosed
    intro x s hx hxs
    have hIcc : s ∈ Set.Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hxs (Eventually.of_forall fun n => (hx n).2)
    refine ⟨?_, hIcc⟩
    choose ts hts hl using fun n => hbound (x n) (hx n).2 (hx n).1
    have hconv : Tendsto (fun n => p (x n)) atTop (𝓝 (p s)) := (hp.tendsto s).comp hxs
    obtain ⟨t0, ht0, hl0⟩ := lonelyAt_of_limit hconv hts hl
    exact ⟨t0, lt_of_lt_of_le hc ht0.1, hl0⟩
  have hsub := hclosed.Icc_subset_of_forall_mem_nhdsWithin (a := (0 : ℝ)) (b := 1) h0 (by
    intro x hx
    exact mem_nhdsWithin_of_mem_nhds (hopen x (Set.Ico_subset_Icc_self hx.2) hx.1))
  exact hsub (Set.right_mem_Icc.mpr zero_le_one)

/-- **Margin gives local stability along a path.**  If at `p s` the subject is lonely at `t > 0` with margin `ε > 0`,
then at every `r` near `s` the subject is lonely (at the same `t`). -/
theorem eventually_lonely_of_margin {p : ℝ → Fin 8 → ℝ} (hp : Continuous p) {k : Fin 8} {s t ε : ℝ}
    (hε : 0 < ε) (ht : 0 < t) (hm : ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ + ε ≤ circDist (sep (p s) k i t)) :
    ∀ᶠ r in 𝓝 s, LRC.Spec.LonelyForSubject (p r) k := by
  set η := ε / (2 * t) with hη
  have hη0 : 0 < η := by positivity
  have hev : ∀ᶠ r in 𝓝 s, ∀ i : Fin 8, |p r i - p s i| ≤ η := by
    rw [Filter.eventually_all]
    intro i
    have hc : Continuous (fun r => p r i) := (continuous_apply i).comp hp
    have := (Metric.tendsto_nhds.mp (hc.tendsto s)) η hη0
    filter_upwards [this] with r hr
    rw [Real.dist_eq] at hr; exact hr.le
  filter_upwards [hev] with r hr
  refine ⟨t, ht, lonelyAt_of_close hm hr ?_⟩
  rw [abs_of_pos ht, hη]; field_simp; ring_nf; exact le_refl _

/-- **The deformation theorem, with margin.**  Along a continuous path of speeds: lonely at the start; wherever the
subject is lonely it is lonely somewhere with a positive margin; and some lonely instant always lies in `[c, T]`,
`c > 0`.  Then the subject is lonely at the end. -/
theorem lonely_along_path_of_margin {p : ℝ → Fin 8 → ℝ} (hp : Continuous p) {k : Fin 8} {c T : ℝ}
    (hc : 0 < c) (h0 : LRC.Spec.LonelyForSubject (p 0) k)
    (hmargin : ∀ s ∈ Set.Icc (0 : ℝ) 1, LRC.Spec.LonelyForSubject (p s) k →
      ∃ t ε : ℝ, 0 < t ∧ 0 < ε ∧ ∀ i : Fin 8, i ≠ k → (8 : ℝ)⁻¹ + ε ≤ circDist (sep (p s) k i t))
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, LRC.Spec.LonelyForSubject (p s) k →
      ∃ t ∈ Set.Icc c T, LonelyAt (p s) k t) :
    LRC.Spec.LonelyForSubject (p 1) k := by
  refine lonely_along_path hp hc h0 ?_ hbound
  intro s hs hl
  obtain ⟨t, ε, ht, hε, hm⟩ := hmargin s hs hl
  exact eventually_lonely_of_margin hp hε ht hm

end LRC.Deformation
