import Mathlib
import Fresh.Framework
import Fresh.Grid
import Fresh.Localisation
import Fresh.LonelyCells
import Fresh.Gate

/-!
# Path laws: openness, closedness and the dichotomy for the isolation set (Task AE)

Written 2026-10-08.  Imports `Mathlib`, `Fresh.Framework` and the Fresh modules `Grid`, `Localisation`, `LonelyCells`,
`Gate`; nothing from the existing `LonelyRunner` repo.  Exact reals; every speed positive; nothing is counted, covered
or bounded as the shape of a result.

Setting.  A path of speeds `v : ℝ → Fin 8 → ℝ`, `ContinuousOn v (Set.Icc 0 1)` (as `Framework.DisplacementPath`), a
fixed subject `k`.  The reading of runner `i` at parameter `s` and instant `t` is `(v s i - v s k) * t`.  The pair
`(s, t)` is *lonely* when `IsolatedAt (v s) k t`.  The *isolation set* is
`isoSet v k = {s ∈ [0,1] | ∃ t > 0, IsolatedAt (v s) k t}` (`Framework.Isolation`).

Results ([L] = Lean, `#print axioms` below each).
* (0) `distInt_lipschitz`: `|distInt x - distInt y| ≤ |x - y|`.
* (1) OPENNESS.  `isolatedAt_transfer` (the explicit modulus: if `(s₀, t₀)` is lonely with margin `e`, and the
  readings at `(s, t)` differ from the readings at `(s₀, t₀)` by at most `e`, then `(s, t)` is lonely);
  `isolatedAt_transfer_s` (fixed instant: `|Δ reading| * t₀ ≤ e`); `isolatedAt_transfer_t` (fixed parameter:
  `|t - t₀| * |reading| ≤ e`); `openness_s`, `openness_t` (the same, as neighbourhoods, from continuity).
* (2) CLOSEDNESS.  `lonely_limit`: `(s_a, t_a)` lonely, `s_a → s₀`, `t_a → t₀` (a FINITE limit) implies `(s₀, t₀)`
  lonely, and `t₀ ≠ 0` automatically (`not_isolatedAt_zero`); with `t_a > 0`, `t₀ > 0` (`lonely_limit_pos`).
* ESCAPE.  `lonely_time_lower` (`1/8 ≤ |reading| * t` at a lonely instant, so `t ≥ 1/(8 |reading|)`);
  `lonely_time_escapes` (if a reading tends to `0` along lonely `(s_a, t_a)`, then `t_a → ∞`);
  `not_isolatedAt_of_coincide` (two equal speeds: no lonely instant at all).  The explicit family `escapeEx`
  (speeds `(1, 1+s, 3, 4, …, 8)`, subject `0`): at `s_N = 1/(2N)` the instant `N + 1/8` is lonely
  (`escapeEx_lonely`), `s_N → 0`, `t_N → ∞`, and at `s = 0` (two speeds equal, so not an arrangement) there is no
  lonely instant (`escapeEx_zero_none`).
* (3) THE DICHOTOMY.  `isoSet_closed_of_bdd` (bounded limits stay in the isolation set); `isoSet_dichotomy`
  (`s_n ∈ Z`, `s_n → s₀ ∈ [0,1]`: either every witness sequence tends to `∞` or `s₀ ∈ Z`);
  `isoSet_open_of_strict` (a lonely point of positive margin at `s₀` gives `Z` a neighbourhood of `s₀`);
  `strict_iff_margin`; `interior_iff_strict` (a lonely instant is an interior point of the lonely set iff every
  runner is strictly clear); `loss_needs_boundary` (if `s₀ ∈ Z` but `Z` is not a neighbourhood of `s₀`, every lonely
  instant at `s₀` has a runner at exactly `1/8`, is not interior, and no lonely interval of positive width exists at
  `s₀`); `isoSet_open_of_cell` (a cell of positive width at `s₀` gives `Z` a neighbourhood of `s₀`, via
  `Gate.interior_strictly_clear`).
* The content OWED, named and not assumed: `PathLonelyBound` (a uniform bound on the lonely witnesses; cap-shaped,
  rule 7) and `SuccessorIsolation` (isolation at `s₀` persists to a neighbourhood).  `isoSet_eq_of_owed` is the
  CONDITIONAL implication from these two (plus `0 ∈ Z`) to `Z = [0,1]`; it is recorded to show where the two owed
  statements enter, it is not offered as the argument.

Provenance.  The existing repo has the same circle-distance continuity in `LRC/Cascade/Arrangement.lean` and the
path/continuity discussion in `LRC/Spec`; I did not locate a declaration for the dichotomy and wrote every proof here
(no proof copied).  `Gate.interior_strictly_clear`, `Gate.lonelyAt_image_iff`, `Gate.cell_persists` and
`Gate.lonely_interval_ceases_only_at_touch` are reused from this folder.
-/

open Classical Filter Topology

namespace Fresh

namespace PathLaws

/-! ## (0) Lipschitz bound for the circle distance -/

/-- `distInt` is 1-Lipschitz [L]. -/
theorem distInt_lipschitz (x y : ℝ) : |distInt x - distInt y| ≤ |x - y| := by
  have h : ∀ a b : ℝ, distInt a ≤ distInt b + |a - b| := by
    intro a b
    have h1 := Localisation.distInt_le a (round b)
    have h2 : |a - ((round b : ℤ) : ℝ)| ≤ |a - b| + |b - ((round b : ℤ) : ℝ)| := by
      have := abs_add_le (a - b) (b - ((round b : ℤ) : ℝ))
      simpa using this
    have h3 : distInt b = |b - ((round b : ℤ) : ℝ)| := rfl
    linarith
  have h1 := h x y
  have h2 := h y x
  rw [abs_sub_comm y x] at h2
  rw [abs_le]
  constructor <;> linarith

#print axioms distInt_lipschitz

theorem continuous_distInt : Continuous distInt := by
  have : LipschitzWith 1 distInt := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simpa [Real.dist_eq] using distInt_lipschitz x y
  exact this.continuous

#print axioms continuous_distInt

/-! ## (1) Openness, with an explicit modulus -/

/-- **The transfer lemma (explicit modulus)** [L]: if every runner other than `k` is at distance at least `1/8 + e`
at `(v, t)`, and the readings at `(w, t')` differ from those by at most `e`, then `k` is isolated for `w` at `t'`. -/
theorem isolatedAt_transfer {v w : Fin 8 → ℝ} {k : Fin 8} {t t' e : ℝ}
    (h : ∀ i, i ≠ k → 1 / 8 + e ≤ distInt ((v i - v k) * t))
    (hclose : ∀ i, i ≠ k → |(w i - w k) * t' - (v i - v k) * t| ≤ e) : IsolatedAt w k t' := by
  intro i hi
  have h1 := distInt_lipschitz ((w i - w k) * t') ((v i - v k) * t)
  have h2 := hclose i hi
  have h3 := h i hi
  have h4 := (abs_le.mp h1).1
  linarith

#print axioms isolatedAt_transfer

/-- Fixed instant: the modulus is `|(w i - w k) - (v i - v k)| * t ≤ e` [L]. -/
theorem isolatedAt_transfer_s {v w : Fin 8 → ℝ} {k : Fin 8} {t e : ℝ} (ht : 0 ≤ t)
    (h : ∀ i, i ≠ k → 1 / 8 + e ≤ distInt ((v i - v k) * t))
    (hclose : ∀ i, i ≠ k → |(w i - w k) - (v i - v k)| * t ≤ e) : IsolatedAt w k t := by
  refine isolatedAt_transfer h fun i hi => ?_
  have : (w i - w k) * t - (v i - v k) * t = ((w i - w k) - (v i - v k)) * t := by ring
  rw [this, abs_mul, abs_of_nonneg ht]
  exact hclose i hi

#print axioms isolatedAt_transfer_s

/-- Fixed parameter: the modulus is `|t' - t| * |v i - v k| ≤ e` [L]. -/
theorem isolatedAt_transfer_t {v : Fin 8 → ℝ} {k : Fin 8} {t t' e : ℝ}
    (h : ∀ i, i ≠ k → 1 / 8 + e ≤ distInt ((v i - v k) * t))
    (hclose : ∀ i, i ≠ k → |t' - t| * |v i - v k| ≤ e) : IsolatedAt v k t' := by
  refine isolatedAt_transfer h fun i hi => ?_
  have : (v i - v k) * t' - (v i - v k) * t = (v i - v k) * (t' - t) := by ring
  rw [this, abs_mul, mul_comm]
  exact hclose i hi

#print axioms isolatedAt_transfer_t

/-- **Openness in the parameter** [L]: a lonely point `(s₀, t₀)` of margin `e > 0` stays lonely at `t₀` for every `s`
in `[0,1]` near `s₀`.  (`t₀ ≥ 0` is all that is used; the explicit modulus is `isolatedAt_transfer_s`.) -/
theorem openness_s {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1)
    {k : Fin 8} {t₀ e : ℝ} (ht₀ : 0 ≤ t₀) (he : 0 < e)
    (h : ∀ i, i ≠ k → 1 / 8 + e ≤ distInt ((v s₀ i - v s₀ k) * t₀)) :
    ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, IsolatedAt (v s) k t₀ := by
  have hc : ContinuousWithinAt v (Set.Icc 0 1) s₀ := hv s₀ hs₀
  have hall' : ∀ i, ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, |(v s i - v s k) - (v s₀ i - v s₀ k)| * t₀ ≤ e := by
    intro i
    have hi : ContinuousWithinAt (fun s => v s i - v s k) (Set.Icc 0 1) s₀ :=
      ((continuousAt_apply i _).comp_continuousWithinAt hc).sub
        ((continuousAt_apply k _).comp_continuousWithinAt hc)
    have hg : ContinuousWithinAt (fun s => |(v s i - v s k) - (v s₀ i - v s₀ k)| * t₀) (Set.Icc 0 1) s₀ :=
      ((hi.sub continuousWithinAt_const).abs).mul continuousWithinAt_const
    have h0 : |(v s₀ i - v s₀ k) - (v s₀ i - v s₀ k)| * t₀ = 0 := by simp
    have ht : Tendsto (fun s => |(v s i - v s k) - (v s₀ i - v s₀ k)| * t₀) (𝓝[Set.Icc 0 1] s₀) (𝓝 0) := by
      simpa [h0] using hg.tendsto
    exact (ht.eventually_lt_const he).mono fun s hs => hs.le
  have := (Filter.eventually_all.mpr hall')
  filter_upwards [this] with s hs
  exact isolatedAt_transfer_s ht₀ h fun i _ => hs i

#print axioms openness_s

/-- **Openness in the instant** [L]: for fixed `s`, a lonely `t₀` of margin `e > 0` stays lonely for `t` near `t₀`. -/
theorem openness_t (v : Fin 8 → ℝ) {k : Fin 8} {t₀ e : ℝ} (he : 0 < e)
    (h : ∀ i, i ≠ k → 1 / 8 + e ≤ distInt ((v i - v k) * t₀)) :
    ∀ᶠ t in 𝓝 t₀, IsolatedAt v k t := by
  have hall : ∀ i, ∀ᶠ t in 𝓝 t₀, |t - t₀| * |v i - v k| ≤ e := by
    intro i
    have hg : Continuous fun t : ℝ => |t - t₀| * |v i - v k| := by fun_prop
    have h0 : |t₀ - t₀| * |v i - v k| = 0 := by simp
    have ht : Tendsto (fun t : ℝ => |t - t₀| * |v i - v k|) (𝓝 t₀) (𝓝 0) := by
      simpa [h0] using hg.tendsto t₀
    exact (ht.eventually_lt_const he).mono fun t hs => hs.le
  filter_upwards [Filter.eventually_all.mpr hall] with t ht
  exact isolatedAt_transfer_t h fun i _ => ht i

#print axioms openness_t

/-! ## (2) Closedness -/

/-- At instant `0` nobody is isolated (the reading of every runner is `0`) [L]. -/
theorem not_isolatedAt_zero (v : Fin 8 → ℝ) (k : Fin 8) : ¬ IsolatedAt v k 0 := by
  intro h
  obtain ⟨i, hi⟩ : ∃ i : Fin 8, i ≠ k := by
    by_cases hk : k = 0
    · exact ⟨1, by rw [hk]; decide⟩
    · exact ⟨0, fun h => hk h.symm⟩
  have := h i hi
  have h0 : distInt ((v i - v k) * 0) = 0 := by simp [distInt]
  linarith [h0]

#print axioms not_isolatedAt_zero

/-- **Closedness of the lonely set, for a finite limit** [L]: along any filter, if `s_a → s₀` inside `[0,1]`,
`t_a → t₀` (a finite real) and each `(s_a, t_a)` is lonely, then `(s₀, t₀)` is lonely.  Continuity of the path on
`[0,1]` is all that is used. -/
theorem lonely_limit {α : Type*} {l : Filter α} [l.NeBot] {v : ℝ → Fin 8 → ℝ}
    (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8} {s t : α → ℝ} {s₀ t₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) (hs : ∀ a, s a ∈ Set.Icc (0 : ℝ) 1)
    (hst : Tendsto s l (𝓝 s₀)) (htt : Tendsto t l (𝓝 t₀))
    (hl : ∀ a, IsolatedAt (v (s a)) k (t a)) : IsolatedAt (v s₀) k t₀ := by
  intro i hi
  have hs' : Tendsto s l (𝓝[Set.Icc 0 1] s₀) := tendsto_nhdsWithin_iff.mpr ⟨hst, Filter.Eventually.of_forall hs⟩
  have hc : Tendsto (fun a => v (s a)) l (𝓝 (v s₀)) := (hv s₀ hs₀).tendsto.comp hs'
  have hi' : Tendsto (fun a => v (s a) i - v (s a) k) l (𝓝 (v s₀ i - v s₀ k)) :=
    ((continuous_apply i).tendsto _ |>.comp hc).sub ((continuous_apply k).tendsto _ |>.comp hc)
  have hm : Tendsto (fun a => distInt ((v (s a) i - v (s a) k) * t a)) l (𝓝 (distInt ((v s₀ i - v s₀ k) * t₀))) :=
    (continuous_distInt.tendsto _).comp (hi'.mul htt)
  exact ge_of_tendsto hm (Filter.Eventually.of_forall fun a => hl a i hi)

#print axioms lonely_limit

/-- With positive instants, the limit instant is positive: `t₀ = 0` is excluded by `not_isolatedAt_zero` [L]. -/
theorem lonely_limit_pos {α : Type*} {l : Filter α} [l.NeBot] {v : ℝ → Fin 8 → ℝ}
    (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8} {s t : α → ℝ} {s₀ t₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) (hs : ∀ a, s a ∈ Set.Icc (0 : ℝ) 1)
    (hst : Tendsto s l (𝓝 s₀)) (htt : Tendsto t l (𝓝 t₀))
    (hl : ∀ a, IsolatedAt (v (s a)) k (t a)) (hpos : ∀ a, 0 < t a) :
    0 < t₀ ∧ IsolatedAt (v s₀) k t₀ := by
  have hlim := lonely_limit hv hs₀ hs hst htt hl
  have hge : 0 ≤ t₀ := ge_of_tendsto htt (Filter.Eventually.of_forall fun a => (hpos a).le)
  refine ⟨lt_of_le_of_ne hge fun h0 => ?_, hlim⟩
  rw [← h0] at hlim
  exact not_isolatedAt_zero _ _ hlim

#print axioms lonely_limit_pos

/-! ## Escape to infinity -/

/-- A lonely instant satisfies `1/8 ≤ |reading| * t` for every runner [L]. -/
theorem lonely_time_lower {v : Fin 8 → ℝ} {k : Fin 8} {t : ℝ} (ht : 0 ≤ t) (h : IsolatedAt v k t) {i : Fin 8}
    (hi : i ≠ k) : 1 / 8 ≤ |v i - v k| * t := by
  have h1 := h i hi
  have h2 := Localisation.distInt_le ((v i - v k) * t) 0
  simp only [Int.cast_zero, sub_zero] at h2
  rw [abs_mul, abs_of_nonneg ht] at h2
  linarith

#print axioms lonely_time_lower

/-- **Escape is forced when a reading tends to `0`** [L]: if `(s_a, t_a)` is lonely with `t_a > 0` and runner `i`'s
reading `v (s_a) i - v (s_a) k` tends to `0`, then `t_a → ∞`.  This is the quantitative content of the lower bound
`1/(8 d_min) ≤ t` (Theorem 7; `Localisation.lonely_ge_bound`). -/
theorem lonely_time_escapes {α : Type*} {l : Filter α} {v : α → Fin 8 → ℝ} {k : Fin 8} {t : α → ℝ} {i : Fin 8}
    (hi : i ≠ k) (hl : ∀ a, IsolatedAt (v a) k (t a)) (hpos : ∀ a, 0 < t a)
    (h0 : Tendsto (fun a => v a i - v a k) l (𝓝 0)) : Tendsto t l atTop := by
  rw [tendsto_atTop]
  intro B
  have hB : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsmall : ∀ᶠ a in l, |v a i - v a k| < 1 / (8 * max B 1) := by
    have h0' : Tendsto (fun a => |v a i - v a k|) l (𝓝 0) := by simpa using h0.abs
    exact h0'.eventually_lt_const (by positivity)
  filter_upwards [hsmall] with a ha
  by_contra hlt
  rw [not_le] at hlt
  have h1 := lonely_time_lower (hpos a).le (hl a) hi
  have hlt' : t a ≤ max B 1 := (hlt.trans_le (le_max_left _ _)).le
  have h2 : |v a i - v a k| * t a ≤ |v a i - v a k| * max B 1 :=
    mul_le_mul_of_nonneg_left hlt' (abs_nonneg _)
  have h3 : |v a i - v a k| * max B 1 < 1 / (8 * max B 1) * max B 1 := mul_lt_mul_of_pos_right ha hB
  have h4 : 1 / (8 * max B 1) * max B 1 = 1 / 8 := by field_simp
  linarith

#print axioms lonely_time_escapes

/-- Two equal speeds: no instant is lonely [L].  This is the obstruction that rule 4 says an arrangement never meets. -/
theorem not_isolatedAt_of_coincide {v : Fin 8 → ℝ} {k i : Fin 8} (hi : i ≠ k) (hvi : v i = v k) (t : ℝ) :
    ¬ IsolatedAt v k t := by
  intro h
  have := h i hi
  have h0 : distInt ((v i - v k) * t) = 0 := by simp [hvi, distInt]
  linarith

#print axioms not_isolatedAt_of_coincide

/-- The explicit family: subject `0` at speed `1`, runner `1` at speed `1 + s`, the others at `3, 4, …, 8`. -/
def escapeEx (s : ℝ) : Fin 8 → ℝ := ![1, 1 + s, 3, 4, 5, 6, 7, 8]

theorem escapeEx_pos {s : ℝ} (hs : 0 ≤ s) : ∀ i, 0 < escapeEx s i := by
  intro i
  fin_cases i <;> simp [escapeEx] <;> linarith

/-- For `0 < s < 2` the speeds are pairwise distinct: `escapeEx s` is an arrangement [L]. -/
theorem escapeEx_arrangement {s : ℝ} (hs : 0 < s) (hs2 : s < 1) : IsArrangement (escapeEx s) := by
  refine ⟨escapeEx_pos hs.le, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [escapeEx] at hij ⊢ <;> linarith

/-- At `s = 0` runners `0` and `1` coincide: the endpoint is not an arrangement [L]. -/
theorem escapeEx_zero_none (t : ℝ) : ¬ IsolatedAt (escapeEx 0) 0 t :=
  not_isolatedAt_of_coincide (i := 1) (by decide) (by simp [escapeEx]) t

theorem escapeEx_continuous : Continuous escapeEx := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [escapeEx] <;> fun_prop

/-- The lonely instant `N + 1/8` at `s = 1/(2N)` (`N ≥ 1`) [L]. -/
theorem escapeEx_lonely (N : ℕ) (hN : 1 ≤ N) :
    IsolatedAt (escapeEx (1 / (2 * (N : ℝ)))) 0 ((N : ℝ) + 1 / 8) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  intro i hi
  -- runners 2..7 : reading j * (N + 1/8) = j/8 + j*N
  have key : ∀ j : ℕ, 2 ≤ j → j ≤ 7 → (1 / 8 : ℝ) ≤ distInt ((j : ℝ) * ((N : ℝ) + 1 / 8)) := by
    intro j hj2 hj7
    have : (j : ℝ) * ((N : ℝ) + 1 / 8) = (j : ℝ) / 8 + ((j * N : ℤ) : ℝ) := by push_cast; ring
    rw [this, distInt_add_int]
    have hnd : ¬ (8 : ℤ) ∣ (j : ℤ) := by
      intro hd
      have := Int.le_of_dvd (by omega) hd
      omega
    simpa using distInt_int_div_eight hnd
  fin_cases i
  · exact absurd rfl hi
  · -- runner 1
    have hread : (escapeEx (1 / (2 * (N : ℝ))) 1 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8)
        = 1 / 2 + 1 / (16 * N) := by
      simp [escapeEx]; field_simp; ring
    show (1 / 8 : ℝ) ≤ distInt ((escapeEx (1 / (2 * (N : ℝ))) 1 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8))
    rw [hread, Localisation.le_distInt_iff]
    intro z
    have hq : 0 < 1 / (16 * (N : ℝ)) := by positivity
    have hq' : 1 / (16 * (N : ℝ)) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    rcases le_or_gt z 0 with hz | hz
    · have : (z : ℝ) ≤ 0 := by exact_mod_cast hz
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (1 : ℝ) ≤ z := by exact_mod_cast hz
      rw [abs_of_nonpos (by linarith)]; linarith
  · have e : escapeEx (1 / (2 * (N : ℝ))) 2 - escapeEx (1 / (2 * (N : ℝ))) 0 = ((2 : ℕ) : ℝ) := by
      simp [escapeEx]; norm_num
    show (1 / 8 : ℝ) ≤ distInt ((escapeEx (1 / (2 * (N : ℝ))) 2 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8))
    rw [e]; exact key 2 (by norm_num) (by norm_num)
  · have e : escapeEx (1 / (2 * (N : ℝ))) 3 - escapeEx (1 / (2 * (N : ℝ))) 0 = ((3 : ℕ) : ℝ) := by
      simp [escapeEx]; norm_num
    show (1 / 8 : ℝ) ≤ distInt ((escapeEx (1 / (2 * (N : ℝ))) 3 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8))
    rw [e]; exact key 3 (by norm_num) (by norm_num)
  · have e : escapeEx (1 / (2 * (N : ℝ))) 4 - escapeEx (1 / (2 * (N : ℝ))) 0 = ((4 : ℕ) : ℝ) := by
      simp [escapeEx]; norm_num
    show (1 / 8 : ℝ) ≤ distInt ((escapeEx (1 / (2 * (N : ℝ))) 4 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8))
    rw [e]; exact key 4 (by norm_num) (by norm_num)
  · have e : escapeEx (1 / (2 * (N : ℝ))) 5 - escapeEx (1 / (2 * (N : ℝ))) 0 = ((5 : ℕ) : ℝ) := by
      simp [escapeEx]; norm_num
    show (1 / 8 : ℝ) ≤ distInt ((escapeEx (1 / (2 * (N : ℝ))) 5 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8))
    rw [e]; exact key 5 (by norm_num) (by norm_num)
  · have e : escapeEx (1 / (2 * (N : ℝ))) 6 - escapeEx (1 / (2 * (N : ℝ))) 0 = ((6 : ℕ) : ℝ) := by
      simp [escapeEx]; norm_num
    show (1 / 8 : ℝ) ≤ distInt ((escapeEx (1 / (2 * (N : ℝ))) 6 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8))
    rw [e]; exact key 6 (by norm_num) (by norm_num)
  · have e : escapeEx (1 / (2 * (N : ℝ))) 7 - escapeEx (1 / (2 * (N : ℝ))) 0 = ((7 : ℕ) : ℝ) := by
      simp [escapeEx]; norm_num
    show (1 / 8 : ℝ) ≤ distInt ((escapeEx (1 / (2 * (N : ℝ))) 7 - escapeEx (1 / (2 * (N : ℝ))) 0) * ((N : ℝ) + 1 / 8))
    rw [e]; exact key 7 (by norm_num) (by norm_num)


#print axioms escapeEx_pos
#print axioms escapeEx_arrangement
#print axioms escapeEx_zero_none
#print axioms escapeEx_continuous
#print axioms escapeEx_lonely

/-- **The escape sequence** [L]: along `s_N = 1/(2(N+1)) → 0` (each `escapeEx s_N` an arrangement, the path
continuous with positive speeds on `[0,1]`), the instants `t_N = N + 1 + 1/8 → ∞` are lonely for subject `0`, and at
the limit `s = 0` no instant is lonely.  So the finite-limit hypothesis of `lonely_limit` cannot be dropped in general;
the failure here is that the limit is not an arrangement (two speeds coincide), which `lonely_time_escapes` shows is
the only way a reading can tend to `0`. -/
theorem escapeEx_escape :
    ContinuousOn escapeEx (Set.Icc 0 1) ∧ (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i, 0 < escapeEx s i) ∧
    (∀ N : ℕ, IsArrangement (escapeEx (1 / (2 * ((N : ℝ) + 1)))) ∧
        IsolatedAt (escapeEx (1 / (2 * ((N : ℝ) + 1)))) 0 (((N : ℝ) + 1) + 1 / 8)) ∧
    Tendsto (fun N : ℕ => 1 / (2 * ((N : ℝ) + 1))) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) + 1 / 8) atTop atTop ∧
    (∀ t, ¬ IsolatedAt (escapeEx 0) 0 t) := by
  refine ⟨escapeEx_continuous.continuousOn, fun s hs => escapeEx_pos hs.1, fun N => ?_, ?_, ?_,
    escapeEx_zero_none⟩
  · have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hs : 0 < 1 / (2 * ((N : ℝ) + 1)) := by positivity
    have hs1 : 1 / (2 * ((N : ℝ) + 1)) < 1 := by
      rw [div_lt_one (by positivity)]; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
    refine ⟨escapeEx_arrangement hs hs1, ?_⟩
    have := escapeEx_lonely (N + 1) (by omega)
    push_cast at this
    exact this
  · have h1 : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => 2 * ((N : ℝ) + 1)) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) h1
    have := h2.inv_tendsto_atTop
    simpa only [one_div] using this
  · exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

#print axioms escapeEx_escape


/-! ## (3) The isolation set and the dichotomy -/

/-- The isolation set of a path: parameters in `[0,1]` at which subject `k` is isolated at some positive instant. -/
def isoSet (v : ℝ → Fin 8 → ℝ) (k : Fin 8) : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) 1 ∧ Isolation (v s) k}

theorem exists_ne (k : Fin 8) : ∃ i : Fin 8, i ≠ k := by
  by_cases hk : k = 0
  · exact ⟨1, by rw [hk]; decide⟩
  · exact ⟨0, fun h => hk h.symm⟩

/-- **Closedness of the isolation set under bounded limits** [L]: if `s_n ∈ [0,1]`, `s_n → s₀`, each `s_n` has a lonely
instant `t_n > 0`, and the `t_n` are bounded above, then `s₀` is in the isolation set.  The proof extracts a convergent
subsequence of the bounded `t_n` (Bolzano) and applies `lonely_limit_pos`. -/
theorem isoSet_closed_of_bdd {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8}
    {s t : ℕ → ℝ} {s₀ B : ℝ} (hs : ∀ n, s n ∈ Set.Icc (0 : ℝ) 1) (hst : Tendsto s atTop (𝓝 s₀))
    (hl : ∀ n, IsolatedAt (v (s n)) k (t n)) (hpos : ∀ n, 0 < t n) (hB : ∀ n, t n ≤ B) : s₀ ∈ isoSet v k := by
  have hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1 :=
    isClosed_Icc.mem_of_tendsto hst (Filter.Eventually.of_forall hs)
  obtain ⟨t₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (0 : ℝ) B)
    (x := t) (fun n => ⟨(hpos n).le, hB n⟩)
  have hsφ : Tendsto (s ∘ φ) atTop (𝓝 s₀) := hst.comp hφ.tendsto_atTop
  obtain ⟨h0, hiso⟩ := lonely_limit_pos hv hs₀ (fun n => hs (φ n)) hsφ hlim (fun n => hl (φ n))
    (fun n => hpos (φ n))
  exact ⟨hs₀, t₀, h0, hiso⟩

#print axioms isoSet_closed_of_bdd

/-- **The dichotomy for a sequence in the isolation set** [L]: if `s_n → s₀`, with `s_n` having lonely instants
`t_n > 0`, then either `t_n → ∞` (the witnesses escape; nothing is claimed at `s₀`) or `s₀` is in the isolation set.
The `t_n` are arbitrary: no bound is assumed.  What this does NOT say is that the first alternative cannot occur at an
arrangement `s₀`: that is the content owed (`PathLonelyBound`, `SuccessorIsolation`), not a result. -/
theorem isoSet_dichotomy {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8}
    {s t : ℕ → ℝ} {s₀ : ℝ} (hs : ∀ n, s n ∈ Set.Icc (0 : ℝ) 1) (hst : Tendsto s atTop (𝓝 s₀))
    (hl : ∀ n, IsolatedAt (v (s n)) k (t n)) (hpos : ∀ n, 0 < t n) :
    Tendsto t atTop atTop ∨ s₀ ∈ isoSet v k := by
  by_cases h : Tendsto t atTop atTop
  · exact Or.inl h
  · right
    rw [tendsto_atTop] at h
    push Not at h
    obtain ⟨b, hb⟩ := h
    have hfreq : ∃ᶠ n in atTop, t n < b := hb
    obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_of_frequently_atTop hfreq
    exact isoSet_closed_of_bdd hv (s := s ∘ φ) (t := t ∘ φ) (B := b) (fun n => hs (φ n))
      (hst.comp hφ.tendsto_atTop) (fun n => hl (φ n)) (fun n => hpos (φ n)) (fun n => (hφb n).le)

#print axioms isoSet_dichotomy

/-- Strict clearness at every other runner is the same as a positive margin [L]. -/
theorem strict_iff_margin (f : Fin 8 → ℝ) (k : Fin 8) :
    (∃ e : ℝ, 0 < e ∧ ∀ i, i ≠ k → 1 / 8 + e ≤ f i) ↔ ∀ i, i ≠ k → 1 / 8 < f i := by
  constructor
  · rintro ⟨e, he, h⟩ i hi
    linarith [h i hi]
  · intro h
    obtain ⟨j, hj⟩ := exists_ne k
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.univ.erase k) f
      ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
    have hi₀k : i₀ ≠ k := (Finset.mem_erase.mp hi₀).1
    refine ⟨(f i₀ - 1 / 8) / 2, by linarith [h i₀ hi₀k], fun i hi => ?_⟩
    have := hmin i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    have h1 := h i₀ hi₀k
    linarith

#print axioms strict_iff_margin

/-- **Openness of the isolation set at a lonely point of positive margin** [L]: if `(s₀, t₀)` is lonely with every other
runner strictly clear, then every `s` in `[0,1]` near `s₀` is in the isolation set (witness `t₀`). -/
theorem isoSet_open_of_strict {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {k : Fin 8} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ i, i ≠ k → 1 / 8 < distInt ((v s₀ i - v s₀ k) * t₀)) :
    ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, s ∈ isoSet v k := by
  obtain ⟨e, he, hm⟩ := (strict_iff_margin (fun i => distInt ((v s₀ i - v s₀ k) * t₀)) k).mpr h
  filter_upwards [openness_s hv hs₀ ht₀.le he hm, self_mem_nhdsWithin] with s hs hsI
  exact ⟨hsI, t₀, ht₀, hs⟩

#print axioms isoSet_open_of_strict

/-- The disparities of subject `k`, indexed by the other runners (absolute values of the readings). -/
def absRead (v : Fin 8 → ℝ) (k : Fin 8) : {i : Fin 8 // i ≠ k} → ℝ := fun i => |v i.1 - v k|

/-- `IsolatedAt` is the lonely condition of `Cascade` for the disparities `absRead` [L]. -/
theorem isolatedAt_iff_lonelyAt (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    IsolatedAt v k t ↔ Cascade.LonelyAt (Finset.univ.image (absRead v k)) t := by
  rw [Gate.lonelyAt_image_iff]
  constructor
  · intro h i
    simp only [absRead]
    rw [Localisation.distInt_abs_mul]
    exact h i.1 i.2
  · intro h i hi
    have := h ⟨i, hi⟩
    simp only [absRead] at this
    rw [Localisation.distInt_abs_mul] at this
    exact this

#print axioms isolatedAt_iff_lonelyAt

/-- **Interior points of the lonely set** [L]: a lonely instant is an interior point of the lonely set exactly when every
other runner is strictly clear at it (so a runner standing at exactly `1/8` is a boundary point).  `←` is `openness_t`;
`→` is `Gate.interior_strictly_clear` applied to a small lonely interval around the instant. -/
theorem interior_iff_strict (v : Fin 8 → ℝ) (k : Fin 8) {t₀ : ℝ} (hl : IsolatedAt v k t₀) :
    t₀ ∈ interior {t | IsolatedAt v k t} ↔ ∀ i, i ≠ k → 1 / 8 < distInt ((v i - v k) * t₀) := by
  constructor
  · intro hint
    have hnhds : {t | IsolatedAt v k t} ∈ 𝓝 t₀ := mem_interior_iff_mem_nhds.mp hint
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    have hpos : ∀ d ∈ Finset.univ.image (absRead v k), 0 < d := by
      intro d hd
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
      have h1 := hl i.1 i.2
      have hne : v i.1 - v k ≠ 0 := by
        intro h0
        have : distInt ((v i.1 - v k) * t₀) = 0 := by simp [h0, distInt]
        linarith
      exact abs_pos.mpr hne
    have hsub : Set.Icc (t₀ - ε / 2) (t₀ + ε / 2) ⊆ LonelyCells.lonelySet (Finset.univ.image (absRead v k)) := by
      intro t ht
      have : t ∈ Metric.ball t₀ ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [ht.1, ht.2]
      exact (isolatedAt_iff_lonelyAt v k t).mp (hball this)
    intro i hi
    have := Gate.interior_strictly_clear hpos hsub (by linarith : t₀ - ε / 2 < t₀)
      (by linarith : t₀ < t₀ + ε / 2) (d := absRead v k ⟨i, hi⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    simp only [absRead] at this
    rwa [Localisation.distInt_abs_mul] at this
  · intro h
    obtain ⟨e, he, hm⟩ := (strict_iff_margin (fun i => distInt ((v i - v k) * t₀)) k).mpr h
    exact mem_interior_iff_mem_nhds.mpr (openness_t v he hm)

#print axioms interior_iff_strict

/-- **How an isolation can be lost** [L]: suppose `s₀` is in the isolation set but the isolation set is not a
neighbourhood of `s₀` in `[0,1]`.  Then every lonely instant `t > 0` at `s₀` has some runner at exactly `1/8` (zero
margin) and is not an interior point of the lonely set.  Equivalently, at a loss every positive lonely point of `s₀`
is a boundary point; this is `isoSet_open_of_strict` read backwards.  Nothing here says a loss occurs or does not. -/
theorem loss_needs_boundary {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {k : Fin 8}
    (hnot : ¬ ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, s ∈ isoSet v k) :
    ∀ t : ℝ, 0 < t → IsolatedAt (v s₀) k t →
      (∃ i, i ≠ k ∧ distInt ((v s₀ i - v s₀ k) * t) = 1 / 8) ∧ t ∉ interior {t | IsolatedAt (v s₀) k t} := by
  intro t ht hl
  have hns : ¬ ∀ i, i ≠ k → 1 / 8 < distInt ((v s₀ i - v s₀ k) * t) := fun h =>
    hnot (isoSet_open_of_strict hv hs₀ ht h)
  refine ⟨?_, fun hint => hns ((interior_iff_strict _ _ hl).mp hint)⟩
  push Not at hns
  obtain ⟨i, hi, hle⟩ := hns
  exact ⟨i, hi, le_antisymm hle (hl i hi)⟩

#print axioms loss_needs_boundary

/-- **At a loss there is no lonely interval of positive width** [L]: under the hypotheses of `loss_needs_boundary`, the
lonely set of `v s₀` contains no interval `[u, w]` with `0 ≤ u < w`; every lonely cell at `s₀` is a single point (a
touch, `LonelyCells.degenerate_opener_ne_closer`). -/
theorem loss_no_interval {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {k : Fin 8}
    (hnot : ¬ ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, s ∈ isoSet v k) {u w : ℝ} (hu : 0 ≤ u) (huw : u < w) :
    ¬ ∀ t ∈ Set.Icc u w, IsolatedAt (v s₀) k t := by
  intro hall
  set m := (u + w) / 2 with hm
  have hum : u < m := by rw [hm]; linarith
  have hmw : m < w := by rw [hm]; linarith
  have hmint : m ∈ interior {t | IsolatedAt (v s₀) k t} :=
    interior_maximal (t := Set.Ioo u w) (fun t ht => hall t ⟨ht.1.le, ht.2.le⟩) isOpen_Ioo ⟨hum, hmw⟩
  exact (loss_needs_boundary hv hs₀ hnot m (by linarith) (hall m ⟨hum.le, hmw.le⟩)).2 hmint

#print axioms loss_no_interval

/-- **A cell of positive width at `s₀` gives the isolation set a neighbourhood of `s₀`** [L] (the carried-by-a-cell
case; the cell persists as a cell by `Gate.cell_persists` when the path is continuous at `s₀` in all of `ℝ`). -/
theorem isoSet_open_of_cell {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) 1) {k : Fin 8} {u w : ℝ} (hu : 0 ≤ u) (huw : u < w)
    (hall : ∀ t ∈ Set.Icc u w, IsolatedAt (v s₀) k t) : ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, s ∈ isoSet v k := by
  by_contra hnot
  exact loss_no_interval hv hs₀ hnot hu huw hall

#print axioms isoSet_open_of_cell

/-! ## The content owed, named and not assumed -/

/-- OWED, cap-shaped (rule 7): the lonely witnesses along the path can be chosen below one bound.  Asserted nowhere. -/
-- STANDING: OWED
def PathLonelyBound (v : ℝ → Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ B : ℝ, ∀ s ∈ isoSet v k, ∃ t : ℝ, 0 < t ∧ t ≤ B ∧ IsolatedAt (v s) k t

/-- OWED, the successor-cell statement: isolation at `s₀` persists to a neighbourhood of `s₀` in `[0,1]` (at a touch
this needs a lonely instant other than the degenerate one).  Asserted nowhere. -/
-- STANDING: OWED
def SuccessorIsolation (v : ℝ → Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∀ s₀ ∈ isoSet v k, ∀ᶠ s in 𝓝[Set.Icc 0 1] s₀, s ∈ isoSet v k

theorem isoSet_subset (v : ℝ → Fin 8 → ℝ) (k : Fin 8) : isoSet v k ⊆ Set.Icc 0 1 := fun _ h => h.1

/-- A bound on the witnesses makes the isolation set closed [L] (`isoSet_closed_of_bdd` applied to witnesses chosen
below `B`).  Hypothesis `PathLonelyBound` is OWED, not proved. -/
theorem isClosed_isoSet_of_bound {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8}
    (hB : PathLonelyBound v k) : IsClosed (isoSet v k) := by
  obtain ⟨B, hB⟩ := hB
  refine IsSeqClosed.isClosed fun x p hx hxp => ?_
  choose t ht0 htB htl using fun n => hB (x n) (hx n)
  exact isoSet_closed_of_bdd hv (fun n => (hx n).1) hxp htl ht0 htB

#print axioms isClosed_isoSet_of_bound

/-- CONDITIONAL, recorded to show where the two owed statements enter; not offered as the argument that the isolation
set is `[0,1]`.  Hypotheses `PathLonelyBound` and `SuccessorIsolation` are OWED.  Rule 7: the first is cap-shaped.
The proof is real-line induction on a closed set that is open to the right at each of its points. -/
theorem isoSet_eq_of_owed {v : ℝ → Fin 8 → ℝ} (hv : ContinuousOn v (Set.Icc 0 1)) {k : Fin 8}
    (hB : PathLonelyBound v k) (hS : SuccessorIsolation v k) (h0 : (0 : ℝ) ∈ isoSet v k) :
    Set.Icc (0 : ℝ) 1 ⊆ isoSet v k := by
  have hcl := isClosed_isoSet_of_bound hv hB
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin (hcl.inter isClosed_Icc) h0 ?_
  intro x ⟨hx, hxI⟩
  have hmem : Set.Icc (0 : ℝ) 1 ∈ 𝓝[>] x :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hxI.2) (fun y hy => ⟨hxI.1.trans hy.1.le, hy.2.le⟩)
  have := (hS x hx)
  have hle : 𝓝[>] x ≤ 𝓝[Set.Icc 0 1] x := nhdsWithin_le_of_mem hmem
  filter_upwards [hle this] with y hy
  exact hy

#print axioms isoSet_eq_of_owed

end PathLaws

end Fresh
