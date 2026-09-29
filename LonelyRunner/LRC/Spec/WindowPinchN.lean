import LonelyRunner.LRC.Cascade.Arrangement
import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# Exact lap windows and the first pinch along an AP deformation

These are fixed-lap statements, not global cascade termination. Closed endpoints
are retained: a pinched singleton time is still an isolation witness. A finite
family of affine constraints has its first loss at the least decreasing-slack
root; simultaneous roots and a root at zero are allowed.
-/

namespace LRC.WindowPinch

variable {ι : Type*}

/-- A finite family of closed intervals intersects iff every lower endpoint is
below every upper endpoint. The maximum lower endpoint is an explicit witness. -/
theorem intervals_iff (S : Finset ι) (hS : S.Nonempty) (lo hi : ι → ℝ) :
    (∃ t : ℝ, ∀ i ∈ S, lo i ≤ t ∧ t ≤ hi i) ↔
      ∀ i ∈ S, ∀ j ∈ S, lo i ≤ hi j := by
  constructor
  · rintro ⟨t, ht⟩ i hiS j hjS
    exact (ht i hiS).1.trans (ht j hjS).2
  · intro h
    refine ⟨S.sup' hS lo, fun i hiS => ⟨Finset.le_sup' lo hiS, ?_⟩⟩
    exact (Finset.sup'_le_iff hS lo).mpr (fun j hj => h j hj i hiS)

/-- The same criterion in literal maximum-lower/minimum-upper form. -/
theorem intervals_iff_max_le_min (S : Finset ι) (hS : S.Nonempty)
    (lo hi : ι → ℝ) :
    (∃ t : ℝ, ∀ i ∈ S, lo i ≤ t ∧ t ≤ hi i) ↔
      S.sup' hS lo ≤ S.inf' hS hi := by
  rw [intervals_iff S hS]
  simp only [Finset.sup'_le_iff, Finset.le_inf'_iff]
  constructor <;> intro h i hiS j hjS <;> exact h j hjS i hiS

/-- Exact closed clear band on a specified lap, expressed as a time interval. -/
theorem band_iff {d t : ℝ} (hd : 0 < d) (q : ℤ) :
    ((q : ℝ) + 1 / 8 ≤ d * t ∧ d * t ≤ q + 7 / 8) ↔
      ((8 * (q : ℝ) + 1) / (8 * d) ≤ t ∧
        t ≤ (8 * (q : ℝ) + 7) / (8 * d)) := by
  rw [div_le_iff₀ (by positivity : 0 < 8 * d),
    le_div_iff₀ (by positivity : 0 < 8 * d)]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- No enumeration: fixed-lap feasibility is exactly a family of homogeneous
linear inequalities in the disparities. -/
theorem lap_windows_iff (S : Finset ι) (hS : S.Nonempty)
    (d : ι → ℝ) (q : ι → ℤ) (hd : ∀ i ∈ S, 0 < d i) :
    (∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ) + 1 / 8 ≤ d i * t ∧ d i * t ≤ q i + 7 / 8) ↔
    ∀ i ∈ S, ∀ j ∈ S,
      (8 * (q i : ℝ) + 1) * d j ≤ (8 * (q j : ℝ) + 7) * d i := by
  have hb : (∃ t : ℝ, ∀ i ∈ S,
      (q i : ℝ) + 1 / 8 ≤ d i * t ∧ d i * t ≤ q i + 7 / 8) ↔
      ∃ t : ℝ, ∀ i ∈ S,
        (8 * (q i : ℝ) + 1) / (8 * d i) ≤ t ∧
        t ≤ (8 * (q i : ℝ) + 7) / (8 * d i) := by
    constructor <;> rintro ⟨t, ht⟩ <;> refine ⟨t, fun i hi => ?_⟩
    · exact (band_iff (hd i hi) (q i)).mp (ht i hi)
    · exact (band_iff (hd i hi) (q i)).mpr (ht i hi)
  rw [hb, intervals_iff S hS]
  apply forall_congr'; intro i
  apply forall_congr'; intro hi
  apply forall_congr'; intro j
  apply forall_congr'; intro hj
  rw [div_le_div_iff₀ (mul_pos (by norm_num) (hd i hi))
    (mul_pos (by norm_num) (hd j hj))]
  constructor <;> intro h <;> nlinarith

/-- The window witness really proves the arrangement-level predicate, not just
an auxiliary ratio predicate. Absolute disparities handle both speed directions. -/
theorem lonely_of_windows (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ)
    (q : Fin 8 → ℤ)
    (h : ∀ i, i ≠ k →
      (q i : ℝ) + 1 / 8 ≤ |v i - v k| * t ∧
      |v i - v k| * t ≤ q i + 7 / 8) : Arrangement.LonelyAt v k t := by
  intro i hi
  have hc := TwoPinner.clear_of_band (h i hi).1 (h i hi).2
  rwa [Arrangement.circDist_abs_mul, ← Arrangement.sep_eq] at hc

/-- The seven-runner fixed-lap inequalities produce a positive isolation time
for the original subject, with no auxiliary global-isolation assumption. -/
theorem exists_lonely_of_lap_inequalities (v : Fin 8 → ℝ)
    (hv : Function.Injective v) (k : Fin 8) (q : Fin 8 → ℕ)
    (h : ∀ i, i ≠ k → ∀ j, j ≠ k →
      (8 * (q i : ℝ) + 1) * |v j - v k| ≤
      (8 * (q j : ℝ) + 7) * |v i - v k|) :
    ∃ t : ℝ, 0 < t ∧ Arrangement.LonelyAt v k t := by
  classical
  let S := Finset.univ.erase k
  have hS : S.Nonempty := Arrangement.others_nonempty k
  have hd : ∀ i ∈ S, 0 < |v i - v k| := by
    intro i hi
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hi).1 (hv he))
  have hlin : ∀ i ∈ S, ∀ j ∈ S,
      (8 * ((q i : ℤ) : ℝ) + 1) * |v j - v k| ≤
      (8 * ((q j : ℤ) : ℝ) + 7) * |v i - v k| := by
    intro i hi j hj
    simpa using h i (Finset.mem_erase.mp hi).1 j (Finset.mem_erase.mp hj).1
  obtain ⟨t, ht⟩ := (lap_windows_iff S hS (fun i => |v i - v k|)
    (fun i => (q i : ℤ)) hd).mpr hlin
  have htpos : 0 < t := by
    obtain ⟨i, hi⟩ := hS
    have hb := (ht i hi).1
    have hq : 0 ≤ ((q i : ℤ) : ℝ) := by positivity
    have hp : 0 < |v i - v k| * t := by linarith
    exact pos_of_mul_pos_right hp (hd i hi).le
  refine ⟨t, htpos, lonely_of_windows v k t (fun i => (q i : ℤ)) ?_⟩
  intro i hi
  exact ht i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)

/-- Turning the rescaled AP inequalities into an interval for the scale. -/
theorem ratio_window_iff {rho lam lo hi : ℝ}
    (hlam : 0 < lam) (hlo : 0 < lo) (hhi : 0 < hi) :
    (lo ≤ rho / lam ∧ rho / lam ≤ hi) ↔
      (rho / hi ≤ lam ∧ lam ≤ rho / lo) := by
  rw [le_div_iff₀ hlam, div_le_iff₀ hlam,
    div_le_iff₀ hhi, le_div_iff₀ hlo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- The finite max/min criterion includes a positive scale witness. It describes
the chosen windows only; other lap assignments may also produce isolation. -/
theorem scale_windows_iff (S : Finset ι) (hS : S.Nonempty)
    (rho lo hi : ι → ℝ)
    (hrho : ∀ i ∈ S, 0 < rho i)
    (hlo : ∀ i ∈ S, 0 < lo i) (hhi : ∀ i ∈ S, 0 < hi i) :
    (∃ lam : ℝ, 0 < lam ∧ ∀ i ∈ S,
      lo i ≤ rho i / lam ∧ rho i / lam ≤ hi i) ↔
    ∀ i ∈ S, ∀ j ∈ S, rho i / hi i ≤ rho j / lo j := by
  constructor
  · rintro ⟨lam, hp, h⟩ i hiS j hjS
    exact ((ratio_window_iff hp (hlo i hiS) (hhi i hiS)).mp (h i hiS)).1.trans
      ((ratio_window_iff hp (hlo j hjS) (hhi j hjS)).mp (h j hjS)).2
  · intro h
    obtain ⟨lam, hlam⟩ := (intervals_iff S hS
      (fun i => rho i / hi i) (fun i => rho i / lo i)).mpr h
    obtain ⟨i, hiS⟩ := hS
    have hp : 0 < lam := (div_pos (hrho i hiS) (hhi i hiS)).trans_le (hlam i hiS).1
    exact ⟨lam, hp, fun j hj =>
      (ratio_window_iff hp (hlo j hj) (hhi j hj)).mpr (hlam j hj)⟩

/-- For a signed AP disparity `r` and deviation difference `w`, preserving
speed order makes the absolute-disparity ratio exactly affine in the parameter.
This treats runners on either side of the subject, not just positive `r`. -/
theorem disparity_ratio_affine {r w s : ℝ} (hr : r ≠ 0)
    (horder : 0 < (r + s * w) / r) :
    |r + s * w| / |r| = 1 + s * (w / r) := by
  rw [← abs_div, abs_of_pos horder]
  field_simp

/-- Along a straight deformation, boundary ordering depends on direction alone. -/
theorem boundary_order_iff {s b c : ℝ} (hs : 0 < s) :
    1 + s * b ≤ 1 + s * c ↔ b ≤ c := by
  constructor
  · intro h
    exact (mul_le_mul_iff_right₀ hs).mp (by linarith : s * b ≤ s * c)
  · intro h
    nlinarith

/-- Exact slack between the upper scale bound of one runner and the lower
scale bound of another; no linearisation or small-deviation assumption. -/
theorem slack_affine (s b c lo hi : ℝ) :
    (1 + s * c) / lo - (1 + s * b) / hi =
      (1 / lo - 1 / hi) + s * (c / lo - b / hi) := by ring

/-- The AP window formula is exactly the ordinary lap band at the rescaled
time. Here `b = a*r` and `d = r*rho`; the integer `q` is the chosen AP lap. -/
theorem ap_window_iff {a r rho lam : ℝ} (ha : 0 < a) (hr : 0 < r)
    (q : ℤ) :
    (((8 * (q : ℝ) + 1) / (a * r) ≤ rho / lam) ∧
      rho / lam ≤ (8 * (q : ℝ) + 7) / (a * r)) ↔
    ((q : ℝ) + 1 / 8 ≤ (r * rho) * (a / (8 * lam)) ∧
      (r * rho) * (a / (8 * lam)) ≤ q + 7 / 8) := by
  have har : 0 < a * r := mul_pos ha hr
  have he : (r * rho) * (a / (8 * lam)) = (a * r) * (rho / lam) / 8 := by ring
  rw [he, div_le_iff₀ har, le_div_iff₀ har]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- A decreasing affine slack is nonnegative exactly up to its root. -/
theorem decreasing_slack_iff {A B s : ℝ} (hB : B < 0) :
    0 ≤ A + s * B ↔ s ≤ A / (-B) := by
  rw [le_div_iff₀ (neg_pos.mpr hB)]
  constructor <;> intro h <;> nlinarith

/-- Given the least decreasing-slack root, it is the exact first pinch. The
active constraint becomes strictly false at EVERY later parameter. Other
constraints may tie there; the initial slack may be zero. -/
theorem first_pinch (S : Finset ι) (A B : ι → ℝ) (p : ι)
    (hp : p ∈ S) (hA : ∀ i ∈ S, 0 ≤ A i) (hBp : B p < 0)
    (hfirst : ∀ i ∈ S, B i < 0 → A p / (-B p) ≤ A i / (-B i)) :
    let tau := A p / (-B p)
    0 ≤ tau ∧
    (∀ s, 0 ≤ s → s ≤ tau → ∀ i ∈ S, 0 ≤ A i + s * B i) ∧
    A p + tau * B p = 0 ∧
    (∀ s, tau < s → A p + s * B p < 0) := by
  dsimp
  refine ⟨div_nonneg (hA p hp) (neg_pos.mpr hBp).le, ?_, ?_, ?_⟩
  · intro s hs ht i hi
    by_cases hBi : B i < 0
    · exact (decreasing_slack_iff hBi).mpr (ht.trans (hfirst i hi hBi))
    · exact add_nonneg (hA i hi) (mul_nonneg hs (le_of_not_gt hBi))
  · have hn : B p ≠ 0 := ne_of_lt hBp
    field_simp
    ring
  · intro s hs
    exact lt_of_not_ge (fun h => (not_le_of_gt hs) ((decreasing_slack_iff hBp).mp h))

/-- The first active constraint is obtained from a finite minimum, not assumed.
This covers arbitrary simultaneous pinches, including immediate failure at zero. -/
theorem exists_first_pinch (S : Finset ι) (A B : ι → ℝ)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hdec : ∃ i ∈ S, B i < 0) :
    ∃ p ∈ S, B p < 0 ∧
      let tau := A p / (-B p)
      0 ≤ tau ∧
      (∀ s, 0 ≤ s → s ≤ tau → ∀ i ∈ S, 0 ≤ A i + s * B i) ∧
      A p + tau * B p = 0 ∧
      (∀ s, tau < s → A p + s * B p < 0) := by
  classical
  let T := S.filter (fun i => B i < 0)
  have hT : T.Nonempty := by
    obtain ⟨i, hi, hb⟩ := hdec
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hb⟩⟩
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_inf' hT (fun i => A i / (-B i))
  have hpS := (Finset.mem_filter.mp hp).1
  have hpB := (Finset.mem_filter.mp hp).2
  refine ⟨p, hpS, hpB, first_pinch S A B p hpS hA hpB ?_⟩
  intro i hi hb
  rw [← he]
  exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hi, hb⟩)

/-- If no constraint decreases, there is no later pinch on the positive ray. -/
theorem no_pinch_of_nonnegative_slopes (S : Finset ι) (A B : ι → ℝ)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hB : ∀ i ∈ S, 0 ≤ B i)
    {s : ℝ} (hs : 0 ≤ s) : ∀ i ∈ S, 0 ≤ A i + s * B i := by
  intro i hi
  exact add_nonneg (hA i hi) (mul_nonneg hs (hB i hi))

/-- Apply the affine slack calculation to ALL pairs of scale endpoints. -/
theorem deformed_scale_iff (S : Finset ι) (hS : S.Nonempty)
    (beta lo hi : ι → ℝ) (s : ℝ)
    (hrho : ∀ i ∈ S, 0 < 1 + s * beta i)
    (hlo : ∀ i ∈ S, 0 < lo i) (hhi : ∀ i ∈ S, 0 < hi i) :
    (∃ lam : ℝ, 0 < lam ∧ ∀ i ∈ S,
      lo i ≤ (1 + s * beta i) / lam ∧ (1 + s * beta i) / lam ≤ hi i) ↔
    ∀ i ∈ S, ∀ j ∈ S,
      0 ≤ (1 / lo j - 1 / hi i) + s * (beta j / lo j - beta i / hi i) := by
  rw [scale_windows_iff S hS _ lo hi hrho hlo hhi]
  apply forall_congr'; intro i
  apply forall_congr'; intro hiS
  apply forall_congr'; intro j
  apply forall_congr'; intro hjS
  rw [← slack_affine]
  exact sub_nonneg.symm

/-- A first pinching PAIR of runners exists whenever some endpoint slack
decreases. The conclusion names both active runners and gives the exact
feasibility interval for every positive-disparity point on the deformation.
There is no conclusion that a different lap assignment restores feasibility. -/
theorem first_scale_pinch (S : Finset ι) (hS : S.Nonempty)
    (beta lo hi : ι → ℝ)
    (hlo : ∀ i ∈ S, 0 < lo i) (hhi : ∀ i ∈ S, 0 < hi i)
    (hAP : ∀ i ∈ S, lo i ≤ 1 ∧ 1 ≤ hi i)
    (hdec : ∃ i ∈ S, ∃ j ∈ S, beta j / lo j - beta i / hi i < 0) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ tau : ℝ, 0 ≤ tau ∧
      (1 / lo j - 1 / hi i) + tau * (beta j / lo j - beta i / hi i) = 0 ∧
      (∀ s, 0 ≤ s → (∀ z ∈ S, 0 < 1 + s * beta z) →
        ((∃ lam : ℝ, 0 < lam ∧ ∀ z ∈ S,
          lo z ≤ (1 + s * beta z) / lam ∧ (1 + s * beta z) / lam ≤ hi z)
          ↔ s ≤ tau)) := by
  classical
  let A : ι × ι → ℝ := fun p => 1 / lo p.2 - 1 / hi p.1
  let B : ι × ι → ℝ := fun p => beta p.2 / lo p.2 - beta p.1 / hi p.1
  have hA : ∀ p ∈ S ×ˢ S, 0 ≤ A p := by
    intro p hp
    obtain ⟨hiS, hjS⟩ := Finset.mem_product.mp hp
    dsimp [A]
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (hhi p.1 hiS) (hlo p.2 hjS)).mpr
    have h1 := (hAP p.1 hiS).2
    have h2 := (hAP p.2 hjS).1
    nlinarith
  have hB : ∃ p ∈ S ×ˢ S, B p < 0 := by
    obtain ⟨i, hiS, j, hjS, hb⟩ := hdec
    exact ⟨(i, j), Finset.mem_product.mpr ⟨hiS, hjS⟩, hb⟩
  obtain ⟨p, hp, _, ht, hbefore, heq, hafter⟩ := exists_first_pinch (S ×ˢ S) A B hA hB
  obtain ⟨hiS, hjS⟩ := Finset.mem_product.mp hp
  refine ⟨p.1, hiS, p.2, hjS, A p / (-B p), ht, heq, ?_⟩
  intro s hs hrho
  rw [deformed_scale_iff S hS beta lo hi s hrho hlo hhi]
  constructor
  · intro h
    by_contra hn
    have hf := hafter s (lt_of_not_ge hn)
    have hh := h p.1 hiS p.2 hjS
    exact (not_lt_of_ge hh) hf
  · intro h i hiS j hjS
    exact hbefore s hs h (i, j) (Finset.mem_product.mpr ⟨hiS, hjS⟩)

end LRC.WindowPinch
