import Fresh.Cascade

set_option maxRecDepth 4096

namespace Fresh.FiniteRelations

open scoped BigOperators
open Set

noncomputable def character (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I)

private theorem character_add (x y : ℝ) :
    character (x+y) = character x * character y := by
  simp [character, add_mul, Complex.exp_add]

private theorem character_norm (x : ℝ) : ‖character x‖ = 1 := by
  simp [character, Complex.norm_exp]

private theorem character_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [character]
  | insert i s hi ih => simp [hi, character_add, ih]

private theorem character_pow (x : ℝ) (n : ℕ) :
    character (n*x) = character x ^ n := by
  induction n with
  | zero => simp [character]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, character_add, ih, pow_succ]

noncomputable def bump (x : ℝ) : ℝ :=
  ((1 - Real.cos (2 * Real.pi * x))/2)^32

def indices := Finset.range 65

noncomputable def weight (j : ℕ) : ℝ :=
  (Nat.choose 64 j : ℝ) / 4^32

noncomputable def coeff (j : ℕ) : ℂ :=
  (weight j : ℂ) * (-1 : ℂ)^j

private theorem bump_expansion (x : ℝ) :
    (bump x : ℂ) = ∑ j ∈ indices, coeff j *
      character (2 * Real.pi * x * ((j : ℝ)-32)) := by
  let z := 2 * Real.pi * x
  have hcos : (Real.cos z : ℂ) = (character z + character (-z))/2 := by
    rw [Complex.ofReal_cos, Complex.cos]
    congr 2
    simp [character, mul_comm]
  have hbase : ((1 : ℂ) - (Real.cos z : ℂ))/2 =
      character (-z) * ((1 - character z)^2 / 4) * (-1) := by
    rw [hcos]
    have hz : character (-z)*character z = 1 := by
      rw [← character_add, neg_add_cancel]
      simp [character]
    linear_combination (character z - 2)/4 * hz
  change ((((1 - Real.cos z)/2)^32 : ℝ) : ℂ) = _
  push_cast
  rw [← Complex.ofReal_cos, hbase]
  simp only [mul_pow, div_pow, ← pow_mul]
  norm_num only [show (2:ℕ)*32 = 64 by decide, show (-1:ℂ)^32 = 1 by norm_num, mul_one]
  rw [show (1 - character z)^64 = ((-character z) + 1)^64 by congr 1; ring, add_pow]
  simp only [one_pow, mul_one, div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (-character z)^j = (-1:ℂ)^j * character ((j:ℝ)*z) := by
    rw [character_pow, ← mul_pow]
    simp
  have hcomb : character ((32:ℝ)*(-z))*character ((j:ℝ)*z) =
      character (z*((j:ℝ)-32)) := by
    rw [← character_add]
    congr 1
    ring
  simp only [hj, ← character_pow (-z) 32]
  unfold coeff weight
  push_cast
  change _ = _ * character (z*((j:ℝ)-32))
  norm_num only [show (4:ℂ)^32 = 18446744073709551616 by norm_num]
  rw [← hcomb]
  ring

private theorem weight_sum : ∑ j ∈ indices, weight j = 1 := by
  simp only [indices, weight, ← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  norm_num


private theorem bump_nonneg (x : ℝ) : 0 ≤ bump x := by
  unfold bump
  exact pow_nonneg (by linarith [Real.cos_le_one (2*Real.pi*x)]) _

private theorem bump_le_one (x : ℝ) : bump x ≤ 1 := by
  unfold bump
  exact pow_le_one₀ (by linarith [Real.cos_le_one (2*Real.pi*x)])
    (by linarith [Real.neg_one_le_cos (2*Real.pi*x)])

private theorem bump_bad {x : ℝ} (h : distInt x ≤ 1/8) : bump x ≤ (1/4:ℝ)^32 := by
  let y := x - (round x : ℝ)
  have hy : |y| ≤ 1/8 := h
  have hc : Real.cos (2*Real.pi*x) = Real.cos (2*Real.pi*y) := by
    rw [show 2*Real.pi*x = 2*Real.pi*y + (round x : ℝ)*(2*Real.pi) by dsimp [y]; ring]
    exact Real.cos_add_int_mul_two_pi _ _
  have hs : |Real.sin (Real.pi*y)| ≤ 1/2 := by
    calc
      _ ≤ |Real.pi*y| := Real.abs_sin_le_abs
      _ = Real.pi*|y| := by rw [abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ Real.pi*(1/8) := mul_le_mul_of_nonneg_left hy Real.pi_pos.le
      _ ≤ _ := by linarith [Real.pi_lt_four]
  unfold bump
  rw [hc, show 2*Real.pi*y = 2*(Real.pi*y) by ring, Real.cos_two_mul']
  have hsq := sq_le_sq.mpr (show |Real.sin (Real.pi*y)| ≤ |(1/2:ℝ)| by simpa using hs)
  apply pow_le_pow_left₀
  · linarith [sq_nonneg (Real.sin (Real.pi*y)), Real.sin_sq_add_cos_sq (Real.pi*y)]
  · linarith [Real.sin_sq_add_cos_sq (Real.pi*y)]

private theorem character_integral_bound {a b f : ℝ} (hf : f ≠ 0) :
    ‖∫ t in a..b, character (2*Real.pi*f*t)‖ ≤ 1/|f| := by
  let c : ℂ := (↑(2*Real.pi*f) : ℂ) * Complex.I
  have hn : ‖c‖ = 2*Real.pi*|f| := by
    simp [c, abs_of_pos Real.pi_pos]
  have hcn : c ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hn]
    positivity
  have he (t : ℝ) : character (2*Real.pi*f*t) = Complex.exp (c*t) := by
    simp only [character, c, Complex.ofReal_mul]
    ring_nf
  simp_rw [he]
  rw [integral_exp_mul_complex hcn, norm_div, hn]
  have hnum : ‖Complex.exp (c * b) - Complex.exp (c * a)‖ ≤ 2 := by
    rw [← he, ← he]
    simpa only [character_norm, one_add_one_eq_two] using
      norm_sub_le (character (2*Real.pi*f*b)) (character (2*Real.pi*f*a))
  have hfpos : 0 < |f| := abs_pos.mpr hf
  apply (div_le_div_iff₀ (by positivity) hfpos).2
  nlinarith [mul_le_mul_of_nonneg_right hnum hfpos.le, Real.pi_gt_three]

/-- Deleting modes with frequency at least `D` costs at most `1/D`
in the interval integral when the sum of their absolute coefficients is
at most one. This estimate applies to any finite Fourier expansion. -/
theorem spectral_tail_bound {ι : Type*} (modes : Finset ι) (A : ι → ℂ)
    (f : ι → ℝ) {a b D : ℝ} (hD : 0 < D)
    (ha : ∑ i ∈ modes, ‖A i‖ ≤ 1)
    (hf : ∀ i ∈ modes, D ≤ |f i|) :
    ‖∑ i ∈ modes, A i * (∫ t in a..b, character (2*Real.pi*f i*t))‖ ≤ 1/D := by
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ modes, ‖A i‖*(1/D) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hp : 0 < |f i| := hD.trans_le (hf i hi)
      exact (character_integral_bound (abs_pos.mp hp)).trans
        (one_div_le_one_div_of_le hD (hf i hi))
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (by positivity) ha

/-- Frequency separation bounds the error of retaining a specified
subset of modes. The retained modes can have arbitrary frequencies. -/
theorem projected_integral_error {ι : Type*} [DecidableEq ι]
    (modes retained : Finset ι) (A : ι → ℂ) (f : ι → ℝ) {a b D : ℝ}
    (hr : retained ⊆ modes) (hD : 0 < D)
    (ha : ∑ i ∈ modes, ‖A i‖ ≤ 1)
    (hf : ∀ i ∈ modes \ retained, D ≤ |f i|) :
    ‖(∫ t in a..b, ∑ i ∈ modes, A i * character (2*Real.pi*f i*t)) -
      (∫ t in a..b, ∑ i ∈ retained, A i * character (2*Real.pi*f i*t))‖ ≤ 1/D := by
  have hint (i : ι) : IntervalIntegrable
      (fun t => A i * character (2*Real.pi*f i*t)) MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    unfold character
    fun_prop
  let term (i : ι) := A i * (∫ t in a..b, character (2*Real.pi*f i*t))
  have integrate (S : Finset ι) :
      (∫ t in a..b, ∑ i ∈ S, A i * character (2*Real.pi*f i*t)) = ∑ i ∈ S, term i := by
    rw [intervalIntegral.integral_finset_sum (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    exact intervalIntegral.integral_const_mul (A i) (fun t => character (2*Real.pi*f i*t))
  rw [integrate modes, integrate retained]
  have hs : (∑ i ∈ modes \ retained, term i) + (∑ i ∈ retained, term i) =
      ∑ i ∈ modes, term i := Finset.sum_sdiff hr
  rw [show (∑ i ∈ modes, term i) - (∑ i ∈ retained, term i) =
      ∑ i ∈ modes \ retained, term i by linear_combination -hs]
  apply spectral_tail_bound _ A f hD _ hf
  exact (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    (fun i _ _ => norm_nonneg (A i))).trans ha

abbrev Mode (n : ℕ) := Fin n → Fin 65

noncomputable def amplitude {n : ℕ} (m : Mode n) : ℂ :=
  ∏ i, coeff (m i).val

def center (n : ℕ) : Mode n := fun _ => 32

def row {n : ℕ} (m : Mode n) : Fin n → ℤ := fun i => (m i).val - 32

def frequency {n : ℕ} (m : Mode n) (v : Fin n → ℝ) : ℝ :=
  ∑ i, (row m i : ℝ) * v i

private theorem weight_sum_fin : ∑ j : Fin 65, weight j.val = 1 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact weight_sum

private theorem amplitude_norm_sum (n : ℕ) :
    ∑ m : Mode n, ‖amplitude m‖ = 1 := by
  have hnorm (j : ℕ) : ‖coeff j‖ = weight j := by
    have hp : 0 ≤ weight j := by unfold weight; positivity
    simp [coeff, norm_pow, abs_of_nonneg hp]
  simp only [amplitude, norm_prod, hnorm]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (j : Fin 65) => weight j.val)]
  simp [weight_sum_fin]

private theorem center_amplitude (n : ℕ) :
    amplitude (center n) = ((weight 32)^n : ℝ) := by
  simp [amplitude, center, coeff, Finset.prod_const]
  norm_num

private theorem product_expansion {n : ℕ} (v x : Fin n → ℝ) (t : ℝ) :
    ((∏ i, bump (v i*t+x i) : ℝ) : ℂ) =
      ∑ m : Mode n, (amplitude m * character (2*Real.pi*frequency m x)) *
        character (2*Real.pi*frequency m v*t) := by
  push_cast
  have hex (i : Fin n) := bump_expansion (v i*t+x i)
  simp only [indices, ← Fin.sum_univ_eq_sum_range] at hex
  simp_rw [hex, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.prod_mul_distrib, ← character_sum]
  unfold amplitude
  rw [mul_assoc, ← character_add]
  congr 2
  unfold frequency row
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every obstruction on a bounded time interval forces a nonzero integer
relation with small coefficients and a bounded error. Initial phases are arbitrary. -/
theorem clear_or_short_relation {n : ℕ} (hn : n ≤ 7) (v x : Fin n → ℝ)
    {a b : ℝ} (hab : a < b) :
    (∃ t ∈ Icc a b, ∀ i, (1/8:ℝ) < distInt (v i*t+x i)) ∨
      ∃ m : Mode n, m ≠ center n ∧ |frequency m v| ≤ (10:ℝ)^9/(b-a) := by
  classical
  by_contra! hnclear
  let F : ℝ → ℂ := fun t => ((∏ i, bump (v i*t+x i) : ℝ) : ℂ)
  let A : Mode n → ℂ := fun m => amplitude m * character (2*Real.pi*frequency m x)
  let J : Mode n → ℂ := fun m => ∫ t in a..b, character (2*Real.pi*frequency m v*t)
  have hlen : 0 < b-a := sub_pos.mpr hab
  have hF : Continuous F := by unfold F bump; fun_prop
  have hnorm (m : Mode n) : ‖A m‖ = ‖amplitude m‖ := by simp [A, character_norm]
  have hphase (m : Mode n) :
      IntervalIntegrable (fun t => A m * character (2*Real.pi*frequency m v*t))
        MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    unfold character
    fun_prop
  have hfint : (∫ t in a..b, F t) = ∑ m, A m * J m := by
    rw [show F = (fun t => ∑ m, A m * character (2*Real.pi*frequency m v*t)) by
      funext t
      exact product_expansion v x t]
    rw [intervalIntegral.integral_finset_sum (fun m _ => hphase m)]
    apply Finset.sum_congr rfl
    intro m _
    exact intervalIntegral.integral_const_mul (A m) (fun t => character (2*Real.pi*frequency m v*t))
  have hFsmall : ‖∫ t in a..b, F t‖ ≤ (b-a)*(1/4:ℝ)^32 := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab.le).trans ?_
    rw [← smul_eq_mul, ← intervalIntegral.integral_const (c := (1/4:ℝ)^32)]
    apply intervalIntegral.integral_mono_on hab.le (hF.norm.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    intro t ht
    obtain ⟨i,hi⟩ := hnclear.1 t ht
    rw [show ‖F t‖ = ∏ j, bump (v j*t+x j) by
      simp only [F, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (Finset.prod_nonneg fun j _ => bump_nonneg _)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => bump (v j*t+x j)) (Finset.mem_univ i)]
    exact (mul_le_of_le_one_right (bump_nonneg _) (Finset.prod_le_one
      (fun j _ => bump_nonneg _) (fun j _ => bump_le_one _))).trans (bump_bad hi)
  have herror : ‖∑ m ∈ Finset.univ.erase (center n), A m * J m‖ ≤ (b-a)/(10:ℝ)^9 := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ m ∈ Finset.univ.erase (center n), ‖amplitude m‖ * ((b-a)/(10:ℝ)^9) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul, hnorm]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have hm' := hnclear.2 m (Finset.mem_erase.mp hm).1
        have hpos : 0 < |frequency m v| := by
          exact (show 0 < (10:ℝ)^9/(b-a) by positivity).trans hm'
        apply (character_integral_bound (abs_pos.mp hpos)).trans
        apply (div_le_div_iff₀ hpos (by positivity)).2
        simpa only [one_mul, mul_comm (b-a)] using ((div_lt_iff₀ hlen).mp hm').le
      _ ≤ ∑ m : Mode n, ‖amplitude m‖ * ((b-a)/(10:ℝ)^9) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro m _ _
        positivity
      _ = _ := by rw [← Finset.sum_mul, amplitude_norm_sum, one_mul]
  have hz (w : Fin n → ℝ) : frequency (center n) w = 0 := by
    simp [frequency, row, center]
  have hcenter : A (center n) * J (center n) =
      (((weight 32)^n*(b-a) : ℝ) : ℂ) := by
    simp [A, J, hz, character, center_amplitude, intervalIntegral.integral_const]
    change (↑(b-a) : ℂ) * _ = _
    push_cast
    ring
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Mode n)))
    (fun m => A m * J m) (Finset.mem_univ (center n))
  dsimp only at hsplit
  rw [← hfint, hcenter] at hsplit
  have htriangle := norm_sub_le (∫ t in a..b, F t)
    (∑ m ∈ Finset.univ.erase (center n), A m * J m)
  have hsub : (∫ t in a..b, F t) - (∑ m ∈ Finset.univ.erase (center n), A m * J m) =
      (((weight 32)^n*(b-a) : ℝ) : ℂ) := by linear_combination -hsplit
  rw [hsub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by unfold weight; positivity)] at htriangle
  have hw0 : (0:ℝ) ≤ weight 32 := by unfold weight; positivity
  have hw1 : weight 32 ≤ 1 := by unfold weight; norm_num [show Nat.choose 64 32 = 1832624140942590534 by decide]
  have hlower : (weight 32)^7 ≤ (weight 32)^n :=
    pow_le_pow_of_le_one hw0 hw1 hn
  have hconst : (1/4:ℝ)^32 + 1/(10:ℝ)^9 < (weight 32)^7 := by
    unfold weight
    norm_num [show Nat.choose 64 32 = 1832624140942590534 by decide]
  nlinarith only [htriangle, hFsmall, herror, mul_le_mul_of_nonneg_right hlower (sub_pos.mpr hab).le,
    mul_lt_mul_of_pos_right hconst (sub_pos.mpr hab)]


theorem row_ne_zero {n : ℕ} {m : Mode n} (hm : m ≠ center n) : row m ≠ 0 := by
  intro h
  apply hm
  funext i
  apply Fin.ext
  have hh := congrFun h i
  change ((m i).val : ℤ) - 32 = 0 at hh
  change (m i).val = 32
  omega

theorem row_bounds {n : ℕ} (m : Mode n) (i : Fin n) :
    -(32:ℤ) ≤ row m i ∧ row m i ≤ 32 := by
  have hi := (m i).isLt
  unfold row
  omega

/-- All candidate relation rows, with the zero row removed. -/
def catalogue (n : ℕ) : Finset (Mode n) := Finset.univ.erase (center n)

theorem mem_catalogue {n : ℕ} (m : Mode n) :
    m ∈ catalogue n ↔ m ≠ center n := by
  simp only [catalogue, Finset.mem_erase, Finset.mem_univ, and_true]

noncomputable def reducedReadings (v : Fin 8 → ℝ) (k : Fin 8) (j : Fin 7)
    (minimum : ℝ) : Fin 6 → ℝ :=
  fun i => |v (k.succAbove (j.succAbove i)) - v k| / minimum

private theorem pinned_clear {t : ℝ} (ht : t ∈ Icc (1/8:ℝ) (7/8)) :
    (1/8:ℝ) ≤ distInt t := by
  unfold distInt
  by_cases h : round t ≤ 0
  · have hcast : (round t : ℝ) ≤ 0 := by exact_mod_cast h
    exact (by linarith [ht.1] : (1/8:ℝ) ≤ t - (round t : ℝ)).trans (le_abs_self _)
  · have hi : 1 ≤ round t := by omega
    have hcast : (1:ℝ) ≤ (round t : ℝ) := by exact_mod_cast hi
    exact (by linarith [ht.2] : (1/8:ℝ) ≤ -(t - (round t : ℝ))).trans (neg_le_abs _)

/-- Every arrangement and subject either has a witness in the first normalized
window, or its six other normalized readings enter one of the explicitly
bounded nonzero relation slabs. -/
theorem arrangement_first_window (v : Fin 8 → ℝ) (hv : IsArrangement v) (k : Fin 8)
    {minimum : ℝ} (hm : IsDmin v k minimum) :
    ∃ j : Fin 7, |v (k.succAbove j)-v k| = minimum ∧
      ((∃ t ∈ Icc (1/8:ℝ) (7/8), IsolatedAt v k (t/minimum)) ∨
        ∃ m ∈ catalogue 6, |frequency m (reducedReadings v k j minimum)| ≤
          (4*10^9/3:ℝ)) := by
  obtain ⟨l, hl, hval⟩ := Finset.mem_image.mp hm.1
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hl).1
  refine ⟨j,hval,?_⟩
  have hmpos := Cascade.disparitySet_pos hv k minimum hm.1
  rcases clear_or_short_relation (by decide : 6 ≤ 7) (reducedReadings v k j minimum)
      (fun _ => 0) (by norm_num : (1/8:ℝ) < 7/8) with hc | hr
  · obtain ⟨t,ht,hi⟩ := hc
    refine Or.inl ⟨t,ht,(Cascade.isolatedAt_iff_lonelyAt v k _).2 ?_⟩
    intro d hd
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hl).1
    by_cases h : r = j
    · subst r
      rw [hval, mul_div_cancel₀ t hmpos.ne']
      exact pinned_clear ht
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq h
      have hh := (hi i).le
      simp only [reducedReadings, add_zero] at hh
      convert hh using 2
      ring
  · obtain ⟨m,hn,hr⟩ := hr
    have he : (10:ℝ)^9 / ((7/8)-(1/8)) = 4*10^9/3 := by norm_num
    apply Or.inr
    refine ⟨m,(mem_catalogue m).2 hn,?_⟩
    rw [← he]
    exact hr

theorem arrangement_cascade_or_relation (v : Fin 8 → ℝ) (hv : IsArrangement v) (k : Fin 8)
    {minimum : ℝ} (hm : IsDmin v k minimum) :
    CascadeFixes (disparitySet v k) (1/(8*minimum)) ∨
      ∃ j : Fin 7, |v (k.succAbove j)-v k| = minimum ∧
        ∃ m ∈ catalogue 6, |frequency m (reducedReadings v k j minimum)| ≤
          (4*10^9/3:ℝ) := by
  obtain ⟨j, hj, h⟩ := arrangement_first_window v hv k hm
  rcases h with ⟨t,ht,hiso⟩ | hr
  · have hmpos := Cascade.disparitySet_pos hv k minimum hm.1
    exact Or.inl ((Cascade.cascadeFixes_iff_isolation hv hm).1
      ⟨t/minimum, div_pos (by linarith [ht.1]) hmpos, hiso⟩)
  · exact Or.inr ⟨j,hj,hr⟩

#print axioms projected_integral_error
#print axioms clear_or_short_relation
#print axioms arrangement_cascade_or_relation



/-- On an unrestricted positive time horizon the finite relation catalogue
can use exact equalities. Taking a longer interval makes the error in
the short relation arbitrarily small with the same finite set of rows. -/
theorem clear_or_exact_relation {n : ℕ} (hn : n ≤ 7) (v x : Fin n → ℝ) :
    (∃ t : ℝ, 0 < t ∧ ∀ i, (1/8:ℝ) < distInt (v i*t+x i)) ∨
      ∃ m ∈ catalogue n, frequency m v = 0 := by
  classical
  by_contra! h
  let s : ℝ := ∑ m ∈ catalogue n, (1:ℝ)/|frequency m v|
  have hs : 0 ≤ s := Finset.sum_nonneg fun _ _ => by positivity
  let b := 2+10^9*s
  have hab : (1:ℝ) < b := by dsimp [b]; linarith
  rcases clear_or_short_relation hn v x hab with hc | ⟨m,hm,hf⟩
  · obtain ⟨t,ht,hi⟩ := hc
    obtain ⟨i,hi'⟩ := h.1 t (lt_of_lt_of_le zero_lt_one ht.1)
    exact (hi i).not_ge hi'
  · have hmem := (mem_catalogue m).2 hm
    have hp : 0 < |frequency m v| := abs_pos.mpr (h.2 m hmem)
    have hle : (1:ℝ)/|frequency m v| ≤ s :=
      Finset.single_le_sum (f := fun j => (1:ℝ)/|frequency j v|)
        (fun j _ => by positivity) hmem
    have hs' := (div_le_iff₀ hp).1 hle
    have hf' := (le_div_iff₀ (sub_pos.mpr hab)).1 hf
    dsimp [b] at hf'
    nlinarith only [hf',hp,show (10:ℝ)^9 ≤ (10:ℝ)^9*s*|frequency m v| by
      linear_combination ((10:ℝ)^9)*hs']

/-- For any real eight-runner arrangement and any subject, either the
cascade reaches a fixed point or the seven disparities satisfy an exact
relation in the same finite catalogue. -/
theorem arrangement_cascade_or_exact_relation (v : Fin 8 → ℝ) (hv : IsArrangement v)
    (k : Fin 8) {minimum : ℝ} (hm : IsDmin v k minimum) :
    CascadeFixes (disparitySet v k) (1/(8*minimum)) ∨
      ∃ m ∈ catalogue 7, frequency m (fun i => |v (k.succAbove i)-v k|) = 0 := by
  rcases clear_or_exact_relation (by decide : 7 ≤ 7)
      (fun i => |v (k.succAbove i)-v k|) (fun _ => 0) with hc | hr
  · obtain ⟨t,ht,hi⟩ := hc
    apply Or.inl
    apply (Cascade.cascadeFixes_iff_isolation hv hm).1
    refine ⟨t,ht,(Cascade.isolatedAt_iff_lonelyAt v k _).2 ?_⟩
    intro d hd
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hl).1
    simpa only [add_zero] using (hi i).le
  · exact Or.inr hr

#print axioms clear_or_exact_relation
#print axioms arrangement_cascade_or_exact_relation



/-- Classical isolation for arbitrary real arrangements is equivalent to
checking the finite set of exact, nonzero relation types. Each type is
an obligation on the arrangements satisfying its relation. -/
theorem lonelyRunnerEight_iff_exact_types :
    LonelyRunnerEight ↔
      ∀ m ∈ catalogue 7, ∀ v : Fin 8 → ℝ, IsArrangement v →
        ∀ k : Fin 8, frequency m (fun i => |v (k.succAbove i)-v k|) = 0 →
          Isolation v k := by
  constructor
  · intro h _ _ v hv k _
    exact h v hv k
  · intro h v hv k
    obtain ⟨minimum,hm⟩ := Cascade.exists_dmin (v := v) k
    rcases arrangement_cascade_or_exact_relation v hv k hm with hfix | ⟨m,hmem,he⟩
    · exact (Cascade.cascadeFixes_iff_isolation hv hm).2 hfix
    · exact h m hmem v hv k he

/-- The corresponding finite reduction for any allowed time set that contains
the first window, including the union of the two cascade windows.
The type of a normalized input includes its pinned minimum label. -/
theorem windows_iff_bounded_types (W : Set ℝ) (hW : Icc (1/8:ℝ) (7/8) ⊆ W) :
    (∀ v : Fin 8 → ℝ, IsArrangement v → ∀ (k : Fin 8) (minimum : ℝ),
      IsDmin v k minimum → ∃ t ∈ W, IsolatedAt v k (t/minimum)) ↔
    (∀ m ∈ catalogue 6, ∀ v : Fin 8 → ℝ, IsArrangement v →
      ∀ (k : Fin 8) (minimum : ℝ), IsDmin v k minimum →
        ∀ j : Fin 7, |v (k.succAbove j)-v k| = minimum →
          |frequency m (reducedReadings v k j minimum)| ≤ (4*10^9/3:ℝ) →
            ∃ t ∈ W, IsolatedAt v k (t/minimum)) := by
  constructor
  · intro h _ _ v hv k minimum hm _ _ _
    exact h v hv k minimum hm
  · intro h v hv k minimum hm
    obtain ⟨j,hj,hw | ⟨m,hmem,hfreq⟩⟩ := arrangement_first_window v hv k hm
    · obtain ⟨t,ht,hiso⟩ := hw
      exact ⟨t,hW ht,hiso⟩
    · exact h m hmem v hv k minimum hm j hj hfreq

#print axioms lonelyRunnerEight_iff_exact_types
#print axioms windows_iff_bounded_types

end Fresh.FiniteRelations
