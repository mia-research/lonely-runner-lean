import LonelyRunner.LRC.Defs
import LonelyRunner.LRC.SmallN.IntLRC_4

/-!
# `intLRC 5` — Bienia's `k = 4` argument (helpers)

Four moving runners + observer, target gap `1/5`. Literature `n = 4`
(observer omitted), proved by Bienia–Goddyn–Gvozdjak–Sebő–Tarsi 1998 with an
elementary self-contained argument using that `n + 1 = 5` is prime.

This file collects the machinery; `IntLRC_5.lean` assembles the main theorem.

## Roadmap (Bienia §3–§4)
* **Generalised shift lemmas** (below): lift the gap-`1/4` shift lemmas of
  `IntLRC_4_Bienia` to any gap `g ≤ 1/4`, so the pre-jump works at `1/5`.
* **Lemma (3)** (prime pigeonhole): among the five times `t + j/5`, a speed
  divisible by 5 is fixed while every other cycles through all nonzero fifths;
  a counting argument gives a fully-distant time.
* Cases `|D| = 0` (`t = 1/5`, done in `IntLRC_5.lean`), `|D| ∈ {2,3}`
  (induction + Lemma 3), `|D| = 1` (gcd split + doubling).
-/

open MeasureTheory Set

/-- Integer shifts leave `circDist` unchanged (local copy; the one in
    `IntLRC_4_Bienia` is `private`). -/
private theorem circDist_add_intCast' (z : ℝ) (n : ℤ) :
    circDist (z + (n : ℝ)) = circDist z := by
  unfold circDist; rw [Int.fract_add_intCast]

/-- **Equispaced shift, general gap `g ≤ 1/4`.**  For `m ≥ 2`, some shift
    `k/m` (`k : ℤ`) lands `y` in the distant arc `[g, 1-g]`.  Consecutive shifts
    are `1/m ≤ 1/2 ≤ 1-2g` apart, so they cannot jump over the arc. -/
theorem exists_shift_distant_gen (m : ℕ) (hm : 2 ≤ m) (g : ℝ) (hg0 : 0 < g) (hg4 : g ≤ 1 / 4)
    (y : ℝ) : ∃ k : ℤ, circDist (y + (k : ℝ) / (m : ℝ)) ≥ g := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hinvm : (1 : ℝ) / (m : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hmR
  refine ⟨⌈(m : ℝ) * (g - y)⌉, ?_⟩
  set K : ℤ := ⌈(m : ℝ) * (g - y)⌉ with hK
  have hk_lb : (m : ℝ) * (g - y) ≤ (K : ℝ) := Int.le_ceil _
  have hk_ub : (K : ℝ) < (m : ℝ) * (g - y) + 1 := Int.ceil_lt_add_one _
  have hz_lb : g ≤ y + (K : ℝ) / (m : ℝ) := by
    have h : (g - y) ≤ (K : ℝ) / (m : ℝ) := (le_div_iff₀ hm0).mpr (by rw [mul_comm]; exact hk_lb)
    linarith
  have hz_ub : y + (K : ℝ) / (m : ℝ) ≤ 1 - g := by
    have h : (K : ℝ) / (m : ℝ) < (g - y) + 1 / (m : ℝ) := by
      rw [div_lt_iff₀ hm0]
      have hid : ((g - y) + 1 / (m : ℝ)) * (m : ℝ) = (m : ℝ) * (g - y) + 1 := by field_simp
      rw [hid]; exact hk_ub
    have h1m : 1 / (m : ℝ) ≤ 1 - 2 * g := by linarith
    linarith
  have hfr : Int.fract (y + (K : ℝ) / (m : ℝ)) = y + (K : ℝ) / (m : ℝ) :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  unfold circDist
  rw [hfr, ge_iff_le, le_min_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Pre-jump shift, arbitrary multiplier, general gap `g ≤ 1/4`.**  If `d ≥ 2`
    and `d ∤ v`, some shift `v·K/d` places `y` in the distant arc `[g, 1-g]`.
    The orbit `{v·K/d mod 1}` is the order-`d/gcd(v,d) ≥ 2` cyclic subgroup;
    combine `exists_shift_distant_gen` with Bézout. -/
theorem exists_step_distant_gen (v d : ℕ) (hd : 2 ≤ d) (hdvd : ¬ (d ∣ v))
    (g : ℝ) (hg0 : 0 < g) (hg4 : g ≤ 1 / 4) (y : ℝ) :
    ∃ K : ℤ, circDist (y + (v : ℝ) * (K : ℝ) / (d : ℝ)) ≥ g := by
  have hd0 : 0 < d := by omega
  have he_pos : 0 < Nat.gcd v d := Nat.gcd_pos_of_pos_right v hd0
  set e : ℕ := Nat.gcd v d with he
  have he_dvd_d : e ∣ d := Nat.gcd_dvd_right v d
  have he_dvd_v : e ∣ v := Nat.gcd_dvd_left v d
  have he_ne_d : e ≠ d := fun h => hdvd (h ▸ he_dvd_v)
  obtain ⟨mm, hmm⟩ := id he_dvd_d
  have hmm2 : 2 ≤ mm := by rcases mm with _ | _ | mm <;> omega
  set D : ℕ := d / e with hD
  have hD_eq : D = mm := by rw [hD, hmm, Nat.mul_div_cancel_left mm he_pos]
  have hD_ge2 : 2 ≤ D := by rw [hD_eq]; exact hmm2
  set V : ℕ := v / e with hV
  have hveq : (e : ℝ) * (V : ℝ) = (v : ℝ) := by exact_mod_cast Nat.mul_div_cancel' he_dvd_v
  have hdeq : (e : ℝ) * (D : ℝ) = (d : ℝ) := by exact_mod_cast Nat.mul_div_cancel' he_dvd_d
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he_pos.ne'
  have hcop : Nat.Coprime V D := Nat.coprime_div_gcd_div_gcd he_pos
  have hcopZ : IsCoprime (V : ℤ) (D : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨a, b, hab⟩ := hcopZ
  have habR : (a : ℝ) * (V : ℝ) + (b : ℝ) * (D : ℝ) = 1 := by exact_mod_cast hab
  obtain ⟨k₀, hk₀⟩ := exists_shift_distant_gen D hD_ge2 g hg0 hg4 y
  refine ⟨a * k₀, ?_⟩
  have hfinal :
      y + (v : ℝ) * ((a * k₀ : ℤ) : ℝ) / (d : ℝ)
        = (y + (k₀ : ℝ) / (D : ℝ)) + ((-(b * k₀) : ℤ) : ℝ) := by
    have h1 : (v : ℝ) * ((a * k₀ : ℤ) : ℝ) / (d : ℝ)
        = ((V : ℝ) * ((a * k₀ : ℤ) : ℝ)) / (D : ℝ) := by
      rw [← hveq, ← hdeq, mul_assoc, mul_div_mul_left _ _ heR]
    have hVa : (V : ℝ) * ((a * k₀ : ℤ) : ℝ) = (k₀ : ℝ) - (b : ℝ) * (k₀ : ℝ) * (D : ℝ) := by
      push_cast; linear_combination (k₀ : ℝ) * habR
    rw [h1, hVa]; push_cast; field_simp; ring
  rw [hfinal, circDist_add_intCast']
  exact hk₀

/-! ### Lemma (3) geometry — when a `+s/5` shift lands in the near-zero arc

For `f = fract y ∈ [0,1)`, the four shifted points `f + s/5` (`s = 1,2,3,4`) are
"bad" (`circDist < 1/5`, i.e. within `1/5` of an integer) exactly on the open
intervals `bad₁=(3/5,1)`, `bad₂=(2/5,4/5)`, `bad₃=(1/5,3/5)`, `bad₄=(0,2/5)`.
These adjacent intervals have no triple overlap, so at any `f` at most two shifts
are bad — and at most one unless `f` lies in the interior set
`C₂ = (1/5,2/5)∪(2/5,3/5)∪(3/5,4/5)`. -/

private theorem bad_fifth_one (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1) :
    circDist (f + 1 / 5) < 1 / 5 ↔ 3 / 5 < f := by
  unfold circDist
  rcases lt_or_ge (f + 1 / 5) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩, min_lt_iff]
    constructor
    · rintro (h | h) <;> linarith
    · intro h; right; linarith
  · rw [show f + 1 / 5 = (f - 4 / 5) + 1 from by ring, Int.fract_add_one,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩, min_lt_iff]
    constructor
    · intro _; linarith
    · intro _; left; linarith

private theorem bad_fifth_two (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1) :
    circDist (f + 2 / 5) < 1 / 5 ↔ (2 / 5 < f ∧ f < 4 / 5) := by
  unfold circDist
  rcases lt_or_ge (f + 2 / 5) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩, min_lt_iff]
    constructor
    · rintro (h | h)
      · exfalso; linarith
      · exact ⟨by linarith, by linarith⟩
    · intro ⟨_, _⟩; right; linarith
  · rw [show f + 2 / 5 = (f - 3 / 5) + 1 from by ring, Int.fract_add_one,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩, min_lt_iff]
    constructor
    · rintro (h | h)
      · exact ⟨by linarith, by linarith⟩
      · exfalso; linarith
    · intro ⟨_, _⟩; left; linarith

private theorem bad_fifth_three (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1) :
    circDist (f + 3 / 5) < 1 / 5 ↔ (1 / 5 < f ∧ f < 3 / 5) := by
  unfold circDist
  rcases lt_or_ge (f + 3 / 5) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩, min_lt_iff]
    constructor
    · rintro (h | h)
      · exfalso; linarith
      · exact ⟨by linarith, by linarith⟩
    · intro ⟨_, _⟩; right; linarith
  · rw [show f + 3 / 5 = (f - 2 / 5) + 1 from by ring, Int.fract_add_one,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩, min_lt_iff]
    constructor
    · rintro (h | h)
      · exact ⟨by linarith, by linarith⟩
      · exfalso; linarith
    · intro ⟨_, _⟩; left; linarith

private theorem bad_fifth_four (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1) :
    circDist (f + 4 / 5) < 1 / 5 ↔ (0 < f ∧ f < 2 / 5) := by
  unfold circDist
  rcases lt_or_ge (f + 4 / 5) 1 with hlt | hge
  · rw [Int.fract_eq_self.mpr ⟨by linarith, hlt⟩, min_lt_iff]
    constructor
    · rintro (h | h)
      · exfalso; linarith
      · exact ⟨by linarith, by linarith⟩
    · intro ⟨_, _⟩; right; linarith
  · rw [show f + 4 / 5 = (f - 1 / 5) + 1 from by ring, Int.fract_add_one,
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩, min_lt_iff]
    constructor
    · rintro (h | h)
      · exact ⟨by linarith, by linarith⟩
      · exfalso; linarith
    · intro ⟨_, _⟩; left; linarith

/-- **Lemma-3 count bound (in terms of `f = fract y`).** At most two of the four
    `+s/5` shifts are non-distant.  Split `{1,2,3,4} = {1,3} ∪ {2,4}`: `bad₁,bad₃`
    are disjoint and `bad₂,bad₄` are disjoint, so each half contributes ≤ 1. -/
theorem badShift_le_two_f (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1) :
    ((Finset.Icc 1 4).filter (fun s : ℕ => circDist (f + (s : ℝ) / 5) < 1 / 5)).card ≤ 2 := by
  have hsplit : (Finset.Icc 1 4 : Finset ℕ) = {1, 3} ∪ {2, 4} := by decide
  rw [hsplit, Finset.filter_union]
  refine le_trans (Finset.card_union_le _ _) ?_
  have h13 : (({1, 3} : Finset ℕ).filter
      (fun s : ℕ => circDist (f + (s : ℝ) / 5) < 1 / 5)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
    obtain ⟨ha1, hpa⟩ := ha; obtain ⟨hb1, hpb⟩ := hb
    rcases ha1 with rfl | rfl <;> rcases hb1 with rfl | rfl
    · rfl
    · exfalso; norm_num at hpa hpb
      rw [bad_fifth_one f h0 h1] at hpa; rw [bad_fifth_three f h0 h1] at hpb; linarith
    · exfalso; norm_num at hpa hpb
      rw [bad_fifth_three f h0 h1] at hpa; rw [bad_fifth_one f h0 h1] at hpb; linarith
    · rfl
  have h24 : (({2, 4} : Finset ℕ).filter
      (fun s : ℕ => circDist (f + (s : ℝ) / 5) < 1 / 5)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at ha hb
    obtain ⟨ha1, hpa⟩ := ha; obtain ⟨hb1, hpb⟩ := hb
    rcases ha1 with rfl | rfl <;> rcases hb1 with rfl | rfl
    · rfl
    · exfalso; norm_num at hpa hpb
      rw [bad_fifth_two f h0 h1] at hpa; rw [bad_fifth_four f h0 h1] at hpb; linarith
    · exfalso; norm_num at hpa hpb
      rw [bad_fifth_four f h0 h1] at hpa; rw [bad_fifth_two f h0 h1] at hpb; linarith
    · rfl
  omega

/-- **Residue injection.** For `5 ∤ v`, the actual bad-shift count (over times
    `t + j/5`) is at most the `+s/5` count, via the injection `j ↦ (j·v) mod 5`
    on `{1,2,3,4}` (a bijection since `v` is invertible mod the prime `5`). -/
theorem nbad_le_badShift (v : ℕ) (hv : ¬ 5 ∣ v) (y : ℝ) :
    ((Finset.Icc 1 4).filter (fun j : ℕ => circDist (y + (j : ℝ) * (v : ℝ) / 5) < 1 / 5)).card
      ≤ ((Finset.Icc 1 4).filter (fun s : ℕ => circDist (y + (s : ℝ) / 5) < 1 / 5)).card := by
  have hcop : Nat.Coprime 5 v := (Nat.Prime.coprime_iff_not_dvd (p := 5) (by decide)).mpr hv
  apply Finset.card_le_card_of_injOn (fun j => (j * v) % 5)
  · intro j hj
    obtain ⟨hjIcc, hbad⟩ := Finset.mem_filter.mp hj
    obtain ⟨hj1, hj4⟩ := Finset.mem_Icc.mp hjIcc
    have hjv : ¬ (5 ∣ j * v) := fun h => by
      have h5j : (5 : ℕ) ∣ j := hcop.dvd_of_dvd_mul_right h
      exact absurd (Nat.le_of_dvd (by omega) h5j) (by omega)
    have hmod_pos : (j * v) % 5 ≠ 0 := fun h => hjv (Nat.dvd_of_mod_eq_zero h)
    have hmod_lt : (j * v) % 5 < 5 := Nat.mod_lt _ (by norm_num)
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have key : y + (j : ℝ) * (v : ℝ) / 5
        = (y + (((j * v) % 5 : ℕ) : ℝ) / 5) + (((j * v) / 5 : ℕ) : ℝ) := by
      have hc : (j : ℝ) * (v : ℝ) = ((j * v : ℕ) : ℝ) := by push_cast; ring
      have hdm : ((j * v : ℕ) : ℝ) = 5 * (((j * v) / 5 : ℕ) : ℝ) + (((j * v) % 5 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod (j * v) 5).symm
      rw [hc, hdm]; ring
    have heq : circDist (y + (j : ℝ) * (v : ℝ) / 5)
        = circDist (y + (((j * v) % 5 : ℕ) : ℝ) / 5) := by
      rw [key]; unfold circDist; rw [Int.fract_add_natCast]
    rw [← heq]; exact hbad
  · intro j1 hj1 j2 hj2 heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hj1 hj2
    have hmod : j1 * v ≡ j2 * v [MOD 5] := heq
    have hj : j1 ≡ j2 [MOD 5] := Nat.ModEq.cancel_right_of_coprime hcop hmod
    have h3 : j1 % 5 = j2 % 5 := hj
    omega

/-- `circDist` depends only on the fractional part (modulo the added constant). -/
theorem circDist_add_eq_fract (y c : ℝ) : circDist (y + c) = circDist (Int.fract y + c) := by
  conv_lhs => rw [← Int.floor_add_fract y]
  rw [show (↑⌊y⌋ + Int.fract y) + c = (Int.fract y + c) + (↑⌊y⌋ : ℝ) from by ring]
  unfold circDist; rw [Int.fract_add_intCast]

/-- At `f = 0` no `+s/5` shift is bad (the count is `0`). -/
theorem badShift_zero_f :
    ((Finset.Icc 1 4).filter (fun s : ℕ => circDist ((0 : ℝ) + (s : ℝ) / 5) < 1 / 5)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s hs
  obtain ⟨hs1, hs4⟩ := Finset.mem_Icc.mp hs
  have hsR1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hsR4 : (s : ℝ) ≤ 4 := by exact_mod_cast hs4
  rw [zero_add, not_lt]
  unfold circDist
  rw [Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩, le_min_iff]
  exact ⟨by linarith, by linarith⟩

/-- **Lemma-3 refined count bound:** off the interior set `C₂` (i.e. when
    `f ≤ 1/5 ∨ 4/5 ≤ f ∨ f = 2/5 ∨ f = 3/5`), at most *one* `+s/5` shift is bad.
    In each of the four cases all bad shifts are forced to a single value. -/
theorem badShift_le_one_f (f : ℝ) (h0 : 0 ≤ f) (h1 : f < 1)
    (hC2 : f ≤ 1 / 5 ∨ 4 / 5 ≤ f ∨ f = 2 / 5 ∨ f = 3 / 5) :
    ((Finset.Icc 1 4).filter (fun s : ℕ => circDist (f + (s : ℝ) / 5) < 1 / 5)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter, Finset.mem_Icc] at ha hb
  obtain ⟨⟨ha1, ha4⟩, hpa⟩ := ha
  obtain ⟨⟨hb1, hb4⟩, hpb⟩ := hb
  rcases hC2 with h | h | h | h
  · have F : ∀ s : ℕ, 1 ≤ s → s ≤ 4 → circDist (f + (s : ℝ) / 5) < 1 / 5 → s = 4 := by
      intro s hs1 hs4 hb'
      interval_cases s
      · exfalso; norm_num at hb'; rw [bad_fifth_one f h0 h1] at hb'; linarith
      · exfalso; norm_num at hb'; rw [bad_fifth_two f h0 h1] at hb'; linarith [hb'.1, hb'.2]
      · exfalso; norm_num at hb'; rw [bad_fifth_three f h0 h1] at hb'; linarith [hb'.1, hb'.2]
      · rfl
    rw [F a ha1 ha4 hpa, F b hb1 hb4 hpb]
  · have F : ∀ s : ℕ, 1 ≤ s → s ≤ 4 → circDist (f + (s : ℝ) / 5) < 1 / 5 → s = 1 := by
      intro s hs1 hs4 hb'
      interval_cases s
      · rfl
      · exfalso; norm_num at hb'; rw [bad_fifth_two f h0 h1] at hb'; linarith [hb'.1, hb'.2]
      · exfalso; norm_num at hb'; rw [bad_fifth_three f h0 h1] at hb'; linarith [hb'.1, hb'.2]
      · exfalso; norm_num at hb'; rw [bad_fifth_four f h0 h1] at hb'; linarith [hb'.1, hb'.2]
    rw [F a ha1 ha4 hpa, F b hb1 hb4 hpb]
  · have F : ∀ s : ℕ, 1 ≤ s → s ≤ 4 → circDist (f + (s : ℝ) / 5) < 1 / 5 → s = 3 := by
      intro s hs1 hs4 hb'
      interval_cases s
      · exfalso; norm_num at hb'; rw [bad_fifth_one f h0 h1] at hb'; linarith
      · exfalso; norm_num at hb'; rw [bad_fifth_two f h0 h1] at hb'; linarith [hb'.1, hb'.2]
      · rfl
      · exfalso; norm_num at hb'; rw [bad_fifth_four f h0 h1] at hb'; linarith [hb'.1, hb'.2]
    rw [F a ha1 ha4 hpa, F b hb1 hb4 hpb]
  · have F : ∀ s : ℕ, 1 ≤ s → s ≤ 4 → circDist (f + (s : ℝ) / 5) < 1 / 5 → s = 2 := by
      intro s hs1 hs4 hb'
      interval_cases s
      · exfalso; norm_num at hb'; rw [bad_fifth_one f h0 h1] at hb'; linarith
      · rfl
      · exfalso; norm_num at hb'; rw [bad_fifth_three f h0 h1] at hb'; linarith [hb'.1, hb'.2]
      · exfalso; norm_num at hb'; rw [bad_fifth_four f h0 h1] at hb'; linarith [hb'.1, hb'.2]
    rw [F a ha1 ha4 hpa, F b hb1 hb4 hpb]

/-- Reduce the `+s/5` count to the fractional part of `y`. -/
theorem badShift_eq (y : ℝ) :
    ((Finset.Icc 1 4).filter (fun s : ℕ => circDist (y + (s : ℝ) / 5) < 1 / 5)).card
      = ((Finset.Icc 1 4).filter
          (fun s : ℕ => circDist (Int.fract y + (s : ℝ) / 5) < 1 / 5)).card := by
  congr 1
  apply Finset.filter_congr
  intro s _
  rw [circDist_add_eq_fract]

/-- A non-`5`-divisible runner is non-distant at ≤ 2 of the four times `t + j/5`. -/
theorem nbad_le_two (v : ℕ) (hv : ¬ 5 ∣ v) (y : ℝ) :
    ((Finset.Icc 1 4).filter
      (fun j : ℕ => circDist (y + (j : ℝ) * (v : ℝ) / 5) < 1 / 5)).card ≤ 2 := by
  refine le_trans (nbad_le_badShift v hv y) ?_
  rw [badShift_eq]
  exact badShift_le_two_f _ (Int.fract_nonneg y) (Int.fract_lt_one y)

/-- If moreover `fract y` is off the interior `C₂`, the count drops to ≤ 1. -/
theorem nbad_le_one (v : ℕ) (hv : ¬ 5 ∣ v) (y : ℝ)
    (hC2 : Int.fract y ≤ 1 / 5 ∨ 4 / 5 ≤ Int.fract y ∨ Int.fract y = 2 / 5 ∨ Int.fract y = 3 / 5) :
    ((Finset.Icc 1 4).filter
      (fun j : ℕ => circDist (y + (j : ℝ) * (v : ℝ) / 5) < 1 / 5)).card ≤ 1 := by
  refine le_trans (nbad_le_badShift v hv y) ?_
  rw [badShift_eq]
  exact badShift_le_one_f _ (Int.fract_nonneg y) (Int.fract_lt_one y) hC2

/-- If `fract y = 0` (runner at the origin), the count is 0. -/
theorem nbad_eq_zero_fract (v : ℕ) (hv : ¬ 5 ∣ v) (y : ℝ) (hf : Int.fract y = 0) :
    ((Finset.Icc 1 4).filter
      (fun j : ℕ => circDist (y + (j : ℝ) * (v : ℝ) / 5) < 1 / 5)).card = 0 := by
  have h1 := nbad_le_badShift v hv y
  rw [badShift_eq, hf, badShift_zero_f] at h1
  omega

/-- A `5`-divisible runner stays fixed under `+j/5`; if distant at `t`, count 0. -/
theorem nbad_dvd5 (v : ℕ) (h5 : 5 ∣ v) (y : ℝ) (hdist : 1 / 5 ≤ circDist y) :
    ((Finset.Icc 1 4).filter
      (fun j : ℕ => circDist (y + (j : ℝ) * (v : ℝ) / 5) < 1 / 5)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  rw [not_lt]
  obtain ⟨m, hm⟩ := h5
  have hval : y + (j : ℝ) * (v : ℝ) / 5 = y + ((j * m : ℕ) : ℝ) := by rw [hm]; push_cast; ring
  rw [hval]
  have hsh : circDist (y + ((j * m : ℕ) : ℝ)) = circDist y := by
    unfold circDist; rw [Int.fract_add_natCast]
  rw [hsh]; exact hdist

/-- The "off `C₂`" predicate: `fract y` not in the open interior `C₂`. -/
def offC2 (x : ℝ) : Prop := x ≤ 1 / 5 ∨ 4 / 5 ≤ x ∨ x = 2 / 5 ∨ x = 3 / 5

noncomputable instance : DecidablePred offC2 := fun x => by unfold offC2; infer_instance

/-- **Bienia's Lemma (3) — prime pigeonhole.**  Suppose the `5`-divisible runners
    (`D`) are all distant at `t`, and `|R₂| < |R₀|` where `R₀` collects the
    `5`-divisible-or-at-origin runners and `R₂` the non-`5`-divisible runners whose
    phase lies in the interior `C₂`.  Then some time `t + j/5` (`j ∈ {1,2,3,4}`)
    makes *every* runner distant.  Proof: a double-count.  Each runner is
    non-distant at ≤ `wtᵢ = [i∉R₀] + [i∈R₂]` of the four shifted times, so
    `Σᵢ nbadᵢ ≤ (4−|R₀|)+|R₂| < 4`; but if no shift worked every time has a bad
    runner, forcing `Σᵢ nbadᵢ ≥ 4` — contradiction. -/
theorem lemma3 (speeds : Fin 4 → ℕ) (t : ℝ)
    (hD : ∀ i, 5 ∣ speeds i → 1 / 5 ≤ circDist ((speeds i : ℝ) * t))
    (hcard :
      (Finset.univ.filter
          (fun i => ¬ 5 ∣ speeds i ∧ ¬ offC2 (Int.fract ((speeds i : ℝ) * t)))).card
        < (Finset.univ.filter
          (fun i => 5 ∣ speeds i ∨ Int.fract ((speeds i : ℝ) * t) = 0)).card) :
    ∃ j ∈ (Finset.Icc 1 4 : Finset ℕ),
      ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * (t + (j : ℝ) / 5)) := by
  by_contra hcon
  push_neg at hcon
  set R0 := Finset.univ.filter
    (fun i => 5 ∣ speeds i ∨ Int.fract ((speeds i : ℝ) * t) = 0) with hR0
  set R2 := Finset.univ.filter
    (fun i => ¬ 5 ∣ speeds i ∧ ¬ offC2 (Int.fract ((speeds i : ℝ) * t))) with hR2
  have hlow : 4 ≤ ∑ i : Fin 4, ((Finset.Icc 1 4).filter
      (fun j : ℕ => circDist ((speeds i : ℝ) * (t + (j : ℝ) / 5)) < 1 / 5)).card := by
    have hdc : ∑ i : Fin 4, ((Finset.Icc 1 4).filter
          (fun j : ℕ => circDist ((speeds i : ℝ) * (t + (j : ℝ) / 5)) < 1 / 5)).card
        = ∑ j ∈ (Finset.Icc 1 4 : Finset ℕ), (Finset.univ.filter
          (fun i : Fin 4 => circDist ((speeds i : ℝ) * (t + (j : ℝ) / 5)) < 1 / 5)).card := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
    rw [hdc]
    have hcard4 : (Finset.Icc 1 4 : Finset ℕ).card = 4 := by decide
    calc (4 : ℕ) = ∑ _j ∈ (Finset.Icc 1 4 : Finset ℕ), 1 := by simp [Finset.sum_const, hcard4]
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨i, hi⟩ := hcon j hj
          exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have key : ∀ i : Fin 4, ((Finset.Icc 1 4).filter
        (fun j : ℕ => circDist ((speeds i : ℝ) * (t + (j : ℝ) / 5)) < 1 / 5)).card
      ≤ (if i ∉ R0 then 1 else 0) + (if i ∈ R2 then 1 else 0) := by
    intro i
    have hcongr : ((Finset.Icc 1 4).filter
          (fun j : ℕ => circDist ((speeds i : ℝ) * (t + (j : ℝ) / 5)) < 1 / 5))
        = ((Finset.Icc 1 4).filter
          (fun j : ℕ => circDist ((speeds i : ℝ) * t + (j : ℝ) * (speeds i : ℝ) / 5) < 1 / 5)) := by
      apply Finset.filter_congr; intro j _
      rw [show (speeds i : ℝ) * (t + (j : ℝ) / 5)
          = (speeds i : ℝ) * t + (j : ℝ) * (speeds i : ℝ) / 5 from by ring]
    rw [hcongr]
    by_cases h0 : i ∈ R0
    · rw [if_neg (not_not.mpr h0)]
      have hz : ((Finset.Icc 1 4).filter
          (fun j : ℕ => circDist ((speeds i : ℝ) * t + (j : ℝ) * (speeds i : ℝ) / 5) < 1 / 5)).card
          = 0 := by
        simp only [hR0, Finset.mem_filter, Finset.mem_univ, true_and] at h0
        rcases h0 with h5 | hfr
        · exact nbad_dvd5 (speeds i) h5 _ (hD i h5)
        · by_cases h5 : 5 ∣ speeds i
          · exact nbad_dvd5 (speeds i) h5 _ (hD i h5)
          · exact nbad_eq_zero_fract (speeds i) h5 _ hfr
      rw [hz]; exact Nat.zero_le _
    · rw [if_pos h0]
      have h5 : ¬ 5 ∣ speeds i := fun h =>
        h0 (by rw [hR0]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl h⟩)
      by_cases h2 : i ∈ R2
      · rw [if_pos h2]; exact le_trans (nbad_le_two (speeds i) h5 _) (by norm_num)
      · rw [if_neg h2]
        have hoff : offC2 (Int.fract ((speeds i : ℝ) * t)) := by
          by_contra hno
          exact h2 (by rw [hR2]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨h5, hno⟩⟩)
        exact le_trans (nbad_le_one (speeds i) h5 _ hoff) (by norm_num)
  have hf2 : Finset.univ.filter (fun i : Fin 4 => i ∈ R2) = R2 := by ext i; simp
  have hf0 : Finset.univ.filter (fun i : Fin 4 => i ∉ R0) = Finset.univ \ R0 := by ext i; simp
  have hup : (∑ i : Fin 4, ((Finset.Icc 1 4).filter
        (fun j : ℕ => circDist ((speeds i : ℝ) * (t + (j : ℝ) / 5)) < 1 / 5)).card)
      ≤ (4 - R0.card) + R2.card := by
    refine le_trans (Finset.sum_le_sum (fun i _ => key i)) ?_
    rw [Finset.sum_add_distrib]
    have e1 : ∑ i : Fin 4, (if i ∈ R2 then 1 else 0) = R2.card := by
      rw [← Finset.sum_filter, hf2, Finset.sum_const, smul_eq_mul, mul_one]
    have e2 : ∑ i : Fin 4, (if i ∉ R0 then 1 else 0) = 4 - R0.card := by
      rw [← Finset.sum_filter, hf0, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_sdiff]
      simp
    rw [e1, e2]
  have hR0le : R0.card ≤ 4 := by
    rw [hR0]
    exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, Fintype.card_fin])
  omega

/-! ### Bienia §4 — applying Lemma (3) -/

/-- A non-distant runner has its phase off `C₂`, hence cannot lie in `R₂`. -/
theorem not_distant_offC2 (x : ℝ) (h : circDist x < 1 / 5) :
    Int.fract x ≤ 1 / 5 ∨ 4 / 5 ≤ Int.fract x ∨ Int.fract x = 2 / 5 ∨ Int.fract x = 3 / 5 := by
  unfold circDist at h
  rcases min_lt_iff.mp h with h' | h'
  · exact Or.inl (le_of_lt h')
  · exact Or.inr (Or.inl (by linarith))

/-- Three sorted runners with (symmetric) coprimality are simultaneously distant
    at gap `1/4` — `intLRC 4` specialised to the explicit ordered triple `![a,b,c]`. -/
theorem three_runner_quarter_ordered (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hcop : ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ c → d = 1) :
    ∃ t : ℝ, 1 / 4 ≤ circDist ((a : ℝ) * t) ∧ 1 / 4 ≤ circDist ((b : ℝ) * t) ∧
      1 / 4 ≤ circDist ((c : ℝ) * t) := by
  have hmono : StrictMono (![a, b, c] : Fin 3 → ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.lt_def] <;> omega
  have hpos : ∀ i, 0 < (![a, b, c] : Fin 3 → ℕ) i := by
    intro i; fin_cases i <;> simp <;> omega
  have hg : Finset.gcd Finset.univ (![a, b, c] : Fin 3 → ℕ) = 1 := by
    apply hcop
    · simpa using Finset.gcd_dvd (Finset.mem_univ (0 : Fin 3))
    · simpa using Finset.gcd_dvd (Finset.mem_univ (1 : Fin 3))
    · simpa using Finset.gcd_dvd (Finset.mem_univ (2 : Fin 3))
  obtain ⟨t, ht⟩ := intLRC_four (![a, b, c]) hmono hpos hg
  exact ⟨t, by have := ht 0; simpa using this, by have := ht 1; simpa using this,
    by have := ht 2; simpa using this⟩

/-- Unordered version: any three distinct coprime runners are distant at gap `1/4`. -/
theorem three_runner_quarter (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcop : ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ c → d = 1) :
    ∃ t : ℝ, 1 / 4 ≤ circDist ((a : ℝ) * t) ∧ 1 / 4 ≤ circDist ((b : ℝ) * t) ∧
      1 / 4 ≤ circDist ((c : ℝ) * t) := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · obtain ⟨t, p, q, r⟩ := three_runner_quarter_ordered a b c ha h1 h2 hcop; exact ⟨t, p, q, r⟩
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · obtain ⟨t, p, q, r⟩ := three_runner_quarter_ordered a c b ha h3 h2
          (fun d d1 d2 d3 => hcop d d1 d3 d2)
        exact ⟨t, p, r, q⟩
      · exact absurd h3 hac
      · obtain ⟨t, p, q, r⟩ := three_runner_quarter_ordered c a b hc h3 h1
          (fun d d1 d2 d3 => hcop d d2 d3 d1)
        exact ⟨t, q, r, p⟩
  · exact absurd h1 hab
  · rcases lt_trichotomy a c with h3 | h3 | h3
    · obtain ⟨t, p, q, r⟩ := three_runner_quarter_ordered b a c hb h1 h3
        (fun d d1 d2 d3 => hcop d d2 d1 d3)
      exact ⟨t, q, p, r⟩
    · exact absurd h3 hac
    · rcases lt_trichotomy b c with h2 | h2 | h2
      · obtain ⟨t, p, q, r⟩ := three_runner_quarter_ordered b c a hb h2 h3
          (fun d d1 d2 d3 => hcop d d3 d1 d2)
        exact ⟨t, r, p, q⟩
      · exact absurd h2 hbc
      · obtain ⟨t, p, q, r⟩ := three_runner_quarter_ordered c b a hc h2 h1
          (fun d d1 d2 d3 => hcop d d3 d2 d1)
        exact ⟨t, r, q, p⟩

/-- **Three distinct runners are simultaneously distant at gap `1/5`.**  Divide by
    `g = gcd`, apply `three_runner_quarter` (gap `1/4 ≥ 1/5`) to the coprime triple,
    rescale time by `1/g`. -/
theorem three_runner_fifth (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ t : ℝ, 1 / 5 ≤ circDist ((a : ℝ) * t) ∧ 1 / 5 ≤ circDist ((b : ℝ) * t) ∧
      1 / 5 ≤ circDist ((c : ℝ) * t) := by
  set g := Nat.gcd a (Nat.gcd b c) with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_iff.mpr (Or.inl ha)
  have hga : g ∣ a := Nat.gcd_dvd_left _ _
  have hgbc : g ∣ Nat.gcd b c := Nat.gcd_dvd_right _ _
  have hgb : g ∣ b := hgbc.trans (Nat.gcd_dvd_left _ _)
  have hgc : g ∣ c := hgbc.trans (Nat.gcd_dvd_right _ _)
  have hae : a = g * (a / g) := (Nat.mul_div_cancel' hga).symm
  have hbe : b = g * (b / g) := (Nat.mul_div_cancel' hgb).symm
  have hce : c = g * (c / g) := (Nat.mul_div_cancel' hgc).symm
  have ha' : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha hga) hg0
  have hb' : 0 < b / g := Nat.div_pos (Nat.le_of_dvd hb hgb) hg0
  have hc' : 0 < c / g := Nat.div_pos (Nat.le_of_dvd hc hgc) hg0
  have hd1 : a / g ≠ b / g := fun h => hab (by rw [hae, hbe, h])
  have hd2 : a / g ≠ c / g := fun h => hac (by rw [hae, hce, h])
  have hd3 : b / g ≠ c / g := fun h => hbc (by rw [hbe, hce, h])
  have hcop : ∀ d : ℕ, d ∣ a / g → d ∣ b / g → d ∣ c / g → d = 1 := by
    intro d hda hdb hdc
    have kda : d * g ∣ a := by obtain ⟨k, hk⟩ := hda; exact ⟨k, by rw [hae, hk]; ring⟩
    have kdb : d * g ∣ b := by obtain ⟨k, hk⟩ := hdb; exact ⟨k, by rw [hbe, hk]; ring⟩
    have kdc : d * g ∣ c := by obtain ⟨k, hk⟩ := hdc; exact ⟨k, by rw [hce, hk]; ring⟩
    have key : d * g ∣ g := Nat.dvd_gcd kda (Nat.dvd_gcd kdb kdc)
    have heq : d * g = g := Nat.dvd_antisymm key (dvd_mul_left g d)
    exact Nat.eq_of_mul_eq_mul_right hg0 (by rw [heq, one_mul])
  obtain ⟨τ, p, q, r⟩ := three_runner_quarter (a / g) (b / g) (c / g) ha' hb' hc' hd1 hd2 hd3 hcop
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
  refine ⟨τ / (g : ℝ), ?_, ?_, ?_⟩
  · rw [show (a : ℝ) * (τ / (g : ℝ)) = ((a / g : ℕ) : ℝ) * τ from by
        rw [show (a : ℝ) = (g : ℝ) * ((a / g : ℕ) : ℝ) from by exact_mod_cast hae]; field_simp]
    linarith
  · rw [show (b : ℝ) * (τ / (g : ℝ)) = ((b / g : ℕ) : ℝ) * τ from by
        rw [show (b : ℝ) = (g : ℝ) * ((b / g : ℕ) : ℝ) from by exact_mod_cast hbe]; field_simp]
    linarith
  · rw [show (c : ℝ) * (τ / (g : ℝ)) = ((c / g : ℕ) : ℝ) * τ from by
        rw [show (c : ℝ) = (g : ℝ) * ((c / g : ℕ) : ℝ) from by exact_mod_cast hce]; field_simp]
    linarith

open Finset in
/-- **`|D| = 3` case.** Three speeds divisible by 5: `three_runner_fifth` gives a
    time where they (and so all of `D`) are distant; then `|R₂| ≤ 1 < 3 ≤ |R₀|`,
    so `lemma3` finishes. -/
theorem case_D3 (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hD3 : (univ.filter (fun i => 5 ∣ speeds i)).card = 3) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  obtain ⟨i, j, k, hij, hik, hjk, hDeq⟩ := Finset.card_eq_three.mp hD3
  have getmem : ∀ m, m ∈ ({i, j, k} : Finset (Fin 4)) → 5 ∣ speeds m := by
    intro m hm
    have : m ∈ univ.filter (fun n => 5 ∣ speeds n) := by rw [hDeq]; exact hm
    exact (Finset.mem_filter.mp this).2
  obtain ⟨τ, di, dj, dk⟩ := three_runner_fifth (speeds i) (speeds j) (speeds k)
    (hpos i) (hpos j) (hpos k)
    (hmono.injective.ne hij) (hmono.injective.ne hik) (hmono.injective.ne hjk)
  have hDdist : ∀ m, 5 ∣ speeds m → 1 / 5 ≤ circDist ((speeds m : ℝ) * τ) := by
    intro m hm
    have hmem : m ∈ univ.filter (fun n => 5 ∣ speeds n) := by simp [hm]
    rw [hDeq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact di
    · exact dj
    · exact dk
  have hcard : (univ.filter (fun m => ¬ 5 ∣ speeds m ∧
        ¬ offC2 (Int.fract ((speeds m : ℝ) * τ)))).card
      < (univ.filter (fun m => 5 ∣ speeds m ∨ Int.fract ((speeds m : ℝ) * τ) = 0)).card := by
    have hsub0 : univ.filter (fun m => 5 ∣ speeds m)
        ⊆ univ.filter (fun m => 5 ∣ speeds m ∨ Int.fract ((speeds m : ℝ) * τ) = 0) := by
      intro m hm; rw [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, Or.inl hm.2⟩
    have h1 : 3 ≤ (univ.filter (fun m => 5 ∣ speeds m ∨
        Int.fract ((speeds m : ℝ) * τ) = 0)).card := by rw [← hD3]; exact Finset.card_le_card hsub0
    have hsub2 : univ.filter (fun m => ¬ 5 ∣ speeds m ∧
          ¬ offC2 (Int.fract ((speeds m : ℝ) * τ)))
        ⊆ univ.filter (fun m => ¬ 5 ∣ speeds m) := by
      intro m hm; rw [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, hm.2.1⟩
    have hneg : (univ.filter (fun m => ¬ 5 ∣ speeds m)).card = 1 := by
      have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (univ : Finset (Fin 4))) (p := fun m => 5 ∣ speeds m)
      rw [Finset.card_univ, Fintype.card_fin, hD3] at hsplit
      omega
    have h2 : (univ.filter (fun m => ¬ 5 ∣ speeds m ∧
        ¬ offC2 (Int.fract ((speeds m : ℝ) * τ)))).card ≤ 1 := by
      rw [← hneg]; exact Finset.card_le_card hsub2
    omega
  obtain ⟨jj, _, hall⟩ := lemma3 speeds τ hDdist hcard
  exact ⟨τ + (jj : ℝ) / 5, hall⟩

open Finset in
/-- **`|D| = 2` case.** Two speeds divisible by 5: `two_runner_quarter` gives a
    time where they (so all of `D`) are distant.  Either all four are distant
    (done), or some non-`D` runner is not — by `not_distant_offC2` it lies off
    `C₂`, so `|R₂| ≤ 1 < 2 ≤ |R₀|` and `lemma3` finishes. -/
theorem case_D2 (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hD2 : (univ.filter (fun i => 5 ∣ speeds i)).card = 2) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  obtain ⟨i, j, hij, hDeq⟩ := Finset.card_eq_two.mp hD2
  obtain ⟨τ, di', dj'⟩ := two_runner_quarter (speeds i) (speeds j) (hpos i) (hpos j)
    (hmono.injective.ne hij)
  have hDdist : ∀ m, 5 ∣ speeds m → 1 / 5 ≤ circDist ((speeds m : ℝ) * τ) := by
    intro m hm
    have hmem : m ∈ univ.filter (fun n => 5 ∣ speeds n) := by simp [hm]
    rw [hDeq, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · linarith [di']
    · linarith [dj']
  by_cases hall : ∀ m, 1 / 5 ≤ circDist ((speeds m : ℝ) * τ)
  · exact ⟨τ, hall⟩
  · push_neg at hall
    obtain ⟨m, hm⟩ := hall
    have hmlt : circDist ((speeds m : ℝ) * τ) < 1 / 5 := hm
    have hmnD : ¬ 5 ∣ speeds m := fun h => absurd (hDdist m h) (not_le.mpr hmlt)
    have hoffm : offC2 (Int.fract ((speeds m : ℝ) * τ)) := not_distant_offC2 _ hmlt
    have hcard : (univ.filter (fun n => ¬ 5 ∣ speeds n ∧
          ¬ offC2 (Int.fract ((speeds n : ℝ) * τ)))).card
        < (univ.filter (fun n => 5 ∣ speeds n ∨ Int.fract ((speeds n : ℝ) * τ) = 0)).card := by
      have h1 : 2 ≤ (univ.filter (fun n => 5 ∣ speeds n ∨
          Int.fract ((speeds n : ℝ) * τ) = 0)).card := by
        rw [← hD2]; apply Finset.card_le_card
        intro n hn; rw [Finset.mem_filter] at hn ⊢; exact ⟨hn.1, Or.inl hn.2⟩
      have hmfilt : m ∈ univ.filter (fun n => ¬ 5 ∣ speeds n) := by simp [hmnD]
      have hmR2 : m ∉ univ.filter (fun n => ¬ 5 ∣ speeds n ∧
          ¬ offC2 (Int.fract ((speeds n : ℝ) * τ))) := by
        rw [Finset.mem_filter]; rintro ⟨-, -, hno⟩; exact hno hoffm
      have hsub2 : univ.filter (fun n => ¬ 5 ∣ speeds n ∧
            ¬ offC2 (Int.fract ((speeds n : ℝ) * τ)))
          ⊆ (univ.filter (fun n => ¬ 5 ∣ speeds n)).erase m := by
        intro n hn
        rw [Finset.mem_erase, Finset.mem_filter]
        exact ⟨by rintro rfl; exact hmR2 hn, mem_univ n, (Finset.mem_filter.mp hn).2.1⟩
      have hneg2 : (univ.filter (fun n => ¬ 5 ∣ speeds n)).card = 2 := by
        have hs := Finset.filter_card_add_filter_neg_card_eq_card
          (s := (univ : Finset (Fin 4))) (p := fun n => 5 ∣ speeds n)
        rw [Finset.card_univ, Fintype.card_fin, hD2] at hs
        omega
      have h2 : (univ.filter (fun n => ¬ 5 ∣ speeds n ∧
          ¬ offC2 (Int.fract ((speeds n : ℝ) * τ)))).card ≤ 1 := by
        calc _ ≤ ((univ.filter (fun n => ¬ 5 ∣ speeds n)).erase m).card :=
              Finset.card_le_card hsub2
          _ = (univ.filter (fun n => ¬ 5 ∣ speeds n)).card - 1 := Finset.card_erase_of_mem hmfilt
          _ = 1 := by rw [hneg2]
      omega
    obtain ⟨jj, _, hallj⟩ := lemma3 speeds τ hDdist hcard
    exact ⟨τ + (jj : ℝ) / 5, hallj⟩

/-- **Distance doubling.**  If `circDist z ≤ 1/4`, doubling the time doubles the
    distance: `circDist (2z) = 2·circDist z`.  (First brick of Bienia's `|D|=1`
    doubling argument for the ÷5-runner-not-fastest sub-case.) -/
theorem circDist_two_mul (z : ℝ) (hz : circDist z ≤ 1 / 4) :
    circDist (2 * z) = 2 * circDist z := by
  have hf0 := Int.fract_nonneg z
  have hf1 := Int.fract_lt_one z
  set f := Int.fract z with hfdef
  have hfr : Int.fract (2 * z) = Int.fract (2 * f) := by
    conv_lhs => rw [← Int.floor_add_fract z]
    rw [mul_add, show 2 * (↑⌊z⌋ : ℝ) + 2 * f = 2 * f + ((2 * ⌊z⌋ : ℤ) : ℝ) from by push_cast; ring,
      Int.fract_add_intCast]
  have hcz : circDist z = min f (1 - f) := by rw [circDist]
  rw [hcz] at hz
  rw [circDist, hfr, hcz]
  rcases le_or_gt f (1 / 2) with hf | hf
  · rw [min_eq_left (show f ≤ 1 - f by linarith)] at hz ⊢
    rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩, min_eq_left (by linarith)]
  · rw [min_eq_right (show 1 - f ≤ f by linarith)] at hz ⊢
    have hfr2 : Int.fract (2 * f) = 2 * f - 1 := by
      conv_lhs => rw [show 2 * f = (2 * f - 1) + 1 from by ring]
      rw [Int.fract_add_one, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [hfr2, min_eq_right (by linarith)]
    ring

/-- **Iterated distance doubling.**  If `2ʲ·circDist w ≤ 1/2`, then
    `circDist (2ʲ·w) = 2ʲ·circDist w`.  The engine of the doubling minimality. -/
theorem circDist_two_pow (w : ℝ) (j : ℕ) (h : (2 : ℝ) ^ j * circDist w ≤ 1 / 2) :
    circDist ((2 : ℝ) ^ j * w) = (2 : ℝ) ^ j * circDist w := by
  induction j with
  | zero => simp
  | succ n ih =>
    have hstep : (2 : ℝ) ^ (n + 1) * circDist w = 2 * ((2 : ℝ) ^ n * circDist w) := by
      rw [pow_succ]; ring
    have hn4 : (2 : ℝ) ^ n * circDist w ≤ 1 / 4 := by rw [hstep] at h; linarith
    have hn2 : (2 : ℝ) ^ n * circDist w ≤ 1 / 2 := by linarith
    have hcn : circDist ((2 : ℝ) ^ n * w) ≤ 1 / 4 := by rw [ih hn2]; exact hn4
    rw [show (2 : ℝ) ^ (n + 1) * w = 2 * ((2 : ℝ) ^ n * w) from by rw [pow_succ]; ring,
      circDist_two_mul _ hcn, ih hn2, hstep]

/-- **Doubling step (Bienia §4 crux).**  Suppose at base time `x`: the fastest
    runner `vF` is at the origin (`fract(vF·x)=0`), the ÷5 runner `vE` is *not*
    distant (`0 < δe := circDist(vE·x) < 1/5`), and the third runner `v3` has
    `circDist(v3·x) ≤ δe/2`.  Doubling time to `t = 2ᴶx` (least `J` with
    `2ᴶ·δe ≥ 1/5`) keeps `vF` at the origin, makes `vE` distant, and keeps `v3`
    non-distant.  Distances double in lockstep (`circDist_two_pow`); minimality of
    `J` gives `2ᴶ·δe < 2/5`, so `2ᴶ·(δe/2) < 1/5` bounds `v3`. -/
theorem doubling_step (vF vE v3 : ℕ) (x : ℝ)
    (hF : Int.fract ((vF : ℝ) * x) = 0)
    (hδe_pos : 0 < circDist ((vE : ℝ) * x))
    (hδe_lt : circDist ((vE : ℝ) * x) < 1 / 5)
    (hδ3 : circDist ((v3 : ℝ) * x) ≤ circDist ((vE : ℝ) * x) / 2) :
    ∃ t : ℝ, Int.fract ((vF : ℝ) * t) = 0 ∧ 1 / 5 ≤ circDist ((vE : ℝ) * t) ∧
      circDist ((v3 : ℝ) * t) < 1 / 5 := by
  set δe := circDist ((vE : ℝ) * x) with hδe_def
  set δ3 := circDist ((v3 : ℝ) * x) with hδ3_def
  have hex : ∃ j : ℕ, (1 : ℝ) / 5 ≤ 2 ^ j * δe := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 / 5) / δe)
    refine ⟨N, ?_⟩
    have h2N : (N : ℝ) ≤ 2 ^ N := by
      calc (N : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self.le
        _ = 2 ^ N := by push_cast; ring
    have h1 : (1 : ℝ) / 5 < (N : ℝ) * δe := (div_lt_iff₀ hδe_pos).mp hN
    have h2 : (N : ℝ) * δe ≤ 2 ^ N * δe := mul_le_mul_of_nonneg_right h2N hδe_pos.le
    linarith
  classical
  set J := Nat.find hex with hJ
  have hJspec : (1 : ℝ) / 5 ≤ 2 ^ J * δe := Nat.find_spec hex
  have hJ0 : J ≠ 0 := by
    intro h; rw [h, pow_zero, one_mul] at hJspec; linarith
  have hJpred : 2 ^ (J - 1) * δe < 1 / 5 :=
    not_le.mp (Nat.find_min hex (show J - 1 < J by omega))
  have hpow : (2 : ℝ) ^ J = 2 ^ (J - 1) * 2 := by
    conv_lhs => rw [show J = (J - 1) + 1 by omega]
    rw [pow_succ]
  have hJlt : 2 ^ J * δe < 2 / 5 := by rw [hpow]; nlinarith [hJpred]
  have hpowpos : (0 : ℝ) < 2 ^ J := by positivity
  refine ⟨2 ^ J * x, ?_, ?_, ?_⟩
  · have hz : (vF : ℝ) * x = ((⌊(vF : ℝ) * x⌋ : ℤ) : ℝ) := by
      have h := Int.floor_add_fract ((vF : ℝ) * x)
      rw [hF, add_zero] at h; exact h.symm
    rw [show (vF : ℝ) * (2 ^ J * x) = 2 ^ J * ((vF : ℝ) * x) by ring, hz,
      show (2 : ℝ) ^ J * ((⌊(vF : ℝ) * x⌋ : ℤ) : ℝ) = (((2 ^ J : ℤ) * ⌊(vF : ℝ) * x⌋ : ℤ) : ℝ) by
        push_cast; ring]
    exact Int.fract_intCast _
  · rw [show (vE : ℝ) * (2 ^ J * x) = 2 ^ J * ((vE : ℝ) * x) by ring,
      circDist_two_pow ((vE : ℝ) * x) J (by rw [← hδe_def]; linarith), ← hδe_def]
    exact hJspec
  · have h3half : 2 ^ J * δ3 ≤ 2 ^ J * δe / 2 := by nlinarith [hδ3]
    rw [show (v3 : ℝ) * (2 ^ J * x) = 2 ^ J * ((v3 : ℝ) * x) by ring,
      circDist_two_pow ((v3 : ℝ) * x) J (by rw [← hδ3_def]; nlinarith), ← hδ3_def]
    nlinarith

/-- A nonzero integer of absolute value `< m` is not divisible by `m`. -/
theorem not_dvd_of_natAbs_lt (m : ℕ) (c : ℤ) (hc : c ≠ 0) (hlt : c.natAbs < m) :
    ¬ (m : ℤ) ∣ c := by
  intro hdvd
  have hna : (m : ℤ).natAbs ∣ c.natAbs := Int.natAbs_dvd_natAbs.mpr hdvd
  rw [Int.natAbs_natCast] at hna
  exact absurd (Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hna) (not_le.mpr hlt)

/-- `circDist` of an integer fraction `c / m` in terms of `c % m`. -/
theorem circDist_intCast_div (c : ℤ) (m : ℕ) :
    circDist ((c : ℝ) / (m : ℝ)) =
      min ((↑(c % (m : ℤ)) : ℝ) / (m : ℝ)) (1 - (↑(c % (m : ℤ)) : ℝ) / (m : ℝ)) := by
  rw [circDist, Int.fract_div_intCast_eq_div_intCast_mod]

/-- **Bézout-position distances.**  At `x = α/vF` with `α·v3 ≡ 1 (mod vF)` and
    `gcd(α, vF) = 1`: runner `v3` sits at distance exactly `1/vF`, and runner `vE`
    (with `0<vE<vF`, `vE ≠ v3`, `vE+v3 ≠ vF`) sits at distance `≥ 2/vF` — the
    "twice fact", because `α·vE ≢ 0, ±1 (mod vF)`. -/
theorem bezout_distances (vF vE v3 : ℕ) (α : ℤ) (hvE0 : 0 < vE) (hvEF : vE < vF)
    (hv30 : 0 < v3) (hv3F : v3 < vF) (hEne3 : vE ≠ v3) (hsum : vE + v3 ≠ vF)
    (hcopα : IsCoprime (α : ℤ) (vF : ℤ)) (h1 : (α : ℤ) * v3 ≡ 1 [ZMOD vF]) :
    circDist ((v3 : ℝ) * ((α : ℝ) / (vF : ℝ))) = 1 / (vF : ℝ) ∧
      2 / (vF : ℝ) ≤ circDist ((vE : ℝ) * ((α : ℝ) / (vF : ℝ))) := by
  have hvF2 : 2 ≤ vF := by omega
  have hvF0 : 0 < vF := by omega
  have hvFR : (0 : ℝ) < (vF : ℝ) := by exact_mod_cast hvF0
  have hvFRne : (vF : ℝ) ≠ 0 := hvFR.ne'
  have hcopFα : IsCoprime (vF : ℤ) (α : ℤ) := hcopα.symm
  have h1vF : (1 : ℤ) % (vF : ℤ) = 1 := Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hvF2)
  -- runner v3 at exactly 1/vF
  have hc3mod : ((α : ℤ) * v3) % (vF : ℤ) = 1 := by
    have := h1; rw [Int.ModEq] at this; rw [this, h1vF]
  have hpos3 : (v3 : ℝ) * ((α : ℝ) / (vF : ℝ)) = ((α * (v3 : ℤ) : ℤ) : ℝ) / (vF : ℝ) := by
    push_cast; ring
  have h3 : circDist ((v3 : ℝ) * ((α : ℝ) / (vF : ℝ))) = 1 / (vF : ℝ) := by
    rw [hpos3, circDist_intCast_div, hc3mod]
    have hle : (1 : ℝ) / (vF : ℝ) ≤ 1 - 1 / (vF : ℝ) := by
      rw [le_sub_iff_add_le]
      have e : (1 : ℝ) / (vF : ℝ) + 1 / (vF : ℝ) = 2 / (vF : ℝ) := by ring
      rw [e, div_le_one hvFR]; exact_mod_cast hvF2
    simpa using min_eq_left hle
  refine ⟨h3, ?_⟩
  -- runner vE at ≥ 2/vF
  set ρ : ℤ := ((α : ℤ) * vE) % (vF : ℤ) with hρdef
  have hρ0 : 0 ≤ ρ := Int.emod_nonneg _ (by exact_mod_cast hvF0.ne')
  have hρlt : ρ < (vF : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hvF0)
  -- ρ ≠ 0
  have hρne0 : ρ ≠ 0 := by
    intro h
    have hdvd : (vF : ℤ) ∣ (α : ℤ) * vE := Int.dvd_of_emod_eq_zero (by rw [← hρdef, h])
    have hd : (vF : ℤ) ∣ (vE : ℤ) := hcopFα.dvd_of_dvd_mul_left hdvd
    exact not_dvd_of_natAbs_lt vF vE (by exact_mod_cast hvE0.ne') (by simpa using hvEF) hd
  -- ρ ≠ 1
  have hρne1 : ρ ≠ 1 := by
    intro h
    have hcong : (α : ℤ) * vE ≡ α * v3 [ZMOD vF] := by rw [Int.ModEq, ← hρdef, h, hc3mod]
    have hdvd : (vF : ℤ) ∣ ((α : ℤ) * v3 - α * vE) := (Int.modEq_iff_dvd).mp hcong
    have hdvd2 : (vF : ℤ) ∣ (α : ℤ) * ((v3 : ℤ) - vE) := by rw [mul_sub]; exact hdvd
    have hdvd3 : (vF : ℤ) ∣ ((v3 : ℤ) - vE) := hcopFα.dvd_of_dvd_mul_left hdvd2
    have hne : (v3 : ℤ) - vE ≠ 0 := by omega
    have hlt : ((v3 : ℤ) - vE).natAbs < vF := by omega
    exact not_dvd_of_natAbs_lt vF _ hne hlt hdvd3
  -- ρ ≠ vF - 1
  have hρneF : ρ ≠ (vF : ℤ) - 1 := by
    intro h
    have hz : ((α : ℤ) * vE + α * v3) % (vF : ℤ) = 0 := by
      rw [Int.add_emod, ← hρdef, h, hc3mod, show (vF : ℤ) - 1 + 1 = vF by ring, Int.emod_self]
    have hdvd : (vF : ℤ) ∣ ((α : ℤ) * vE + α * v3) := Int.dvd_of_emod_eq_zero hz
    have hdvd2 : (vF : ℤ) ∣ (α : ℤ) * ((vE : ℤ) + v3) := by rw [mul_add]; exact hdvd
    have hdvd3 : (vF : ℤ) ∣ ((vE : ℤ) + v3) := hcopFα.dvd_of_dvd_mul_left hdvd2
    have hdvd4 : (vF : ℤ) ∣ ((vE : ℤ) + v3 - vF) := dvd_sub hdvd3 (dvd_refl _)
    have hne : (vE : ℤ) + v3 - vF ≠ 0 := by omega
    have hlt : ((vE : ℤ) + v3 - vF).natAbs < vF := by omega
    exact not_dvd_of_natAbs_lt vF _ hne hlt hdvd4
  -- combine: 2 ≤ ρ ≤ vF - 2
  have hρ2 : 2 ≤ ρ := by omega
  have hρle : ρ ≤ (vF : ℤ) - 2 := by omega
  have hposE : (vE : ℝ) * ((α : ℝ) / (vF : ℝ)) = ((α * (vE : ℤ) : ℤ) : ℝ) / (vF : ℝ) := by
    push_cast; ring
  rw [hposE, circDist_intCast_div, ← hρdef]
  have hρR2 : (2 : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ2
  have hρRle : (ρ : ℝ) ≤ (vF : ℝ) - 2 := by
    have h2 : ((vF : ℝ) - 2) = (((vF : ℤ) - 2 : ℤ) : ℝ) := by push_cast; ring
    rw [h2]; exact_mod_cast hρle
  apply le_min
  · rw [div_le_iff₀ hvFR, div_mul_cancel₀ _ hvFRne]; exact hρR2
  · rw [le_sub_iff_add_le]
    have e : (2 : ℝ) / (vF : ℝ) + (ρ : ℝ) / (vF : ℝ) = (2 + ρ) / (vF : ℝ) := by ring
    rw [e, div_le_one hvFR]; linarith

open Finset in
/-- **Closing via Lemma 3 (`|D| = 1`).**  At time `t`: the unique ÷5 runner `e` is
    distant, the fastest runner `3` is at the origin, and the chosen runner `i3`
    is *not* distant.  Then `R₀ ⊇ {3, e}` (`|R₀| ≥ 2`) while `R₂` can contain only
    the fourth runner (`|R₂| ≤ 1`), so `lemma3` yields an all-distant time. -/
theorem close_via_lemma3 (speeds : Fin 4 → ℕ) (t : ℝ) (e i3 : Fin 4) (he : 5 ∣ speeds e)
    (hD1 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1)
    (he3 : e ≠ 3) (hi33 : i3 ≠ 3) (hi3e : i3 ≠ e)
    (hEdist : 1 / 5 ≤ circDist ((speeds e : ℝ) * t))
    (hForig : Int.fract ((speeds 3 : ℝ) * t) = 0)
    (h3notdist : circDist ((speeds i3 : ℝ) * t) < 1 / 5) :
    ∃ t' : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t') := by
  -- the ÷5 set is exactly {e}
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hD1
  have hea : e = a := by
    have : e ∈ ({a} : Finset (Fin 4)) := ha ▸ Finset.mem_filter.mpr ⟨mem_univ _, he⟩
    rwa [Finset.mem_singleton] at this
  have hDeq : univ.filter (fun i => 5 ∣ speeds i) = {e} := by rw [ha, hea]
  have hDdist : ∀ m, 5 ∣ speeds m → 1 / 5 ≤ circDist ((speeds m : ℝ) * t) := by
    intro m hm
    have hmem : m ∈ univ.filter (fun n => 5 ∣ speeds n) := mem_filter.mpr ⟨mem_univ _, hm⟩
    rw [hDeq, Finset.mem_singleton] at hmem; subst hmem; exact hEdist
  -- |R₂| ≤ 1 < 2 ≤ |R₀|
  have hcard : (univ.filter (fun i => ¬ 5 ∣ speeds i ∧
        ¬ offC2 (Int.fract ((speeds i : ℝ) * t)))).card
      < (univ.filter (fun i => 5 ∣ speeds i ∨ Int.fract ((speeds i : ℝ) * t) = 0)).card := by
    have h2le : 2 ≤ (univ.filter (fun i => 5 ∣ speeds i ∨
        Int.fract ((speeds i : ℝ) * t) = 0)).card := by
      have hsub : ({(3 : Fin 4), e} : Finset (Fin 4)) ⊆ univ.filter
          (fun i => 5 ∣ speeds i ∨ Int.fract ((speeds i : ℝ) * t) = 0) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact mem_filter.mpr ⟨mem_univ _, Or.inr hForig⟩
        · exact mem_filter.mpr ⟨mem_univ _, Or.inl he⟩
      have hc2 : ({(3 : Fin 4), e} : Finset (Fin 4)).card = 2 := by
        rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr he3.symm),
          Finset.card_singleton]
      rw [← hc2]; exact Finset.card_le_card hsub
    have h1le : (univ.filter (fun i => ¬ 5 ∣ speeds i ∧
        ¬ offC2 (Int.fract ((speeds i : ℝ) * t)))).card ≤ 1 := by
      have hsub : univ.filter (fun i => ¬ 5 ∣ speeds i ∧
            ¬ offC2 (Int.fract ((speeds i : ℝ) * t)))
          ⊆ univ \ {(3 : Fin 4), e, i3} := by
        intro x hx
        rw [mem_filter] at hx
        rw [Finset.mem_sdiff]
        refine ⟨mem_univ _, ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_, ?_⟩
        · rintro rfl
          exact hx.2.2 (by have h0 : offC2 (0 : ℝ) := Or.inl (by norm_num); rwa [← hForig] at h0)
        · rintro rfl; exact hx.2.1 he
        · rintro rfl; exact hx.2.2 (not_distant_offC2 _ h3notdist)
      have hc3 : (univ \ {(3 : Fin 4), e, i3} : Finset (Fin 4)).card = 1 := by
        have hs3 : ({(3 : Fin 4), e, i3} : Finset (Fin 4)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [he3.symm, hi33.symm]),
            Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hi3e.symm), Finset.card_singleton]
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hs3]
      rw [← hc3]; exact Finset.card_le_card hsub
    omega
  obtain ⟨jj, _, hall⟩ := lemma3 speeds t hDdist hcard
  exact ⟨t + (jj : ℝ) / 5, hall⟩

open Finset in
/-- **`|D| = 1`, sub-case B with `gcd(vF, v3) = 1`.**  Bézout gives `α·v3 ≡ 1
    (mod vF)`; at `x = α/vF` the fastest runner `3` is at the origin, `v3` at
    `1/vF < 1/5`, and `vE` at distance `≥ 2/vF`.  If `vE` is already distant we
    close; otherwise `doubling_step` doubles time until `vE` becomes distant while
    `v3` stays `< 1/5`.  Either way `close_via_lemma3` finishes. -/
theorem case_D1_B_gcd1 (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (e i3 : Fin 4) (he : 5 ∣ speeds e)
    (hD1 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1)
    (he3 : e ≠ 3) (hi33 : i3 ≠ 3) (hi3e : i3 ≠ e)
    (hsum : speeds e + speeds i3 ≠ speeds 3)
    (hcop : Nat.Coprime (speeds 3) (speeds i3)) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  have hvE0 : 0 < speeds e := hpos e
  have hv30 : 0 < speeds i3 := hpos i3
  have heV : e < (3 : Fin 4) := by
    have h2 : (e : ℕ) ≠ 3 := fun h => he3 (Fin.ext h)
    have h1 : (e : ℕ) < 4 := e.isLt
    omega
  have hi3V : i3 < (3 : Fin 4) := by
    have h2 : (i3 : ℕ) ≠ 3 := fun h => hi33 (Fin.ext h)
    have h1 : (i3 : ℕ) < 4 := i3.isLt
    omega
  have hvEF : speeds e < speeds 3 := hmono heV
  have hv3F : speeds i3 < speeds 3 := hmono hi3V
  have hvE5 : 5 ≤ speeds e := Nat.le_of_dvd hvE0 he
  have hvF6 : 6 ≤ speeds 3 := by omega
  have hEne3 : speeds e ≠ speeds i3 := hmono.injective.ne hi3e.symm
  have hvFR : (0 : ℝ) < (speeds 3 : ℝ) := by exact_mod_cast (by omega : 0 < speeds 3)
  have hvFRne : (speeds 3 : ℝ) ≠ 0 := hvFR.ne'
  have hvF6R : (6 : ℝ) ≤ (speeds 3 : ℝ) := by exact_mod_cast hvF6
  -- Bézout: α·v3 ≡ 1 (mod vF), gcd(α, vF) = 1
  have hcopZ : IsCoprime ((speeds i3 : ℕ) : ℤ) ((speeds 3 : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨a, b, hab⟩ := hcopZ
  have h1 : (a : ℤ) * (speeds i3) ≡ 1 [ZMOD (speeds 3)] := by
    rw [Int.modEq_iff_dvd]; exact ⟨b, by linear_combination -hab⟩
  have hcopα : IsCoprime (a : ℤ) ((speeds 3 : ℕ) : ℤ) :=
    ⟨speeds i3, b, by linear_combination hab⟩
  obtain ⟨h3eq, hEge⟩ := bezout_distances (speeds 3) (speeds e) (speeds i3) a hvE0 hvEF hv30 hv3F
    hEne3 hsum hcopα h1
  have hForig : Int.fract ((speeds 3 : ℝ) * ((a : ℝ) / (speeds 3 : ℝ))) = 0 := by
    rw [show (speeds 3 : ℝ) * ((a : ℝ) / (speeds 3 : ℝ)) = ((a : ℤ) : ℝ) from by field_simp]
    exact Int.fract_intCast a
  have h1vF5 : (1 : ℝ) / (speeds 3 : ℝ) < 1 / 5 := by
    rw [div_lt_iff₀ hvFR]; nlinarith [hvF6R]
  by_cases hEdist : 1 / 5 ≤ circDist ((speeds e : ℝ) * ((a : ℝ) / (speeds 3 : ℝ)))
  · exact close_via_lemma3 speeds ((a : ℝ) / (speeds 3 : ℝ)) e i3 he hD1 he3 hi33 hi3e hEdist
      hForig (by rw [h3eq]; exact h1vF5)
  · push_neg at hEdist
    have hδepos : 0 < circDist ((speeds e : ℝ) * ((a : ℝ) / (speeds 3 : ℝ))) :=
      lt_of_lt_of_le (div_pos (by norm_num) hvFR) hEge
    have hδ3half : circDist ((speeds i3 : ℝ) * ((a : ℝ) / (speeds 3 : ℝ)))
        ≤ circDist ((speeds e : ℝ) * ((a : ℝ) / (speeds 3 : ℝ))) / 2 := by
      rw [h3eq]
      have e2 : (2 : ℝ) / (speeds 3 : ℝ) = 2 * (1 / (speeds 3 : ℝ)) := by ring
      linarith [hEge, e2]
    obtain ⟨t', hFt', hEt', h3t'⟩ := doubling_step (speeds 3) (speeds e) (speeds i3)
      ((a : ℝ) / (speeds 3 : ℝ)) hForig hδepos hEdist hδ3half
    exact close_via_lemma3 speeds t' e i3 he hD1 he3 hi33 hi3e hEt' hFt' h3t'

/-- If `d ∣ v` (`d > 0`), then `v·(K/d)` is an integer, so `fract = 0`. -/
theorem fract_dvd_mul_div (v d : ℕ) (K : ℤ) (hd : 0 < d) (hdvd : d ∣ v) :
    Int.fract ((v : ℝ) * ((K : ℝ) / (d : ℝ))) = 0 := by
  obtain ⟨m, hm⟩ := hdvd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [show (v : ℝ) * ((K : ℝ) / (d : ℝ)) = (((m : ℤ) * K : ℤ) : ℝ) from by
    rw [hm]; push_cast; field_simp]
  exact Int.fract_intCast _

/-- If `d ∣ v` (`d > 0`), shifting time by `K/d` leaves runner `v`'s distance fixed. -/
theorem circDist_shift_dvd (v d : ℕ) (K : ℤ) (τ : ℝ) (hd : 0 < d) (hdvd : d ∣ v) :
    circDist ((v : ℝ) * (τ + (K : ℝ) / (d : ℝ))) = circDist ((v : ℝ) * τ) := by
  obtain ⟨m, hm⟩ := hdvd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [show (v : ℝ) * (τ + (K : ℝ) / (d : ℝ)) = (v : ℝ) * τ + (((m : ℤ) * K : ℤ) : ℝ) from by
    rw [hm]; push_cast; field_simp]
  exact circDist_add_intCast' _ _

open Finset in
/-- **`|D| = 1`, sub-case B, `gcd(vF, v3) = d > 1`, `d ∤ vE` (Bienia Cor 4).**  At
    `t = K/d` (chosen so `vE` is distant) runners `3` and `i3` (both ÷`d`) sit at
    the origin while `vE` is distant: `|R₀| ≥ 3`, so `close_via_lemma3` finishes. -/
theorem case_D1_B_gcd_ndvd (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (e i3 : Fin 4) (he : 5 ∣ speeds e)
    (hD1 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1)
    (he3 : e ≠ 3) (hi33 : i3 ≠ 3) (hi3e : i3 ≠ e)
    (d : ℕ) (hd2 : 2 ≤ d) (hdF : d ∣ speeds 3) (hd3 : d ∣ speeds i3) (hdE : ¬ d ∣ speeds e) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  have hdpos : 0 < d := by omega
  obtain ⟨K, hK⟩ := exists_step_distant_gen (speeds e) d hd2 hdE (1 / 5) (by norm_num)
    (by norm_num) 0
  refine close_via_lemma3 speeds ((K : ℝ) / (d : ℝ)) e i3 he hD1 he3 hi33 hi3e ?_ ?_ ?_
  · have h := hK; rwa [zero_add, mul_div_assoc] at h
  · exact fract_dvd_mul_div (speeds 3) d K hdpos hdF
  · have h3z : circDist ((speeds i3 : ℝ) * ((K : ℝ) / (d : ℝ))) = 0 := by
      rw [circDist, fract_dvd_mul_div (speeds i3) d K hdpos hd3]; simp
    rw [h3z]; norm_num

/-- **`|D| = 1`, sub-case B, `gcd(vF, v3) = d > 1`, `d ∣ vE` (Bienia pre-jump 2).**
    Then `d ∣ vF, vE, v3` but `d ∤ v₄`: `three_runner_fifth` makes `{vF, vE, v3}`
    distant at `τ`, then a `+K/d` pre-jump lands the fourth runner distant while
    leaving the first three fixed. -/
theorem case_D1_B_gcd_dvd (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (e i3 i4 : Fin 4) (he3 : e ≠ 3) (hi33 : i3 ≠ 3) (hi3e : i3 ≠ e)
    (hi43 : i4 ≠ 3) (hi4e : i4 ≠ e) (hi4i3 : i4 ≠ i3)
    (d : ℕ) (hd2 : 2 ≤ d) (hdF : d ∣ speeds 3) (hd3 : d ∣ speeds i3) (hdE : d ∣ speeds e)
    (hd4 : ¬ d ∣ speeds i4) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  have hdpos : 0 < d := by omega
  obtain ⟨τ, dF, dE, d3⟩ := three_runner_fifth (speeds 3) (speeds e) (speeds i3)
    (hpos 3) (hpos e) (hpos i3) (hmono.injective.ne he3.symm) (hmono.injective.ne hi33.symm)
    (hmono.injective.ne hi3e.symm)
  obtain ⟨K, hK⟩ := exists_step_distant_gen (speeds i4) d hd2 hd4 (1 / 5) (by norm_num)
    (by norm_num) ((speeds i4 : ℝ) * τ)
  refine ⟨τ + (K : ℝ) / (d : ℝ), ?_⟩
  intro i
  have hall4 : ({(3 : Fin 4), e, i3, i4} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [he3.symm, hi33.symm, hi43.symm]),
      Finset.card_insert_of_notMem (by simp [hi3e.symm, hi4e.symm]),
      Finset.card_insert_of_notMem (by simp [hi4i3.symm]), Finset.card_singleton,
      Fintype.card_fin]
  have hi : i ∈ ({(3 : Fin 4), e, i3, i4} : Finset (Fin 4)) := hall4 ▸ Finset.mem_univ i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with h | h | h | h
  · rw [h, circDist_shift_dvd (speeds 3) d K τ hdpos hdF]; exact dF
  · rw [h, circDist_shift_dvd (speeds e) d K τ hdpos hdE]; exact dE
  · rw [h, circDist_shift_dvd (speeds i3) d K τ hdpos hd3]; exact d3
  · rw [h, show (speeds i4 : ℝ) * (τ + (K : ℝ) / (d : ℝ))
        = (speeds i4 : ℝ) * τ + (speeds i4 : ℝ) * (K : ℝ) / (d : ℝ) from by ring]
    exact hK

open Finset in
/-- **`|D| = 1`, easy sub-case:** the divisible-by-5 runner is the fastest.
    Then `t = 1/(5·v₃)` puts it at exactly `1/5` (distant) and every slower runner
    in `(0,1/5) ⊆ C₁`, so `R₂ = ∅` and `lemma3` finishes. -/
theorem case_D1_A (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hD1 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1) (h3 : 5 ∣ speeds (3 : Fin 4)) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hD1
  have h3a : (3 : Fin 4) = a := by
    have : (3 : Fin 4) ∈ ({a} : Finset (Fin 4)) :=
      ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩
    rwa [Finset.mem_singleton] at this
  have hDeq : univ.filter (fun i => 5 ∣ speeds i) = {(3 : Fin 4)} := by rw [ha, h3a]
  have hpos3 : (0 : ℝ) < (speeds 3 : ℝ) := by exact_mod_cast hpos 3
  set t : ℝ := 1 / (5 * (speeds (3 : Fin 4) : ℝ)) with ht
  have hc15 : circDist ((1 : ℝ) / 5) = 1 / 5 := by
    unfold circDist
    rw [Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩, min_eq_left (by norm_num)]
  have hdist3 : 1 / 5 ≤ circDist ((speeds 3 : ℝ) * t) := by
    have hv : (speeds 3 : ℝ) * t = 1 / 5 := by rw [ht]; field_simp
    rw [hv, hc15]
  have hDdist : ∀ m, 5 ∣ speeds m → 1 / 5 ≤ circDist ((speeds m : ℝ) * t) := by
    intro m hm
    have hmem : m ∈ univ.filter (fun i => 5 ∣ speeds i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    rw [hDeq, Finset.mem_singleton] at hmem
    subst hmem; exact hdist3
  have hcard : (univ.filter (fun n => ¬ 5 ∣ speeds n ∧
        ¬ offC2 (Int.fract ((speeds n : ℝ) * t)))).card
      < (univ.filter (fun n => 5 ∣ speeds n ∨ Int.fract ((speeds n : ℝ) * t) = 0)).card := by
    have hR2 : univ.filter (fun n => ¬ 5 ∣ speeds n ∧
        ¬ offC2 (Int.fract ((speeds n : ℝ) * t))) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro n _
      simp only [not_and_or, not_not]
      by_cases hn5 : 5 ∣ speeds n
      · exact Or.inl hn5
      · right
        have hn3 : n ≠ 3 := fun h => hn5 (h ▸ h3)
        have hlt : speeds n < speeds 3 :=
          hmono (Fin.lt_def.mpr (by have := n.isLt; have := Fin.val_ne_of_ne hn3; omega))
        have hltR : (speeds n : ℝ) < (speeds 3 : ℝ) := by exact_mod_cast hlt
        have hval : (speeds n : ℝ) * t = (speeds n : ℝ) / (5 * (speeds 3 : ℝ)) := by rw [ht]; ring
        have hle : (speeds n : ℝ) / (5 * (speeds 3 : ℝ)) ≤ 1 / 5 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        have hfr : Int.fract ((speeds n : ℝ) * t) = (speeds n : ℝ) / (5 * (speeds 3 : ℝ)) := by
          rw [hval, Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩]
        rw [hfr]; exact Or.inl hle
    rw [hR2, Finset.card_empty]
    exact Finset.card_pos.mpr ⟨3, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h3⟩⟩
  obtain ⟨jj, _, hall⟩ := lemma3 speeds t hDdist hcard
  exact ⟨t + (jj : ℝ) / 5, hall⟩

open Finset in
/-- **`|D| = 1`, sub-case B, gcd dispatch.**  With the third runner `i3` fixed
    (`v3 ≠ vF − vE`), split on `d = gcd(vF, v3)`: `d = 1` → `case_D1_B_gcd1`;
    `d > 1 ∧ d ∣ vE` → `case_D1_B_gcd_dvd`; `d > 1 ∧ d ∤ vE` → `case_D1_B_gcd_ndvd`. -/
theorem case_D1_B_dispatch (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (e i3 i4 : Fin 4) (he : 5 ∣ speeds e)
    (hD1 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1) (hgcd : Finset.gcd univ speeds = 1)
    (he3 : e ≠ 3) (hi33 : i3 ≠ 3) (hi3e : i3 ≠ e)
    (hi43 : i4 ≠ 3) (hi4e : i4 ≠ e) (hi4i3 : i4 ≠ i3)
    (hsum : speeds e + speeds i3 ≠ speeds 3) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  by_cases hcop : Nat.Coprime (speeds 3) (speeds i3)
  · exact case_D1_B_gcd1 speeds hmono hpos e i3 he hD1 he3 hi33 hi3e hsum hcop
  · have hdpos : 0 < Nat.gcd (speeds 3) (speeds i3) := Nat.gcd_pos_iff.mpr (Or.inl (hpos 3))
    have hd2 : 2 ≤ Nat.gcd (speeds 3) (speeds i3) := by
      have hne1 : Nat.gcd (speeds 3) (speeds i3) ≠ 1 := hcop
      omega
    set d := Nat.gcd (speeds 3) (speeds i3) with hd_def
    have hdF : d ∣ speeds 3 := Nat.gcd_dvd_left _ _
    have hd3 : d ∣ speeds i3 := Nat.gcd_dvd_right _ _
    by_cases hdE : d ∣ speeds e
    · have hd4 : ¬ d ∣ speeds i4 := by
        intro hcon
        have hall4 : ({(3 : Fin 4), e, i3, i4} : Finset (Fin 4)) = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [Finset.card_insert_of_notMem (by simp [he3.symm, hi33.symm, hi43.symm]),
            Finset.card_insert_of_notMem (by simp [hi3e.symm, hi4e.symm]),
            Finset.card_insert_of_notMem (by simp [hi4i3.symm]), Finset.card_singleton,
            Fintype.card_fin]
        have hdall : ∀ i ∈ (univ : Finset (Fin 4)), d ∣ speeds i := by
          intro i _
          have hmem : i ∈ ({(3 : Fin 4), e, i3, i4} : Finset (Fin 4)) := hall4 ▸ mem_univ i
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h | h <;> rw [h]
          exacts [hdF, hdE, hd3, hcon]
        have hd1 : d ∣ Finset.gcd univ speeds := Finset.dvd_gcd hdall
        rw [hgcd] at hd1
        exact absurd (Nat.le_of_dvd one_pos hd1) (by omega)
      exact case_D1_B_gcd_dvd speeds hmono hpos e i3 i4 he3 hi33 hi3e hi43 hi4e hi4i3 d hd2 hdF hd3
        hdE hd4
    · exact case_D1_B_gcd_ndvd speeds hmono hpos e i3 he hD1 he3 hi33 hi3e d hd2 hdF hd3 hdE

open Finset in
/-- **`|D| = 1`, sub-case B, pick the third runner.**  Of the two non-fastest,
    non-÷5 runners `p, q`, at least one has speed `≠ vF − vE` (they have distinct
    speeds); use it as `i3` and dispatch on `gcd(vF, v3)`. -/
theorem case_D1_B_pick (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (e p q : Fin 4) (he : 5 ∣ speeds e)
    (hD1 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1) (hgcd : Finset.gcd univ speeds = 1)
    (he3 : e ≠ 3) (hp3 : p ≠ 3) (hpe : p ≠ e) (hq3 : q ≠ 3) (hqe : q ≠ e) (hpq : p ≠ q) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  by_cases hbad : speeds p = speeds 3 - speeds e
  · have hsum : speeds e + speeds q ≠ speeds 3 := by
      intro hcon
      have hqv : speeds q = speeds 3 - speeds e := by omega
      rw [← hbad] at hqv
      exact (hmono.injective.ne hpq.symm) hqv
    exact case_D1_B_dispatch speeds hmono hpos e q p he hD1 hgcd he3 hq3 hqe hp3 hpe hpq hsum
  · have hsum : speeds e + speeds p ≠ speeds 3 := fun hcon => hbad (by omega)
    exact case_D1_B_dispatch speeds hmono hpos e p q he hD1 hgcd he3 hp3 hpe hq3 hqe hpq.symm hsum

open Finset in
/-- **`|D| = 1` case.**  Sub-case A (÷5 runner fastest) is `case_D1_A`; sub-case B
    (÷5 runner not fastest) is Bienia's doubling argument (`case_D1_B_pick`). -/
theorem case_D1 (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hgcd : Finset.gcd Finset.univ speeds = 1)
    (hD1 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  by_cases h3 : 5 ∣ speeds (3 : Fin 4)
  · exact case_D1_A speeds hmono hpos hD1 h3
  · obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hD1
    have he : 5 ∣ speeds e := by
      have hmem : e ∈ univ.filter (fun i => 5 ∣ speeds i) := he_eq ▸ Finset.mem_singleton_self e
      exact (Finset.mem_filter.mp hmem).2
    have he3 : e ≠ 3 := fun h => h3 (h ▸ he)
    fin_cases e
    · exact case_D1_B_pick speeds hmono hpos 0 1 2 he hD1 hgcd he3 (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact case_D1_B_pick speeds hmono hpos 1 0 2 he hD1 hgcd he3 (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact case_D1_B_pick speeds hmono hpos 2 0 1 he hD1 hgcd he3 (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact absurd he h3

open Finset in
/-- **Residual assembly.**  Sorted positive `gcd = 1` speeds with at least one
    divisible by 5.  `|D| ∈ {1,2,3}`; `|D| = 2,3` close via `case_D2`/`case_D3`,
    `|D| = 1` via `case_D1`. -/
theorem intLRC_five_residual (speeds : Fin 4 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.gcd univ speeds = 1) (hex : ∃ i, 5 ∣ speeds i) :
    ∃ t : ℝ, ∀ i, 1 / 5 ≤ circDist ((speeds i : ℝ) * t) := by
  have hDpos : 1 ≤ (univ.filter (fun i => 5 ∣ speeds i)).card := by
    obtain ⟨i, hi⟩ := hex
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hDlt : (univ.filter (fun i => 5 ∣ speeds i)).card < 4 := by
    have hle : (univ.filter (fun i => 5 ∣ speeds i)).card ≤ 4 := by simpa using Finset.card_le_univ _
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hDu : univ.filter (fun i => 5 ∣ speeds i) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [h, Fintype.card_fin])
      have h5all : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 5 ∣ speeds i := by
        intro i _
        have hi : i ∈ univ.filter (fun i => 5 ∣ speeds i) := by rw [hDu]; exact Finset.mem_univ i
        exact (Finset.mem_filter.mp hi).2
      have hd5 : (5 : ℕ) ∣ Finset.gcd Finset.univ speeds := Finset.dvd_gcd h5all
      rw [hgcd] at hd5
      exact absurd hd5 (by decide)
  have h123 : (univ.filter (fun i => 5 ∣ speeds i)).card = 1 ∨
      (univ.filter (fun i => 5 ∣ speeds i)).card = 2 ∨
      (univ.filter (fun i => 5 ∣ speeds i)).card = 3 := by omega
  rcases h123 with hc | hc | hc
  · exact case_D1 speeds hmono hpos hgcd hc
  · exact case_D2 speeds hmono hpos hc
  · exact case_D3 speeds hmono hpos hc
