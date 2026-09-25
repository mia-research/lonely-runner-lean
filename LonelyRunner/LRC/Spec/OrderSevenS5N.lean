import LonelyRunner.LRC.Spec.OrderSevenFilterN
import LonelyRunner.LRC.Spec.OrderSevenA4N

/-!
# n = 7 (Barajas–Serra) — §5 integer assembly

Bridges the abstract §5 case lemmas (over `ZMod 7`) to integer band conditions.
The `qz`-sequence `Q j i = qz m (j · d_i)` satisfies the carry recurrence; the
Λ₀ shift `(1 + k · 7^m)` converts abstract `t ∈ ZMod 7` to integer multiplier.
-/

open Finset

namespace LRC.OrderSevenN

/-! ### Carry recurrence: `qz` → `carryStep` format -/

theorem cast_succ_mul (j : ℕ) (x : ℤ) :
    ((j + 1 : ℕ) : ℤ) * x = (j : ℤ) * x + x := by push_cast; ring

/-- The `qz`-sequence `j ↦ qz m (j · x)` satisfies the `carryStep` recurrence
for `Fin 4`, i.e. the hypotheses of `case1_compresses`. -/
theorem qz_carries4 (m : ℕ) (d : Fin 4 → ℤ) :
    let a := fun i => qz m (d i)
    let Q := fun (j : ℕ) (i : Fin 4) => qz m ((j : ℤ) * d i)
    Q 1 = a ∧ ∀ j, 1 ≤ j →
      ∃ b : Fin 4 → Bool, Q (j + 1) = carryStep a b (Q j) := by
  refine ⟨by funext i; simp, fun j _ => ?_⟩
  classical
  have key : ∀ i, ∃ b : Bool,
      qz m ((j : ℤ) * d i + d i) =
      qz m ((j : ℤ) * d i) + qz m (d i) + if b then (1 : ZMod 7) else 0 := by
    intro i
    rcases qz_add_carry m ((j : ℤ) * d i) (d i) with h | h
    · exact ⟨false, by simp [h]⟩
    · exact ⟨true, by simp [h]⟩
  choose bits hbits using key
  exact ⟨bits, by funext i; show qz m (((j + 1 : ℕ) : ℤ) * d i) = _
                  rw [cast_succ_mul]; exact hbits i⟩

/-- Carry recurrence for `Fin 3` (used by `case2_avoids`). -/
theorem qz_carries3 (m : ℕ) (d : Fin 3 → ℤ) :
    let a := fun i => qz m (d i)
    let Q := fun (j : ℕ) (i : Fin 3) => qz m ((j : ℤ) * d i)
    Q 1 = a ∧ ∀ j, 1 ≤ j →
      ∃ b : Fin 3 → Bool, Q (j + 1) = carryStep3 a b (Q j) := by
  refine ⟨by funext i; simp, fun j _ => ?_⟩
  classical
  have key : ∀ i, ∃ b : Bool,
      qz m ((j : ℤ) * d i + d i) =
      qz m ((j : ℤ) * d i) + qz m (d i) + if b then (1 : ZMod 7) else 0 := by
    intro i
    rcases qz_add_carry m ((j : ℤ) * d i) (d i) with h | h
    · exact ⟨false, by simp [h]⟩
    · exact ⟨true, by simp [h]⟩
  choose bits hbits using key
  exact ⟨bits, by funext i; show qz m (((j + 1 : ℕ) : ℤ) * d i) = _
                  rw [cast_succ_mul]; exact hbits i⟩

/-- Additive carry for `Fin 2` (used by `case3_avoids`). -/
theorem qz_hadd2 (m : ℕ) (d : Fin 2 → ℤ) :
    let Q := fun (j : ℕ) (i : Fin 2) => qz m ((j : ℤ) * d i)
    ∀ j k, 1 ≤ j → 1 ≤ k → ∀ i,
      Q (j + k) i = Q j i + Q k i ∨ Q (j + k) i = Q j i + Q k i + 1 := by
  intro Q j k _ _ i; exact qz_seq_hadd m (d i) j k

/-! ### Multiplier unit check -/

/-- `(1 + k · 7^m) · j` is coprime to 7 when `m ≥ 1` and `1 ≤ j ≤ 5`. -/
theorem lam_unit (m : ℕ) (hm : 0 < m) (k : ℤ) (j : ℕ) (hj1 : 1 ≤ j) (hj5 : j ≤ 5) :
    ¬ (7 : ℤ) ∣ (1 + k * 7 ^ m) * (j : ℤ) := by
  intro hdvd
  have hp : Prime (7 : ℤ) := seven_totient_full_int
  rcases hp.dvd_or_dvd hdvd with h1 | h2
  · obtain ⟨c, hc⟩ := h1
    obtain ⟨e, he⟩ := dvd_mul_of_dvd_right (dvd_pow_self (7 : ℤ) (by omega : m ≠ 0)) k
    have : (1 : ℤ) = 7 * (c - e) := by linarith
    omega
  · have : (j : ℤ) % 7 = 0 := Int.emod_eq_zero_of_dvd h2
    omega

/-- The multiplier `(1+k·7^m)·j` avoids `{0,6}` as a `ZMod 7` value:
`(1+k·7^m : ZMod 7) = 1` (for `m ≥ 1`), so `(lam : ZMod 7) = (j : ZMod 7) ∈ {1,...,5}`. -/
theorem lam_avoids06 (m : ℕ) (hm : 0 < m) (k : ℤ) (j : ℕ) (hj1 : 1 ≤ j) (hj5 : j ≤ 5) :
    avoids06 (((1 + k * 7 ^ m) * (j : ℤ) : ℤ) : ZMod 7) := by
  have hlam : (((1 + k * 7 ^ m) * (j : ℤ) : ℤ) : ZMod 7) = (j : ZMod 7) := by
    have : ((7 : ℤ) : ZMod 7) = 0 := by decide
    push_cast
    rw [show (7 : ZMod 7) ^ m = 0 from by rw [show (7 : ZMod 7) = 0 from by decide]; exact zero_pow (by omega)]
    ring
  rw [hlam]
  refine ⟨?_, ?_⟩
  · rw [Ne, ZMod.natCast_eq_zero_iff]; omega
  · have key : ∀ n : ℕ, 1 ≤ n → n ≤ 5 → (n : ZMod 7) ≠ 6 := by decide
    exact key j hj1 hj5

/-! ### Band symmetry under negation -/

/-- The central residue band is symmetric: `band(x) ⟺ band(-x)`. -/
theorem band_neg (m : ℕ) (x : ℤ) :
    ((7 ^ m : ℤ) ≤ x % 7 ^ (m + 1) ∧ x % 7 ^ (m + 1) ≤ 6 * 7 ^ m) ↔
    ((7 ^ m : ℤ) ≤ (-x) % 7 ^ (m + 1) ∧ (-x) % 7 ^ (m + 1) ≤ 6 * 7 ^ m) := by
  set N := (7 : ℤ) ^ (m + 1) with hN_def
  have hN : 0 < N := by positivity
  have hNne : N ≠ 0 := ne_of_gt hN
  have hN7 : N = 7 * 7 ^ m := by ring
  set R := x % N; set R' := (-x) % N
  have hR0 : 0 ≤ R := Int.emod_nonneg x hNne
  have hRN : R < N := Int.emod_lt_of_pos x hN
  have hR'0 : 0 ≤ R' := Int.emod_nonneg (-x) hNne
  have hR'N : R' < N := Int.emod_lt_of_pos (-x) hN
  have hmod0 : (R + R') % N = 0 := by
    show (x % N + (-x) % N) % N = 0
    rw [← Int.add_emod, Int.add_right_neg, Int.zero_emod]
  have hdvd : N ∣ R + R' := Int.dvd_of_emod_eq_zero hmod0
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : 0 ≤ c := by nlinarith
  have hc1 : c ≤ 1 := by nlinarith
  rcases eq_or_lt_of_le hc0 with hc_zero | hc_pos
  · -- c = 0: R = R' = 0, both sides fail
    have hR_z : R = 0 := by nlinarith
    have hR'_z : R' = 0 := by nlinarith
    simp only [hR_z, hR'_z]
  · -- c = 1: R' = N - R
    have hc1' : c = 1 := by omega
    have hR'eq : R' = N - R := by subst hc1'; linarith
    rw [hR'eq, hN7]; constructor
    · intro ⟨hlo, hhi⟩; exact ⟨by nlinarith, by nlinarith⟩
    · intro ⟨hlo, hhi⟩; exact ⟨by nlinarith, by nlinarith⟩

/-- The multiplier `(1+k·7^m)·j` satisfies `7^m ∣ (lam - j)`. Trivially: the
difference is `k·j·7^m`. This structural property is needed for the interior
element band proof (BS eq 8). -/
theorem lam_congr (m : ℕ) (k : ℤ) (j : ℕ) :
    (7 : ℤ) ^ m ∣ ((1 + k * 7 ^ m) * (j : ℤ) - (j : ℤ)) := ⟨k * j, by ring⟩

/-! ### §5 core: Case 1 (same residue) integer assembly -/

/-- **§5 Case 1 integer assembly.** Four integers not divisible by 7, all with the
same `ZMod 7` residue, admit a multiplier `lam` (coprime to 7) with
`qz m (lam · d_i)` avoiding `{0, 6}`.

Proof: `case1_compresses` → `avoidance_of_fitsWindow5` → `qz_shift0`. -/
theorem case1_int_avoid (m : ℕ) (hm : 0 < m) (d : Fin 4 → ℤ)
    (hnotdvd : ∀ i, ¬ (7 : ℤ) ∣ d i)
    (hsame : ∀ i, (d i : ZMod 7) = (d 0 : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ avoids06 ((lam : ℤ) : ZMod 7) ∧
      (∃ j_step : ℕ, 1 ≤ j_step ∧ j_step ≤ 5 ∧ (7 : ℤ) ^ m ∣ (lam - j_step)) ∧
      ∀ i, avoids06 (qz m (lam * d i)) := by
  classical
  set a : Fin 4 → ZMod 7 := fun i => qz m (d i)
  set Q : ℕ → Fin 4 → ZMod 7 := fun j i => qz m ((j : ℤ) * d i)
  obtain ⟨hQ1, hstep⟩ := qz_carries4 m d
  obtain ⟨j, hj1, hj5, hwin⟩ := case1_compresses a Q hQ1 hstep
  obtain ⟨t, ht⟩ := avoidance_of_fitsWindow5 (Q j) hwin
  -- slope = j · s where s = (d 0 : ZMod 7) is the common residue
  set s : ZMod 7 := (d 0 : ZMod 7)
  have hs_ne : s ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hnotdvd 0
  have hj_ne : (j : ZMod 7) ≠ 0 := by
    rw [Ne]; intro h
    have := (ZMod.natCast_eq_zero_iff j 7).mp h
    interval_cases j <;> omega
  set slope : ZMod 7 := (j : ZMod 7) * s
  have hslope_ne : slope ≠ 0 := mul_ne_zero hj_ne hs_ne
  -- k = t · slope⁻¹ so that k · slope = t
  set k : ZMod 7 := t * slope⁻¹
  have hkt : k * slope = t := by
    show t * slope⁻¹ * slope = t
    rw [mul_assoc, inv_mul_cancel₀ hslope_ne, mul_one]
  -- integer lift
  set k_int : ℤ := (k.val : ℤ)
  set lam : ℤ := (1 + k_int * 7 ^ m) * (j : ℤ)
  refine ⟨lam, lam_unit m hm k_int j hj1 hj5, lam_avoids06 m hm k_int j hj1 hj5,
    ⟨j, hj1, hj5, lam_congr m k_int j⟩, fun i => ?_⟩
  -- qz m (lam * d i) = Q j i + t
  have hrw : lam * d i = (1 + k_int * 7 ^ m) * ((j : ℤ) * d i) := by ring
  rw [hrw, qz_shift0]
  -- cast k_int back to ZMod 7
  have hk_cast : ((k_int : ℤ) : ZMod 7) = k :=
    show ((k.val : ℕ) : ZMod 7) = k from ZMod.natCast_rightInverse k
  -- (j · d i : ZMod 7) = slope (same residue)
  have hslope_i : (((j : ℤ) * d i : ℤ) : ZMod 7) = slope := by
    show ((j : ℤ) * d i : ℤ) = (j : ZMod 7) * s
    push_cast; congr 1; exact_mod_cast hsame i
  rw [hk_cast, hslope_i, hkt]
  exact ht i

/-! ### §5 Case 2 integer assembly (3 same + 1 extra) -/

/-- **§5 Case 2 integer assembly.** Three elements with the same residue `s` plus
one extra with coefficient `c = r_extra · s⁻¹ ∈ {2,4}`. -/
theorem case2_int_avoid (m : ℕ) (hm : 0 < m)
    (d_s : Fin 3 → ℤ) (d_e : ℤ)
    (hnd_s : ∀ i, ¬ (7 : ℤ) ∣ d_s i) (hnd_e : ¬ (7 : ℤ) ∣ d_e)
    (hsame : ∀ i, (d_s i : ZMod 7) = (d_s 0 : ZMod 7))
    (hc : (d_e : ZMod 7) * ((d_s 0 : ZMod 7))⁻¹ = 2 ∨
           (d_e : ZMod 7) * ((d_s 0 : ZMod 7))⁻¹ = 4) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ avoids06 ((lam : ℤ) : ZMod 7) ∧
      (∃ j_step : ℕ, 1 ≤ j_step ∧ j_step ≤ 5 ∧ (7 : ℤ) ^ m ∣ (lam - j_step)) ∧
      (∀ i, avoids06 (qz m (lam * d_s i))) ∧
      avoids06 (qz m (lam * d_e)) := by
  classical
  set a := fun i => qz m (d_s i)
  set Q : ℕ → Fin 3 → ZMod 7 := fun j i => qz m ((j : ℤ) * d_s i)
  set B : ℕ → ZMod 7 := fun j => qz m ((j : ℤ) * d_e)
  obtain ⟨hQ1, hstep⟩ := qz_carries3 m d_s
  set s : ZMod 7 := (d_s 0 : ZMod 7)
  have hs_ne : s ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hnd_s 0
  set c : ZMod 7 := (d_e : ZMod 7) * s⁻¹
  obtain ⟨j, hj1, hj3, t, ht_s, ht_e⟩ := case2_avoids a Q hQ1 hstep B c hc
  have hj5 : j ≤ 5 := by omega
  have hj_ne : (j : ZMod 7) ≠ 0 := by
    rw [Ne]; intro h; have := (ZMod.natCast_eq_zero_iff j 7).mp h
    interval_cases j <;> omega
  set slope : ZMod 7 := (j : ZMod 7) * s
  have hslope_ne : slope ≠ 0 := mul_ne_zero hj_ne hs_ne
  set k : ZMod 7 := t * slope⁻¹
  have hkt : k * slope = t := by
    show t * slope⁻¹ * slope = t
    rw [mul_assoc, inv_mul_cancel₀ hslope_ne, mul_one]
  set k_int : ℤ := (k.val : ℤ)
  set lam : ℤ := (1 + k_int * 7 ^ m) * (j : ℤ)
  have hk_cast : ((k_int : ℤ) : ZMod 7) = k :=
    show ((k.val : ℕ) : ZMod 7) = k from ZMod.natCast_rightInverse k
  refine ⟨lam, lam_unit m hm k_int j hj1 hj5, lam_avoids06 m hm k_int j hj1 hj5,
    ⟨j, hj1, hj5, lam_congr m k_int j⟩, fun i => ?_, ?_⟩
  · -- A_s element
    have hrw : lam * d_s i = (1 + k_int * 7 ^ m) * ((j : ℤ) * d_s i) := by ring
    rw [hrw, qz_shift0, hk_cast]
    have : (((j : ℤ) * d_s i : ℤ) : ZMod 7) = slope := by
      push_cast; congr 1; exact_mod_cast hsame i
    rw [this, hkt]; exact ht_s i
  · -- extra element
    have hrw : lam * d_e = (1 + k_int * 7 ^ m) * ((j : ℤ) * d_e) := by ring
    rw [hrw, qz_shift0, hk_cast]
    -- shift = k · (j · d_e : ZMod 7) = k · j · (c · s) = (k · slope) · c = t · c = c * t
    have hre : (((j : ℤ) * d_e : ℤ) : ZMod 7) = (j : ZMod 7) * ((d_e : ZMod 7)) := by push_cast; ring
    have hcs : (d_e : ZMod 7) = c * s := by
      rw [show c = (d_e : ZMod 7) * s⁻¹ from rfl, mul_assoc, inv_mul_cancel₀ hs_ne, mul_one]
    rw [hre, hcs, show (j : ZMod 7) * (c * s) = c * slope from by ring,
      show k * (c * slope) = c * (k * slope) from by ring, hkt]
    exact ht_e

/-! ### §5 Case 3 integer assembly (2 same + 2 extras) -/

/-- **§5 Case 3 integer assembly.** Two elements with the same residue `s` plus
two extras with coefficients `(c₁,c₂) ∈ {(2,2),(2,4),(4,2)}`. -/
theorem case3_int_avoid (m : ℕ) (hm : 0 < m)
    (d_s : Fin 2 → ℤ) (d_e1 d_e2 : ℤ)
    (hnd_s : ∀ i, ¬ (7 : ℤ) ∣ d_s i) (hnd_e1 : ¬ (7 : ℤ) ∣ d_e1) (hnd_e2 : ¬ (7 : ℤ) ∣ d_e2)
    (hsame : ∀ i, (d_s i : ZMod 7) = (d_s 0 : ZMod 7))
    (hcfg : let c1 := (d_e1 : ZMod 7) * ((d_s 0 : ZMod 7))⁻¹
            let c2 := (d_e2 : ZMod 7) * ((d_s 0 : ZMod 7))⁻¹
            (c1 = 2 ∧ c2 = 2) ∨ (c1 = 2 ∧ c2 = 4) ∨ (c1 = 4 ∧ c2 = 2)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ avoids06 ((lam : ℤ) : ZMod 7) ∧
      (∃ j_step : ℕ, 1 ≤ j_step ∧ j_step ≤ 5 ∧ (7 : ℤ) ^ m ∣ (lam - j_step)) ∧
      (∀ i, avoids06 (qz m (lam * d_s i))) ∧
      avoids06 (qz m (lam * d_e1)) ∧ avoids06 (qz m (lam * d_e2)) := by
  classical
  set Q : ℕ → Fin 2 → ZMod 7 := fun j i => qz m ((j : ℤ) * d_s i)
  set B1 : ℕ → ZMod 7 := fun j => qz m ((j : ℤ) * d_e1)
  set B2 : ℕ → ZMod 7 := fun j => qz m ((j : ℤ) * d_e2)
  set s : ZMod 7 := (d_s 0 : ZMod 7)
  have hs_ne : s ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hnd_s 0
  set c1 : ZMod 7 := (d_e1 : ZMod 7) * s⁻¹
  set c2 : ZMod 7 := (d_e2 : ZMod 7) * s⁻¹
  have hQ1 : Q 1 = fun i => qz m (d_s i) := by funext i; show qz m ((1 : ℤ) * _) = _; simp
  have hhadd := qz_hadd2 m d_s
  obtain ⟨j, hj1, hj5, t, ht_s, ht_e1, ht_e2⟩ :=
    case3_avoids (fun i => qz m (d_s i)) Q hQ1 hhadd B1 B2 c1 c2 hcfg
  have hj5' : j ≤ 5 := by omega
  have hj_ne : (j : ZMod 7) ≠ 0 := by
    rw [Ne]; intro h; have := (ZMod.natCast_eq_zero_iff j 7).mp h
    interval_cases j <;> omega
  set slope : ZMod 7 := (j : ZMod 7) * s
  have hslope_ne : slope ≠ 0 := mul_ne_zero hj_ne hs_ne
  set k : ZMod 7 := t * slope⁻¹
  have hkt : k * slope = t := by
    show t * slope⁻¹ * slope = t
    rw [mul_assoc, inv_mul_cancel₀ hslope_ne, mul_one]
  set k_int : ℤ := (k.val : ℤ)
  set lam : ℤ := (1 + k_int * 7 ^ m) * (j : ℤ)
  have hk_cast : ((k_int : ℤ) : ZMod 7) = k :=
    show ((k.val : ℕ) : ZMod 7) = k from ZMod.natCast_rightInverse k
  -- helper for extras: k · (j · d_e : ZMod 7) = c · t
  have extra_shift (d_ex : ℤ) (cx : ZMod 7) (hcx : cx = (d_ex : ZMod 7) * s⁻¹) :
      k * (((j : ℤ) * d_ex : ℤ) : ZMod 7) = cx * t := by
    have hcast : (((j : ℤ) * d_ex : ℤ) : ZMod 7) = (j : ZMod 7) * (d_ex : ZMod 7) := by
      push_cast; ring
    have hde : (d_ex : ZMod 7) = cx * s := by
      rw [hcx, mul_assoc, inv_mul_cancel₀ hs_ne, mul_one]
    rw [hcast, hde, show (j : ZMod 7) * (cx * s) = cx * slope from by ring,
      show k * (cx * slope) = cx * (k * slope) from by ring, hkt]
  refine ⟨lam, lam_unit m hm k_int j hj1 hj5', lam_avoids06 m hm k_int j hj1 hj5',
    ⟨j, hj1, hj5', lam_congr m k_int j⟩, fun i => ?_, ?_, ?_⟩
  · rw [show lam * d_s i = (1 + k_int * 7 ^ m) * ((j : ℤ) * d_s i) from by ring, qz_shift0, hk_cast]
    have : (((j : ℤ) * d_s i : ℤ) : ZMod 7) = slope := by
      push_cast; congr 1; exact_mod_cast hsame i
    rw [this, hkt]; exact ht_s i
  · rw [show lam * d_e1 = (1 + k_int * 7 ^ m) * ((j : ℤ) * d_e1) from by ring, qz_shift0, hk_cast,
      extra_shift d_e1 c1 rfl]; exact ht_e1
  · rw [show lam * d_e2 = (1 + k_int * 7 ^ m) * ((j : ℤ) * d_e2) from by ring, qz_shift0, hk_cast,
      extra_shift d_e2 c2 rfl]; exact ht_e2

/-! ### Normalization: residues to {1,2,4} -/

/-- Normalize an integer to have ZMod 7 residue in {1,2,4}: negate if in {3,5,6}. -/
noncomputable def normalize7 (x : ℤ) : ℤ :=
  if (x : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) then x else -x

theorem neg_in_124 : ∀ r : ZMod 7, r ≠ 0 →
    r ∉ ({1, 2, 4} : Finset (ZMod 7)) → -r ∈ ({1, 2, 4} : Finset (ZMod 7)) := by decide

theorem normalize7_res (x : ℤ) (hx : ¬ (7 : ℤ) ∣ x) :
    (normalize7 x : ZMod 7) ∈ ({1, 2, 4} : Finset (ZMod 7)) := by
  unfold normalize7; split_ifs with h
  · exact h
  · rw [Int.cast_neg]
    exact neg_in_124 _ (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]) h

theorem normalize7_ndvd (x : ℤ) (hx : ¬ (7 : ℤ) ∣ x) : ¬ (7 : ℤ) ∣ normalize7 x := by
  unfold normalize7; split_ifs
  · exact hx
  · rwa [Int.dvd_neg]

/-- `normalize7` only ever flips sign, so it preserves absolute value. -/
theorem normalize7_natAbs (x : ℤ) : (normalize7 x).natAbs = x.natAbs := by
  unfold normalize7; split_ifs <;> simp [Int.natAbs_neg]

/-- **`normalize7` is injective on positive integers.** Since it preserves `|·|`
and positives are determined by their absolute value, no two distinct positives
(in particular no `±`-pair, which positivity already excludes) collide. This lifts
the call-site injectivity of the speed tuple through the `{1,2,4}`-normalization,
so the §6 case theorems may assume their (normalized) tuple is injective. -/
theorem normalize7_injOn_pos {ι : Type*} (d : ι → ℤ) (hpos : ∀ i, 0 < d i)
    (hinj : Function.Injective d) : Function.Injective (fun i => normalize7 (d i)) := by
  intro a b h
  apply hinj
  have hab : (d a).natAbs = (d b).natAbs := by
    simpa [normalize7_natAbs] using congrArg Int.natAbs h
  rcases Int.natAbs_eq_natAbs_iff.mp hab with h1 | h1
  · exact h1
  · exact absurd h1 (by have := hpos a; have := hpos b; omega)

theorem normalize7_band (m : ℕ) (lam x : ℤ) :
    ((7 ^ m : ℤ) ≤ (lam * normalize7 x) % 7 ^ (m + 1) ∧
     (lam * normalize7 x) % 7 ^ (m + 1) ≤ 6 * 7 ^ m) →
    ((7 ^ m : ℤ) ≤ (lam * x) % 7 ^ (m + 1) ∧
     (lam * x) % 7 ^ (m + 1) ≤ 6 * 7 ^ m) := by
  unfold normalize7; split_ifs with h
  · exact id
  · rw [mul_neg]; exact (band_neg m (lam * x)).mpr

-- `four_band` is defined in `OrderSevenS5bN` (which imports this file)
-- to keep each file under 300 lines.

end LRC.OrderSevenN
