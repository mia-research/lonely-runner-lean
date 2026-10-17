import LonelyRunner.LRC.Spec.OrderSevenHalfSemN
import LonelyRunner.LRC.Spec.OrderSevenHalfCoreN

/-!
# Order seven, level 3: what the half-unit certificates give

Each theorem takes its certificate as a hypothesis (the certificates are checked in their own modules):

* `units3_of` (A): any five units share a unit instant of level 3.
* `units3_val1_of` (B): any four units and one runner of valuation 1 share a unit instant of level 3.
* `units5_val1_of` (C): any five units and one runner of valuation 1 share a unit instant of level 2 or 3.

Method: scale by the inverse of one unit (it becomes `1`), replace each speed by its band-symmetric half
representative, sort the indices, read off a common bit of the masks.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7L3
open LRC.O7Grid

theorem chunkAH_spec {i2 i3 i4 i5 : ℕ} (h : chunkAH i2 i2 147 = true) (h3 : i2 ≤ i3) (h4 : i3 ≤ i4)
    (h5 : i4 ≤ i5) (h5' : i5 < 147) :
    (maskL3 0 &&& maskL3 i2 &&& maskL3 i3 &&& maskL3 i4 &&& maskL3 i5) ≠ 0 := by
  simp only [chunkAH] at h
  have b := allR_spec _ _ _ h i3 h3 (by omega)
  have c := allR_spec _ _ _ b i4 h4 (by omega)
  have d := allR_spec _ _ _ c i5 h5 (by omega)
  simpa using d

theorem chunkBH_spec {i2 i3 i4 t : ℕ} (h : chunkBH i2 i2 147 = true) (h3 : i2 ≤ i3) (h4 : i3 ≤ i4)
    (h4' : i4 < 147) (ht : t < 21) :
    (maskL3 0 &&& maskL3 i2 &&& maskL3 i3 &&& maskL3 i4 &&& mmL3 t) ≠ 0 := by
  simp only [chunkBH] at h
  have b := allR_spec _ _ _ h i3 h3 (by omega)
  have c := allR_spec _ _ _ b i4 h4 (by omega)
  have d := allR_spec _ _ _ c t (Nat.zero_le _) (by omega)
  simpa using d

theorem chunkC1_spec (h : chunkC1 = true) {a b c d : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d < 21) : (mask2 0 &&& mask2 a &&& mask2 b &&& mask2 c &&& mask2 d) ≠ 0 ∨ (a, b, c, d) ∈ failH := by
  simp only [chunkC1] at h
  have e := allR_spec _ _ _ (allR_spec _ _ _ (allR_spec _ _ _ (allR_spec _ _ _ h a (Nat.zero_le _) (by omega))
    b hab (by omega)) c hbc (by omega)) d hcd (by omega)
  simpa using e

def mask2SpecB : Bool := allR 42 0 fun i => allR 42 0 fun j =>
  (mask2 i).testBit j == decide (GridOK 2 (unit49 j) (unit49 i))

theorem mask2SpecB_ok : mask2SpecB = true := by decide +kernel

theorem mask2_spec {i j : ℕ} (hi : i < 42) (hj : j < 42) :
    (mask2 i).testBit j = true ↔ GridOK 2 (unit49 j) (unit49 i) := by
  have h := allR_spec _ _ _ (allR_spec _ _ _ mask2SpecB_ok i (Nat.zero_le _) (by omega)) j (Nat.zero_le _) (by omega)
  simp only [beq_iff_eq] at h; rw [h]; simp

def small2B : Bool := allR 42 0 fun i => decide (mask2 i < 2 ^ 42) && decide (unit49 i < 49) && unit49 i % 7 != 0

theorem small2B_ok : small2B = true := by decide +kernel

theorem mask2_small {i j : ℕ} (hi : i < 42) (hj : 42 ≤ j) : (mask2 i).testBit j = false := by
  have h := allR_spec _ _ _ small2B_ok i (Nat.zero_le _) (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h.1.1 (Nat.pow_le_pow_right (by norm_num) hj))

theorem unit49_unit {i : ℕ} (hi : i < 42) : unit49 i < 49 ∧ unit49 i % 7 ≠ 0 := by
  have h := allR_spec _ _ _ small2B_ok i (Nat.zero_le _) (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h
  exact ⟨h.1.2, h.2⟩

theorem unit49_zero : unit49 0 = 1 := by decide +kernel

theorem failH_len : failH.length = 15 := by decide +kernel

theorem sorted_cover3 {W : Finset ℕ} {B : ℕ} (hB : 0 < B) (hc : W.card ≤ 3) (hW : ∀ i ∈ W, i < B) :
    ∃ i2 i3 i4, i2 ≤ i3 ∧ i3 ≤ i4 ∧ i4 < B ∧ ∀ i ∈ W, i = i2 ∨ i = i3 ∨ i = i4 := by
  obtain ⟨i2, i3, i4, i5, h23, h34, h45, h5, hcov⟩ := sorted_cover hB (by omega : W.card ≤ 4) hW
  have hs := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort W)
  have hl : (W.sort (· ≤ ·)).length ≤ 3 := by rw [Finset.length_sort]; exact hc
  have hm : ∀ i, i ∈ W ↔ i ∈ W.sort (· ≤ ·) := fun i => (Finset.mem_sort _).symm
  generalize W.sort (· ≤ ·) = l at hs hl hm
  have hlt : ∀ i ∈ l, i < B := fun i h => hW i ((hm i).mpr h)
  match l, hs, hl, hm, hlt with
  | [], _, _, hm, _ => exact ⟨0, 0, 0, le_rfl, le_rfl, hB, fun i h => by simp [hm] at h⟩
  | [a], _, _, hm, hlt =>
    exact ⟨a, a, a, le_rfl, le_rfl, hlt a (by simp), fun i h => by simp [hm] at h; omega⟩
  | [a, b], hs, _, hm, hlt =>
    have hab : a < b := by simp [List.pairwise_cons] at hs; exact hs
    exact ⟨a, b, b, hab.le, le_rfl, hlt b (by simp), fun i h => by simp [hm] at h; omega⟩
  | [a, b, c], hs, _, hm, hlt =>
    have h1 : a < b ∧ a < c ∧ b < c := by simp [List.pairwise_cons] at hs; omega
    exact ⟨a, b, c, h1.1.le, h1.2.2.le, hlt c (by simp), fun i h => by simp [hm] at h; omega⟩
  | _ :: _ :: _ :: _ :: _, _, hl, _, _ => simp at hl; omega

theorem bit_lt {j : ℕ} (h : (maskL3 0).testBit j = true) : j < 294 := by
  by_contra hge; rw [not_lt] at hge
  rw [maskL3_small (by norm_num) hge] at h; exact absurd h (by simp)

theorem bit_lt2 {j : ℕ} (h : (mask2 0).testBit j = true) : j < 42 := by
  by_contra hge; rw [not_lt] at hge
  rw [mask2_small (by norm_num) hge] at h; exact absurd h (by simp)

theorem unit_mul {c k0 : ℕ} (hc : ¬ 7 ∣ c) (hk : k0 % 7 ≠ 0) : ¬ 7 ∣ c * k0 :=
  fun hd => ((Nat.Prime.dvd_mul (by norm_num)).mp hd).elim hc (fun h => hk (Nat.mod_eq_zero_of_dvd h))

theorem back3 {c k0 u : ℕ} (h : GridOK 3 k0 (c * u % 343)) : GridOK 3 (c * k0) u := by
  rw [gridOK_scale, gridOK_mod, show (7 : ℕ) ^ 3 = 343 by norm_num]; exact h

theorem back2 {c k0 u : ℕ} (h : GridOK 2 k0 (c * u % 343)) : GridOK 2 (c * k0) u := by
  rw [gridOK_scale, gridOK_mod, show (7 : ℕ) ^ 2 = 49 by norm_num]
  rw [gridOK_mod, show (7 : ℕ) ^ 2 = 49 by norm_num, Nat.mod_mod_of_dvd _ (by norm_num : 49 ∣ 343)] at h
  exact h

/-- Half representative mod 49 of a cofactor. -/
def half2 (r : ℕ) : ℕ := if r ≤ 24 then r else 49 - r

theorem half2_spec {r : ℕ} (hr : r < 49) (h7 : r % 7 ≠ 0) :
    half2 r - 1 - half2 r / 7 < 21 ∧ unit49 (half2 r - 1 - half2 r / 7) = half2 r ∧
      ∀ k, GridOK 2 k (half2 r) ↔ GridOK 2 k r := by
  have hh : half2 r < 25 ∧ half2 r % 7 ≠ 0 ∧ ∀ k, GridOK 2 k (half2 r) ↔ GridOK 2 k r := by
    unfold half2; split_ifs with h
    · exact ⟨by omega, h7, fun k => Iff.rfl⟩
    · exact ⟨by omega, by omega, fun k => gridOK2_neg hr⟩
  obtain ⟨h1, h2, h3⟩ := hh
  exact ⟨by omega, (unit49_idx (by omega) h2).1, h3⟩

/-- The cofactor of a valuation-1 runner, after scaling by `c`, has a half index `t < 21`. -/
theorem cofactor_idx {c m : ℕ} (hc : ¬ 7 ∣ c) (hm : ¬ 7 ∣ m) :
    ∃ t, t < 21 ∧ ∀ k0, GridOK 2 k0 (unit49 t) → GridOK 2 (c * k0) m := by
  have hr : c * m % 49 % 7 ≠ 0 := by
    rw [show (49 : ℕ) = 7 * 7 by norm_num, Nat.mod_mul_right_mod]
    exact fun h0 => ((Nat.Prime.dvd_mul (by norm_num)).mp (Nat.dvd_of_mod_eq_zero h0)).elim hc hm
  obtain ⟨h1, h2, h3⟩ := half2_spec (Nat.mod_lt (c * m) (by norm_num : 49 > 0)) hr
  refine ⟨_, h1, fun k0 hk => ?_⟩
  rw [h2] at hk
  have := (h3 k0).mp hk
  rw [gridOK_scale, gridOK_mod, show (7 : ℕ) ^ 2 = 49 by norm_num]; exact this

/-- **Certificate A gives**: any five units share a unit instant of level 3. -/
theorem units3_of (hA : ∀ i2, i2 < 147 → chunkAH i2 i2 147 = true) {U : Finset ℕ} (hc : U.card ≤ 5)
    (hu : ∀ u ∈ U, ¬ 7 ∣ u) : ∃ k, ¬ 7 ∣ k ∧ ∀ u ∈ U, GridOK 3 k u := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨u1, hu1⟩
  · exact ⟨1, by norm_num, fun u h => by simp at h⟩
  obtain ⟨c, hc7, h1, hred⟩ := normalise hu1 hu
  set V := U.image fun u => half3 (c * u % 343) with hV
  have hVu : ∀ v ∈ V, v < 172 ∧ v % 7 ≠ 0 := by
    intro v hv
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨a, b, _⟩ := half3_spec (hred u hu').1 (hred u hu').2
    exact ⟨a, b⟩
  have h1V : 1 ∈ V := Finset.mem_image.mpr ⟨u1, hu1, by rw [h1]; rfl⟩
  set W := (V.erase 1).image fun v => v - 1 - v / 7 with hW
  have hWc : W.card ≤ 4 := by
    have hVc : V.card ≤ 5 := le_trans Finset.card_image_le hc
    have := Finset.card_erase_of_mem h1V
    exact le_trans Finset.card_image_le (by omega)
  have hWlt : ∀ i ∈ W, i < 147 := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    have := hVu v (Finset.mem_of_mem_erase hv); omega
  obtain ⟨i2, i3, i4, i5, h23, h34, h45, h5, hcov⟩ := sorted_cover (by norm_num) hWc hWlt
  have hne := chunkAH_spec (hA i2 (by omega)) h23 h34 h45 h5
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hne
  simp only [Nat.testBit_land, Bool.and_eq_true] at hj
  obtain ⟨⟨⟨⟨b0, b2⟩, b3⟩, b4⟩, b5⟩ := hj
  have hj294 := bit_lt b0
  have good : ∀ i, i < 294 → (maskL3 i).testBit j = true → GridOK 3 (unitL3 j) (unitL3 i) :=
    fun i hi hb => (maskL3_spec hi hj294).mp hb
  have hV_ok : ∀ v ∈ V, GridOK 3 (unitL3 j) v := by
    intro v hv
    by_cases hv1 : v = 1
    · subst hv1; have := good 0 (by norm_num) b0; rwa [unitL3_zero] at this
    · obtain ⟨hlt, h7⟩ := hVu v hv
      have hi : v - 1 - v / 7 ∈ W := Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨hv1, hv⟩, rfl⟩
      obtain ⟨hidx, _⟩ := unitL3_idx (by omega : v < 343) h7
      rw [← hidx]
      rcases hcov _ hi with h | h | h | h <;> rw [h] <;> [exact good _ (by omega) b2; exact good _ (by omega) b3;
        exact good _ (by omega) b4; exact good _ (by omega) b5]
  refine ⟨c * unitL3 j, unit_mul hc7 (unitL3_unit hj294).2, fun u hu' => back3 ?_⟩
  exact ((half3_spec (hred u hu').1 (hred u hu').2).2.2 _).mp (hV_ok _ (Finset.mem_image.mpr ⟨u, hu', rfl⟩))

/-- **Certificate B gives**: any four units and one runner `7m` of valuation 1 share a unit instant of level 3. -/
theorem units3_val1_of (hB : ∀ i2, i2 < 147 → chunkBH i2 i2 147 = true) {U : Finset ℕ} (hc : U.card ≤ 4)
    (hU : U.Nonempty) (hu : ∀ u ∈ U, ¬ 7 ∣ u) {m : ℕ} (hm : ¬ 7 ∣ m) :
    ∃ k, ¬ 7 ∣ k ∧ (∀ u ∈ U, GridOK 3 k u) ∧ GridOK 3 k (7 * m) := by
  obtain ⟨u1, hu1⟩ := hU
  obtain ⟨c, hc7, h1, hred⟩ := normalise hu1 hu
  obtain ⟨t, ht, hmt⟩ := cofactor_idx hc7 hm
  set V := U.image fun u => half3 (c * u % 343) with hV
  have hVu : ∀ v ∈ V, v < 172 ∧ v % 7 ≠ 0 := by
    intro v hv
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨a, b, _⟩ := half3_spec (hred u hu').1 (hred u hu').2
    exact ⟨a, b⟩
  have h1V : 1 ∈ V := Finset.mem_image.mpr ⟨u1, hu1, by rw [h1]; rfl⟩
  set W := (V.erase 1).image fun v => v - 1 - v / 7 with hW
  have hWc : W.card ≤ 3 := by
    have hVc : V.card ≤ 4 := le_trans Finset.card_image_le hc
    have := Finset.card_erase_of_mem h1V
    exact le_trans Finset.card_image_le (by omega)
  have hWlt : ∀ i ∈ W, i < 147 := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    have := hVu v (Finset.mem_of_mem_erase hv); omega
  obtain ⟨i2, i3, i4, h23, h34, h4, hcov⟩ := sorted_cover3 (by norm_num) hWc hWlt
  have hne := chunkBH_spec (hB i2 (by omega)) h23 h34 h4 ht
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hne
  simp only [Nat.testBit_land, Bool.and_eq_true] at hj
  obtain ⟨⟨⟨⟨b0, b2⟩, b3⟩, b4⟩, bt⟩ := hj
  have hj294 := bit_lt b0
  have good : ∀ i, i < 294 → (maskL3 i).testBit j = true → GridOK 3 (unitL3 j) (unitL3 i) :=
    fun i hi hb => (maskL3_spec hi hj294).mp hb
  have hV_ok : ∀ v ∈ V, GridOK 3 (unitL3 j) v := by
    intro v hv
    by_cases hv1 : v = 1
    · subst hv1; have := good 0 (by norm_num) b0; rwa [unitL3_zero] at this
    · obtain ⟨hlt, h7⟩ := hVu v hv
      have hi : v - 1 - v / 7 ∈ W := Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨hv1, hv⟩, rfl⟩
      obtain ⟨hidx, _⟩ := unitL3_idx (by omega : v < 343) h7
      rw [← hidx]
      rcases hcov _ hi with h | h | h <;> rw [h] <;> [exact good _ (by omega) b2; exact good _ (by omega) b3;
        exact good _ (by omega) b4]
  refine ⟨c * unitL3 j, unit_mul hc7 (unitL3_unit hj294).2, fun u hu' => back3 ?_, ?_⟩
  · exact ((half3_spec (hred u hu').1 (hred u hu').2).2.2 _).mp (hV_ok _ (Finset.mem_image.mpr ⟨u, hu', rfl⟩))
  · rw [gridOK3_seven]; exact hmt _ ((mmL3_spec hj294 (by omega)).mp bt)

/-- Representative mod 343 whose residue mod 49 is in the lower half. -/
def half49 (v : ℕ) : ℕ := if v % 49 ≤ 24 then v else 343 - v

theorem half49_spec {v : ℕ} (hv : v < 343) (h7 : v % 7 ≠ 0) :
    half49 v < 343 ∧ half49 v % 7 ≠ 0 ∧ half49 v % 49 ≤ 24 ∧
      (∀ k, GridOK 3 k (half49 v) ↔ GridOK 3 k v) ∧ (∀ k, GridOK 2 k (half49 v) ↔ GridOK 2 k v) := by
  unfold half49; split_ifs with h
  · exact ⟨hv, h7, h, fun k => Iff.rfl, fun k => Iff.rfl⟩
  · refine ⟨by omega, by omega, by omega, fun k => gridOK3_neg hv, fun k => ?_⟩
    rw [gridOK_mod 2 k (343 - v), gridOK_mod 2 k v, show (7 : ℕ) ^ 2 = 49 by norm_num,
      show (343 - v) % 49 = 49 - v % 49 by omega]
    exact gridOK2_neg (by omega)

/-- **Certificates C1 and C2 give**: any five units and one runner `7m` of valuation 1 share a unit instant of level
2 or 3. -/
theorem units5_val1_of (hC1 : chunkC1 = true) (hC2 : ∀ p, p < 15 → chunkC2 p = true) {U : Finset ℕ}
    (hc : U.card ≤ 5) (hU : U.Nonempty) (hu : ∀ u ∈ U, ¬ 7 ∣ u) {m : ℕ} (hm : ¬ 7 ∣ m) :
    ∃ a k, 1 ≤ a ∧ ¬ 7 ∣ k ∧ (∀ u ∈ U, GridOK a k u) ∧ GridOK a k (7 * m) := by
  obtain ⟨u1, hu1⟩ := hU
  obtain ⟨c, hc7, h1, hred⟩ := normalise hu1 hu
  set V := U.image fun u => half49 (c * u % 343) with hV
  have hVu : ∀ v ∈ V, v < 343 ∧ v % 7 ≠ 0 ∧ v % 49 ≤ 24 := by
    intro v hv
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨a, b, d, _⟩ := half49_spec (hred u hu').1 (hred u hu').2
    exact ⟨a, b, d⟩
  have h1V : 1 ∈ V := Finset.mem_image.mpr ⟨u1, hu1, by rw [h1]; rfl⟩
  set W := (V.erase 1).image fun v => 7 * (v % 49 - 1 - v % 49 / 7) + v / 49 with hW
  have hWc : W.card ≤ 4 := by
    have hVc : V.card ≤ 5 := le_trans Finset.card_image_le hc
    have := Finset.card_erase_of_mem h1V
    exact le_trans Finset.card_image_le (by omega)
  have hWlt : ∀ i ∈ W, i < 147 := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hlt, h7, h24⟩ := hVu v (Finset.mem_of_mem_erase hv)
    have hr : v % 49 - 1 - v % 49 / 7 ≤ 20 := by omega
    have hq : v / 49 < 7 := by omega
    calc 7 * (v % 49 - 1 - v % 49 / 7) + v / 49 < 7 * 20 + 7 := by
          have := Nat.mul_le_mul_left 7 hr; omega
      _ = 147 := by norm_num
  obtain ⟨c2, c3, c4, c5, h23, h34, h45, h5, hcov⟩ := sorted_cover (by norm_num) hWc hWlt
  -- each `v ≠ 1` is `unit49 (i/7) + 49 (i % 7)` for one of the sorted codes `i`
  have hrep : ∀ v ∈ V, v ≠ 1 → ∃ i, (i = c2 ∨ i = c3 ∨ i = c4 ∨ i = c5) ∧ unit49 (i / 7) = v % 49 ∧
      v = unit49 (i / 7) + 49 * (i % 7) := by
    intro v hv hv1
    obtain ⟨hlt, h7, h24⟩ := hVu v hv
    have hi : 7 * (v % 49 - 1 - v % 49 / 7) + v / 49 ∈ W :=
      Finset.mem_image.mpr ⟨v, Finset.mem_erase.mpr ⟨hv1, hv⟩, rfl⟩
    refine ⟨_, hcov _ hi, ?_⟩
    have e1 : (7 * (v % 49 - 1 - v % 49 / 7) + v / 49) / 7 = v % 49 - 1 - v % 49 / 7 := by omega
    have e2 : (7 * (v % 49 - 1 - v % 49 / 7) + v / 49) % 7 = v / 49 := by omega
    have hu49 := (unit49_idx (Nat.mod_lt v (by norm_num)) (by omega)).1
    rw [e1, e2, hu49]; exact ⟨rfl, by omega⟩
  have hd : ∀ {x y : ℕ}, x ≤ y → x / 7 ≤ y / 7 := fun h => Nat.div_le_div_right h
  rcases chunkC1_spec hC1 (hd h23) (hd h34) (hd h45) (by omega) with hl2 | hf
  · -- level 2: the five units already share an instant mod 49; the valuation-1 runner is automatic there
    obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hl2
    simp only [Nat.testBit_land, Bool.and_eq_true] at hj
    obtain ⟨⟨⟨⟨b0, b2⟩, b3⟩, b4⟩, b5⟩ := hj
    have hj42 := bit_lt2 b0
    have good : ∀ i, i < 42 → (mask2 i).testBit j = true → GridOK 2 (unit49 j) (unit49 i) :=
      fun i hi hb => (mask2_spec hi hj42).mp hb
    have hV_ok : ∀ v ∈ V, GridOK 2 (unit49 j) v := by
      intro v hv
      by_cases hv1 : v = 1
      · subst hv1; have := good 0 (by norm_num) b0; rwa [unit49_zero] at this
      · obtain ⟨i, hi, he, -⟩ := hrep v hv hv1
        rw [gridOK_mod, show (7 : ℕ) ^ 2 = 49 by norm_num, ← he]
        rcases hi with h | h | h | h <;> subst h <;> [exact good _ (by omega) b2; exact good _ (by omega) b3;
          exact good _ (by omega) b4; exact good _ (by omega) b5]
    have hk := unit_mul hc7 (unit49_unit hj42).2
    refine ⟨2, c * unit49 j, by norm_num, hk, fun u hu' => back2 ?_, gridOK_two_val1 hm hk⟩
    exact ((half49_spec (hred u hu').1 (hred u hu').2).2.2.2.2 _).mp
      (hV_ok _ (Finset.mem_image.mpr ⟨u, hu', rfl⟩))
  · -- one of the 15 failing level-2 tuples: certificate C2 covers every lift to 343
    obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hf
    have hp15 : p < 15 := failH_len ▸ hp
    have hpe' : failH.getD p (0, 0, 0, 0) = (c2 / 7, c3 / 7, c4 / 7, c5 / 7) := by
      rw [List.getD_eq_getElem _ _ hp]; exact hpe
    have hc2 := hC2 p hp15
    simp only [chunkC2, hpe'] at hc2
    obtain ⟨t, ht, hmt⟩ := cofactor_idx hc7 hm
    have e := allR_spec _ _ _ (allR_spec _ _ _ (allR_spec _ _ _ (allR_spec _ _ _ (allR_spec _ _ _ hc2
      (c2 % 7) (Nat.zero_le _) (by omega)) (c3 % 7) (Nat.zero_le _) (by omega)) (c4 % 7) (Nat.zero_le _)
      (by omega)) (c5 % 7) (Nat.zero_le _) (by omega)) t (Nat.zero_le _) (by omega)
    have hne := bne_iff_ne.mp e
    obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hne
    simp only [Nat.testBit_land, Bool.and_eq_true] at hj
    obtain ⟨⟨⟨⟨⟨b0, b2⟩, b3⟩, b4⟩, b5⟩, bt⟩ := hj
    have hj294 := bit_lt b0
    have good : ∀ i, (i = c2 ∨ i = c3 ∨ i = c4 ∨ i = c5) →
        GridOK 3 (unitL3 j) (unitL3 (idx343 (unit49 (i / 7) + 49 * (i % 7)))) := by
      intro i hi
      have hlt : idx343 (unit49 (i / 7) + 49 * (i % 7)) < 294 := by
        have := unit49_unit (by omega : i / 7 < 42); unfold idx343; omega
      rcases hi with h | h | h | h <;> subst h <;> [exact (maskL3_spec hlt hj294).mp b2;
        exact (maskL3_spec hlt hj294).mp b3; exact (maskL3_spec hlt hj294).mp b4;
        exact (maskL3_spec hlt hj294).mp b5]
    have hV_ok : ∀ v ∈ V, GridOK 3 (unitL3 j) v := by
      intro v hv
      by_cases hv1 : v = 1
      · subst hv1; have := (maskL3_spec (by norm_num) hj294).mp b0; rwa [unitL3_zero] at this
      · obtain ⟨hlt, h7, -⟩ := hVu v hv
        obtain ⟨i, hi, -, hv'⟩ := hrep v hv hv1
        have := good i hi
        rw [← hv'] at this
        rwa [show idx343 v = v - 1 - v / 7 from rfl, (unitL3_idx hlt h7).1] at this
    have hk := unit_mul hc7 (unitL3_unit hj294).2
    refine ⟨3, c * unitL3 j, by norm_num, hk, fun u hu' => back3 ?_, ?_⟩
    · exact ((half49_spec (hred u hu').1 (hred u hu').2).2.2.2.1 _).mp
        (hV_ok _ (Finset.mem_image.mpr ⟨u, hu', rfl⟩))
    · rw [gridOK3_seven]; exact hmt _ ((mmL3_spec hj294 (by omega)).mp bt)

end LRC.O7L3
