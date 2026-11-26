import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Grid
import Fresh.Admissible

/-!
# Linking the order-eight residual to the admissible arrangements

Written 2026-10-25.  New file.  The old structure `EightResidual` (`LonelyRunner/LRC/Spec/OrderEightCasesN.lean:770`) cannot be imported here (this tree is built without the old repository), so the fields that bear on the three
proved classes are COPIED, verbatim in statement: `card_eq`, `odd`, `no_common_factor`, `eight`, `spread`, `no_small_resolution` (with `ResolutionClears8` and `resolutionCap8 = 64` copied).  Call the copy `EightResidualCore`;
the old structure has twelve further fields (the flank, first-lap, rational-opening, fast-pair and block-split exclusions), each a further proved class, so `EightResidual → EightResidualCore` and the converse fails.
An integer disparity set `S` is the disparity set of subject `k` in an arrangement `v` (`HasDisp`).  Results (real speeds):
* `spread_iff_not_ratio`: `spread` is the failure of the ratio class.
* `unblocked_iff_resolution`: the unblocked class is `ResolutionClears8 S (min S) 0` (the d_min instant is clear iff every `d mod 8 m` lies in `[m, 7m]`).
* `eight_not_grid`: `eight` with `no_common_factor` excludes the grid class.
* `core_imp_admissible`: for `min S ≤ 64`, `EightResidualCore` gives `Admissible`; for `min S > 64` the cap leaves the case `ResolutionClears8 S (min S) 0` open in the old structure, and it is exactly the unblocked class (`gap_exact`), proved here for every real arrangement without the cap.
Grades: [L].  Not claimed: that `EightResidual` implies `Admissible` for `min S > 64`, or anything about the further fields.
-/

open Classical

namespace Fresh.EightResidualLink

open Fresh Fresh.Admissible

/-- Copied from `OrderEightCasesN.lean`. -/
-- STANDING: IMPORTED
def ResolutionClears8 (S : Finset ℕ) (D j : ℕ) : Prop :=
  ∀ d ∈ S, D ≤ d * (8 * j + 1) % (8 * D) ∧ d * (8 * j + 1) % (8 * D) ≤ 7 * D

/-- Copied from `OrderEightCasesN.lean`. -/
def resolutionCap8 : ℕ := 64

/-- The fields of the old `EightResidual` that bear on the three proved classes, copied. -/
-- STANDING: IMPORTED
structure EightResidualCore (S : Finset ℕ) : Prop where
  card_eq : S.card = 7
  odd : ∃ d ∈ S, ¬ 2 ∣ d
  no_common_factor : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d
  eight : ∃ d ∈ S, 8 ∣ d
  spread : ∃ a ∈ S, ∃ b ∈ S, 7 * a < b
  no_small_resolution : ∀ D, 0 < D → D ≤ resolutionCap8 → ∀ j, ¬ ResolutionClears8 S D j

/-- `S` is the disparity set of subject `k` in `v`. -/
-- STANDING: DEFINITION
def HasDisp (v : Fin 8 → ℝ) (k : Fin 8) (S : Finset ℕ) : Prop :=
  ∀ x : ℝ, x ∈ disparitySet v k ↔ ∃ d ∈ S, (d : ℝ) = x

theorem hasDisp_dmin {v : Fin 8 → ℝ} {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S) (hinj : Function.Injective v)
    {m : ℝ} (hm : IsDmin v k m) : ∃ a ∈ S, (a : ℝ) = m ∧ ∀ s ∈ S, a ≤ s := by
  have hmem : m ∈ disparitySet v k := hm.1
  obtain ⟨a, haS, hae⟩ := (hS m).1 hmem
  refine ⟨a, haS, hae, fun s hs => ?_⟩
  have : (s : ℝ) ∈ disparitySet v k := (hS _).2 ⟨s, hs, rfl⟩
  have := hm.2 this
  rw [← hae] at this
  exact_mod_cast this

theorem spread_iff_not_ratio {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S) :
    (∃ a ∈ S, ∃ b ∈ S, 7 * a < b) ↔ ¬ RatioClass v k := by
  obtain ⟨m, hm⟩ := exists_dmin hinj k
  obtain ⟨a, haS, hae, hamin⟩ := hasDisp_dmin hS hinj hm
  constructor
  · rintro ⟨a', ha', b, hb, hlt⟩ ⟨m', hm', h7⟩
    have : m' = m := dmin_unique hm' hm
    subst this
    have hb' : (b : ℝ) ∈ disparitySet v k := (hS _).2 ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hb'
    have hik : i ≠ k := (Finset.mem_erase.1 hi).1
    have h1 := h7 i hik
    rw [hie] at h1
    have h2 : (a : ℝ) ≤ a' := by exact_mod_cast hamin a' ha'
    have h3 : (7 * a' : ℝ) < b := by exact_mod_cast hlt
    rw [← hae] at h1
    linarith
  · intro hnr
    by_contra hno
    push Not at hno
    apply hnr
    refine ⟨m, hm, fun i hik => ?_⟩
    have hmem : |v i - v k| ∈ disparitySet v k := Finset.mem_image.2 ⟨i, Finset.mem_erase.2 ⟨hik, Finset.mem_univ _⟩, rfl⟩
    obtain ⟨b, hb, hbe⟩ := (hS _).1 hmem
    have := hno a haS b hb
    rw [← hbe, ← hae]
    exact_mod_cast (by omega : b ≤ 7 * a)

#print axioms hasDisp_dmin
#print axioms spread_iff_not_ratio

theorem nat_clear_iff (a d : ℕ) (ha : 0 < a) :
    (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * (1 / (8 * (a : ℝ)))) ↔ a ≤ d % (8 * a) ∧ d % (8 * a) ≤ 7 * a := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h8 : 0 < 8 * a := by omega
  have hdm := Nat.div_add_mod d (8 * a)
  set q := d / (8 * a) with hq
  set r := d % (8 * a) with hr
  have hrlt : r < 8 * a := Nat.mod_lt _ h8
  have hd : (d : ℝ) = 8 * a * q + r := by exact_mod_cast hdm.symm
  have hy : (d : ℝ) * (1 / (8 * (a : ℝ))) = (r : ℝ) / (8 * a) + (q : ℤ) := by
    rw [hd]; push_cast; field_simp; ring
  rw [hy, Fresh.Localisation.distInt_add_int]
  have hy0 : 0 ≤ (r : ℝ) / (8 * a) := by positivity
  have hy1 : (r : ℝ) / (8 * a) < 1 := by
    rw [div_lt_one (by positivity)]; exact_mod_cast hrlt
  constructor
  · intro h
    rw [Fresh.Localisation.le_distInt_iff] at h
    have h0 := h 0
    have h1 := h 1
    simp only [Int.cast_zero, sub_zero, Int.cast_one] at h0 h1
    rw [abs_of_nonneg hy0] at h0
    rw [abs_of_neg (by linarith)] at h1
    have e1 : (a : ℝ) ≤ r := by
      have := h0; rw [le_div_iff₀ (by positivity)] at this; linarith
    have e2 : (r : ℝ) ≤ 7 * a := by
      have : (r : ℝ) / (8 * a) ≤ 7 / 8 := by linarith
      rw [div_le_iff₀ (by positivity)] at this; linarith
    exact ⟨by exact_mod_cast e1, by exact_mod_cast e2⟩
  · rintro ⟨e1, e2⟩
    have f1 : (a : ℝ) ≤ r := by exact_mod_cast e1
    have f2 : (r : ℝ) ≤ 7 * a := by exact_mod_cast e2
    apply Fresh.Localisation.clear_of_window 0
    · simp only [Int.cast_zero, zero_add]; rw [le_div_iff₀ (by positivity)]; linarith
    · simp only [Int.cast_zero, zero_add]; rw [div_le_iff₀ (by positivity)]; linarith

theorem unblocked_iff_resolution {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    {a : ℕ} (haS : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) : Unblocked v k ↔ ResolutionClears8 S a 0 := by
  obtain ⟨m, hm⟩ := exists_dmin hinj k
  obtain ⟨a', ha'S, hae, ha'min⟩ := hasDisp_dmin hS hinj hm
  have haa : a = a' := le_antisymm (hamin a' ha'S) (ha'min a haS)
  subst haa
  have hapos : 0 < a := by
    have hmpos := (dmin_facts hm hinj).1
    rw [← hae] at hmpos; exact_mod_cast hmpos
  constructor
  · rintro ⟨m', hm', hcl⟩
    have : m' = m := dmin_unique hm' hm
    subst this
    intro d hd
    have hmem : (d : ℝ) ∈ disparitySet v k := (hS _).2 ⟨d, hd, rfl⟩
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hmem
    have hik : i ≠ k := (Finset.mem_erase.1 hi).1
    have := hcl i hik
    rw [hie, ← hae] at this
    have := (nat_clear_iff a d hapos).1 this
    simpa using this
  · intro hres
    refine ⟨m, hm, fun i hik => ?_⟩
    have hmem : |v i - v k| ∈ disparitySet v k := Finset.mem_image.2 ⟨i, Finset.mem_erase.2 ⟨hik, Finset.mem_univ _⟩, rfl⟩
    obtain ⟨d, hd, hde⟩ := (hS _).1 hmem
    rw [← hde, ← hae]
    apply (nat_clear_iff a d hapos).2
    simpa using hres d hd

#print axioms nat_clear_iff
#print axioms unblocked_iff_resolution

theorem exists_ne8 (k : Fin 8) : ∃ j : Fin 8, j ≠ k := by
  by_cases hk : k = 0
  · exact ⟨1, by rw [hk]; decide⟩
  · exact ⟨0, fun h => hk h.symm⟩

/-- A grid has no disparity set with a multiple of `8` and no common factor: in units of the step the disparities are not multiples of `8`, and coprimality forces the step to be `1/q`. -/
theorem eight_not_grid {v : Fin 8 → ℝ} {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    (hcf : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d) (h8 : ∃ e ∈ S, 8 ∣ e) : ¬ GridClass v := by
  rintro ⟨d, v₀, idx, hd, hres, hvv⟩
  obtain ⟨N, hN⟩ : ∃ N : Fin 8 → ℤ, ∀ j, N j = |idx j - idx k| := ⟨_, fun _ => rfl⟩
  have hn : ∀ j, j ≠ k → |v j - v k| = (N j : ℝ) * d := by
    intro j hj
    rw [hN, hvv j, hvv k]
    have : v₀ + (idx j : ℝ) * d - (v₀ + (idx k : ℝ) * d) = ((idx j - idx k : ℤ) : ℝ) * d := by push_cast; ring
    rw [this, abs_mul, abs_of_pos hd, Int.cast_abs]
  have hS' : ∀ s ∈ S, ∃ j, j ≠ k ∧ (s : ℝ) = (N j : ℝ) * d := by
    intro s hs
    have hmem : (s : ℝ) ∈ disparitySet v k := (hS _).2 ⟨s, hs, rfl⟩
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hmem
    have hik : i ≠ k := (Finset.mem_erase.1 hi).1
    exact ⟨i, hik, by rw [← hie, hn i hik]⟩
  have hne : ∀ j, j ≠ k → idx j - idx k ≠ 0 := by
    intro j hj h
    have : idx j % 8 = idx k % 8 := by rw [sub_eq_zero.1 h]
    exact hj (hres j k this)
  have hNpos : ∀ j, j ≠ k → 0 < N j := fun j hj => by rw [hN]; exact abs_pos.2 (hne j hj)
  have hN8 : ∀ j, j ≠ k → ¬ (8 : ℤ) ∣ N j := by
    intro j hj h
    rw [hN, dvd_abs] at h
    have : idx j % 8 = idx k % 8 := Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd h)
    exact hj (hres j k this)
  obtain ⟨e, heS, he8⟩ := h8
  obtain ⟨je, hje, hee⟩ := hS' e heS
  have hnje : (0 : ℤ) < N je := hNpos je hje
  have hnjeR : (0 : ℝ) < (N je : ℝ) := by exact_mod_cast hnje
  set r : ℚ := (e : ℚ) / (N je : ℚ) with hr
  have hrd : (r : ℝ) = d := by
    rw [hr]; push_cast
    rw [div_eq_iff hnjeR.ne']
    linarith [hee]
  have hall : ∀ s ∈ S, ∃ j, j ≠ k ∧ (s : ℚ) = (N j : ℚ) * r := by
    intro s hs
    obtain ⟨j, hjk, hse⟩ := hS' s hs
    refine ⟨j, hjk, ?_⟩
    have : ((s : ℚ) : ℝ) = (((N j : ℚ) * r : ℚ) : ℝ) := by
      push_cast; rw [hrd]; exact hse
    exact_mod_cast this
  have hepos : 0 < e := by
    have h0 : (0 : ℝ) < (e : ℝ) := by rw [hee]; exact mul_pos hnjeR hd
    exact_mod_cast h0
  have hrpos : 0 < r := by
    rw [hr]; apply div_pos
    · exact_mod_cast hepos
    · exact_mod_cast hnje
  have hnum : 0 < r.num := Rat.num_pos.2 hrpos
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := r.reduced
    simpa [Int.gcd, Nat.Coprime] using this
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hdiv : ∀ s ∈ S, r.num ∣ (s : ℤ) := by
    intro s hs
    obtain ⟨j, hjk, hse⟩ := hall s hs
    have h1 : (s : ℚ) = (N j : ℚ) * (r.num / r.den) := by rw [hse, Rat.num_div_den]
    have h2 : (s : ℚ) * r.den = (N j : ℚ) * r.num := by
      rw [h1]; field_simp
    have h3 : (s : ℤ) * r.den = N j * r.num := by exact_mod_cast h2
    have h4 : r.num ∣ (s : ℤ) * r.den := ⟨N j, by rw [h3]; ring⟩
    exact hcop.dvd_of_dvd_mul_right h4
  have hp1 : r.num = 1 := by
    by_contra hne1
    have h2 : 2 ≤ r.num.natAbs := by omega
    obtain ⟨s, hs, hns⟩ := hcf r.num.natAbs h2
    apply hns
    have := hdiv s hs
    have h5 : (r.num.natAbs : ℤ) ∣ (s : ℤ) := by rw [Int.natAbs_dvd]; exact this
    exact_mod_cast h5
  have hrden : r * (r.den : ℚ) = 1 := by
    have h := Rat.mul_den_eq_num r
    rw [hp1] at h
    simpa using h
  have h1 : (e : ℚ) = (N je : ℚ) * r := by rw [hr]; field_simp
  have h2 : (e : ℚ) * r.den = (N je : ℚ) := by
    calc (e : ℚ) * r.den = (N je : ℚ) * (r * r.den) := by rw [h1]; ring
      _ = (N je : ℚ) := by rw [hrden]; ring
  have h3 : (e : ℤ) * r.den = N je := by exact_mod_cast h2
  apply hN8 je hje
  rw [← h3]
  obtain ⟨t, ht⟩ := he8
  exact ⟨t * r.den, by rw [ht]; push_cast; ring⟩

#print axioms eight_not_grid

theorem hasDisp_pos {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    {a : ℕ} (ha : a ∈ S) : 0 < a := by
  have hmem : (a : ℝ) ∈ disparitySet v k := (hS _).2 ⟨a, ha, rfl⟩
  obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hmem
  have hik : i ≠ k := (Finset.mem_erase.1 hi).1
  have : (0 : ℝ) < |v i - v k| := abs_pos.2 (sub_ne_zero.2 (fun h => hik (hinj h)))
  rw [hie] at this
  exact_mod_cast this

/-- **The exact link.**  For an ordered arrangement whose subject has the integer disparity set `S` with a multiple of `8`, no common factor and a spread (three fields of `EightResidual`),
the subject is admissible iff the d_min instant is blocked, in the form `¬ ResolutionClears8 S (min S) 0`. -/
theorem admissible_iff_not_resolution {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    (hcf : ∀ g, 2 ≤ g → ∃ d ∈ S, ¬ g ∣ d) (h8 : ∃ e ∈ S, 8 ∣ e) (hsp : ∃ a ∈ S, ∃ b ∈ S, 7 * a < b)
    {a : ℕ} (haS : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) :
    Admissible v k ↔ ¬ ResolutionClears8 S a 0 := by
  have hinj : Function.Injective v := hv.2.injective
  have hng : ¬ GridClass v := eight_not_grid hS hcf h8
  have hnr : ¬ RatioClass v k := (spread_iff_not_ratio hinj hS).1 hsp
  have hu := unblocked_iff_resolution hinj hS haS hamin
  unfold Admissible Proved
  constructor
  · rintro ⟨_, hn⟩ hres
    exact hn (Or.inr (Or.inr (hu.2 hres)))
  · intro hnres
    refine ⟨hv, ?_⟩
    rintro (h | h | h)
    · exact hng h
    · exact hnr h
    · exact hnres (hu.1 h)

/-- **`EightResidualCore` with the cap gives an admissible subject** when the least disparity is at most `resolutionCap8 = 64`. -/
theorem core_imp_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    (hc : EightResidualCore S) {a : ℕ} (haS : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) (hcap : a ≤ resolutionCap8) : Admissible v k := by
  have hapos := hasDisp_pos hv.2.injective hS haS
  exact (admissible_iff_not_resolution hv hS hc.no_common_factor hc.eight hc.spread haS hamin).2
    (hc.no_small_resolution a hapos hcap 0)

/-- **The gap**: with the cap removed, the d_min-clear sets are exactly the unblocked class, proved for every real arrangement; the old `EightResidual` leaves them open for `min S > 64`. -/
theorem gap_exact {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    (hc : EightResidualCore S) {a : ℕ} (haS : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) (hres : ResolutionClears8 S a 0) :
    Proved v k ∧ ¬ Admissible v k := by
  have hiff := admissible_iff_not_resolution hv hS hc.no_common_factor hc.eight hc.spread haS hamin
  refine ⟨?_, fun h => (hiff.1 h) hres⟩
  exact Or.inr (Or.inr ((unblocked_iff_resolution hv.2.injective hS haS hamin).2 hres))

/-- Conversely, an admissible subject with integer disparities has a spread and a blocked d_min instant. -/
theorem admissible_imp_core_fields {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S)
    (h : Admissible v k) {a : ℕ} (haS : a ∈ S) (hamin : ∀ s ∈ S, a ≤ s) :
    (∃ a' ∈ S, ∃ b ∈ S, 7 * a' < b) ∧ ¬ ResolutionClears8 S a 0 := by
  have hinj := hv.2.injective
  obtain ⟨_, hn⟩ := h
  unfold Proved at hn
  push Not at hn
  obtain ⟨_, hnr, hnu⟩ := hn
  exact ⟨(spread_iff_not_ratio hinj hS).2 hnr, fun hres => hnu ((unblocked_iff_resolution hinj hS haS hamin).2 hres)⟩

#print axioms admissible_iff_not_resolution
#print axioms core_imp_admissible
#print axioms gap_exact
#print axioms admissible_imp_core_fields

end Fresh.EightResidualLink
