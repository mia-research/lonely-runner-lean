import Mathlib
import Fresh.Framework

/-!
# Localisation (v9 sections 4 and 5), native

Task B of the fresh development (2026-10-07).  Imports only Mathlib and `Fresh.Framework`.

* Circle-distance lemmas: `distInt` is symmetric, 1-periodic, at most `1/2`, zero at integers, and
  `1/8 ≤ distInt y` holds exactly when `y` lies in a window `[N + 1/8, N + 7/8]`.
* Theorem 7 (`lonely_ge_bound`): a lonely instant `t > 0` satisfies `1/(8 d_min) ≤ t`.
* Theorem 9 (`localisation`): the subject is isolated at some positive instant iff some flank `e` has an isolated
  opening `(n + 1/8)/e`.  The opening is constructed: it is the largest of the last openings before a lonely `t`.
* `candidateScaleForm_iff`: candidate (c) of `Framework.lean` is equivalent to `LonelyRunnerEight`.
* Theorem 10 (`certificate_iff`): for integer disparities, opening `j` of flank `e` is clear for `d` iff
  `d (8j+1) mod 8e ∈ [e, 7e]`.

Provenance.  The argument of `localisation` is that of `Flanks.exists_flank_of_lonely` /
`Flanks.lonely_iff_exists_flank` (existing repo, `LRC/Cascade/Flanks.lean`), which rests there on
`reading_complete`; here the step is re-derived directly (the window argument below), not copied.  The sign handling
(disparities are absolute values) corresponds to `lonelyAt_iff_lonely_diffSet` (`LRC/Cascade/Arrangement.lean`).
`lonely_ge_bound` is the bound used by `Spec/DoorsN.lean`; `certificate_iff` corresponds to the certificate of P§6 /
`Flanks.clear_of_residue_band`.  Every proof here was written for this file.

No counting or covering step is used anywhere in this file.
-/

open Classical

namespace Fresh.Localisation

open Fresh

/-! ## Circle distance -/

/-- `distInt` is the least distance to an integer. -/
theorem distInt_le (x : ℝ) (z : ℤ) : distInt x ≤ |x - z| := round_le x z

#print axioms distInt_le

theorem distInt_nonneg (x : ℝ) : 0 ≤ distInt x := abs_nonneg _

#print axioms distInt_nonneg

theorem distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := abs_sub_round x

#print axioms distInt_le_half

theorem distInt_intCast (z : ℤ) : distInt (z : ℝ) = 0 := by
  unfold distInt; simp

#print axioms distInt_intCast

theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  apply le_antisymm
  · have := distInt_le (-x) (-round x)
    calc distInt (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := this
      _ = distInt x := by unfold distInt; push_cast; rw [← abs_neg]; ring_nf
  · have := distInt_le x (-round (-x))
    calc distInt x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := this
      _ = distInt (-x) := by unfold distInt; push_cast; rw [← abs_neg]; ring_nf

#print axioms distInt_neg

theorem distInt_add_int (x : ℝ) (z : ℤ) : distInt (x + z) = distInt x := by
  unfold distInt; rw [round_add_intCast]; push_cast; ring_nf

#print axioms distInt_add_int

/-- 1-periodicity. -/
theorem distInt_add_one (x : ℝ) : distInt (x + 1) = distInt x := by
  simpa using distInt_add_int x 1

#print axioms distInt_add_one

theorem distInt_abs (x : ℝ) : distInt |x| = distInt x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact distInt_neg x

#print axioms distInt_abs

/-- Clearance is a statement about every integer. -/
theorem le_distInt_iff (c x : ℝ) : c ≤ distInt x ↔ ∀ z : ℤ, c ≤ |x - z| := by
  constructor
  · intro h z; exact h.trans (distInt_le x z)
  · intro h; exact h (round x)

#print axioms le_distInt_iff

/-- The window: a point in `[N + 1/8, N + 7/8]` is clear. -/
theorem clear_of_window {y : ℝ} (N : ℤ) (h1 : (N : ℝ) + 1 / 8 ≤ y) (h2 : y ≤ (N : ℝ) + 7 / 8) :
    (1 / 8 : ℝ) ≤ distInt y := by
  rw [le_distInt_iff]
  intro z
  rcases le_or_gt z N with hz | hz
  · have : (z : ℝ) ≤ N := by exact_mod_cast hz
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : (N : ℝ) + 1 ≤ z := by exact_mod_cast hz
    rw [abs_of_nonpos (by linarith)]; linarith

#print axioms clear_of_window

/-- Clearance read through the floor: `1/8 ≤ distInt y` iff the fractional part lies in `[1/8, 7/8]`. -/
theorem clear_iff_fract (y : ℝ) :
    (1 / 8 : ℝ) ≤ distInt y ↔ 1 / 8 ≤ Int.fract y ∧ Int.fract y ≤ 7 / 8 := by
  constructor
  · intro h
    rw [le_distInt_iff] at h
    have h0 := h ⌊y⌋
    have h1 := h (⌊y⌋ + 1)
    have hf0 := Int.fract_nonneg y
    have hf1 := Int.fract_lt_one y
    unfold Int.fract at hf0 hf1 ⊢
    push_cast at h1
    rw [abs_of_nonneg hf0] at h0
    rw [abs_of_neg (by linarith)] at h1
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    apply clear_of_window ⌊y⌋
    · unfold Int.fract at h1; linarith
    · unfold Int.fract at h2; linarith

#print axioms clear_iff_fract

/-! ## Disparities of an arrangement -/

theorem mem_disparitySet {v : Fin 8 → ℝ} {k : Fin 8} {e : ℝ} :
    e ∈ disparitySet v k ↔ ∃ i, i ≠ k ∧ |v i - v k| = e := by
  unfold disparitySet; simp [Finset.mem_image, Finset.mem_erase]

#print axioms mem_disparitySet

/-- In an arrangement every disparity is positive (speeds pairwise distinct). -/
theorem disparity_pos {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {e : ℝ}
    (he : e ∈ disparitySet v k) : 0 < e := by
  obtain ⟨i, hik, rfl⟩ := mem_disparitySet.mp he
  apply abs_pos.mpr
  intro h
  exact hik (hv.2 (sub_eq_zero.mp h))

#print axioms disparity_pos

theorem disparitySet_nonempty (v : Fin 8 → ℝ) (k : Fin 8) : (disparitySet v k).Nonempty := by
  unfold disparitySet
  apply Finset.Nonempty.image
  refine ⟨k + 1, ?_⟩
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  intro h
  have := congrArg (fun x => x - k) h
  simp at this

#print axioms disparitySet_nonempty

/-- A sign on the speed difference does not change the circle distance. -/
theorem distInt_abs_mul (x t : ℝ) : distInt (|x| * t) = distInt (x * t) := by
  rcases abs_choice x with h | h <;> rw [h]
  rw [neg_mul, distInt_neg]

#print axioms distInt_abs_mul

/-- Isolation at `t` read on the disparity set: signs do not matter. -/
theorem isolatedAt_iff (v : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    IsolatedAt v k t ↔ ∀ d ∈ disparitySet v k, (1 / 8 : ℝ) ≤ distInt (d * t) := by
  constructor
  · intro h d hd
    obtain ⟨i, hik, rfl⟩ := mem_disparitySet.mp hd
    rw [distInt_abs_mul]; exact h i hik
  · intro h i hik
    have := h _ (mem_disparitySet.mpr ⟨i, hik, rfl⟩)
    rwa [distInt_abs_mul] at this

#print axioms isolatedAt_iff

/-! ## Theorem 7: the bound -/

/-- **Theorem 7** (v9 section 4).  A lonely instant `t > 0` satisfies `t ≥ 1/(8 d_min)`.  Only the nearest runner
is used: before `1/(8 d_min)` it has not yet left the subject's eighth. -/
theorem lonely_ge_bound {v : Fin 8 → ℝ} (hv : IsArrangement v) {k : Fin 8} {m t : ℝ}
    (hm : IsDmin v k m) (ht : 0 < t) (hiso : IsolatedAt v k t) : 1 / (8 * m) ≤ t := by
  have hmem : m ∈ disparitySet v k := hm.1
  have hm0 : 0 < m := disparity_pos hv hmem
  have hc := (isolatedAt_iff v k t).mp hiso m hmem
  by_contra hlt
  rw [not_le] at hlt
  have hmt : m * t < 1 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at hlt
    nlinarith
  have := distInt_le (m * t) 0
  simp only [Int.cast_zero, sub_zero] at this
  rw [abs_of_pos (by positivity)] at this
  linarith

#print axioms lonely_ge_bound

/-! ## Theorem 9: localisation -/

/-- The last opening of flank `e` at or before `t`: `(⌊e t⌋ + 1/8)/e`. -/
noncomputable def lastOpening (e t : ℝ) : ℝ := (((⌊e * t⌋ : ℤ) : ℝ) + 1 / 8) / e

/-- At a lonely instant, the last opening of every clear flank lies at or before `t`. -/
theorem lastOpening_le {e t : ℝ} (he : 0 < e) (hc : (1 / 8 : ℝ) ≤ distInt (e * t)) :
    lastOpening e t ≤ t := by
  have hf := ((clear_iff_fract _).mp hc).1
  unfold Int.fract at hf
  unfold lastOpening
  rw [div_le_iff₀ he]
  linarith

#print axioms lastOpening_le

/-- The window step.  If `d` is clear at `t`, and `s ≤ t` lies at or after `d`'s last opening, then `d` is clear at
`s`: between its last opening `⌊dt⌋ + 1/8` and `dt ≤ ⌊dt⌋ + 7/8` the reading never leaves the window. -/
theorem clear_between {d s t : ℝ} (hd : 0 < d) (hc : (1 / 8 : ℝ) ≤ distInt (d * t))
    (hlo : lastOpening d t ≤ s) (hhi : s ≤ t) : (1 / 8 : ℝ) ≤ distInt (d * s) := by
  have hf := (clear_iff_fract _).mp hc
  unfold Int.fract at hf
  unfold lastOpening at hlo
  rw [div_le_iff₀ hd] at hlo
  apply clear_of_window ⌊d * t⌋
  · linarith
  · have : d * s ≤ d * t := mul_le_mul_of_nonneg_left hhi hd.le
    linarith [hf.2]

#print axioms clear_between

/-- Localisation on a set of positive disparities: a lonely `t > 0` gives a lonely opening `(n + 1/8)/e`
of some flank `e`, namely the latest of the last openings before `t`. -/
theorem exists_opening_of_lonely {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hne : ds.Nonempty)
    {t : ℝ} (ht : 0 < t) (hl : ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * t)) :
    ∃ e ∈ ds, ∃ n : ℕ, ∀ d ∈ ds, (1 / 8 : ℝ) ≤ distInt (d * (((n : ℝ) + 1 / 8) / e)) := by
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image ds (fun e => lastOpening e t) hne
  have he0 := hpos e he
  have hfl : (0 : ℤ) ≤ ⌊e * t⌋ := Int.floor_nonneg.mpr (by positivity)
  refine ⟨e, he, ⌊e * t⌋.toNat, fun d hd => ?_⟩
  have hcast : ((⌊e * t⌋.toNat : ℕ) : ℝ) = ((⌊e * t⌋ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hfl
  rw [hcast]
  exact clear_between (hpos d hd) (hl d hd) (hmax d hd) (lastOpening_le he0 (hl e he))

#print axioms exists_opening_of_lonely

/-- **Theorem 9 (Localisation)** (v9 section 5).  For an arrangement, the subject is isolated at some positive instant
iff some flank `e` (a disparity) has an isolated opening `(n + 1/8)/e`. -/
theorem localisation {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) :
    Isolation v k ↔
      ∃ e ∈ disparitySet v k, ∃ n : ℕ, IsolatedAt v k (((n : ℝ) + 1 / 8) / e) := by
  constructor
  · rintro ⟨t, ht, hiso⟩
    obtain ⟨e, he, n, hn⟩ := exists_opening_of_lonely (fun d hd => disparity_pos hv hd)
      (disparitySet_nonempty v k) ht ((isolatedAt_iff v k t).mp hiso)
    exact ⟨e, he, n, (isolatedAt_iff v k _).mpr hn⟩
  · rintro ⟨e, he, n, hiso⟩
    refine ⟨_, ?_, hiso⟩
    have := disparity_pos hv he
    positivity

#print axioms localisation

/-! ## Candidate (c) -/

/-- On an arrangement, a clear candidate scale is the same as an isolated flank opening. -/
theorem candidateScaleClear_iff {v : Fin 8 → ℝ} (k : Fin 8) :
    CandidateScaleClear (disparitySet v k) ↔
      ∃ e ∈ disparitySet v k, ∃ n : ℕ, IsolatedAt v k (((n : ℝ) + 1 / 8) / e) := by
  unfold CandidateScaleClear
  simp only [isolatedAt_iff]

#print axioms candidateScaleClear_iff

/-- **Classification of candidate (c)**: the candidate-scale form is equivalent to the conjecture at n = 8.  It is a
restatement through Theorem 9, so it carries no information beyond `LonelyRunnerEight`. -/
theorem candidateScaleForm_iff : CandidateScaleForm ↔ LonelyRunnerEight := by
  unfold CandidateScaleForm LonelyRunnerEight
  constructor
  · intro h v hv k
    exact (localisation hv k).mpr ((candidateScaleClear_iff k).mp (h v hv k))
  · intro h v hv k
    exact (candidateScaleClear_iff k).mpr ((localisation hv k).mp (h v hv k))

#print axioms candidateScaleForm_iff

/-! ## Theorem 10: the certificate for integer disparities -/

/-- The fractional part of `N / M` for integers, `M > 0`. -/
theorem fract_int_div {N M : ℤ} (hM : 0 < M) :
    Int.fract ((N : ℝ) / M) = ((N % M : ℤ) : ℝ) / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Int.fract_eq_iff]
  refine ⟨div_nonneg (by exact_mod_cast Int.emod_nonneg N hM.ne') hMr.le, ?_, ?_⟩
  · rw [div_lt_one hMr]; exact_mod_cast Int.emod_lt_of_pos N hM
  · refine ⟨N / M, ?_⟩
    have h := Int.emod_add_mul_ediv N M
    have h' : ((N % M : ℤ) : ℝ) + (M : ℝ) * ((N / M : ℤ) : ℝ) = N := by exact_mod_cast h
    field_simp
    linarith

#print axioms fract_int_div

/-- **Theorem 10, one runner** (v9 section 5).  For integers `d` and `e > 0`, the runner at `d` is clear at opening
`j` of flank `e` iff `d (8j+1) mod 8e` lies in `[e, 7e]`. -/
theorem certificate_clear_iff (d e : ℤ) (he : 0 < e) (j : ℕ) :
    (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * (((j : ℝ) + 1 / 8) / e)) ↔
      e ≤ d * (8 * j + 1) % (8 * e) ∧ d * (8 * j + 1) % (8 * e) ≤ 7 * e := by
  have he8 : (0 : ℤ) < 8 * e := by omega
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hx : (d : ℝ) * (((j : ℝ) + 1 / 8) / e) = ((d * (8 * j + 1) : ℤ) : ℝ) / ((8 * e : ℤ) : ℝ) := by
    push_cast; field_simp
  rw [hx, clear_iff_fract, fract_int_div he8]
  set r := d * (8 * j + 1) % (8 * e)
  have h8e : ((8 * e : ℤ) : ℝ) = 8 * (e : ℝ) := by push_cast; ring
  rw [h8e, le_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : (e : ℝ) ≤ r := by linarith
      exact_mod_cast this
    · have : (r : ℝ) ≤ 7 * e := by linarith
      exact_mod_cast this
  · rintro ⟨h1, h2⟩
    have h1' : (e : ℝ) ≤ r := by exact_mod_cast h1
    have h2' : (r : ℝ) ≤ 7 * e := by exact_mod_cast h2
    constructor <;> linarith

#print axioms certificate_clear_iff

/-- **Theorem 10 (certificate)** (v9 section 5).  For a set of integer disparities and an integer flank `e > 0`,
opening `j` of `e` is lonely iff `d (8j+1) mod 8e ∈ [e, 7e]` for every disparity `d`. -/
theorem certificate_iff (D : Finset ℤ) (e : ℤ) (he : 0 < e) (j : ℕ) :
    (∀ d ∈ D, (1 / 8 : ℝ) ≤ distInt ((d : ℝ) * (((j : ℝ) + 1 / 8) / e))) ↔
      ∀ d ∈ D, e ≤ d * (8 * j + 1) % (8 * e) ∧ d * (8 * j + 1) % (8 * e) ≤ 7 * e := by
  exact forall₂_congr fun d _ => certificate_clear_iff d e he j

#print axioms certificate_iff

/-- The certificate is periodic in `j` with period `e`: opening `j + e` has the same residues as opening `j`. -/
theorem certificate_periodic (d : ℤ) (e : ℕ) (j : ℕ) :
    d * (8 * ((j + e : ℕ) : ℤ) + 1) % (8 * (e : ℤ)) = d * (8 * (j : ℤ) + 1) % (8 * (e : ℤ)) := by
  have : d * (8 * ((j + e : ℕ) : ℤ) + 1) = d * (8 * j + 1) + (8 * (e : ℤ)) * d := by push_cast; ring
  rw [this, Int.add_mul_emod_self_left]

#print axioms certificate_periodic

end Fresh.Localisation
