import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Prop11

/-!
# BHK §5 — Case 5.1 (`v₁ = k·D`, `k ≥ 3`): the triple-configuration argument

Bohman–Holzman–Kleitman 2001, EJC **8** (2001) R3, §5, Case 5.1 (pp. 14–16).

We are in the case `{v₁ t₀} = 0` (runner 1 at the origin whenever runner 3
passes runner 2), with `t₀ v₁ = k` for an integer `k ≥ 3`.  In speed terms this
is `v₁ = k·D` where `D = v₃ − v₂`.  When `k ≥ 3` there is no single 123-gap of
length `2/3`, so Lemma 4 does not apply directly.  BHK's idea: there *usually*
are two or more nearby 123-gaps of length `≥ 1/2` ("triple/multiple
configurations"), which force `x₄ = v₃/v₄` into two incompatible ranges
(eqns (27)/(30) vs (33)), a contradiction — except in four narrow `x₁`-windows,
handled explicitly in Cases 5.1.1 / 5.1.2.

Everything is in *real-time* units (`t : ℝ`, `circDist (vᵢ · t)`).  BHK's
normalised length `L` (taken with `v₃ = 1`) is real-time length `L / v₃`; the
"23-closeness window" `j k x₁ ≤ t ≤ (j+1/6) k x₁` is, in real time,
`{D·t} ≤ 1/6` (since `k x₁ = v₃/D` normalised `= 1/D` real-time).

## Status
Foundational geometry (the `circDist` triangle inequality, the runner-1 period
`1/D`, and the 2,3-closeness lemma) is proved here.  The configuration counting
(Claims 9–10, eqns (26)–(33)) and the two explicit sub-cases remain as
faithfully-stated `sorry`s feeding `bhk_s5_case51_main`.

## Source
T. Bohman, R. Holzman, D. Kleitman, *Six Lonely Runners*, EJC **8** (2001) R3,
§5, Case 5.1, pp. 14–16.
-/

open MeasureTheory Set

namespace BHK

/-! ## Foundational `circDist` geometry -/

/-- `circDist x ≤ |x − m|` for every integer `m`: the circle distance is at most
    the distance to any integer. -/
lemma circDist_le_abs_sub_int (x : ℝ) (m : ℤ) : circDist x ≤ |x - (m : ℝ)| := by
  rw [circDist_eq_infDist, ← Real.dist_eq]
  exact Metric.infDist_le_dist_of_mem ⟨m, rfl⟩

/-- `circDist` is realised by an integer: `∃ m, circDist x = |x − m|`.  The
    nearest integer is `⌊x⌋` (when `{x} ≤ 1/2`) or `⌊x⌋ + 1` (otherwise). -/
lemma circDist_exists_int (x : ℝ) : ∃ m : ℤ, circDist x = |x - (m : ℝ)| := by
  have hfr0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hfr1 : Int.fract x < 1 := Int.fract_lt_one x
  by_cases h : Int.fract x ≤ 1 / 2
  · refine ⟨⌊x⌋, ?_⟩
    have hxe : x - (⌊x⌋ : ℝ) = Int.fract x := by rw [Int.fract]
    rw [hxe, abs_of_nonneg hfr0]
    unfold circDist
    rw [min_eq_left (show Int.fract x ≤ 1 - Int.fract x by linarith)]
  · rw [not_le] at h
    refine ⟨⌊x⌋ + 1, ?_⟩
    have hxe : x - ((⌊x⌋ + 1 : ℤ) : ℝ) = -(1 - Int.fract x) := by
      rw [Int.fract]; push_cast; ring
    rw [hxe, abs_neg, abs_of_nonneg (by linarith)]
    unfold circDist
    rw [min_eq_right (show 1 - Int.fract x ≤ Int.fract x by linarith)]

/-- **Triangle inequality for `circDist`** (the circle is a metric space):
    `circDist a ≤ circDist b + circDist (a − b)`. -/
lemma circDist_triangle (a b : ℝ) :
    circDist a ≤ circDist b + circDist (a - b) := by
  obtain ⟨m, hm⟩ := circDist_exists_int b
  obtain ⟨k, hk⟩ := circDist_exists_int (a - b)
  calc circDist a ≤ |a - ((m + k : ℤ) : ℝ)| := circDist_le_abs_sub_int a (m + k)
    _ = |(b - (m : ℝ)) + ((a - b) - (k : ℝ))| := by push_cast; ring_nf
    _ ≤ |b - (m : ℝ)| + |(a - b) - (k : ℝ)| := abs_add_le _ _
    _ = circDist b + circDist (a - b) := by rw [hm, hk]

/-- Lower-bound form: `circDist a ≥ circDist b − circDist (a − b)`.  If runner
    `b` is safe with margin exceeding the closeness `circDist (a − b)`, runner
    `a` is safe too. -/
lemma circDist_ge_sub (a b : ℝ) :
    circDist a ≥ circDist b - circDist (a - b) := by
  have h := circDist_triangle b a
  have hsymm : circDist (b - a) = circDist (a - b) := by
    rw [show b - a = -(a - b) from by ring, circDist.symm_neg]
  rw [hsymm] at h; linarith

/-! ## Case 5.1 specific structure -/

/-- In Case 5.1, `D = v₃ − v₂ > 0`. -/
lemma bhk_s5_case51_D_pos (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds) (D : ℕ)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩) : 0 < D := by
  have h12 : speeds ⟨1, by omega⟩ < speeds ⟨2, by omega⟩ := by
    apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
  omega

/-- Real cast of `D`: `(D : ℝ) = v₃ − v₂`. -/
lemma bhk_s5_case51_D_cast (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds) (D : ℕ)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩) :
    (D : ℝ) = (speeds ⟨2, by omega⟩ : ℝ) - (speeds ⟨1, by omega⟩ : ℝ) := by
  have h12 : speeds ⟨1, by omega⟩ ≤ speeds ⟨2, by omega⟩ := by
    apply le_of_lt; apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
  rw [hD, Nat.cast_sub h12]

/-- **Runner 1 has period `1/D`.**  Since `v₁ = k·D`, `D ∣ v₁`, so advancing
    time by `1/D` leaves runner 1's circle-distance unchanged. -/
lemma bhk_s5_case51_period1 (speeds : Fin 5 → ℕ) (k D : ℕ) (hDpos : 0 < D)
    (hkD : speeds ⟨0, by omega⟩ = D * k) (t : ℝ) :
    circDist ((speeds ⟨0, by omega⟩ : ℝ) * (t + 1 / D))
      = circDist ((speeds ⟨0, by omega⟩ : ℝ) * t) := by
  have hdvd : D ∣ speeds ⟨0, by omega⟩ := ⟨k, hkD⟩
  exact bhk_prop11_period (speeds ⟨0, by omega⟩) D hDpos hdvd t

/-- **2,3-closeness (BHK eqn (31)).**  Runner 3's circle distance is at least
    runner 2's minus the runner-`D` closeness:
    `circDist (v₃ t) ≥ circDist (v₂ t) − circDist (D t)`.  When `circDist (D t)`
    is small (the window `{D·t} ≤ 1/6`), a safe runner 2 with margin forces a
    safe runner 3, which is what lengthens the 23-gap in Case 5.1. -/
lemma bhk_s5_case51_runner3_close (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (D : ℕ) (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩) (t : ℝ) :
    circDist ((speeds ⟨2, by omega⟩ : ℝ) * t)
      ≥ circDist ((speeds ⟨1, by omega⟩ : ℝ) * t) - circDist ((D : ℝ) * t) := by
  have hDcast := bhk_s5_case51_D_cast speeds hmono D hD
  have hkey : (speeds ⟨2, by omega⟩ : ℝ) * t - (speeds ⟨1, by omega⟩ : ℝ) * t
      = (D : ℝ) * t := by rw [hDcast]; ring
  have h := circDist_ge_sub ((speeds ⟨2, by omega⟩ : ℝ) * t)
    ((speeds ⟨1, by omega⟩ : ℝ) * t)
  rwa [hkey] at h

/-! ## The configuration counting (BHK Claims 9–10, eqns (26)–(33))

These are the heart of Case 5.1 and remain to be formalised.  The configuration
existence (how triple/multiple configurations arise from `k ≥ 3`, eqns
(31)–(33)), Claims 9–10 (no 4-block in `I₂`, `I₁`, `I₃`, giving (26)), and the
counting (27)/(30) plus the two explicit sub-cases (5.1.1, 5.1.2) go here.
-/

/-- **Case 5.1 main argument.**  For Case-5.1 speeds (`v₁ = k·D`, `k ≥ 3`,
    `D = v₃ − v₂`, `3 v₁ < v₃`, `gcd = 1`), there is a time at which every runner
    is `≥ 1/6` from the origin.  *Argument under construction* — the
    configuration counting (Claims 9–10, eqns (26)–(33)) and the two explicit
    sub-cases (5.1.1, 5.1.2) remain. -/
theorem bhk_s5_case51_main (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) :
    ∃ t : ℝ, ∀ i, circDist ((speeds i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  sorry

end BHK
