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

/-- **Claim 9 arithmetic core (main case).**  The flanking pieces of `I₁`, `I₃`
    around a 4-block in `I₂` sum to `5/(3v₄) − 1/(2v₃)` and are each `< 1/(3v₅)`,
    so `5/(3v₄) − 1/(2v₃) < 2/(3v₅)`; with `v₄ < v₅` and `3v₄ < 4v₃` (eqn (22))
    this is impossible. -/
lemma bhk_s5_case51_claim9_arithA (v3 v4 v5 : ℝ) (hv3 : 0 < v3) (hv4 : 0 < v4)
    (h45 : v4 < v5) (h22 : 3 * v4 < 4 * v3)
    (h : 5 / (3 * v4) - 1 / (2 * v3) < 2 / (3 * v5)) : False := by
  have step1 : (2 : ℝ) / (3 * v5) ≤ 2 / (3 * v4) := by gcongr
  have h2 : 5 / (3 * v4) - 1 / (2 * v3) < 2 / (3 * v4) := by linarith
  have hpos : (0 : ℝ) < 6 * v3 * v4 := by positivity
  have e : (5 / (3 * v4) - 1 / (2 * v3)) * (6 * v3 * v4) = 10 * v3 - 3 * v4 := by
    field_simp; ring
  have e2 : (2 / (3 * v4)) * (6 * v3 * v4) = 4 * v3 := by field_simp; ring
  have h3 : 10 * v3 - 3 * v4 < 4 * v3 := by
    nlinarith [mul_lt_mul_of_pos_right h2 hpos, e, e2]
  linarith

/-- **Claim 9 arithmetic core (degenerate case).**  If a whole flank (`I₁` or
    `I₃`, length `1/(2v₃)`) lies in `B₅`, then `1/(2v₃) < 1/(3v₅)`, impossible
    since `v₃ < v₅`. -/
lemma bhk_s5_case51_claim9_arithBC (v3 v5 : ℝ) (hv3 : 0 < v3) (h35 : v3 < v5)
    (h : 1 / (2 * v3) < 1 / (3 * v5)) : False := by
  have step : (1 : ℝ) / (3 * v5) ≤ 1 / (3 * v3) := by gcongr
  have step2 : (1 : ℝ) / (3 * v3) < 1 / (2 * v3) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-! ## The configuration counting (BHK Claims 9–10, eqns (26)–(33))

These are the heart of Case 5.1 and remain to be formalised.  The configuration
existence (how triple/multiple configurations arise from `k ≥ 3`, eqns
(31)–(33)), Claims 9–10 (no 4-block in `I₂`, `I₁`, `I₃`, giving (26)), and the
counting (27)/(30) plus the two explicit sub-cases (5.1.1, 5.1.2) go here.
-/

/-- **BHK Claim 9.**  If the flanks `I₁ = [t, t+1/(2v₃)]` and
    `I₃ = [t+1/v₃, t+3/(2v₃)]` are covered by runners 4,5 and `3v₄ < 4v₃`
    (eqn (22)), then no runner-4 block fits strictly inside
    `I₂ = (t+1/(2v₃), t+1/v₃)`: there is no integer `j` with both
    `(j±1/6)/v₄ ∈ I₂`.  (BHK p. 14.)  The runner-4 block in `I₂` would force the
    flanking gap-pieces of `I₁`, `I₃` into `B₅`, and their lengths are too long
    for `bhk_lemma_4`/`gap_piece_bound`. -/
lemma bhk_s5_case51_claim9 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (t : ℝ)
    (hI1 : Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩)
    (hI3 : Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjL : t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hjR : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast this
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast this
  set v3 := (speeds ⟨2, by omega⟩ : ℝ) with hv3def
  set v4 := (speeds ⟨3, by omega⟩ : ℝ) with hv4def
  set v5 := (speeds ⟨4, by omega⟩ : ℝ) with hv5def
  have h35 : v3 < v5 := lt_trans h34 h45
  -- Block centre relative to `t`; this makes `t` cancel in all the algebra.
  set u := (j : ℝ) / v4 - t with hu
  have hu_lo : 1 / (2 * v3) + 1 / (6 * v4) ≤ u := by
    have e : ((j : ℝ) - 1 / 6) / v4 = u + t - 1 / (6 * v4) := by rw [hu]; field_simp; ring
    rw [e] at hjL; linarith
  have hu_hi : u ≤ 1 / v3 - 1 / (6 * v4) := by
    have e : ((j : ℝ) + 1 / 6) / v4 = u + t + 1 / (6 * v4) := by rw [hu]; field_simp; ring
    rw [e] at hjR; linarith
  -- Cleared monotonicity facts (all reduce to `v₄ < 2v₃`, from eqn (22)).
  have hkey1 : (1 : ℝ) / v3 - 1 / (6 * v4) ≤ 1 / (2 * v3) + 5 / (6 * v4) := by
    rw [div_sub_div _ _ (ne_of_gt hv3) (by positivity),
      div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hv3 hv4) (show (0 : ℝ) < 2 * v3 - v4 by linarith)]
  have hkey2 : (1 : ℝ) / v3 - 5 / (6 * v4) ≤ 1 / (2 * v3) + 1 / (6 * v4) := by
    rw [div_sub_div _ _ (ne_of_gt hv3) (by positivity),
      div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hv3 hv4) (show (0 : ℝ) < 2 * v3 - v4 by linarith)]
  -- The "always" facts: the inner ends of the two gap-pieces lie inside I₁, I₃.
  have hF1 : ((j : ℝ) - 5 / 6) / v4 ≤ t + 1 / (2 * v3) := by
    have e : ((j : ℝ) - 5 / 6) / v4 = u + t - 5 / (6 * v4) := by rw [hu]; field_simp; ring
    rw [e]; have := le_trans hu_hi hkey1; linarith
  have hF2 : t + 1 / v3 ≤ ((j : ℝ) + 5 / 6) / v4 := by
    have e : ((j : ℝ) + 5 / 6) / v4 = u + t + 5 / (6 * v4) := by rw [hu]; field_simp; ring
    rw [e]; have := le_trans hkey2 hu_lo; linarith
  have hab1 : t ≤ t + 1 / (2 * v3) := by
    have : (0 : ℝ) < 1 / (2 * v3) := by positivity
    linarith
  have hab3 : t + 1 / v3 ≤ t + 3 / (2 * v3) := by
    have : (1 : ℝ) / v3 ≤ 3 / (2 * v3) := by
      rw [div_le_div_iff₀ hv3 (by positivity)]; nlinarith [hv3]
    linarith
  by_cases hB : ((j : ℝ) - 5 / 6) / v4 < t
  · -- I₁ lies entirely in the runner-4 gap `(j-1)` ⇒ I₁ ⊆ B₅.
    have hbnd : (t + 1 / (2 * v3)) - t < 1 / (3 * v5) :=
      gap_piece_bound speeds hpos t (t + 1 / (2 * v3)) hab1 hI1 (j - 1) t (t + 1 / (2 * v3))
        (le_refl t) (le_refl _) hab1
        (by rw [show (((j - 1 : ℤ) : ℝ) + 1 / 6) / v4 = ((j : ℝ) - 5 / 6) / v4 from by
              push_cast; ring]; exact le_of_lt hB)
        (by rw [show (((j - 1 : ℤ) : ℝ) + 5 / 6) / v4 = ((j : ℝ) - 1 / 6) / v4 from by
              push_cast; ring]; exact hjL)
    exact bhk_s5_case51_claim9_arithBC v3 v5 hv3 h35 (by linarith)
  · push_neg at hB
    by_cases hC : t + 3 / (2 * v3) < ((j : ℝ) + 5 / 6) / v4
    · -- I₃ lies entirely in the runner-4 gap `j` ⇒ I₃ ⊆ B₅.
      have hbnd : (t + 3 / (2 * v3)) - (t + 1 / v3) < 1 / (3 * v5) :=
        gap_piece_bound speeds hpos (t + 1 / v3) (t + 3 / (2 * v3)) hab3 hI3 j
          (t + 1 / v3) (t + 3 / (2 * v3)) (le_refl _) (le_refl _) hab3
          hjR (le_of_lt hC)
      refine bhk_s5_case51_claim9_arithBC v3 v5 hv3 h35 ?_
      have : (t + 3 / (2 * v3)) - (t + 1 / v3) = 1 / (2 * v3) := by field_simp; ring
      linarith [hbnd, this]
    · push_neg at hC
      -- Both gap-pieces are valid: piece₁ ⊆ I₁, piece₂ ⊆ I₃, each < 1/(3v₅).
      have hp1 : (t + 1 / (2 * v3)) - ((j : ℝ) - 5 / 6) / v4 < 1 / (3 * v5) :=
        gap_piece_bound speeds hpos t (t + 1 / (2 * v3)) hab1 hI1 (j - 1)
          (((j : ℝ) - 5 / 6) / v4) (t + 1 / (2 * v3)) hB (le_refl _) hF1
          (by rw [show (((j - 1 : ℤ) : ℝ) + 1 / 6) / v4 = ((j : ℝ) - 5 / 6) / v4 from by
                push_cast; ring])
          (by rw [show (((j - 1 : ℤ) : ℝ) + 5 / 6) / v4 = ((j : ℝ) - 1 / 6) / v4 from by
                push_cast; ring]; exact hjL)
      have hp2 : ((j : ℝ) + 5 / 6) / v4 - (t + 1 / v3) < 1 / (3 * v5) :=
        gap_piece_bound speeds hpos (t + 1 / v3) (t + 3 / (2 * v3)) hab3 hI3 j
          (t + 1 / v3) (((j : ℝ) + 5 / 6) / v4) (le_refl _) hC hF2
          hjR (le_refl _)
      refine bhk_s5_case51_claim9_arithA v3 v4 v5 hv3 hv4 h45 h22 ?_
      have hsum : ((t + 1 / (2 * v3)) - ((j : ℝ) - 5 / 6) / v4)
          + (((j : ℝ) + 5 / 6) / v4 - (t + 1 / v3)) = 5 / (3 * v4) - 1 / (2 * v3) := by
        field_simp; ring
      have htwo : (1 : ℝ) / (3 * v5) + 1 / (3 * v5) = 2 / (3 * v5) := by ring
      linarith [hp1, hp2, hsum, htwo]

/-- **The (30)/(33) incompatibility — BHK's contradiction.**  A multiple
    configuration with `l ≥ i` forces `x₄ > (6l+3)/(6l+4)` (eqn (30)); the
    configuration's origin (eqn (33)) forces `x₄ < (6i+2)/(6i+3)`.  Since
    `(6i+2)/(6i+3) ≤ (6l+3)/(6l+4)` whenever `i ≤ l` (the difference of
    cross-products is `6(l−i)+1 > 0`), the two bounds on `x₄ = v₃/v₄` are
    contradictory.  This is the logical climax of Case 5.1: every multiple
    configuration with `l ≥ i` is impossible. -/
lemma bhk_s5_case51_x4_incompatible (x₄ : ℝ) (i l : ℕ) (hil : i ≤ l)
    (h30 : (6 * (l : ℝ) + 3) / (6 * l + 4) < x₄)
    (h33 : x₄ < (6 * (i : ℝ) + 2) / (6 * i + 3)) : False := by
  have hl : (i : ℝ) ≤ l := by exact_mod_cast hil
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have d1 : (0 : ℝ) < 6 * (l : ℝ) + 4 := by positivity
  have d2 : (0 : ℝ) < 6 * (i : ℝ) + 3 := by positivity
  have hkey : (6 * (i : ℝ) + 2) / (6 * i + 3) ≤ (6 * (l : ℝ) + 3) / (6 * l + 4) := by
    rw [div_le_div_iff₀ d2 d1]; nlinarith [hl, hi0]
  linarith

/-- **BHK eqn (30) extraction.**  A multiple configuration of `l+1` gaps spanned
    by runner-4 blocks gives `(l + 2/3)·x₄ > l + 1/2` (eqn (29) arithmetic);
    hence `x₄ > (6l+3)/(6l+4)`.  This is the bound fed to
    `bhk_s5_case51_x4_incompatible`.  (`l = 1` recovers eqn (27), `x₄ > 9/10`.) -/
lemma bhk_s5_case51_eqn30 (x₄ : ℝ) (l : ℕ)
    (h : (l + 2 / 3) * x₄ > (l : ℝ) + 1 / 2) :
    (6 * (l : ℝ) + 3) / (6 * l + 4) < x₄ := by
  rw [div_lt_iff₀ (by positivity)]; nlinarith [h]

/-- **BHK eqn (33) extraction.**  The configuration's placement (`t = i + 1/3`)
    gives `(i + 1/2)·x₄ < i + 1/3`; hence `x₄ < (6i+2)/(6i+3)`.  The upper bound
    fed to `bhk_s5_case51_x4_incompatible`. -/
lemma bhk_s5_case51_eqn33 (x₄ : ℝ) (i : ℕ)
    (h : (i + 1 / 2) * x₄ < (i : ℝ) + 1 / 3) :
    x₄ < (6 * (i : ℝ) + 2) / (6 * i + 3) := by
  rw [lt_div_iff₀ (by positivity)]; nlinarith [h]

/-- **BHK eqn (22).**  If a 123-gap `I₁` of length `1/(2 v₃)` (BHK's normalised
    `1/2`) is covered by runners 4 and 5, then `x₄ > 3/4`, i.e. `3 v₄ < 4 v₃`.
    Direct from `bhk_lemma_4` (`|I₁| < 2/(3 v₄)`). -/
lemma bhk_s5_case51_x4_from_I1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) {a : ℝ}
    (hI : Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩) :
    3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ) := by
  have hv2 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hab : a ≤ a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) :=
    le_add_of_nonneg_right (by positivity)
  have hlen := bhk_lemma_4 speeds hmono hpos a
    (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) hab hI
  rw [add_sub_cancel_left] at hlen
  rw [div_lt_div_iff₀ (mul_pos (by norm_num) hv2) (mul_pos (by norm_num) hv3)] at hlen
  linarith

/-! ## Claim 10 tiling infrastructure

A **1234-gap** — an interval on which runners 1, 2, 3, 4 are all `≥ 1/6` from the
origin — is, under the covering hypothesis, covered by runner 5 *alone* (no other
runner can be near), hence lies in a single 5-block and is short (`< 1/(3 v₅)`).
This is the runner-5 analogue of `bhk_prop11_gap_covered`, and the basic counting
unit of Claim 10 (BHK p. 15). -/

/-- A 1234-gap (runners 1–4 all safe on `[a,b]`) is `⊆ B₅` under the covering
    hypothesis: every time is covered by some runner, and runners 1–4 are
    excluded, so runner 5 covers it. -/
lemma bhk_s5_case51_gap1234_subset (speeds : Fin 5 → ℕ)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    {a b : ℝ}
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    Set.Icc a b ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
  intro s hs
  obtain ⟨i, hi⟩ := hcover s
  fin_cases i
  · exact absurd hi (not_lt.mpr (hgap s hs 0))
  · exact absurd hi (not_lt.mpr (hgap s hs 1))
  · exact absurd hi (not_lt.mpr (hgap s hs 2))
  · exact absurd hi (not_lt.mpr (hgap s hs 3))
  · exact (mem_unsafeOf_iff speeds _ s).mpr hi

/-- **The 1234-gap length bound.**  A 1234-gap has length `< 1/(3 v₅)`: being
    `⊆ B₅`, it lies in a single 5-block (`block_length_bound`).  The runner-5
    analogue of `bhk_lemma_4` for `B₄ ∪ B₅`. -/
lemma bhk_s5_case51_gap1234_short (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    b - a < 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) :=
  block_length_bound speeds ⟨4, by omega⟩ (hpos _) a b hab
    (bhk_s5_case51_gap1234_subset speeds hcover hgap)

/-- **Runner 4 is safe on a 4-gap.**  If `t` lies in the `k`-th runner-4 gap
    `[(k+1/6)/v₄, (k+5/6)/v₄]`, then `circDist (v₄ t) ≥ 1/6`.  Used to upgrade a
    123-gap to a 1234-gap on the parts flanking a 4-block. -/
lemma bhk_s5_case51_runner4_safe_on_gap (speeds : Fin 5 → ℕ)
    (hv4 : 0 < speeds ⟨3, by omega⟩) (k : ℤ) (t : ℝ)
    (h1 : ((k : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ t)
    (h2 : t ≤ ((k : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) :
    (1 : ℝ) / 6 ≤ circDist ((speeds ⟨3, by omega⟩ : ℝ) * t) := by
  have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ hv4 k t h1 h2
  rw [mem_unsafeOf_iff] at hnot
  exact not_lt.mp hnot

/-- **Claim 10, eqn (24) — the `I₁` decomposition.**  If the 123-gap
    `I₁ = [t, t+1/(2v₃)]` contains a runner-4 block `[(j−1/6)/v₄, (j+1/6)/v₄]`
    (eqn (23)), then — under covering and `3v₄ < 4v₃` — the two pieces of `I₁`
    flanking the 4-block are 1234-gaps (each `< 1/(3v₅)`), so
    `1/(2v₃) < 2/(3v₅) + 1/(3v₄)`.  This is the second inequality of BHK eqn (24);
    it is the first assembly of the 1234-gap machinery. -/
lemma bhk_s5_case51_claim10_decomp (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hjt' : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      < 2 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) + 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  set v3 := (speeds ⟨2, by omega⟩ : ℝ) with hv3def
  set v4 := (speeds ⟨3, by omega⟩ : ℝ) with hv4def
  set v5 := (speeds ⟨4, by omega⟩ : ℝ) with hv5def
  have h12v3 : (1 : ℝ) / (2 * v3) ≤ 1 / v4 := one_div_le_one_div_of_le hv4 (by linarith)
  have hjj : ((j : ℝ) - 1 / 6) / v4 ≤ ((j : ℝ) + 1 / 6) / v4 := by
    rw [div_le_div_iff₀ hv4 hv4]; nlinarith [hv4]
  have hI1bound : ((j : ℝ) - 1 / 6) / v4 ≤ t + 1 / (2 * v3) := le_trans hjj hjt'
  have htj1 : t ≤ ((j : ℝ) + 1 / 6) / v4 := le_trans hjt hjj
  -- Positioning: block j-1 is left of I₁, block j+1 is right of I₁ (uses `3v₄<4v₃`).
  have hF1 : ((j : ℝ) - 5 / 6) / v4 ≤ t := by
    have e : ((j : ℝ) - 5 / 6) / v4 = ((j : ℝ) + 1 / 6) / v4 - 1 / v4 := by
      field_simp; ring
    linarith [hjt', h12v3, e]
  have hF2 : t + 1 / (2 * v3) ≤ ((j : ℝ) + 5 / 6) / v4 := by
    have e : ((j : ℝ) + 5 / 6) / v4 = ((j : ℝ) - 1 / 6) / v4 + 1 / v4 := by
      field_simp; ring
    linarith [hjt, h12v3, e]
  -- The left flank [t, (j-1/6)/v₄] is a 1234-gap.
  have hLshort : ((j : ℝ) - 1 / 6) / v4 - t < 1 / (3 * v5) := by
    apply bhk_s5_case51_gap1234_short speeds hpos hcover hjt
    intro s hs i
    fin_cases i
    · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 0
    · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 1
    · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 2
    · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) (j - 1) s
      · rw [show (((j - 1 : ℤ) : ℝ) + 1 / 6) / v4 = ((j : ℝ) - 5 / 6) / v4 from by
            push_cast; ring]
        linarith [hF1, hs.1]
      · rw [show (((j - 1 : ℤ) : ℝ) + 5 / 6) / v4 = ((j : ℝ) - 1 / 6) / v4 from by
            push_cast; ring]
        exact hs.2
  -- The right flank [(j+1/6)/v₄, t+1/(2v₃)] is a 1234-gap.
  have hRshort : (t + 1 / (2 * v3)) - ((j : ℝ) + 1 / 6) / v4 < 1 / (3 * v5) := by
    apply bhk_s5_case51_gap1234_short speeds hpos hcover hjt'
    intro s hs i
    fin_cases i
    · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 0
    · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 1
    · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 2
    · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) j s
      · exact hs.1
      · exact le_trans hs.2 hF2
  -- Sum the two flank lengths.
  have hsum : (((j : ℝ) - 1 / 6) / v4 - t) + ((t + 1 / (2 * v3)) - ((j : ℝ) + 1 / 6) / v4)
      = 1 / (2 * v3) - 1 / (3 * v4) := by field_simp; ring
  have htwo : (1 : ℝ) / (3 * v5) + 1 / (3 * v5) = 2 / (3 * v5) := by ring
  linarith [hLshort, hRshort, hsum, htwo]

/-- The left flank `[t, (j−1/6)/v₄]` of a 4-block in the 123-gap `I₁` is a
    1234-gap, hence `⊆ B₅`.  (Helper for eqn (24)'s distinct-5-blocks argument.) -/
lemma bhk_s5_case51_flank_left_subset (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt' : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    Set.Icc t (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h12v3 : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨3, by omega⟩ : ℝ) :=
    one_div_le_one_div_of_le hv4 (by linarith)
  have hjj : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [div_le_div_iff₀ hv4 hv4]; nlinarith [hv4]
  have hI1bound : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := le_trans hjj hjt'
  have hF1 : ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ t := by
    have e : ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    linarith [hjt', h12v3, e]
  apply bhk_s5_case51_gap1234_subset speeds hcover
  intro s hs i
  fin_cases i
  · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 0
  · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 1
  · exact hgap123 s ⟨hs.1, le_trans hs.2 hI1bound⟩ 2
  · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) (j - 1) s
    · rw [show (((j - 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
      linarith [hF1, hs.1]
    · rw [show (((j - 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
      exact hs.2

/-- The right flank `[(j+1/6)/v₄, t+1/(2v₃)]` of a 4-block in `I₁` is a 1234-gap,
    hence `⊆ B₅`. -/
lemma bhk_s5_case51_flank_right_subset (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) :
    Set.Icc (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ unsafeOf speeds ⟨4, by omega⟩ := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h12v3 : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨3, by omega⟩ : ℝ) :=
    one_div_le_one_div_of_le hv4 (by linarith)
  have hjj : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [div_le_div_iff₀ hv4 hv4]; nlinarith [hv4]
  have htj1 : t ≤ ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := le_trans hjt hjj
  have hF2 : t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    have e : ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) + 1 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    linarith [hjt, h12v3, e]
  apply bhk_s5_case51_gap1234_subset speeds hcover
  intro s hs i
  fin_cases i
  · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 0
  · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 1
  · exact hgap123 s ⟨le_trans htj1 hs.1, hs.2⟩ 2
  · apply bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) j s
    · exact hs.1
    · exact le_trans hs.2 hF2

/-- **Claim 10, eqn (24), first inequality** (`2x₅/3 < x₄/3`).  A 4-block
    `[(j−1/6)/v₄, (j+1/6)/v₄] ⊆ I₁` splits the 123-gap `I₁` into two 1234-gaps.
    Each lies in a single 5-block (`block_containment`), and the two 5-blocks are
    *distinct* (`I₁` is longer than one 5-block since `v₅ > v₃`); the 5-gap
    between them therefore lies inside the 4-block, forcing `2/(3v₅) < 1/(3v₄)`. -/
lemma bhk_s5_case51_claim10_5gap (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgap123 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (hjt : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hjt' : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    2 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h34 : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    have h45 : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    have : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := lt_trans h34 h45
    exact_mod_cast this
  -- Each flank is ⊆ B₅; pin it inside a single 5-block.
  have hLsub := bhk_s5_case51_flank_left_subset speeds hpos hcover t hgap123 h22 j hjt'
  have hRsub := bhk_s5_case51_flank_right_subset speeds hpos hcover t hgap123 h22 j hjt
  obtain ⟨k1, hk1a, hk1b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _) t
    (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) hjt hLsub
  obtain ⟨k2, hk2a, hk2b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) hjt' hRsub
  set v3 := (speeds ⟨2, by omega⟩ : ℝ) with hv3def
  set v4 := (speeds ⟨3, by omega⟩ : ℝ) with hv4def
  set v5 := (speeds ⟨4, by omega⟩ : ℝ) with hv5def
  -- The two 5-blocks `k1, k2` are distinct: I₁ is longer than one 5-block.
  have hv5_2v3 : (1 : ℝ) / 2 < v5 / (2 * v3) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hexp : v5 * (t + 1 / (2 * v3)) = v5 * t + v5 / (2 * v3) := by ring
  have hk12 : (k1 : ℝ) < (k2 : ℝ) := by linarith [hk1a, hk2b, hexp, hv5_2v3]
  have hk1k2R : (k1 : ℝ) + 1 ≤ (k2 : ℝ) := by
    have h1 : k1 < k2 := by exact_mod_cast hk12
    have h2 : k1 + 1 ≤ k2 := by omega
    exact_mod_cast h2
  -- The 5-gap between blocks k1, k2 lies inside the 4-block ⇒ width bound.
  have key : ((k2 : ℝ) - 1 / 6) - ((k1 : ℝ) + 1 / 6)
      < v5 * (((j : ℝ) + 1 / 6) / v4) - v5 * (((j : ℝ) - 1 / 6) / v4) := by
    linarith [hk1b, hk2a]
  have hdiff : v5 * (((j : ℝ) + 1 / 6) / v4) - v5 * (((j : ℝ) - 1 / 6) / v4)
      = v5 / (3 * v4) := by field_simp; ring
  have h23 : (2 : ℝ) / 3 < v5 / (3 * v4) := by rw [← hdiff]; linarith [key, hk1k2R]
  have h2v4v5 : 2 * v4 < v5 := by rw [lt_div_iff₀ (by positivity)] at h23; linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith

/-- **BHK eqn (24) ⟹ `1/4 < x₅ < 1/2`.**  From the two inequalities of eqn (24)
    (`2/(3v₅) < 1/(3v₄)` and `1/(2v₃) < 2/(3v₅) + 1/(3v₄)`) together with `x₄ < 1`
    (`v₃ < v₄`), the runner-5 reciprocal `x₅ = v₃/v₅` satisfies `x₅ < 1/2`
    (`2v₃ < v₅`) and `x₅ > 1/4` (`v₅ < 4v₃`). -/
lemma bhk_s5_case51_x5_bounds (v3 v4 v5 : ℝ) (hv3 : 0 < v3) (hv5 : 0 < v5) (h34 : v3 < v4)
    (h24a : 2 / (3 * v5) < 1 / (3 * v4))
    (h24b : 1 / (2 * v3) < 2 / (3 * v5) + 1 / (3 * v4)) :
    2 * v3 < v5 ∧ v5 < 4 * v3 := by
  have hv4 : 0 < v4 := lt_trans hv3 h34
  have hb : (1 : ℝ) / (3 * v4) < 1 / (3 * v3) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  refine ⟨?_, ?_⟩
  · -- `x₅ < 1/2`: `2/(3v₅) < 1/(3v₄) < 1/(3v₃)`.
    have h : (2 : ℝ) / (3 * v5) < 1 / (3 * v3) := lt_trans h24a hb
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h; linarith
  · -- `x₅ > 1/4`: `2/(3v₅) > 1/(2v₃) − 1/(3v₄) > 1/(6v₃)`.
    have e : (1 : ℝ) / (2 * v3) - 1 / (3 * v3) = 1 / (6 * v3) := by field_simp; ring
    have hlow : (1 : ℝ) / (6 * v3) < 2 / (3 * v5) := by linarith [h24b, hb, e]
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hlow; linarith

/-- **BHK: `x₄/3 + x₅/3 < 1/2`.**  From `x₅ < 1/2` (`2v₃ < v₅`) and `x₄ < 1`
    (`v₃ < v₄`): `1/(3v₄) + 1/(3v₅) < 1/(3v₃) + 1/(6v₃) = 1/(2v₃)`.  This is the
    bound that forces a 4-block into `I₃` (eqn (25)). -/
lemma bhk_s5_case51_x45_sum (v3 v4 v5 : ℝ) (hv3 : 0 < v3) (h34 : v3 < v4)
    (h2v3v5 : 2 * v3 < v5) :
    1 / (3 * v4) + 1 / (3 * v5) < 1 / (2 * v3) := by
  have hb1 : (1 : ℝ) / (3 * v4) < 1 / (3 * v3) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hb2 : (1 : ℝ) / (3 * v5) < 1 / (6 * v3) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have e : (1 : ℝ) / (3 * v3) + 1 / (6 * v3) = 1 / (2 * v3) := by field_simp; ring
  linarith [hb1, hb2, e]

/-- **Claim 10, steps D/E — the consecutive-5-blocks counting core (BHK p. 15).**
    The pure-arithmetic heart of Claim 10's contradiction.  Inputs are the
    runner-5 block indices `a₁, a₂, a₃` containing the three relevant 1234-gaps —
    the two flanks `g₁ = [t, (j−1/6)/v₄]`, `g₂ = [(j+1/6)/v₄, t+1/(2v₃)]` of `I₁`
    and the left flank `g₃ = [t+1/v₃, (j+5/6)/v₄]` of `I₃` — each pinned inside a
    single 5-block by `block_containment` (`hG·a` = left edge below the scaled
    left end, `hG·b` = scaled right end below the right edge), together with the
    upper `x₅` bound (`v₅ < 4v₃`, BHK `x₅ > 1/4`) and eqn (24a) (`2v₄ < v₅`); the
    lower bound `2v₃ < v₅` (BHK `x₅ < 1/2`) is implied by `2v₄ < v₅` and `v₃ < v₄`.

    *Step D*: `g₁, g₂` lie in **consecutive** 5-blocks (`a₂ = a₁+1`) — no 5-block
    fits the 4-block, since `v₅ < 4v₃ < 4v₄`.  The two consecutive blocks span the
    length-`1/(2v₃)` gap `I₁`, giving `v₅ < 8v₃/3` (BHK `4x₅/3 > 1/2`).
    *Step E*: that bound forces `g₂, g₃` into consecutive 5-blocks (`a₃ = a₂+1`) —
    no 5-block fits `I₂` — and the 4-gap between the two 4-blocks, spanned by the
    two consecutive 5-blocks, gives `v₅ < 2v₄` (BHK `4x₅/3 > 2x₄/3`), contradicting
    eqn (24a) `2v₄ < v₅`. -/
lemma bhk_s5_case51_claim10_count
    (v3 v4 v5 t : ℝ) (j a1 a2 a3 : ℤ)
    (hv3 : 0 < v3) (hv4 : 0 < v4)
    (hv54v3 : v5 < 4 * v3)
    (h34 : v3 < v4) (h24a : 2 * v4 < v5)
    (hG1a : (a1 : ℝ) - 1 / 6 < v5 * t)
    (hG1b : v5 * (((j : ℝ) - 1 / 6) / v4) < (a1 : ℝ) + 1 / 6)
    (hG2a : (a2 : ℝ) - 1 / 6 < v5 * (((j : ℝ) + 1 / 6) / v4))
    (hG2b : v5 * (t + 1 / (2 * v3)) < (a2 : ℝ) + 1 / 6)
    (hG3a : (a3 : ℝ) - 1 / 6 < v5 * (t + 1 / v3))
    (hG3b : v5 * (((j : ℝ) + 5 / 6) / v4) < (a3 : ℝ) + 1 / 6) :
    False := by
  have hv3' : v3 ≠ 0 := hv3.ne'
  have hv4' : v4 ≠ 0 := hv4.ne'
  have hv5 : 0 < v5 := by linarith
  -- Field bridges relating the scaled block edges.
  have hbrBlock : v5 * (((j : ℝ) + 1 / 6) / v4) - v5 * (((j : ℝ) - 1 / 6) / v4)
      = v5 / (3 * v4) := by field_simp; ring
  have hbrGap : v5 * (((j : ℝ) + 5 / 6) / v4) - v5 * (((j : ℝ) + 1 / 6) / v4)
      = 2 * v5 / (3 * v4) := by field_simp; ring
  have hbrI1 : v5 * (t + 1 / (2 * v3)) - v5 * t = v5 / (2 * v3) := by field_simp; ring
  have hbrI2 : v5 * (t + 1 / v3) - v5 * (t + 1 / (2 * v3)) = v5 / (2 * v3) := by
    field_simp; ring
  -- Magnitude bounds on the scaled block-edge gaps.
  have hBlockLt : v5 / (3 * v4) < 4 / 3 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hI1Gt : (1 : ℝ) < v5 / (2 * v3) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hGapGt : (2 : ℝ) / 3 < 2 * v5 / (3 * v4) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  -- Step D: `a₂ = a₁ + 1` (the I₁ flanks lie in consecutive 5-blocks).
  have hlow12 : (2 : ℝ) / 3 < (a2 : ℝ) - (a1 : ℝ) := by
    linarith [hG1a, hG2b, hbrI1, hI1Gt]
  have hupp12 : (a2 : ℝ) - (a1 : ℝ) < 2 := by
    linarith [hG1b, hG2a, hbrBlock, hBlockLt]
  have ha12 : a2 = a1 + 1 := by
    have hltz : a1 < a2 := by exact_mod_cast (by linarith : (a1 : ℝ) < a2)
    have hubz : a2 < a1 + 2 := by exact_mod_cast (by linarith : (a2 : ℝ) < a1 + 2)
    omega
  have ha2eq : (a2 : ℝ) = (a1 : ℝ) + 1 := by exact_mod_cast ha12
  -- Step D output: `v₅ < 8 v₃ / 3` (BHK `4x₅/3 > 1/2`), the I₁ two-block span.
  have hStepD : v5 / (2 * v3) < 4 / 3 := by linarith [hG1a, hG2b, hbrI1, ha2eq]
  -- Step E: `a₃ = a₂ + 1` (g₂, g₃ lie in consecutive 5-blocks).
  have hlow23 : (1 : ℝ) / 3 < (a3 : ℝ) - (a2 : ℝ) := by
    linarith [hG2a, hG3b, hbrGap, hGapGt]
  have hupp23 : (a3 : ℝ) - (a2 : ℝ) < 2 := by
    linarith [hG2b, hG3a, hbrI2, hStepD]
  have ha23 : a3 = a2 + 1 := by
    have hltz : a2 < a3 := by exact_mod_cast (by linarith : (a2 : ℝ) < a3)
    have hubz : a3 < a2 + 2 := by exact_mod_cast (by linarith : (a3 : ℝ) < a2 + 2)
    omega
  have ha3eq : (a3 : ℝ) = (a2 : ℝ) + 1 := by exact_mod_cast ha23
  -- Step E output: the 4-gap spanned by the two consecutive 5-blocks ⇒ `v₅ < 2 v₄`,
  -- contradicting eqn (24a) (`2 v₄ < v₅`).
  have hStepE : 2 * v5 / (3 * v4) < 4 / 3 := by linarith [hG2a, hG3b, hbrGap, ha3eq]
  have hv52v4 : v5 < 2 * v4 := by
    rw [div_lt_iff₀ (by positivity)] at hStepE; linarith
  linarith [h24a, hv52v4]

/-- **Claim 10 — no 4-block in `I₁` together with one in `I₃` (BHK p. 15).**
    The geometric wrapper of the D/E counting core.  Given the triple
    configuration (`I₁ = [t, t+1/(2v₃)]` and `I₃ = [t+1/v₃, t+3/(2v₃)]` are
    123-gaps, both `⊆ B₄ ∪ B₅` via the covering `hcover`), a 4-block in `I₁`
    (eqn (23): `h23a`/`h23b`) and the forced 4-block in `I₃` (eqn (25):
    `h25a`/`h25b`) are contradictory.  We extract the runner-5 blocks of the two
    `I₁` flanks (`flank_left/right_subset` + `block_containment`) and of the left
    `I₃` flank (`flank_left_subset` re-used at `t' = t+1/v₃`, `j' = j+1`), then
    invoke `bhk_s5_case51_claim10_count`.  This is the `(23) ∧ (25) ⇒ False` half
    of Claim 10; deriving (25) from (23) (eqn (25) geometry) is the separate
    `x₄/3 + x₅/3 < 1/2` step (`bhk_s5_case51_x45_sum`). -/
lemma bhk_s5_case51_claim10_contra (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (h25a : t + 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h25b : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  -- eqn (24) and the `x₅` bounds `2v₃ < v₅ < 4v₃`.
  have h24a := bhk_s5_case51_claim10_5gap speeds hmono hpos hcover t hgapI1 h22 j h23a h23b
  have h24b := bhk_s5_case51_claim10_decomp speeds hpos hcover t hgapI1 h22 j h23a h23b
  obtain ⟨_, hv54v3⟩ := bhk_s5_case51_x5_bounds _ _ _ hv3 hv5 h34 h24a h24b
  -- eqn (24a) in the form `2 v₄ < v₅`.
  have h24a' : 2 * (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at h24a; linarith
  -- The two `I₁` flanks are 1234-gaps `⊆ B₅`; pin each in a single 5-block.
  have hL1 := bhk_s5_case51_flank_left_subset speeds hpos hcover t hgapI1 h22 j h23b
  have hR1 := bhk_s5_case51_flank_right_subset speeds hpos hcover t hgapI1 h22 j h23a
  obtain ⟨a1, hG1a, hG1b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _) t
    (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) h23a hL1
  obtain ⟨a2, hG2a, hG2b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) h23b hR1
  -- The left `I₃` flank: re-use `flank_left_subset` at `t' = t+1/v₃`, `j' = j+1`.
  have hL3 := bhk_s5_case51_flank_left_subset speeds hpos hcover
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) hgapI3 h22 (j + 1)
    (by rw [show (((j + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]; exact h25b)
  rw [show (((j + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring] at hL3
  obtain ⟨a3, hG3a, hG3b⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    h25a hL3
  exact bhk_s5_case51_claim10_count (speeds ⟨2, by omega⟩ : ℝ) (speeds ⟨3, by omega⟩ : ℝ)
    (speeds ⟨4, by omega⟩ : ℝ) t j a1 a2 a3 hv3 hv4 hv54v3 h34 h24a'
    hG1a hG1b hG2a hG2b hG3a hG3b

/-- **A 4-safe sub-interval of `I₁` is a short 1234-gap.**  Companion to
    `bhk_s5_case51_I3_4safe_short` for the gap `I₁ = [t, t+1/(2v₃)]`: if
    `[a,b] ⊆ I₁` lies in the `k`-th runner-4 gap `[(k+1/6)/v₄, (k+5/6)/v₄]`, then
    `[a,b]` is a 1234-gap, so `b−a < 1/(3v₅)` (`gap1234_short`). -/
lemma bhk_s5_case51_I1_4safe_short (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (k : ℤ) (a b : ℝ) (hab : a ≤ b)
    (ha : t ≤ a) (hb : b ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hg1 : ((k : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ a)
    (hg2 : b ≤ ((k : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) :
    b - a < 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) := by
  apply bhk_s5_case51_gap1234_short speeds hpos hcover hab
  intro s hs i
  fin_cases i
  · exact hgapI1 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 0
  · exact hgapI1 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 1
  · exact hgapI1 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 2
  · exact bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) k s
      (le_trans hg1 hs.1) (le_trans hs.2 hg2)

/-- **Helper for eqn (25): a 4-safe sub-interval of `I₃` is a short 1234-gap.**
    If `[a,b] ⊆ I₃ = [t+1/v₃, t+3/(2v₃)]` lies in the `k`-th runner-4 gap
    `[(k+1/6)/v₄, (k+5/6)/v₄]`, then `[a,b]` is a 1234-gap, so `b−a < 1/(3v₅)`
    (`gap1234_short`).  Runner-5 analogue of the I₁ flank helpers, for I₃. -/
lemma bhk_s5_case51_I3_4safe_short (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (k : ℤ) (a b : ℝ) (hab : a ≤ b)
    (ha : t + 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ a)
    (hb : b ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hg1 : ((k : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ a)
    (hg2 : b ≤ ((k : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) :
    b - a < 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) := by
  apply bhk_s5_case51_gap1234_short speeds hpos hcover hab
  intro s hs i
  fin_cases i
  · exact hgapI3 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 0
  · exact hgapI3 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 1
  · exact hgapI3 s ⟨le_trans ha hs.1, le_trans hs.2 hb⟩ 2
  · exact bhk_s5_case51_runner4_safe_on_gap speeds (hpos ⟨3, by omega⟩) k s
      (le_trans hg1 hs.1) (le_trans hs.2 hg2)

/-- **BHK eqn (25): the forced 4-block in `I₃`.**  Given a 4-block in `I₁`
    (eqn (23)) and `I₃ = [t+1/v₃, t+3/(2v₃)] ⊆ B₄ ∪ B₅` (via `hcover` + the I₃
    123-gap), the `(j+1)`-th runner-4 block lies inside `I₃`.  The `j`-th block is
    left of `I₃` and the `(j+2)`-th is right of it (P1/P2, from (23) + `h22`), so
    `(j+1)` is the only candidate; if it is not contained, `I₃` is covered by at
    most one 4-block part plus one 1234-gap flank, of total length `< 1/(3v₄) +
    1/(3v₅) < 1/(2v₃) = |I₃|` (`x45_sum`, `h45sum`), or `I₃` lies in a single
    4-gap forcing `|I₃| < 1/(3v₅)` (`v₅ > 2v₃`, `h2v3v5`) — both impossible. -/
lemma bhk_s5_case51_eqn25 (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (h2v3v5 : 2 * (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ))
    (h45sum : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ))
      < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    t + 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hpos2 : (0 : ℝ) < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by positivity
  -- P1: the j-th 4-block right edge is at/left of I₃'s left end.
  have hP1 : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) := by
    have h : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) :=
      one_div_le_one_div_of_le hv3 (by linarith)
    linarith [h23b, h]
  -- P2: the (j+2)-th 4-block left edge is right of I₃'s right end.
  have hP2 : t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    have e : ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) + 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    have h32 : 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e2 : (1 : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
    linarith [h23a, e, h32, e2]
  have hlen : (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      - (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  have hblk : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    field_simp; ring
  have ecast1 : (((j + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast2 : (((j + 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  rcases le_or_gt (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
    (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hbl | hbl
  · rcases le_or_gt (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · exact ⟨hbl, hbr⟩
    · exfalso
      rcases le_or_gt (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hmiss | hstr
      · -- (j+1)-th block right of I₃: I₃ ⊆ left 4-gap (k = j) ⊆ B₅, too long for one 5-block.
        have hI3 := bhk_s5_case51_I3_4safe_short speeds hpos hcover t hgapI3 j
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _) hP1 hmiss
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI3
        linarith
      · -- (j+1)-th block straddles I₃'s right end: I₃ = (left flank, k = j) + (block part).
        have hL := bhk_s5_case51_I3_4safe_short speeds hpos hcover t hgapI3 j
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          hbl (le_refl _) (le_of_lt hstr) hP1 (le_refl _)
        linarith [hL, hblk, hbr, h45sum]
  · rcases le_or_gt (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · exfalso
      rcases le_or_gt (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) with hmiss | hstr
      · -- (j+1)-th block left of I₃: I₃ ⊆ right 4-gap (k = j+1) ⊆ B₅, too long.
        have hI3 := bhk_s5_case51_I3_4safe_short speeds hpos hcover t hgapI3 (j + 1)
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _)
          (by rw [ecast1]; exact hmiss) (by rw [ecast2]; exact hP2)
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI3
        linarith
      · -- (j+1)-th block straddles I₃'s left end: I₃ = (block part) + (right flank, k = j+1).
        have hR := bhk_s5_case51_I3_4safe_short speeds hpos hcover t hgapI3 (j + 1)
          (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          hbr (le_of_lt hstr) (le_refl _)
          ecast1.le (by rw [ecast2]; exact hP2)
        linarith [hR, hblk, hbl, h45sum]
    · -- (j+1)-th block ⊇ I₃: impossible since |block| = 1/(3v₄) < 1/(2v₃) = |I₃|.
      exfalso
      have h : (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          - (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        linarith [hblk, hbl, hbr]
      rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at h
      linarith

/-- **BHK eqn (25), reflected: the forced 4-block in `I₁`.**  Mirror of
    `bhk_s5_case51_eqn25` under the left↔right symmetry of the triple
    configuration: a 4-block in `I₃` (the `j`-th) together with the covered
    123-gap `I₁ = [t, t+1/(2v₃)]` forces the `(j−1)`-th 4-block inside `I₁`.
    The `j`-th block is right of `I₁` and the `(j−2)`-th is left of it (P1'/P2'),
    so `(j−1)` is the only candidate; the same length accounting (`h45sum`,
    `h2v3v5`) rules out every non-contained position. -/
lemma bhk_s5_case51_eqn25' (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (h2v3v5 : 2 * (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ))
    (h45sum : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ))
      < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    t ≤ ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hpos2 : (0 : ℝ) < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by positivity
  -- P1': the j-th 4-block left edge is at/right of I₁'s right end.
  have hP1 : t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : (1 : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) :=
      one_div_le_one_div_of_le hv3 (by linarith)
    linarith [h23a, h]
  -- P2': the (j-2)-th 4-block right edge is left of I₁'s left end.
  have hP2 : ((j : ℝ) - 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ t := by
    have e : ((j : ℝ) - 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) - 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      field_simp; ring
    have h32 : 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 2 / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e2 : (1 : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
    linarith [h23b, e, h32, e2]
  have hlen : (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) - t
      = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  have hblk : ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    field_simp; ring
  have ecast1 : (((j - 2 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast2 : (((j - 2 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast3 : (((j - 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have ecast4 : (((j - 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  rcases le_or_gt t (((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hbl | hbl
  · rcases le_or_gt (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · exact ⟨hbl, hbr⟩
    · exfalso
      rcases le_or_gt (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hmiss | hstr
      · -- (j-1)-th block right of I₁: I₁ ⊆ left 4-gap (k = j-2) ⊆ B₅, too long.
        have hI1 := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgapI1 (j - 2)
          t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _)
          (by rw [ecast1]; exact hP2) (by rw [ecast2]; exact hmiss)
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI1
        linarith
      · -- (j-1)-th block straddles I₁'s right end: I₁ = (left flank, k=j-2) + (block part).
        have hL := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgapI1 (j - 2)
          t (((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          hbl (le_refl _) (le_of_lt hstr) (by rw [ecast1]; exact hP2) ecast2.symm.le
        linarith [hL, hblk, hbr, h45sum]
  · rcases le_or_gt (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hbr | hbr
    · exfalso
      rcases le_or_gt (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) t with hmiss | hstr
      · -- (j-1)-th block left of I₁: I₁ ⊆ right 4-gap (k = j-1) ⊆ B₅, too long.
        have hI1 := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgapI1 (j - 1)
          t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          (by linarith) (le_refl _) (le_refl _)
          (by rw [ecast3]; exact hmiss) (by rw [ecast4]; exact hP1)
        rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at hI1
        linarith
      · -- (j-1)-th block straddles I₁'s left end: I₁ = (block part) + (right flank, k=j-1).
        have hR := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgapI1 (j - 1)
          (((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          hbr (le_of_lt hstr) (le_refl _) ecast3.le (by rw [ecast4]; exact hP1)
        linarith [hR, hblk, hbl, h45sum]
    · -- (j-1)-th block ⊇ I₁: impossible since |block| = 1/(3v₄) < 1/(2v₃) = |I₁|.
      exfalso
      have h : (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) - t
          < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        linarith [hblk, hbl, hbr]
      rw [hlen, div_lt_div_iff₀ (by positivity) (by positivity)] at h
      linarith

/-- **Claim 10 (BHK p. 15): no 4-block is contained in `I₁`.**  In the triple
    configuration (`I₁ = [t, t+1/(2v₃)]` and `I₃ = [t+1/v₃, t+3/(2v₃)]` are
    123-gaps `⊆ B₄ ∪ B₅` under the covering `hcover`), a 4-block in `I₁`
    (eqn (23): `h23a`/`h23b`) is contradictory.  Assembles the section: eqn (24)
    (`claim10_5gap`/`claim10_decomp`) ⟹ `1/4 < x₅ < 1/2` (`x5_bounds`) and
    `x₄/3+x₅/3 < 1/2` (`x45_sum`) ⟹ a forced 4-block in `I₃` (eqn (25),
    `eqn25`) ⟹ the consecutive-5-block counting `False` (`claim10_contra`).  By
    the left-right symmetry of the triple configuration this also rules out a
    4-block in `I₃`. -/
lemma bhk_s5_case51_claim10_no4block_I1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h24a := bhk_s5_case51_claim10_5gap speeds hmono hpos hcover t hgapI1 h22 j h23a h23b
  have h24b := bhk_s5_case51_claim10_decomp speeds hpos hcover t hgapI1 h22 j h23a h23b
  obtain ⟨h2v3v5, _⟩ := bhk_s5_case51_x5_bounds _ _ _ hv3 hv5 h34 h24a h24b
  have h45sum := bhk_s5_case51_x45_sum _ _ _ hv3 h34 h2v3v5
  obtain ⟨h25a, h25b⟩ :=
    bhk_s5_case51_eqn25 speeds hpos hcover t hgapI3 h22 h34 j h23a h23b h2v3v5 h45sum
  exact bhk_s5_case51_claim10_contra speeds hmono hpos hcover t hgapI1 hgapI3 h22 j
    h23a h23b h25a h25b

/-- **Claim 10 (BHK p. 15): no 4-block is contained in `I₃`.**  The left↔right
    mirror of `bhk_s5_case51_claim10_no4block_I1`: a 4-block in `I₃` (the `j`-th)
    is contradictory.  Eqn (24)/`x5_bounds`/`x45_sum` (applied to the `I₃` block)
    feed the reflected `eqn25'`, which forces the `(j−1)`-th block into `I₁`;
    `claim10_contra` (at index `j−1`) then closes it.  Together with the `I₁`
    lemma this is the full Claim 10. -/
lemma bhk_s5_case51_claim10_no4block_I3 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (j : ℤ)
    (h23a : t + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (h23b : ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  -- eqn (24) and the `x₅` bounds, from the `I₃` 4-block (gap start `t+1/v₃`).
  have h24a := bhk_s5_case51_claim10_5gap speeds hmono hpos hcover
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) hgapI3 h22 j h23a h23b
  have h24b := bhk_s5_case51_claim10_decomp speeds hpos hcover
    (t + 1 / (speeds ⟨2, by omega⟩ : ℝ)) hgapI3 h22 j h23a h23b
  obtain ⟨h2v3v5, _⟩ := bhk_s5_case51_x5_bounds _ _ _ hv3 hv5 h34 h24a h24b
  have h45sum := bhk_s5_case51_x45_sum _ _ _ hv3 h34 h2v3v5
  -- Reflected eqn (25): the `(j-1)`-th 4-block lies in `I₁`.
  obtain ⟨h25a, h25b⟩ :=
    bhk_s5_case51_eqn25' speeds hpos hcover t hgapI1 h22 h34 j h23a h23b h2v3v5 h45sum
  -- `claim10_contra` at index `j-1`: the `I₁` block `(j-1)` and the `I₃` block `j`.
  have c1 : (((j - 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have c2 : (((j - 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have c3 : (((j - 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  have c4 : (((j - 1 : ℤ) : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by push_cast; ring
  exact bhk_s5_case51_claim10_contra speeds hmono hpos hcover t hgapI1 hgapI3 h22 (j - 1)
    (by rw [c1]; exact h25a) (by rw [c2]; exact h25b)
    (by rw [c3]; exact h23a) (by rw [c4]; exact h23b)

/-- **A covered 123-gap meets a 4-block.**  The length-`1/(2v₃)` gap
    `I = [a, a+1/(2v₃)]` (123-safe, so `⊆ B₄ ∪ B₅` under covering) cannot be
    4-safe throughout — that would make it a 1234-gap of length `1/(2v₃)`, but
    `gap1234_short` bounds 1234-gaps by `1/(3v₅) < 1/(2v₃)` (`v₅ > v₃`).  So some
    point of `I` lies in a runner-4 block.  Foundational for the span bound
    (29)/(30): each gap of a multiple configuration meets a 4-block. -/
lemma bhk_s5_case51_gap_meets_block (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (a : ℝ)
    (hgap : ∀ s ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ)) :
    ∃ p ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      p ∈ unsafeOf speeds ⟨3, by omega⟩ := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hsub := bhk_prop11_gap_covered speeds hcover hgap
  by_contra hcon
  push_neg at hcon
  -- Every point of `I` avoids `B₄`, so `I ⊆ B₅`.
  have hsub5 : Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      ⊆ unsafeOf speeds ⟨4, by omega⟩ := fun p hp => (hsub hp).resolve_left (hcon p hp)
  have hab : a ≤ a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    have : (0 : ℝ) < 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by positivity
    linarith
  have hlen := block_length_bound speeds ⟨4, by omega⟩ (hpos _) a
    (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) hab hsub5
  rw [add_sub_cancel_left, div_lt_div_iff₀ (by positivity) (by positivity)] at hlen
  linarith

/-- **A covered 123-gap with no full 4-block has a *straddling* block.**  By
    `gap_meets_block` some block `m` overlaps `G = [a, a+1/(2v₃)]`; since `G`
    contains no full 4-block (`hnofull`), block `m` must extend past one endpoint
    of `G` (left edge `< a`, or right edge `> a+1/(2v₃)`).  This pins the block at
    an end of the gap — step 1–2 of the span bound (29)/(30). -/
lemma bhk_s5_case51_gap_straddle (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (a : ℝ)
    (hgap : ∀ s ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ))
    (hnofull : ∀ m : ℤ, ¬ (a ≤ ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        ≤ a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))) :
    ∃ m : ℤ, a < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ∧
      (((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < a ∨
        a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
          < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) := by
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  obtain ⟨p, hpG, hpB⟩ := bhk_s5_case51_gap_meets_block speeds hpos hcover a hgap h35
  rw [mem_unsafeOf_iff_bhkB] at hpB
  obtain ⟨m, hm⟩ := hpB
  have habs := abs_lt.mp hm
  have hpl : ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < p := by
    rw [div_lt_iff₀ hv4]; nlinarith [habs.1]
  have hpr : p < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [lt_div_iff₀ hv4]; nlinarith [habs.2]
  refine ⟨m, by linarith [hpG.1, hpr], by linarith [hpl, hpG.2], ?_⟩
  by_contra hcon
  push_neg at hcon
  exact hnofull m ⟨hcon.1, hcon.2⟩

/-- **At most one 4-block overlaps a length-`1/(2v₃)` gap.**  Two blocks `m < m'`
    both overlapping `[a, a+1/(2v₃)]` would have
    `(m'−1/6)/v₄ − (m+1/6)/v₄ < 1/(2v₃)`, but `m'−m ≥ 1` makes that difference
    `≥ (2/3)/v₄ > 1/(2v₃)` (eqn 22, `3v₄ < 4v₃`) — impossible.  So the straddling
    block from `gap_straddle` is *the* block meeting the gap. -/
lemma bhk_s5_case51_block_unique (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ)) (a : ℝ)
    (m m' : ℤ)
    (hm : a < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hm2 : ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hm' : a < ((m' : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hm'2 : ((m' : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    m = m' := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  -- Helper: `p < q` (integers) is impossible for two overlapping blocks.
  have key : ∀ p q : ℤ, p < q → a < ((p : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) →
      ((q : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        → False := by
    intro p q hpq hp hq
    have hpq' : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
    have h1 : a * (speeds ⟨3, by omega⟩ : ℝ) < (p : ℝ) + 1 / 6 := (lt_div_iff₀ hv4).mp hp
    have h2 : (q : ℝ) - 1 / 6 < (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        * (speeds ⟨3, by omega⟩ : ℝ) := (div_lt_iff₀ hv4).mp hq
    have h2' : (q : ℝ) - 1 / 6 < a * (speeds ⟨3, by omega⟩ : ℝ)
        + (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      have he : (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) * (speeds ⟨3, by omega⟩ : ℝ)
          = a * (speeds ⟨3, by omega⟩ : ℝ)
            + (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        field_simp
      linarith [h2, he]
    have h3 : (2 : ℝ) / 3 < (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      linarith [h1, h2', hpq']
    rw [lt_div_iff₀ (by positivity)] at h3
    linarith
  rcases lt_trichotomy m m' with h | h | h
  · exact absurd (key m m' h hm hm'2) (by simp)
  · exact h
  · exact absurd (key m' m h hm' hm2) (by simp)

/-- **The blocks of adjacent gaps differ by 1 or 2.**  If block `m` overlaps a
    gap `G = [a, a+1/(2v₃)]` and block `m'` overlaps the next gap
    `G' = [a+1/v₃, a+1/v₃+1/(2v₃)]`, then `m+1 ≤ m' ≤ m+2`.  The gaps are `1/v₃`
    apart and the block period is `1/v₄ ∈ (3/(4v₃), 1/v₃)`, so the index advances
    by 1 or 2 — Claim 9 (no full block in the middle) later forces it to exactly
    1 (consecutiveness, for the span). -/
lemma bhk_s5_case51_block_step (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ)) (a : ℝ) (m m' : ℤ)
    (hmL : a < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hmR : ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hm'L : a + 1 / (speeds ⟨2, by omega⟩ : ℝ) < ((m' : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hm'R : ((m' : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    m + 1 ≤ m' ∧ m' ≤ m + 2 := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have e1 : a * (speeds ⟨3, by omega⟩ : ℝ) < (m : ℝ) + 1 / 6 := (lt_div_iff₀ hv4).mp hmL
  have e2 : (m : ℝ) - 1 / 6
      < a * (speeds ⟨3, by omega⟩ : ℝ)
        + (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    have h := (div_lt_iff₀ hv4).mp hmR
    have x : (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) * (speeds ⟨3, by omega⟩ : ℝ)
        = a * (speeds ⟨3, by omega⟩ : ℝ)
          + (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp
    linarith [h, x]
  have e3 : a * (speeds ⟨3, by omega⟩ : ℝ) + (speeds ⟨3, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
      < (m' : ℝ) + 1 / 6 := by
    have h := (lt_div_iff₀ hv4).mp hm'L
    have x : (a + 1 / (speeds ⟨2, by omega⟩ : ℝ)) * (speeds ⟨3, by omega⟩ : ℝ)
        = a * (speeds ⟨3, by omega⟩ : ℝ)
          + (speeds ⟨3, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by
      field_simp
    linarith [h, x]
  have e4 : (m' : ℝ) - 1 / 6
      < a * (speeds ⟨3, by omega⟩ : ℝ)
        + 3 * (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    have h := (div_lt_iff₀ hv4).mp hm'R
    have x : (a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
          * (speeds ⟨3, by omega⟩ : ℝ)
        = a * (speeds ⟨3, by omega⟩ : ℝ)
          + 3 * (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
      field_simp; ring
    linarith [h, x]
  have r1 : (speeds ⟨3, by omega⟩ : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
      = 2 * ((speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ))) := by
    field_simp
  have hbig : (1 : ℝ) / 2 < (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  have hsml : 3 * (speeds ⟨3, by omega⟩ : ℝ) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) < 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  refine ⟨?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have hmm : (m' : ℝ) ≤ m := by exact_mod_cast (by omega : m' ≤ m)
    linarith [e2, e3, hmm, r1, hbig]
  · by_contra hc
    push_neg at hc
    have hmm : (m : ℝ) + 3 ≤ m' := by exact_mod_cast (by omega : m + 3 ≤ m')
    linarith [e1, e4, hmm, hsml]

/-- **Consecutive gaps have consecutive blocks (`p' = p + 1`).**  If block `p`
    meets a covered 123-gap `G = [a, a+1/(2v₃)]` and block `p'` meets the next
    gap `G' = [a+1/v₃, a+1/v₃+1/(2v₃)]`, then `p' = p + 1`.  `block_step` gives
    `p+1 ≤ p' ≤ p+2`; the skip `p' = p+2` traps block `p+1` strictly inside the
    middle `(a+1/(2v₃), a+1/v₃)` — its left edge `> a+1/(2v₃)` (from `hpL` and the
    block period `1/v₄ > 3/(4v₃)`, i.e. (22)) and its right edge `< a+1/v₃` (from
    `hp'R` and (22)) — contradicting Claim 9 (no 4-block in `I₂`).  The
    consecutiveness step of the span bound (29)/(30). -/
lemma bhk_s5_case51_block_succ (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (a : ℝ)
    (hgapA : ∀ s ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapB : ∀ s ∈ Set.Icc (a + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (p p' : ℤ)
    (hpL : a < ((p : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hpR : ((p : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
    (hp'L : a + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      < ((p' : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hp'R : ((p' : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    p' = p + 1 := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3' : (speeds ⟨2, by omega⟩ : ℝ) ≠ 0 := ne_of_gt hv3
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  obtain ⟨hstep1, hstep2⟩ :=
    bhk_s5_case51_block_step speeds hpos h22 h34 a p p' hpL hpR hp'L hp'R
  rcases (show p' = p + 1 ∨ p' = p + 2 by omega) with h | h
  · exact h
  · exfalso
    subst h
    -- The two gaps in the `⊆ B₄ ∪ B₅` form Claim 9 consumes.
    have hsubA := bhk_prop11_gap_covered speeds hcover hgapA
    have hsubB : Set.Icc (a + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (a + 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        ⊆ unsafeOf speeds ⟨3, by omega⟩ ∪ unsafeOf speeds ⟨4, by omega⟩ := by
      rw [show a + 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
            = a + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
            from by field_simp; ring]
      exact bhk_prop11_gap_covered speeds hcover hgapB
    -- The shared `1/(2v₃) < 2/(3v₄)` slack (eqn (22): `3v₄ < 4v₃`).
    have hslack : 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) < 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; linarith
    -- Block `p+1`'s left edge is strictly right of `I₁`'s end.
    have hmidL : a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        < (((p + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [show (((p + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = ((p : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              + 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by push_cast; field_simp; ring]
      linarith [hpL, hslack]
    -- Block `p+1`'s right edge is strictly left of `I₃`'s start.
    have hmidR : (((p + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        < a + 1 / (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [show (((p + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = (((p + 2 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              - 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by push_cast; field_simp; ring]
      linarith [hp'R, hslack]
    exact bhk_s5_case51_claim9 speeds hmono hpos a hsubA hsubB h22 (p + 1)
      (le_of_lt hmidL) (le_of_lt hmidR)

/-- **A covered 123-gap overlaps a 4-block — extracting the block index.**
    `gap_straddle` without the straddle/`hnofull` part: a covered 123-gap
    `[a, a+1/(2v₃)]` meets some 4-block `m` (`a < (m+1/6)/v₄` and
    `(m−1/6)/v₄ < a+1/(2v₃)`).  The existence half feeding the consecutiveness
    induction `span_consec`. -/
lemma bhk_s5_case51_gap_block_idx (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (a : ℝ)
    (hgap : ∀ s ∈ Set.Icc a (a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    ∃ m : ℤ, a < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        < a + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  obtain ⟨p, hpG, hpB⟩ := bhk_s5_case51_gap_meets_block speeds hpos hcover a hgap h35
  rw [mem_unsafeOf_iff_bhkB] at hpB
  obtain ⟨m, hm⟩ := hpB
  have habs := abs_lt.mp hm
  have hpl : ((m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < p := by
    rw [div_lt_iff₀ hv4]; nlinarith [habs.1]
  have hpr : p < ((m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [lt_div_iff₀ hv4]; nlinarith [habs.2]
  exact ⟨m, by linarith [hpG.1, hpr], by linarith [hpl, hpG.2]⟩

/-- **Consecutiveness across a multiple configuration (BHK eqn (29) skeleton).**
    Given `l+1` covered 123-gaps `G_m = [t+m/v₃, t+m/v₃+1/(2v₃)]` (`m ≤ l`), there
    is a block index `j` such that block `j` meets `G_0` *and* block `j+l` meets
    `G_l`.  Induction on `l`: existence of a meeting block is `gap_block_idx`; the
    step `j+m ↦ j+(m+1)` is `block_succ` (consecutive gaps ⟹ consecutive blocks).
    This is the consecutiveness backbone of the span bound (29)/(30): it carries
    the *outer two* blocks to the configuration's ends, where the endpoint
    extraction (covering of the end-flanks) then yields the eqn (29) bounds. -/
lemma bhk_s5_case51_span_consec (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    ∃ j : ℤ,
      (t < ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
        ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          < t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) ∧
      (t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
          < ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ∧
        ((j : ℝ) + (l : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          < t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) := by
  revert hgaps
  induction l with
  | zero =>
    intro hgaps
    obtain ⟨j, hjL, hjR⟩ := bhk_s5_case51_gap_block_idx speeds hmono hpos hcover t
      (by have h := hgaps 0 (le_refl 0); simpa only [Nat.cast_zero, zero_div, add_zero] using h)
    exact ⟨j, ⟨hjL, hjR⟩,
      by simpa only [Nat.cast_zero, zero_div, add_zero] using hjL,
      by simpa only [Nat.cast_zero, zero_div, add_zero] using hjR⟩
  | succ n ih =>
    intro hgaps
    obtain ⟨j, ⟨hj0L, hj0R⟩, hjnL, hjnR⟩ := ih (fun m hm => hgaps m (by omega))
    have hbr : t + (n : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (speeds ⟨2, by omega⟩ : ℝ)
        = t + ((n + 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by push_cast; ring
    obtain ⟨p, hqL, hqR⟩ := bhk_s5_case51_gap_block_idx speeds hmono hpos hcover
      (t + ((n + 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps (n + 1) (le_refl _))
    have hcast : (((j + (n : ℤ)) : ℤ) : ℝ) = (j : ℝ) + (n : ℝ) := by push_cast; ring
    have hstep : p = j + (n : ℤ) + 1 := by
      refine bhk_s5_case51_block_succ speeds hmono hpos hcover
        (t + (n : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps n (by omega)) ?_ h22
        (j + (n : ℤ)) p ?_ ?_ ?_ ?_
      · rw [hbr]; exact hgaps (n + 1) (le_refl _)
      · rw [hcast]; exact hjnL
      · rw [hcast]; exact hjnR
      · rw [hbr]; exact hqL
      · rw [hbr]; exact hqR
    refine ⟨j, ⟨hj0L, hj0R⟩, ?_, ?_⟩
    · rw [show (j : ℝ) + ((n + 1 : ℕ) : ℝ) = (p : ℝ) from by rw [hstep]; push_cast; ring]
      exact hqL
    · rw [show (j : ℝ) + ((n + 1 : ℕ) : ℝ) = (p : ℝ) from by rw [hstep]; push_cast; ring]
      exact hqR

/-- **BHK eqn (27): `x₄ > 9/10` (= `9 v₄ < 10 v₃`), the `l = 1` span bound.**
    For a triple configuration (`I₁ = [t, t+1/(2v₃)]` and `I₃ = [t+1/v₃,
    t+3/(2v₃)]` are 123-gaps `⊆ B₄ ∪ B₅`), `9 v₄ < 10 v₃`.  Proof by contradiction:
    assume `10 v₃ ≤ 9 v₄`; locate `t` via `j = ⌊v₄ t + 1/6⌋`; a δ-range case
    analysis shows every position of the runner-4 blocks either places a full
    4-block inside `I₁`/`I₃` (killed by `claim10_no4block_I1`/`_I3`) or leaves a
    4-safe stretch `≥ 1/(3v₄) > 1/(3v₅)` inside `I₁`/`I₃` (killed by the covering
    bounds `I1_4safe_short`/`I3_4safe_short`). -/
lemma bhk_s5_case51_span_l1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ)
    (hgapI1 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgapI3 : ∀ s ∈ Set.Icc (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ)) :
    9 * (speeds ⟨3, by omega⟩ : ℝ) < 10 * (speeds ⟨2, by omega⟩ : ℝ) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h_v45 : 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h23 : 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) ≤ 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  by_contra hcon
  push_neg at hcon
  -- `hcon : 10 v₃ ≤ 9 v₄`.  Locate `t`: `(j-1/6)/v₄ ≤ t < (j+5/6)/v₄`.
  obtain ⟨j, hjlo, hjhi⟩ : ∃ j : ℤ, (j : ℝ) - 1 / 6 ≤ (speeds ⟨3, by omega⟩ : ℝ) * t ∧
      (speeds ⟨3, by omega⟩ : ℝ) * t < (j : ℝ) + 5 / 6 := by
    refine ⟨⌊(speeds ⟨3, by omega⟩ : ℝ) * t + 1 / 6⌋, ?_, ?_⟩
    · have h := Int.floor_le ((speeds ⟨3, by omega⟩ : ℝ) * t + 1 / 6); linarith
    · have h := Int.lt_floor_add_one ((speeds ⟨3, by omega⟩ : ℝ) * t + 1 / 6); linarith
  have hjt_lo : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) ≤ t := by
    rw [div_le_iff₀ hv4]; linarith [hjlo, mul_comm (speeds ⟨3, by omega⟩ : ℝ) t]
  have hjt_hi : t < ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
    rw [lt_div_iff₀ hv4]; linarith [hjhi, mul_comm (speeds ⟨3, by omega⟩ : ℝ) t]
  rcases le_or_gt (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) t with hB | hA
  · -- Case B: `I₁` starts in the 4-gap after block `j` (`(j+1/6)/v₄ ≤ t`).
    rcases le_or_gt (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
      (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hB1 | hB2
    · -- B1: `I₁ ⊆` 4-gap `j`, so all of `I₁` is a 4-safe stretch `= 1/(2v₃) ≥ 1/(3v₄)`.
      have h_2v3_3v4 : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have hsafe := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgapI1 j t
        (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (le_add_of_nonneg_right (by positivity)) (le_refl _) (le_refl _) hB hB1
      linarith [hsafe, h_2v3_3v4, h_v45]
    · rcases le_or_gt t (((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)) with hB2a | hB2b
      · -- B2a: `I₁`'s left part `[t, (j+5/6)/v₄]` is a 4-safe gap `≥ 1/(3v₄)`.
        have bD : ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
              = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
          field_simp; ring
        have hsafe := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgapI1 j t
          (((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
          (le_of_lt hjt_hi) (le_refl _) (le_of_lt hB2) hB (le_refl _)
        have hlong : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
            ≤ ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) - t := by linarith [hB2a, bD]
        linarith [hsafe, hlong, h_v45]
      · rcases le_or_gt (t + 1 / (speeds ⟨2, by omega⟩ : ℝ))
          (((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) with hB2bi | hB2bii
        · -- B2b-i: block `j+2 ⊆ I₃` — killed by `claim10_no4block_I3`.
          have bE : ((j : ℝ) + 13 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
                = 5 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by field_simp; ring
          have h_10v3' : 5 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
              ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
            rw [show 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
                  = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring,
              div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
          exact bhk_s5_case51_claim10_no4block_I3 speeds hmono hpos hcover t hgapI1 hgapI3
            h22 (j + 2)
            (by rw [show (((j + 2 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                exact hB2bi)
            (by rw [show (((j + 2 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 13 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                linarith [hB2b, bE, h_10v3'])
        · -- B2b-ii: block `j+1 ⊆ I₁` — killed by `claim10_no4block_I1`.
          have bF : ((j : ℝ) + 11 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
              - ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                = 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
            field_simp; ring
          have ehalf : 1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
              = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
          exact bhk_s5_case51_claim10_no4block_I1 speeds hmono hpos hcover t hgapI1 hgapI3
            h22 (j + 1)
            (by rw [show (((j + 1 : ℤ) : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                exact le_of_lt hjt_hi)
            (by rw [show (((j + 1 : ℤ) : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
                  = ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) from by push_cast; ring]
                linarith [hB2bii, bF, h23, ehalf])
  · -- Case A: `t < (j+1/6)/v₄`, i.e. `I₁` starts inside block `j`.
    rcases le_or_gt (((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ))
      (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) with hA1 | hA2
    · -- A1: `I₁`'s right flank `[(j+1/6)/v₄, t+1/(2v₃)]` is a 4-safe gap `≥ 1/(3v₄)`.
      have e2 : ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have e3 : ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have hAend : t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
          < ((j : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by linarith [hA, e3, h23]
      have hpos34 : (0 : ℝ) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by positivity
      have hsafe := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgapI1 j
        (((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (by linarith [hA1, e2, hpos34]) (le_of_lt hA) (le_refl _) (le_refl _) (le_of_lt hAend)
      have hlong : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
            - ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by linarith [hA1, e2]
      linarith [hsafe, hlong, h_v45]
    · -- A2: `I₃`'s 4-safe stretch after block `j+1` is `≥ 1/(3v₄)`.
      have bA : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
            = 2 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have bB : (((j + 1 : ℤ) : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
            = 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        push_cast; field_simp; ring
      have bC : ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
            = 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        field_simp; ring
      have ehalf : 1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
          = 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp; ring
      have h_1v3 : 1 / (speeds ⟨2, by omega⟩ : ℝ) ≤ 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      have h_8v3 : 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        rw [show 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
              = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have h_10v3 : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by
        rw [show 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) + 4 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
              = 5 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by ring,
          show 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
              = 3 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring,
          div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have hsafe := bhk_s5_case51_I3_4safe_short speeds hpos hcover t hgapI3 (j + 1)
        (((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
        (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
        (by linarith [hjt_lo, bC, h_8v3]) (by linarith [hA2, bA, h23, ehalf]) (le_refl _)
        (le_of_eq (by push_cast; ring)) (by linarith [hA2, bB, h_1v3])
      have hlong : 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ))
          ≤ (t + 1 / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)))
            - ((j : ℝ) + 7 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := by
        linarith [hjt_lo, bC, h_10v3]
      linarith [hsafe, hlong, h_v45]

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
  -- Indirect form: suppose the runners cover every time within `1/6` of the
  -- origin, and derive a contradiction (BHK's `B₀ = ℝ⁺`).
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ t, ∃ i, circDist (vᵢ t) < 1/6`  — the covering assumption, in the
  -- exact shape consumed by `bhk_prop11_gap_covered`.
  --
  -- REMAINING ROADMAP (BHK §5, Case 5.1, pp. 14–16):
  --  1. Configuration existence (eqns (31)–(32)): from `k ≥ 3` and the
  --     runner-1 period `1/D` (`bhk_s5_case51_period1`) plus 2,3-closeness
  --     (`bhk_s5_case51_runner3_close`), produce, for suitable `i ≤ l`, a
  --     *multiple configuration* — `l+1` consecutive 123-gaps of length
  --     `≥ 1/(2 v₃)` starting near time `i`.  Each 123-gap is forced into
  --     `B₄ ∪ B₅` by `bhk_prop11_gap_covered hcon`.
  --  2. Claims 9–10 + eqn (26)/(27)/(30): the covered configuration forces
  --     `x₄ > (6l+3)/(6l+4)` (no 4-block fits `I₂`, `I₁`, `I₃`).
  --  3. eqn (33): the configuration's placement forces `x₄ < (6i+2)/(6i+3)`
  --     (via `bhk_s5_case51_x4_from_I1`-style `bhk_lemma_4` bounds).
  --  4. `bhk_s5_case51_x4_incompatible` closes the generic case (`i ≤ l`).
  --  5. Sub-cases 5.1.1 (`k ≥ 3 ∧ x₁ < 14/3`) and 5.1.2 (`k = 3 ∧ 8 < x₁ < 26/3`)
  --     handle the four narrow `x₁`-windows where no `l ≥ i` configuration
  --     exists, by explicit 1234-gap / margin arguments.
  sorry

end BHK
