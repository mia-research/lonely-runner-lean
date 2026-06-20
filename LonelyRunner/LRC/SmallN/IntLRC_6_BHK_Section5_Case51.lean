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

/-- **Discrete drift crossing.**  A real sequence `ψ` that decreases by a fixed
    step `S` per index (`ψ (m+1) = ψ m - S`), starts at `ψ 0 ≥ B`, ends at
    `ψ l ≤ T`, and whose step is smaller than the window (`S < T - B`), must land
    inside `[B, T]` at some index `m ≤ l`.  (Used with the eqn-(22) identity
    `S < W` to force a 4-block fully inside a gap, contradicting Claim 10: the
    block cannot "jump over" the window in a single step.) -/
lemma drift_crossing (ψ : ℕ → ℝ) (B T S : ℝ) (l : ℕ)
    (hstep : ∀ m, ψ (m + 1) = ψ m - S) (h0 : B ≤ ψ 0) (hl : ψ l ≤ T)
    (hSW : S < T - B) : ∃ m, m ≤ l ∧ B ≤ ψ m ∧ ψ m ≤ T := by
  classical
  have hex : ∃ m, ψ m ≤ T := ⟨l, hl⟩
  refine ⟨Nat.find hex, Nat.find_le hl, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
  · rw [hz]; exact h0
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hkmin : ¬ ψ k ≤ T := Nat.find_min hex (by omega)
    push_neg at hkmin
    have hstepf : ψ (Nat.find hex) = ψ k - S := by rw [hk]; exact hstep k
    rw [hstepf]; linarith

/-- **A 4-block fully inside a gap of a multiple configuration is impossible.**
    For a multiple configuration `G_0, …, G_l` (`1 ≤ l`, each `G_m =
    [t+m/v₃, t+m/v₃+1/(2v₃)]` a 123-gap), if the `(j+m)`-th runner-4 block lies
    *fully inside* `G_m` for some `m ≤ l` then `False`.  Dispatches on position:
    an initial/middle gap (`m < l`) is an `I₁` with partner `I₃ = G_{m+1}`
    (`claim10_no4block_I1`); the final gap (`m = l`) is an `I₃` with partner
    `I₁ = G_{l-1}` (the mirror `claim10_no4block_I3`).  This is the leaf consumed
    by the drift-window bad-case argument for eqn (29). -/
lemma bhk_s5_case51_block_fully_in_gap_absurd (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (j : ℤ) (m : ℕ) (hm : m ≤ l)
    (hfullL : t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
      ≤ (((j : ℝ) + (m : ℝ)) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hfullR : (((j : ℝ) + (m : ℝ)) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    False := by
  have hcast : (((j + (m : ℤ)) : ℤ) : ℝ) = (j : ℝ) + (m : ℝ) := by push_cast; ring
  rcases lt_or_eq_of_le hm with hlt | heq
  · -- `m < l`: block `j+m` is fully inside `G_m = I₁`; partner `I₃ = G_{m+1}`.
    have hbr : t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (speeds ⟨2, by omega⟩ : ℝ)
        = t + ((m + 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by push_cast; ring
    refine bhk_s5_case51_claim10_no4block_I1 speeds hmono hpos hcover
      (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps m hm) ?_ h22 (j + (m : ℤ)) ?_ ?_
    · rw [hbr]; exact hgaps (m + 1) (by omega)
    · rw [hcast]; exact hfullL
    · rw [hcast]; exact hfullR
  · -- `m = l`: block `j+m` is fully inside `G_m = I₃`; partner `I₁ = G_{m-1}`.
    have hm1 : 1 ≤ m := by omega
    have hτ : t + ((m - 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
          + 1 / (speeds ⟨2, by omega⟩ : ℝ)
        = t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [Nat.cast_sub hm1]; push_cast; field_simp; ring
    refine bhk_s5_case51_claim10_no4block_I3 speeds hmono hpos hcover
      (t + ((m - 1 : ℕ) : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) (hgaps (m - 1) (by omega)) ?_ h22
      (j + (m : ℤ)) ?_ ?_
    · rw [hτ]; exact hgaps m hm
    · rw [hcast, hτ]; exact hfullL
    · rw [hcast, hτ]; exact hfullR

/-- **The bad alignment of eqn (29) is impossible (drift-window argument).**
    In a multiple configuration (`1 ≤ l`, every `G_m = [t+m/v₃, t+m/v₃+1/(2v₃)]`
    a 123-gap), the negation of eqn (29)'s disjunction — block `j` does *not* poke
    left of `G_0` (`t ≤ (j-1/6)/v₄`, i.e. `ψ_0 ≥ B`) *and* block `j+l` does *not*
    poke right of `G_l` (`(j+l+1/6)/v₄ ≤ t+l/v₃+1/(2v₃)`, i.e. `ψ_l ≤ T`) — forces,
    under `(22)`, some block `j+m` fully inside `G_m`, contradicting Claim 10.
    The drift sequence `ψ_m = (j+m)/v₄ − (t+m/v₃)` decreases by the fixed step
    `S = 1/v₃ − 1/v₄ > 0`; the window `[B,T]` (block `j+m ⊆ G_m`) has width
    `W = T − B = 1/(2v₃) − 1/(3v₄)`, and `(22)` is *exactly* `S < W`, so `ψ`
    cannot skip the window between `ψ_0 ≥ B` and `ψ_l ≤ T` (`drift_crossing`). -/
lemma bhk_s5_case51_bad_case_absurd (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (j : ℤ)
    (hbad0 : t ≤ ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (hbadl : ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      ≤ t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h3ne : (speeds ⟨2, by omega⟩ : ℝ) ≠ 0 := hv3.ne'
  have h4ne : (speeds ⟨3, by omega⟩ : ℝ) ≠ 0 := hv4.ne'
  -- drift sequence `ψ_m = (j+m)/v₄ − (t + m/v₃)`.
  set ψ : ℕ → ℝ := fun m =>
    ((j : ℝ) + (m : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
      - (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)) with hψdef
  -- step `ψ (m+1) = ψ m − S`, `S = 1/v₃ − 1/v₄`.
  have hstep : ∀ m, ψ (m + 1)
      = ψ m - (1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ)) := by
    intro m; simp only [hψdef]; push_cast; field_simp; ring
  -- `ψ 0 ≥ B`, `B = 1/(6v₄)` (block `j` does not poke left of `G_0`).
  have h0 : (1 : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) ≤ ψ 0 := by
    simp only [hψdef, Nat.cast_zero, add_zero, zero_div]
    rw [show ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = (j : ℝ) / (speeds ⟨3, by omega⟩ : ℝ) - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp] at hbad0
    linarith
  -- `ψ l ≤ T`, `T = 1/(2v₃) − 1/(6v₄)` (block `j+l` does not poke right of `G_l`).
  have hlT : ψ l ≤ 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    simp only [hψdef]
    rw [show ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + (l : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
          + 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp] at hbadl
    linarith
  -- `S < W = T − B` ⟺ `(22)` (`3v₄ < 4v₃`).
  have hSW : 1 / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ)
      < (1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [show (1 : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) - 1 / (speeds ⟨3, by omega⟩ : ℝ)
        = ((speeds ⟨3, by omega⟩ : ℝ) - (speeds ⟨2, by omega⟩ : ℝ))
          / ((speeds ⟨2, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp,
      show (1 / (2 * (speeds ⟨2, by omega⟩ : ℝ)) - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
            - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
        = (3 * (speeds ⟨3, by omega⟩ : ℝ) - 2 * (speeds ⟨2, by omega⟩ : ℝ))
          / (6 * ((speeds ⟨2, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ)))
      from by field_simp; ring,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos hv3 hv4) (sub_pos.mpr h22), mul_pos hv3 hv4, hv3, hv4]
  obtain ⟨m, hml, hmB, hmT⟩ := drift_crossing ψ _ _ _ l hstep h0 hlT hSW
  simp only [hψdef] at hmB hmT
  refine bhk_s5_case51_block_fully_in_gap_absurd speeds hmono hpos hcover h22 t l hl
    hgaps j m hml ?_ ?_
  · rw [show ((j : ℝ) + (m : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + (m : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
          - 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp]
    linarith
  · rw [show ((j : ℝ) + (m : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((j : ℝ) + (m : ℝ)) / (speeds ⟨3, by omega⟩ : ℝ)
          + 1 / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      from by field_simp]
    linarith

/-- **eqn (29a.right): the gap after block `j+l` reaches past `G_l` (covering).**
    If block `j+l` meets `G_l` on its right (`t+l/v₃ < (j+l+1/6)/v₄`), then the
    1234-gap centre `(j+l+1/2)/v₄` lies *past* `G_l`'s right end.  Otherwise the
    4-safe stretch `[(j+l+1/6)/v₄, (j+l+1/2)/v₄] ⊆ G_l ⊆ B₄∪B₅` would be a 1234-gap
    of length `1/(3v₄)`, but `I3_4safe_short` bounds such gaps by `1/(3v₅) < 1/(3v₄)`
    (`v₄ < v₅`).  This is the always-true right half of eqn (29)'s branch 1. -/
lemma bhk_s5_case51_endpoint_right_covering (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ) (l : ℕ) (j : ℤ)
    (hgapl : ∀ s ∈ Set.Icc (t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hmeetR : t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
      < ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)) :
    t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      < ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ) := by
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have hjl : (((j + (l : ℤ)) : ℤ) : ℝ) = (j : ℝ) + (l : ℝ) := by push_cast; ring
  by_contra hcon
  push_neg at hcon
  have hbridge : t + ((l : ℝ) - 1) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (speeds ⟨2, by omega⟩ : ℝ)
      = t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by field_simp; ring
  have hshort := bhk_s5_case51_I3_4safe_short speeds hpos hcover
    (t + ((l : ℝ) - 1) / (speeds ⟨2, by omega⟩ : ℝ))
    (by rw [hbridge]; exact hgapl) (j + (l : ℤ))
    (((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ))
    (by rw [← sub_nonneg, show ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
    (by rw [hbridge]; exact le_of_lt hmeetR)
    (by rw [hbridge]; exact hcon) (le_of_eq (by rw [hjl]))
    (by rw [hjl, ← sub_nonneg, show ((j : ℝ) + (l : ℝ) + 5 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
  have hba : ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by field_simp; ring
  rw [hba] at hshort
  have hlt : 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-- **eqn (29b.left): the gap before block `j` reaches before `G_0` (covering).**
    Mirror of `endpoint_right_covering`: if block `j` meets `G_0` on its left
    (`(j-1/6)/v₄ < t+1/(2v₃)`), then the 1234-gap centre `(j-1/2)/v₄` lies *before*
    `G_0`'s left end `t`.  Otherwise `[(j-1/2)/v₄, (j-1/6)/v₄] ⊆ G_0` is a 1234-gap
    of length `1/(3v₄) > 1/(3v₅)` (`I1_4safe_short`).  The always-true left half of
    eqn (29)'s branch 2. -/
lemma bhk_s5_case51_endpoint_left_covering (speeds : Fin 5 → ℕ)
    (hmono : StrictMono speeds) (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6) (t : ℝ) (j : ℤ)
    (hgap0 : ∀ s ∈ Set.Icc t (t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hmeetL : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      < t + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ) < t := by
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have hjl : (((j - 1 : ℤ)) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
  by_contra hcon
  push_neg at hcon
  have hshort := bhk_s5_case51_I1_4safe_short speeds hpos hcover t hgap0 (j - 1)
    (((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ))
    (((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ))
    (by rw [← sub_nonneg, show ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
    hcon (le_of_lt hmeetL)
    (by rw [hjl, ← sub_nonneg, show ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) from by field_simp; ring]; positivity)
    (le_of_eq (by rw [hjl]; ring))
  have hba : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
      - ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
      = 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) := by field_simp; ring
  rw [hba] at hshort
  have hlt : 1 / (3 * (speeds ⟨4, by omega⟩ : ℝ)) < 1 / (3 * (speeds ⟨3, by omega⟩ : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  linarith

/-- **BHK eqns (29)+(30): the general-`l` span bound `(6l+3)v₄ < (6l+4)v₃`.**
    For a multiple configuration of `l+1` gaps (`1 ≤ l`, every `G_m` a 123-gap),
    `span_consec` pins the straddling blocks to `j, …, j+l`.  The covering gives
    the always-true endpoint facts `29a.right`/`29b.left`
    (`endpoint_right`/`left_covering`); a case split on which end pokes (block `j`
    left, or block `j+l` right) supplies the matching half of eqn (29), and the
    bad alignment (neither) is excluded by `bad_case_absurd`.  Subtracting eqn
    (29)'s two inequalities (`(l+2/3)/v₄ > (l+1/2)/v₃` in both branches) gives the
    bound.  (`l = 1` recovers `span_l1`'s `9v₄ < 10v₃`; here general `l`.) -/
lemma bhk_s5_case51_span_l (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ))
    (t : ℝ) (l : ℕ) (hl : 1 ≤ l)
    (hgaps : ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (t + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ i : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    (6 * (l : ℝ) + 3) * (speeds ⟨3, by omega⟩ : ℝ)
      < (6 * (l : ℝ) + 4) * (speeds ⟨2, by omega⟩ : ℝ) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hU : (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      = (2 * (l : ℝ) + 1) / (2 * (speeds ⟨2, by omega⟩ : ℝ)) := by field_simp
  -- both eqn-(29) branches reduce to this single inequality, then clear denominators.
  have finish : (2 * (l : ℝ) + 1) / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        < ((l : ℝ) + 2 / 3) / (speeds ⟨3, by omega⟩ : ℝ) →
      (6 * (l : ℝ) + 3) * (speeds ⟨3, by omega⟩ : ℝ)
        < (6 * (l : ℝ) + 4) * (speeds ⟨2, by omega⟩ : ℝ) := by
    intro hstep
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hstep
    nlinarith [hstep]
  obtain ⟨j, ⟨_, hm0R⟩, hmlL, _⟩ :=
    bhk_s5_case51_span_consec speeds hmono hpos hcover h22 t l hgaps
  have h29aR := bhk_s5_case51_endpoint_right_covering speeds hmono hpos hcover t l j
    (hgaps l (le_refl l)) hmlL
  have h29bL := bhk_s5_case51_endpoint_left_covering speeds hmono hpos hcover t j
    (by simpa only [Nat.cast_zero, zero_div, add_zero] using hgaps 0 (by omega)) hm0R
  by_cases h29aL : ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < t
  · -- branch 1: block `j` pokes left (`29a.left`) + `29a.right`.
    apply finish
    have hBC : ((j : ℝ) + (l : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
        - ((j : ℝ) - 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        = ((l : ℝ) + 2 / 3) / (speeds ⟨3, by omega⟩ : ℝ) := by field_simp; ring
    rw [← hU, ← hBC]; linarith [h29aR, h29aL]
  · push_neg at h29aL
    by_cases h29bR : t + (l : ℝ) / (speeds ⟨2, by omega⟩ : ℝ)
        + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        < ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
    · -- branch 2: block `j+l` pokes right (`29b.right`) + `29b.left`.
      apply finish
      have hBC : ((j : ℝ) + (l : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
          - ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
          = ((l : ℝ) + 2 / 3) / (speeds ⟨3, by omega⟩ : ℝ) := by field_simp; ring
      rw [← hU, ← hBC]; linarith [h29bR, h29bL]
    · -- bad alignment: neither poke — impossible.
      push_neg at h29bR
      exact (bhk_s5_case51_bad_case_absurd speeds hmono hpos hcover h22 t l hl hgaps j
        h29aL h29bR).elim

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

/-- **Runner 3 is automatically safe on a config window.**  On the `m`-th window
    `[(i+m+1/3)/v₃, (i+m+5/6)/v₃]` (placement `t₀ = (i+1/3)/v₃`), `v₃ s` lies in
    `[(i+m)+1/3, (i+m)+5/6] ⊆` the `(i+m)`-th runner-3 gap `[(i+m)+1/6, (i+m)+5/6]`,
    so `circDist (v₃ s) ≥ 1/6`.  The clean third of the 123-gap condition for
    `config_exists` (runners 1, 2 need slowness / 2,3-closeness). -/
lemma bhk_s5_case51_runner3_safe_window (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (i m : ℕ) (s : ℝ)
    (hs1 : ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
      + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) ≤ s)
    (hs2 : s ≤ ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
      + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    (1 : ℝ) / 6 ≤ circDist ((speeds ⟨2, by omega⟩ : ℝ) * s) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h3ne : (speeds ⟨2, by omega⟩ : ℝ) ≠ 0 := hv3.ne'
  rw [← add_div, div_le_iff₀ hv3] at hs1
  rw [show ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
        + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
      = ((i : ℝ) + (m : ℝ) + 5 / 6) / (speeds ⟨2, by omega⟩ : ℝ) from by field_simp; ring,
    le_div_iff₀ hv3] at hs2
  have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos ⟨2, by omega⟩)
    ((i : ℤ) + (m : ℤ)) s ?_ ?_
  · rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · rw [show (((i : ℤ) + (m : ℤ) : ℤ) : ℝ) = (i : ℝ) + (m : ℝ) from by push_cast; ring,
      div_le_iff₀ hv3]; linarith
  · rw [show (((i : ℤ) + (m : ℤ) : ℤ) : ℝ) = (i : ℝ) + (m : ℝ) from by push_cast; ring,
      le_div_iff₀ hv3]; linarith

/-- **Runner 1 is safe on a config window.**  On window `m ≤ l`, `s` lies in the
    global config span `[(i+1/3)/v₃, (i+l+5/6)/v₃]`, so `v₁ s ∈ [1/6, 5/6]` (the
    `0`-th runner-1 gap) by eqn (32)'s outer bounds `hA` (`v₃ ≤ v₁(6i+2)`) and `hC`
    (`v₁(6i+6l+5) ≤ 5v₃`).  Runner 1 stays in its first safe stretch. -/
lemma bhk_s5_case51_runner1_safe_window (speeds : Fin 5 → ℕ) (hpos : ∀ i, 0 < speeds i)
    (i l m : ℕ) (s : ℝ) (hml : m ≤ l)
    (hA : (speeds ⟨2, by omega⟩ : ℝ) ≤ (speeds ⟨0, by omega⟩ : ℝ) * (6 * (i : ℝ) + 2))
    (hC : (speeds ⟨0, by omega⟩ : ℝ) * (6 * (i : ℝ) + 6 * (l : ℝ) + 5)
      ≤ 5 * (speeds ⟨2, by omega⟩ : ℝ))
    (hs1 : ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
      + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) ≤ s)
    (hs2 : s ≤ ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
      + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    (1 : ℝ) / 6 ≤ circDist ((speeds ⟨0, by omega⟩ : ℝ) * s) := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hml' : (m : ℝ) ≤ (l : ℝ) := by exact_mod_cast hml
  have hslo : (1 : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) ≤ s := by
    have h1 : (1 : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ))
        ≤ ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hv3]; nlinarith [hA]
    have h2 : (0 : ℝ) ≤ (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by positivity
    linarith
  have hshi : s ≤ (5 : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
    have heq : ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
        + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        = ((i : ℝ) + (m : ℝ) + 5 / 6) / (speeds ⟨2, by omega⟩ : ℝ) := by
      field_simp; ring
    have h2 : ((i : ℝ) + (m : ℝ) + 5 / 6) / (speeds ⟨2, by omega⟩ : ℝ)
        ≤ (5 : ℝ) / (6 * (speeds ⟨0, by omega⟩ : ℝ)) := by
      rw [div_le_div_iff₀ hv3 (by positivity)]
      nlinarith [hC, mul_nonneg (sub_nonneg.mpr hml') hv1.le]
    rw [heq] at hs2; linarith [hs2, h2]
  have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos ⟨0, by omega⟩) 0 s ?_ ?_
  · rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · rw [show ((0 : ℤ) : ℝ) + 1 / 6 = 1 / 6 from by norm_num, div_div]; exact hslo
  · rw [show ((0 : ℤ) : ℝ) + 5 / 6 = 5 / 6 from by norm_num, div_div]; exact hshi

/-- **Runner 2 is safe on a config window.**  On window `m ≤ l`, `2,3`-closeness
    (`{D s} ≤ 1/6`, BHK eqn (31)) keeps `v₂ s` in the `(i+m)`-th runner-2 gap
    `[(i+m)+1/6, (i+m)+5/6]`: the lower edge uses eqn (32)'s `hB` (`D(6i+6l+2) ≤ v₃`,
    so `v₂ ≥ D(6i+6l+1)`), the upper edge uses `v₂ < v₃`. -/
lemma bhk_s5_case51_runner2_safe_window (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (i l m : ℕ) (s : ℝ) (hml : m ≤ l)
    (D : ℕ) (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hB : (D : ℝ) * (6 * (i : ℝ) + 6 * (l : ℝ) + 2) ≤ (speeds ⟨2, by omega⟩ : ℝ))
    (hs1 : ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
      + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) ≤ s)
    (hs2 : s ≤ ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
      + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))) :
    (1 : ℝ) / 6 ≤ circDist ((speeds ⟨1, by omega⟩ : ℝ) * s) := by
  have hv2 : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2le3 : (speeds ⟨1, by omega⟩ : ℝ) ≤ (speeds ⟨2, by omega⟩ : ℝ) := by
    have : speeds ⟨1, by omega⟩ ≤ speeds ⟨2, by omega⟩ := by
      apply le_of_lt; apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast this
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast bhk_s5_case51_D_pos speeds hmono D hD
  have hv3eq : (speeds ⟨2, by omega⟩ : ℝ) = (speeds ⟨1, by omega⟩ : ℝ) + (D : ℝ) := by
    have := bhk_s5_case51_D_cast speeds hmono D hD; linarith
  have hml' : (m : ℝ) ≤ (l : ℝ) := by exact_mod_cast hml
  have hv2lo : (D : ℝ) * (6 * (i : ℝ) + 6 * (l : ℝ) + 1) ≤ (speeds ⟨1, by omega⟩ : ℝ) := by
    nlinarith [hB, hv3eq]
  have hslo2 : ((i : ℝ) + (m : ℝ) + 1 / 6) / (speeds ⟨1, by omega⟩ : ℝ) ≤ s := by
    have step1 : ((i : ℝ) + (m : ℝ) + 1 / 6) / (speeds ⟨1, by omega⟩ : ℝ)
        ≤ ((i : ℝ) + (m : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ hv2 hv3, hv3eq]
      nlinarith [hv2lo, mul_nonneg (sub_nonneg.mpr hml') hDR.le]
    have hwl : ((i : ℝ) + (m : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
        = ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
          + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) := by field_simp; ring
    rw [hwl] at step1; linarith [step1, hs1]
  have hshi2 : s ≤ ((i : ℝ) + (m : ℝ) + 5 / 6) / (speeds ⟨1, by omega⟩ : ℝ) := by
    have hwr : ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
        + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))
        = ((i : ℝ) + (m : ℝ) + 5 / 6) / (speeds ⟨2, by omega⟩ : ℝ) := by field_simp; ring
    have step : ((i : ℝ) + (m : ℝ) + 5 / 6) / (speeds ⟨2, by omega⟩ : ℝ)
        ≤ ((i : ℝ) + (m : ℝ) + 5 / 6) / (speeds ⟨1, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ hv3 hv2]
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + (m : ℝ) + 5 / 6)
        (sub_nonneg.mpr hv2le3)]
    rw [hwr] at hs2; linarith [hs2, step]
  have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos ⟨1, by omega⟩)
    ((i : ℤ) + (m : ℤ)) s ?_ ?_
  · rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · rw [show (((i : ℤ) + (m : ℤ) : ℤ) : ℝ) = (i : ℝ) + (m : ℝ) from by push_cast; ring]
    exact hslo2
  · rw [show (((i : ℤ) + (m : ℤ) : ℤ) : ℝ) = (i : ℝ) + (m : ℝ) from by push_cast; ring]
    exact hshi2

/-- **A multiple configuration is a sequence of 123-gaps.**  Given `i, l` and the
    three eqn-(32) bounds `hA`/`hB`/`hC`, every window
    `G_m = [(i+m+1/3)/v₃, (i+m+5/6)/v₃]` (`m ≤ l`) is a 123-gap: runner 3 is
    auto-safe (`runner3_safe_window`), runner 1 stays in `[1/6,5/6]`, runner 2
    follows by `2,3`-closeness. -/
lemma bhk_s5_case51_config_window_safe (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (i l D : ℕ)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hA : (speeds ⟨2, by omega⟩ : ℝ) ≤ (speeds ⟨0, by omega⟩ : ℝ) * (6 * (i : ℝ) + 2))
    (hB : (D : ℝ) * (6 * (i : ℝ) + 6 * (l : ℝ) + 2) ≤ (speeds ⟨2, by omega⟩ : ℝ))
    (hC : (speeds ⟨0, by omega⟩ : ℝ) * (6 * (i : ℝ) + 6 * (l : ℝ) + 5)
      ≤ 5 * (speeds ⟨2, by omega⟩ : ℝ)) :
    ∀ m : ℕ, m ≤ l →
      ∀ s ∈ Set.Icc (((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
          + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
        (((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
          + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
        ∀ r : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨r.val, by omega⟩ : ℝ) * s) := by
  intro m hml s hs r
  obtain ⟨hs1, hs2⟩ := hs
  fin_cases r
  · exact bhk_s5_case51_runner1_safe_window speeds hpos i l m s hml hA hC hs1 hs2
  · exact bhk_s5_case51_runner2_safe_window speeds hmono hpos i l m s hml D hD hB hs1 hs2
  · exact bhk_s5_case51_runner3_safe_window speeds hpos i m s hs1 hs2

/-- **BHK configuration feasibility (eqn (32) integer existence).**  Given the
    generic-case exclusions (`14/3 ≤ x₁`, not (`k=3 ∧ 8<x₁<26/3`)), there exist
    `1 ≤ i ≤ l` (BHK takes `i = l = ⌈(x₁-2)/6⌉`) satisfying the three eqn-(32)
    speed bounds `hA`/`hB`/`hC`.  This is BHK's "a multiple configuration with
    `l ≥ i` exists unless conditions 1–4 hold" — the number-theoretic feasibility.
    *Under construction.* -/
lemma bhk_s5_case51_config_feasible (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (h511 : 14 / 3 ≤ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (h512 : ¬(k = 3 ∧ 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)
      ∧ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3)) :
    ∃ i l : ℕ, 1 ≤ i ∧ i ≤ l ∧
      (speeds ⟨2, by omega⟩ : ℝ) ≤ (speeds ⟨0, by omega⟩ : ℝ) * (6 * (i : ℝ) + 2) ∧
      (D : ℝ) * (6 * (i : ℝ) + 6 * (l : ℝ) + 2) ≤ (speeds ⟨2, by omega⟩ : ℝ) ∧
      (speeds ⟨0, by omega⟩ : ℝ) * (6 * (i : ℝ) + 6 * (l : ℝ) + 5)
        ≤ 5 * (speeds ⟨2, by omega⟩ : ℝ) := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hkR3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hkR : (0 : ℝ) < (k : ℝ) := by linarith
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast bhk_s5_case51_D_pos speeds hmono D hD
  set x₁ := (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) with hx1def
  have hx1pos : (0 : ℝ) < x₁ := by rw [hx1def]; exact div_pos hv3 hv1
  have hx1v1 : x₁ * (speeds ⟨0, by omega⟩ : ℝ) = (speeds ⟨2, by omega⟩ : ℝ) := by
    rw [hx1def]; field_simp
  have hkDr : (speeds ⟨0, by omega⟩ : ℝ) = (D : ℝ) * (k : ℝ) := by
    rw [hkD]; push_cast; ring
  -- BHK's index `i = l = ⌈(x₁-2)/6⌉`, the smallest `i` with `x₁/6 ≤ i+1/3`.
  obtain ⟨i, hP1, hP2, hP3⟩ : ∃ i : ℕ,
      x₁ ≤ 6 * (i : ℝ) + 2 ∧ 6 * (i : ℝ) - 4 < x₁ ∧ 1 ≤ i := by
    have hapos : (0 : ℝ) < (x₁ - 2) / 6 := by linarith [h511]
    refine ⟨⌈(x₁ - 2) / 6⌉₊, ?_, ?_, ?_⟩
    · have := Nat.le_ceil ((x₁ - 2) / 6); linarith
    · have := Nat.ceil_lt_add_one hapos.le; linarith
    · have := Nat.ceil_pos.mpr hapos; omega
  -- eqn (32) condition (B), `x₁`-form: `12 i + 2 ≤ k x₁` (runner 2 closeness).
  have hBx1 : 12 * (i : ℝ) + 2 ≤ (k : ℝ) * x₁ := by
    rcases Nat.lt_or_ge i 2 with hi1 | hi2
    · have hi1' : i = 1 := by omega
      subst hi1'; push_cast
      nlinarith [h511, mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 3) hx1pos.le]
    · have hi2R : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
      rcases Nat.lt_or_ge k 4 with hk4 | hk4
      · have hk3' : k = 3 := by omega
        subst hk3'; push_cast
        rcases Nat.lt_or_ge i 3 with hi3 | hi3
        · have hi2' : i = 2 := by omega
          subst hi2'; push_cast
          have hx8 : (8 : ℝ) < x₁ := by push_cast at hP2; linarith [hP2]
          have hge : (26 : ℝ) / 3 ≤ x₁ := by
            by_contra hlt; push_neg at hlt
            exact h512 ⟨rfl, hx8, hlt⟩
          linarith [hge]
        · have hi3R : (3 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi3
          nlinarith [hP2, hi3R]
      · have hk4R : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
        nlinarith [hP2, hi2R,
          mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - 4) hx1pos.le]
  -- eqn (32) condition (C), `x₁`-form: `12 i + 5 ≤ 5 x₁` (runner 1 upper bound).
  have hCx1 : 12 * (i : ℝ) + 5 ≤ 5 * x₁ := by
    rcases Nat.lt_or_ge i 2 with hi1 | hi2
    · have hi1' : i = 1 := by omega
      subst hi1'; push_cast; linarith [h511]
    · have hi2R : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi2
      nlinarith [hP2, hi2R]
  refine ⟨i, i, hP3, le_refl i, ?_, ?_, ?_⟩
  · -- hA: `v₃ ≤ v₁(6i+2)` ⟸ `x₁ ≤ 6i+2`.
    rw [← hx1v1]; nlinarith [hP1, hv1]
  · -- hB: `D(12i+2) ≤ v₃` ⟸ `12i+2 ≤ k x₁` (via `v₁ = Dk`, `x₁ v₁ = v₃`).
    have h1 : (D : ℝ) * (12 * (i : ℝ) + 2) ≤ (D : ℝ) * ((k : ℝ) * x₁) :=
      mul_le_mul_of_nonneg_left hBx1 hDR.le
    have h2 : (D : ℝ) * ((k : ℝ) * x₁) = (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [show (D : ℝ) * ((k : ℝ) * x₁) = ((D : ℝ) * (k : ℝ)) * x₁ from by ring,
        ← hkDr, ← hx1v1]; ring
    nlinarith [h1, h2]
  · -- hC: `v₁(12i+5) ≤ 5 v₃` ⟸ `12i+5 ≤ 5 x₁`.
    have h1 : (speeds ⟨0, by omega⟩ : ℝ) * (12 * (i : ℝ) + 5)
        ≤ (speeds ⟨0, by omega⟩ : ℝ) * (5 * x₁) :=
      mul_le_mul_of_nonneg_left hCx1 hv1.le
    have h2 : (speeds ⟨0, by omega⟩ : ℝ) * (5 * x₁) = 5 * (speeds ⟨2, by omega⟩ : ℝ) := by
      rw [← hx1v1]; ring
    nlinarith [h1, h2]

/-- **BHK configuration existence (eqns (31)/(32)) — the multiple configuration.**
    In the generic case (`14/3 ≤ x₁`, not (`k=3 ∧ 8<x₁<26/3`)), there are integers
    `1 ≤ i ≤ l` such that the `l+1` windows `G_m = [(i+m+1/3)/v₃, (i+m+5/6)/v₃]`
    (`m ≤ l`, BHK placement `t = i+1/3`) are all 123-gaps.  Assembled from
    `config_feasible` (eqn (32) integer existence) and `config_window_safe`
    (the three eqn-(32) bounds force runners 1, 2, 3 safe on every window). -/
lemma bhk_s5_case51_config_exists (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (hcon : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (h511 : 14 / 3 ≤ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (h512 : ¬(k = 3 ∧ 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)
      ∧ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3)) :
    ∃ i l : ℕ, 1 ≤ i ∧ i ≤ l ∧
      ∀ m : ℕ, m ≤ l →
        ∀ s ∈ Set.Icc (((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
            + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ))
          (((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)
            + (m : ℝ) / (speeds ⟨2, by omega⟩ : ℝ) + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
        ∀ r : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨r.val, by omega⟩ : ℝ) * s) := by
  obtain ⟨i, l, hi1, hil, hA, hB, hC⟩ :=
    bhk_s5_case51_config_feasible speeds hmono hpos k D hk3 hD hkD h511 h512
  exact ⟨i, l, hi1, hil,
    bhk_s5_case51_config_window_safe speeds hmono hpos i l D hD hA hB hC⟩

/-- **BHK generic case: the `l ≥ i` multiple configuration and its bounds.**
    When none of BHK conditions 1–4 hold — here `14/3 ≤ x₁` (`x₁ = v₃/v₁`) *and*
    not (`k = 3 ∧ 8 < x₁ < 26/3`) — eqn (32) yields integers `i ≤ l` realising a
    multiple configuration at `t = i + 1/3`.  The span (eqns (29)/(30), `span_l`)
    gives `x₄ > (6l+3)/(6l+4)` and the placement (eqn (33)) gives
    `x₄ < (6i+2)/(6i+3)` (`x₄ = v₃/v₄`); together with `i ≤ l` this is the
    contradiction `bhk_s5_case51_x4_incompatible`.  *Configuration construction
    (eqns (31)/(32) from `period1` + `runner3_close`, and the placement eqn (33))
    under construction.* -/
lemma bhk_s5_case51_config_bounds (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (hcon : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (h511 : 14 / 3 ≤ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (h512 : ¬(k = 3 ∧ 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)
      ∧ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3)) :
    ∃ i l : ℕ, i ≤ l ∧
      (6 * (l : ℝ) + 3) / (6 * l + 4)
        < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ) ∧
      (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ)
        < (6 * (i : ℝ) + 2) / (6 * i + 3) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  obtain ⟨i, l, hi1, hil, hgaps⟩ :=
    bhk_s5_case51_config_exists speeds hmono hpos hgcd hsmall hcon k D hk3 hD hkD h511 h512
  have hl : 1 ≤ l := le_trans hi1 hil
  set t₀ : ℝ := ((i : ℝ) + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ) with ht0def
  -- `G₀` is a covered 123-gap, giving eqn (22) `3v₄ < 4v₃`.
  have hgap0 : ∀ s ∈ Set.Icc t₀ (t₀ + 1 / (2 * (speeds ⟨2, by omega⟩ : ℝ))),
      ∀ r : Fin 3, (1 : ℝ) / 6 ≤ circDist ((speeds ⟨r.val, by omega⟩ : ℝ) * s) := by
    simpa only [Nat.cast_zero, zero_div, add_zero] using hgaps 0 (by omega)
  have h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ) :=
    bhk_s5_case51_x4_from_I1 speeds hmono hpos (bhk_prop11_gap_covered speeds hcon hgap0)
  refine ⟨i, l, hil, ?_, ?_⟩
  · -- eqn (30) via `span_l`.
    have hspan := bhk_s5_case51_span_l speeds hmono hpos hcon h22 t₀ l hl hgaps
    rw [div_lt_div_iff₀ (by positivity) hv4]; nlinarith [hspan]
  · -- eqn (33): `span_consec` gives `j ≥ i+1`; `endpoint_left_covering` gives
    -- `(j-1/2)/v₄ < t₀`, so `(i+1/2)/v₄ < (i+1/3)/v₃`.
    obtain ⟨j, ⟨hm0L, hm0R⟩, _, _⟩ :=
      bhk_s5_case51_span_consec speeds hmono hpos hcon h22 t₀ l hgaps
    have hblock_i : ((i : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) < t₀ := by
      rw [ht0def, div_lt_div_iff₀ hv4 hv3]
      nlinarith [mul_nonneg (Nat.cast_nonneg i : (0:ℝ) ≤ i) (sub_nonneg.mpr h34.le), h34, hv3]
    have hlt_div : ((i : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ)
        < ((j : ℝ) + 1 / 6) / (speeds ⟨3, by omega⟩ : ℝ) := lt_trans hblock_i hm0L
    rw [div_lt_div_iff₀ hv4 hv4] at hlt_div
    have h2 : (i : ℝ) + 1 / 6 < (j : ℝ) + 1 / 6 := lt_of_mul_lt_mul_right hlt_div (le_of_lt hv4)
    have hij : (i : ℤ) + 1 ≤ j := by
      have : (i : ℤ) < j := by exact_mod_cast (by linarith : (i : ℝ) < (j : ℝ))
      omega
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    have hleft := bhk_s5_case51_endpoint_left_covering speeds hmono hpos hcon t₀ j hgap0 hm0R
    have hge : ((i : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ)
        ≤ ((j : ℝ) - 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ) := by
      rw [div_le_div_iff₀ hv4 hv4]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (j:ℝ) - i - 1) (le_of_lt hv4)]
    have hcomb : ((i : ℝ) + 1 / 2) / (speeds ⟨3, by omega⟩ : ℝ) < t₀ :=
      lt_of_le_of_lt hge hleft
    rw [ht0def, div_lt_div_iff₀ hv4 hv3] at hcomb
    apply bhk_s5_case51_eqn33 ((speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨3, by omega⟩ : ℝ)) i
    rw [← mul_div_assoc, div_lt_iff₀ hv4]; nlinarith [hcomb]

/-- **Case 5.1.1, the `v₂` lower bound.**  With `3 v₁ < v₃` (`x₁ > 3`) and
    `k ≥ 3`, BHK's `v₂ = 1 − v₁/k > 8/9`, i.e. `8 v₃ < 9 v₂`.  (`9 v₂ = 9 v₃ −
    9 D` and `9 D ≤ 3 v₁ < v₃`, since `v₁ = k D ≥ 3 D`.) -/
lemma bhk_s5_case51_511_v2_lb (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) :
    8 * (speeds ⟨2, by omega⟩ : ℝ) < 9 * (speeds ⟨1, by omega⟩ : ℝ) := by
  have hDc : (D : ℝ) = (speeds ⟨2, by omega⟩ : ℝ) - (speeds ⟨1, by omega⟩ : ℝ) :=
    bhk_s5_case51_D_cast speeds hmono D hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast bhk_s5_case51_D_pos speeds hmono D hD
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hV1 : (speeds ⟨0, by omega⟩ : ℝ) = (D : ℝ) * (k : ℝ) := by rw [hkD]; push_cast; ring
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsmall
  nlinarith [hDc, hV1, hsmallR, mul_nonneg hDpos.le (by linarith : (0 : ℝ) ≤ (k : ℝ) - 3)]

/-- **Case 5.1.1, the 123-gap `[21/(16 v₃), 11/(6 v₃)]`** (BHK `[21/16, 11/6]`).
    From `8 v₃ < 9 v₂` (v₂ > 8/9), `3 v₁ < v₃` (x₁ > 3) and `3 v₃ < 14 v₁`
    (x₁ < 14/3): runner 1 lies in 1-gap `k = 0`, runners 2, 3 in their `k = 1`
    gaps. -/
lemma bhk_s5_case51_511_gap123 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hv2 : 8 * (speeds ⟨2, by omega⟩ : ℝ) < 9 * (speeds ⟨1, by omega⟩ : ℝ))
    (hsmall : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ))
    (hx1 : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 14 * (speeds ⟨0, by omega⟩ : ℝ)) :
    ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s) := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2p : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6 : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h23m : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    have h : speeds ⟨1, by omega⟩ < speeds ⟨2, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  intro s hs i
  obtain ⟨hs1, hs2⟩ := hs
  fin_cases i
  · -- runner 1 (index 0): 1-gap `k = 0`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 s
      (le_trans (by
        rw [div_le_div_iff₀ hv1 h16, Int.cast_zero]; nlinarith [hx1, hv1]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h6 hv1, Int.cast_zero]; nlinarith [hsmall, hv3]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · -- runner 2 (index 1): 2-gap `k = 1`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 1 s
      (le_trans (by
        rw [div_le_div_iff₀ hv2p h16, Int.cast_one]; nlinarith [hv2, hv2p]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h6 hv2p, Int.cast_one]; nlinarith [h23m, hv2p]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · -- runner 3 (index 2): 2-gap `k = 1`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 1 s
      (le_trans (by
        rw [div_le_div_iff₀ hv3 h16, Int.cast_one]; nlinarith [hv3]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h6 hv3, Int.cast_one]; nlinarith [hv3]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot

/-- **Case 5.1.1, the `x₄` bound `25 v₄ < 32 v₃`** (BHK `2x₄/3 > 25/48`).  The
    covered 123-gap `[21/(16 v₃), 11/(6 v₃)]` (length `25/(48 v₃)`) is `⊆ B₄ ∪ B₅`,
    so `bhk_lemma_4` bounds its length by `2/(3 v₄)`: `25/(48 v₃) < 2/(3 v₄)`,
    i.e. `25 v₄ < 32 v₃`. -/
lemma bhk_s5_case51_511_x4_bound (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (hgap123 : ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    25 * (speeds ⟨3, by omega⟩ : ℝ) < 32 * (speeds ⟨2, by omega⟩ : ℝ) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hab : (21 : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hv3]
  have hcov := bhk_prop11_gap_covered speeds hcover hgap123
  have hlen := bhk_lemma_4 speeds hmono hpos _ _ hab hcov
  rw [show (11 : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ))
        - 21 / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      = 25 / (48 * (speeds ⟨2, by omega⟩ : ℝ)) from by field_simp; ring] at hlen
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hlen
  nlinarith [hlen]

/-- **Case 5.1.1, the 1234-gap `gap1 = [21/(16 v₃), 11/(6 v₄)]`.**  The
    sub-interval of the 123-gap `[21/16, 11/6]` up to the runner-4 `k = 2` block's
    left edge `(11/6) x₄` (BHK's `275/192` is `(11/6)·(25/32)`, a stand-in for this
    edge at the minimal `x₄`).  Runners 1–3 are safe (`⊆ [21/16, 11/6]`); runner 4
    is safe in its `k = 1` gap `[7/(6 v₄), 11/(6 v₄)]` (`8 v₃ ≤ 9 v₄`). -/
lemma bhk_s5_case51_511_gap1 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hv2 : 8 * (speeds ⟨2, by omega⟩ : ℝ) < 9 * (speeds ⟨1, by omega⟩ : ℝ))
    (hsmall : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ))
    (hx1 : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 14 * (speeds ⟨0, by omega⟩ : ℝ)) :
    ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6 : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  intro s hs i
  obtain ⟨hs1, hs2⟩ := hs
  have hs_big : s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
      (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) := by
    refine ⟨hs1, le_trans hs2 ?_⟩
    rw [div_le_div_iff₀ (by positivity) h6]; nlinarith [h34, hv3, hv4]
  fin_cases i
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 0
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 1
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 2
  · -- runner 4 (index 3): 4-gap `k = 1`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 s
      (le_trans (by
        rw [div_le_div_iff₀ hv4 h16, Int.cast_one]; nlinarith [h34, hv3, hv4]) hs1)
      (by rw [show ((1 : ℤ) : ℝ) + 5/6 = (11 : ℝ)/6 from by norm_num, div_div]; exact hs2)
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot

/-- **Case 5.1.1, the branch-A 1234-gap `gap2a = [13/(6 v₄), 11/(6 v₃)]`** (BHK
    `[13 x₄/6, 11/6]`).  The runner-4 `k = 2`–`k = 3` 4-gap; valid when
    `13 x₄ ≤ 11`.  Runners 1–3 safe (`⊆ [21/16, 11/6]`, using `x₄ > 25/32` for the
    left edge); runner 4 safe in its `k = 2` gap (`11 v₄ ≤ 17 v₃` from `x₄ > 25/32`). -/
lemma bhk_s5_case51_511_gap2a (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hv2 : 8 * (speeds ⟨2, by omega⟩ : ℝ) < 9 * (speeds ⟨1, by omega⟩ : ℝ))
    (hsmall : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ))
    (hx1 : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 14 * (speeds ⟨0, by omega⟩ : ℝ))
    (hx4 : 25 * (speeds ⟨3, by omega⟩ : ℝ) < 32 * (speeds ⟨2, by omega⟩ : ℝ)) :
    ∀ s ∈ Set.Icc (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6 : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6v4 : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  intro s hs i
  obtain ⟨hs1, hs2⟩ := hs
  have hs_big : s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
      (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) := by
    refine ⟨le_trans ?_ hs1, hs2⟩
    rw [div_le_div_iff₀ h16 h6v4]; nlinarith [hx4, hv3, hv4]
  fin_cases i
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 0
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 1
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 2
  · -- runner 4 (index 3): 4-gap `k = 2`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 2 s
      (by rw [show ((2 : ℤ) : ℝ) + 1/6 = (13 : ℝ)/6 from by norm_num, div_div]; exact hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h6 hv4, Int.cast_ofNat]; nlinarith [hx4, hv3, hv4]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot

/-- **Case 5.1.1, the branch-B 1234-gap `gap2b = [21/(16 v₃), 121/(78 v₃)]`** (BHK
    `[21/16, 121/78]`).  Valid when `13 x₄ > 11` (`11 v₄ < 13 v₃`): then the
    runner-4 `k = 2` block lies past `121/(78 v₃)`, so the sub-interval of the
    123-gap is also runner-4 safe (4-gap `k = 1`). -/
lemma bhk_s5_case51_511_gap2b (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hv2 : 8 * (speeds ⟨2, by omega⟩ : ℝ) < 9 * (speeds ⟨1, by omega⟩ : ℝ))
    (hsmall : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ))
    (hx1 : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 14 * (speeds ⟨0, by omega⟩ : ℝ))
    (hB : 11 * (speeds ⟨3, by omega⟩ : ℝ) < 13 * (speeds ⟨2, by omega⟩ : ℝ)) :
    ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (121 / (78 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s) := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h34 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h78 : (0 : ℝ) < 78 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6 : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  intro s hs i
  obtain ⟨hs1, hs2⟩ := hs
  have hs_big : s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
      (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) := by
    refine ⟨hs1, le_trans hs2 ?_⟩
    rw [div_le_div_iff₀ h78 h6]; nlinarith [hv3]
  fin_cases i
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 0
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 1
  · exact bhk_s5_case51_511_gap123 speeds hmono hpos hv2 hsmall hx1 s hs_big 2
  · -- runner 4 (index 3): 4-gap `k = 1`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 1 s
      (le_trans (by
        rw [div_le_div_iff₀ hv4 h16, Int.cast_one]; nlinarith [h34, hv3, hv4]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h78 hv4, Int.cast_one]; nlinarith [hB, hv3, hv4]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot

/-- **Case 5.1.1, branch B (`13 x₄ > 11`): runner 5 cannot cover `gap2b`.**  The
    1234-gap `[21/(16 v₃), 121/(78 v₃)]`, being `⊆ B₅`, lies in a single 5-block;
    the width bound `149 v₅ < 208 v₃` forces `k ≤ 1` (left end) while the right end
    forces `k ≥ 2` — no such integer (BHK's "narrowest of margins").  Uses only
    `v₃ < v₅` (`x₅ < 1`); the `bhk_s5_case51_512_no_cover` recipe. -/
lemma bhk_s5_case51_511_no_cover_B (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (hgap : ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (121 / (78 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h78 : (0 : ℝ) < 78 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have hab : (21 : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 121 / (78 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h16 h78]; nlinarith [hv3]
  have hsub := bhk_s5_case51_gap1234_subset speeds hcover hgap
  obtain ⟨k, hkL, hkR⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ))) (121 / (78 * (speeds ⟨2, by omega⟩ : ℝ))) hab hsub
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 21 * (speeds ⟨4, by omega⟩ : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      lt_div_iff₀ h16] at hkL
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (121 / (78 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 121 * (speeds ⟨4, by omega⟩ : ℝ) / (78 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      div_lt_iff₀ h78] at hkR
  -- hkL : ((k:ℝ) - 1/6) * (16 v₃) < 21 v₅ ;  hkR : 121 v₅ < ((k:ℝ) + 1/6) * (78 v₃)
  have width : 149 * (speeds ⟨4, by omega⟩ : ℝ) < 208 * (speeds ⟨2, by omega⟩ : ℝ) := by
    nlinarith [hkL, hkR]
  have hk_lo : (108 : ℝ) < 78 * (k : ℝ) := by
    have step : (108 : ℝ) * (speeds ⟨2, by omega⟩ : ℝ)
        < 78 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkR, h35]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk2 : (2 : ℤ) ≤ k := by
    by_contra h; push_neg at h
    have hk1r : (k : ℝ) ≤ 1 := by exact_mod_cast (by omega : k ≤ 1)
    linarith [hk_lo]
  have hk_hi : 16 * (k : ℝ) < 32 := by
    have step : 16 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ)
        < 32 * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkL, width, hv3]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk1 : k ≤ (1 : ℤ) := by
    by_contra h; push_neg at h
    have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (2 : ℤ) ≤ k)
    linarith [hk_hi]
  omega

/-- **Case 5.1.1, branch A (`13 x₄ ≤ 11`): runner 5 cannot cover `gap1` and
    `gap2a` simultaneously.**  Both are 1234-gaps `⊆ B₅`, each in a single 5-block
    (`k₁` for `gap1`, `k₂` for `gap2a`).  `gap1`'s width bound gives `23 v₅ < 64 v₃`
    so `k₁ ∈ {2, 3}`, whence `gap1`'s right end gives `11 v₅ < 19 v₄` (BHK's
    `19 x₅ > 11 x₄`), bounding `k₂ ∈ {2, 3}`.  The four `(k₁, k₂)` pairs are each
    contradictory (`k₂ = 2`: `11 v₅ < 13 v₃ ≤ 11 v₄ < 11 v₅`; `(2,3)`: `11/13 >
    13/17`; `(3,3)`: `63/136 < 11/19`). -/
lemma bhk_s5_case51_511_no_cover_A (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (hx4 : 25 * (speeds ⟨3, by omega⟩ : ℝ) < 32 * (speeds ⟨2, by omega⟩ : ℝ))
    (hA : 13 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 11 * (speeds ⟨3, by omega⟩ : ℝ))
    (hgap1 : ∀ s ∈ Set.Icc (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s))
    (hgap2 : ∀ s ∈ Set.Icc (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4 : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h45 : (speeds ⟨3, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨3, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h16 : (0 : ℝ) < 16 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6 : (0 : ℝ) < 6 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h6v4 : (0 : ℝ) < 6 * (speeds ⟨3, by omega⟩ : ℝ) := by positivity
  -- `gap1 = [21/(16 v₃), 11/(6 v₄)]` lies in a single 5-block `k₁`.
  have hab1 : (21 : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h16 h6v4]; nlinarith [hx4, hv3, hv4]
  obtain ⟨k₁, hk1L, hk1R⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ))) (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ))) hab1
    (bhk_s5_case51_gap1234_subset speeds hcover hgap1)
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (21 / (16 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 21 * (speeds ⟨4, by omega⟩ : ℝ) / (16 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      lt_div_iff₀ h16] at hk1L
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        = 11 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) from by ring,
      div_lt_iff₀ h6v4] at hk1R
  -- hk1L : ((k₁:ℝ) - 1/6) * (16 v₃) < 21 v₅ ;  hk1R : 11 v₅ < ((k₁:ℝ) + 1/6) * (6 v₄)
  -- `gap2a = [13/(6 v₄), 11/(6 v₃)]` lies in a single 5-block `k₂`.
  have hab2 : (13 : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ))
      ≤ 11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h6v4 h6]; nlinarith [hA, hv3, hv4]
  obtain ⟨k₂, hk2L, hk2R⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ))) (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ))) hab2
    (bhk_s5_case51_gap1234_subset speeds hcover hgap2)
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (13 / (6 * (speeds ⟨3, by omega⟩ : ℝ)))
        = 13 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨3, by omega⟩ : ℝ)) from by ring,
      lt_div_iff₀ h6v4] at hk2L
  rw [show (speeds ⟨4, by omega⟩ : ℝ) * (11 / (6 * (speeds ⟨2, by omega⟩ : ℝ)))
        = 11 * (speeds ⟨4, by omega⟩ : ℝ) / (6 * (speeds ⟨2, by omega⟩ : ℝ)) from by ring,
      div_lt_iff₀ h6] at hk2R
  -- hk2L : ((k₂:ℝ) - 1/6) * (6 v₄) < 13 v₅ ;  hk2R : 11 v₅ < ((k₂:ℝ) + 1/6) * (6 v₃)
  -- `gap1` width bound: `23 v₅ < 64 v₃` (uses `x₄ > 25/32`).
  have hwidth_deg2 : 23 * (speeds ⟨4, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ)
      < 64 * (speeds ⟨2, by omega⟩ : ℝ) * (speeds ⟨3, by omega⟩ : ℝ) := by
    nlinarith [mul_lt_mul_of_pos_right hk1L h6v4, mul_lt_mul_of_pos_right hk1R h16,
               mul_lt_mul_of_pos_right hx4 hv5, hv3, hv4, hv5]
  have hwidth1 : 23 * (speeds ⟨4, by omega⟩ : ℝ) < 64 * (speeds ⟨2, by omega⟩ : ℝ) :=
    lt_of_mul_lt_mul_right hwidth_deg2 hv4.le
  -- `k₁ ∈ {2, 3}`.
  have hk1ge2 : (2 : ℤ) ≤ k₁ := by
    by_contra h; push_neg at h
    have : (k₁ : ℝ) ≤ 1 := by exact_mod_cast (by omega : k₁ ≤ 1)
    nlinarith [hk1R, h45, hv4, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (k₁:ℝ)) hv4.le]
  have hk1le3 : k₁ ≤ (3 : ℤ) := by
    by_contra h; push_neg at h
    have hk4 : (4 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast (by omega : (4 : ℤ) ≤ k₁)
    nlinarith [hk1L, hwidth1, hv3, mul_nonneg (by linarith : (0:ℝ) ≤ (k₁:ℝ) - 4) hv3.le]
  -- `gap1`'s right end + `k₁ ≤ 3` ⟹ `11 v₅ < 19 v₄` (BHK's `19 x₅ > 11 x₄`).
  have hk1le3R : (k₁ : ℝ) ≤ 3 := by exact_mod_cast hk1le3
  have hs19 : 11 * (speeds ⟨4, by omega⟩ : ℝ) < 19 * (speeds ⟨3, by omega⟩ : ℝ) := by
    nlinarith [hk1R, hk1le3R, hv4, mul_nonneg (by linarith : (0:ℝ) ≤ 3 - (k₁:ℝ)) hv4.le]
  -- `k₂ ∈ {2, 3}`.
  have hk2ge2 : (2 : ℤ) ≤ k₂ := by
    by_contra h; push_neg at h
    have : (k₂ : ℝ) ≤ 1 := by exact_mod_cast (by omega : k₂ ≤ 1)
    nlinarith [hk2R, h35, hv3, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (k₂:ℝ)) hv3.le]
  have hk2le3 : k₂ ≤ (3 : ℤ) := by
    by_contra h; push_neg at h
    have hk4 : (4 : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast (by omega : (4 : ℤ) ≤ k₂)
    nlinarith [hk2L, hs19, hv4, mul_nonneg (by linarith : (0:ℝ) ≤ (k₂:ℝ) - 4) hv4.le]
  -- The four `(k₁, k₂) ∈ {2,3} × {2,3}` pairs are each contradictory (linear).
  interval_cases k₁ <;> interval_cases k₂ <;>
    linarith [hk1L, hk1R, hk2L, hk2R, hA, hv3, hv4, h45]

/-- **BHK Case 5.1.1 (`k ≥ 3`, `x₁ < 14/3`).**  Covers BHK conditions 1, 3, 4
    (their `x₁`-bounds `14/3, 14/4, 17/5` all satisfy `x₁ < 14/3`).  No `l ≥ i`
    configuration exists; BHK argues directly (p. 16).

    `v₂ > 8/9` (`511_v2_lb`) makes `[21/16, 11/6]` a 123-gap (`511_gap123`), whence
    `25 v₄ < 32 v₃` (`511_x4_bound`, i.e. `x₄ > 25/32`).  Then split on the runner-4
    `k = 2` block position relative to `121/78`:
    * `13 x₄ > 11` (branch B): `gap2b = [21/16, 121/78]` is a 1234-gap runner 5
      cannot cover (`511_no_cover_B`).
    * `13 x₄ ≤ 11` (branch A): `gap1 = [21/16, (11/6)x₄]` and `gap2a = [13x₄/6, 11/6]`
      are 1234-gaps that runner 5 cannot cover simultaneously (`511_no_cover_A`),
      via BHK's `19 x₅ > 11 x₄` reconstructed as `11 v₅ < 19 v₄` (numerically
      verified, `experiments/bhk_511_endgame_verify.py`). -/
lemma bhk_s5_case51_subcase_511 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (hcon : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (hx1 : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 14 / 3) :
    False := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hsmallR : 3 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsmall
  have hx1R : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 14 * (speeds ⟨0, by omega⟩ : ℝ) := by
    rw [div_lt_div_iff₀ hv1 (by norm_num : (0 : ℝ) < 3)] at hx1; linarith [hx1]
  have hv2lb := bhk_s5_case51_511_v2_lb speeds hmono hsmall k D hk3 hD hkD
  have hgap123 := bhk_s5_case51_511_gap123 speeds hmono hpos hv2lb hsmallR hx1R
  have hx4 := bhk_s5_case51_511_x4_bound speeds hmono hpos hcon hgap123
  by_cases hbranch : 13 * (speeds ⟨2, by omega⟩ : ℝ) ≤ 11 * (speeds ⟨3, by omega⟩ : ℝ)
  · -- branch A (`13 x₄ ≤ 11`)
    exact bhk_s5_case51_511_no_cover_A speeds hmono hpos hcon hx4 hbranch
      (bhk_s5_case51_511_gap1 speeds hmono hpos hv2lb hsmallR hx1R)
      (bhk_s5_case51_511_gap2a speeds hmono hpos hv2lb hsmallR hx1R hx4)
  · -- branch B (`13 x₄ > 11`)
    push_neg at hbranch
    exact bhk_s5_case51_511_no_cover_B speeds hmono hpos hcon
      (bhk_s5_case51_511_gap2b speeds hmono hpos hv2lb hsmallR hx1R hbranch)

/-- **Case 5.1.2, the `v₂` lower bound.**  With `k = 3` and `x₁ > 8`
    (`8 v₁ < v₃`), BHK's `v₂ = 1 − v₁/3 > 23/24`, i.e. `23 v₃ < 24 v₂`. -/
lemma bhk_s5_case51_512_v2_lb (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (k D : ℕ)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) (hk : k = 3)
    (hx1 : 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)) :
    23 * (speeds ⟨2, by omega⟩ : ℝ) < 24 * (speeds ⟨1, by omega⟩ : ℝ) := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hDc : (D : ℝ) = (speeds ⟨2, by omega⟩ : ℝ) - (speeds ⟨1, by omega⟩ : ℝ) :=
    bhk_s5_case51_D_cast speeds hmono D hD
  have hV1 : (speeds ⟨0, by omega⟩ : ℝ) = (D : ℝ) * 3 := by rw [hkD, hk]; push_cast; ring
  rw [lt_div_iff₀ hv1] at hx1
  linarith [hDc, hV1]

/-- **Case 5.1.2, the `x₄` upper bound (`x₄ > 9/10`).**  With `k = 3` and
    `8 < x₁ < 26/3`, the eqn-(32) bounds hold for `i = 2`, `l = 1`, so
    `config_window_safe` yields the triple configuration `I₁`, `I₃` (123-gaps at
    `t₀ = (2+1/3)/v₃`); `span_l1` then gives `9 v₄ < 10 v₃`. -/
lemma bhk_s5_case51_512_x4_ub (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (k D : ℕ) (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k) (hk : k = 3)
    (hx1 : 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (hx1' : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3) :
    9 * (speeds ⟨3, by omega⟩ : ℝ) < 10 * (speeds ⟨2, by omega⟩ : ℝ) := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hDc : (D : ℝ) = (speeds ⟨2, by omega⟩ : ℝ) - (speeds ⟨1, by omega⟩ : ℝ) :=
    bhk_s5_case51_D_cast speeds hmono D hD
  have hV1 : (speeds ⟨0, by omega⟩ : ℝ) = (D : ℝ) * 3 := by rw [hkD, hk]; push_cast; ring
  rw [lt_div_iff₀ hv1] at hx1
  rw [div_lt_iff₀ hv1] at hx1'
  have hsafe := bhk_s5_case51_config_window_safe speeds hmono hpos 2 1 D hD
    (by simp only [Nat.cast_ofNat]; nlinarith [hx1', hv1])
    (by simp only [Nat.cast_ofNat, Nat.cast_one]; nlinarith [hx1, hV1, hDc])
    (by simp only [Nat.cast_ofNat, Nat.cast_one]; nlinarith [hx1])
  simp only [Nat.cast_ofNat] at hsafe
  have hgapI1 := hsafe 0 (by norm_num)
  have hgapI3 := hsafe 1 (by norm_num)
  simp only [Nat.cast_zero, zero_div, add_zero] at hgapI1
  simp only [Nat.cast_one] at hgapI3
  have h22 : 3 * (speeds ⟨3, by omega⟩ : ℝ) < 4 * (speeds ⟨2, by omega⟩ : ℝ) :=
    bhk_s5_case51_x4_from_I1 speeds hmono hpos
      (bhk_prop11_gap_covered speeds hcover hgapI1)
  exact bhk_s5_case51_span_l1 speeds hmono hpos hcover
    ((2 + 1 / 3) / (speeds ⟨2, by omega⟩ : ℝ)) hgapI1 hgapI3 h22

/-- **Case 5.1.2, the 1234-gap.**  The bounds `23 v₃ < 24 v₂` (v₂ > 23/24),
    `9 v₄ < 10 v₃` (x₄ > 9/10) and `8 v₁ < v₃ < (26/3) v₁` (8 < x₁ < 26/3) make
    runners 1, 2, 3, 4 all safe on `[52/(23 v₃), 51/(20 v₃)]` (BHK `[52/23,
    51/20]`): runner 1 lies in 1-gap `k = 0`, runners 2, 3, 4 in their `k = 2`
    gaps. -/
lemma bhk_s5_case51_512_gap1234 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hv2 : 23 * (speeds ⟨2, by omega⟩ : ℝ) < 24 * (speeds ⟨1, by omega⟩ : ℝ))
    (hv4 : 9 * (speeds ⟨3, by omega⟩ : ℝ) < 10 * (speeds ⟨2, by omega⟩ : ℝ))
    (hx1lo : 8 * (speeds ⟨0, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ))
    (hx1hi : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 26 * (speeds ⟨0, by omega⟩ : ℝ)) :
    ∀ s ∈ Set.Icc (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ)))
        (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s) := by
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv2p : (0 : ℝ) < (speeds ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv4p : (0 : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h23 : (0 : ℝ) < 23 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h20 : (0 : ℝ) < 20 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h12 : (speeds ⟨1, by omega⟩ : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by
    have h : speeds ⟨1, by omega⟩ < speeds ⟨2, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h23m : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨3, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨3, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  intro s hs i
  obtain ⟨hs1, hs2⟩ := hs
  fin_cases i
  · -- runner 1 (index 0): 1-gap `k = 0`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨0, by omega⟩ (hpos _) 0 s
      (le_trans (by
        rw [div_le_div_iff₀ hv1 h23, Int.cast_zero]; nlinarith [hx1hi, hv1]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h20 hv1, Int.cast_zero]; nlinarith [hx1lo, hv1]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · -- runner 2 (index 1): 2-gap `k = 2`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨1, by omega⟩ (hpos _) 2 s
      (le_trans (by
        rw [div_le_div_iff₀ hv2p h23, Int.cast_ofNat]; nlinarith [hv2, hv2p, hv3]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h20 hv2p, Int.cast_ofNat]; nlinarith [h12, hv2p, hv3]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · -- runner 3 (index 2): 2-gap `k = 2`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨2, by omega⟩ (hpos _) 2 s
      (le_trans (by
        rw [div_le_div_iff₀ hv3 h23, Int.cast_ofNat]; nlinarith [hv3]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h20 hv3, Int.cast_ofNat]; nlinarith [hv3]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot
  · -- runner 4 (index 3): 2-gap `k = 2`
    have hnot := not_mem_unsafeOf_of_in_gap speeds ⟨3, by omega⟩ (hpos _) 2 s
      (le_trans (by
        rw [div_le_div_iff₀ hv4p h23, Int.cast_ofNat]; nlinarith [h23m, hv4p, hv3]) hs1)
      (le_trans hs2 (by
        rw [div_le_div_iff₀ h20 hv4p, Int.cast_ofNat]; nlinarith [hv4, hv4p, hv3]))
    rw [mem_unsafeOf_iff] at hnot; exact not_lt.mp hnot

/-- **Case 5.1.2, runner 5 cannot cover the gap.**  The 1234-gap `[52/(23 v₃),
    51/(20 v₃)]` (BHK `[52/23, 51/20]`), being `⊆ B₅`, lies in a single 5-block
    `[(k−1/6)/v₅, (k+1/6)/v₅]`.  Subtracting the block edges gives the width bound
    `399 v₅ < 460 v₃`; the right end then forces `k ≥ 3` (via `v₃ < v₅`) while the
    left end forces `k ≤ 2` — no such integer exists.  (Only `v₃ < v₅`, i.e.
    `x₅ < 1`, is used, not BHK's conditional `x₅ < 1/2`.) -/
lemma bhk_s5_case51_512_no_cover (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i)
    (hcover : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (hgap : ∀ s ∈ Set.Icc (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ)))
        (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ))), ∀ i : Fin 4,
      (1 : ℝ) / 6 ≤ circDist ((speeds ⟨i.val, by omega⟩ : ℝ) * s)) :
    False := by
  have hv3 : (0 : ℝ) < (speeds ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hv5 : (0 : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h35 : (speeds ⟨2, by omega⟩ : ℝ) < (speeds ⟨4, by omega⟩ : ℝ) := by
    have h : speeds ⟨2, by omega⟩ < speeds ⟨4, by omega⟩ := by
      apply hmono; exact Fin.mk_lt_mk.mpr (by omega)
    exact_mod_cast h
  have h23 : (0 : ℝ) < 23 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have h20 : (0 : ℝ) < 20 * (speeds ⟨2, by omega⟩ : ℝ) := by positivity
  have hab : (52 : ℝ) / (23 * (speeds ⟨2, by omega⟩ : ℝ))
      ≤ 51 / (20 * (speeds ⟨2, by omega⟩ : ℝ)) := by
    rw [div_le_div_iff₀ h23 h20]; nlinarith [hv3]
  have hsub : Set.Icc (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ)))
      (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ))) ⊆ unsafeOf speeds ⟨4, by omega⟩ :=
    bhk_s5_case51_gap1234_subset speeds hcover hgap
  obtain ⟨k, hkL, hkR⟩ := block_containment speeds ⟨4, by omega⟩ (hpos _)
    (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ))) (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ))) hab hsub
  have hVa : (speeds ⟨4, by omega⟩ : ℝ) * (52 / (23 * (speeds ⟨2, by omega⟩ : ℝ)))
      = 52 * (speeds ⟨4, by omega⟩ : ℝ) / (23 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  have hVb : (speeds ⟨4, by omega⟩ : ℝ) * (51 / (20 * (speeds ⟨2, by omega⟩ : ℝ)))
      = 51 * (speeds ⟨4, by omega⟩ : ℝ) / (20 * (speeds ⟨2, by omega⟩ : ℝ)) := by ring
  rw [hVa, lt_div_iff₀ h23] at hkL
  rw [hVb, div_lt_iff₀ h20] at hkR
  -- hkL : ((k:ℝ) - 1/6) * (23 v₃) < 52 v₅ ;  hkR : 51 v₅ < ((k:ℝ) + 1/6) * (20 v₃)
  have width : 399 * (speeds ⟨4, by omega⟩ : ℝ) < 460 * (speeds ⟨2, by omega⟩ : ℝ) := by
    nlinarith [hkL, hkR]
  have hk_lo : (143 : ℝ) / 3 < 20 * (k : ℝ) := by
    have step : (143 : ℝ) / 3 * (speeds ⟨2, by omega⟩ : ℝ)
        < 20 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkR, h35]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk3 : (3 : ℤ) ≤ k := by
    by_contra h; push_neg at h
    have hk2r : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
    linarith [hk_lo]
  have hk_hi : 23 * (k : ℝ) < 64 := by
    have step : 23 * (k : ℝ) * (speeds ⟨2, by omega⟩ : ℝ)
        < 64 * (speeds ⟨2, by omega⟩ : ℝ) := by nlinarith [hkL, width, hv3]
    exact lt_of_mul_lt_mul_right step (le_of_lt hv3)
  have hk2 : k ≤ (2 : ℤ) := by
    by_contra h; push_neg at h
    have hk3r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (3 : ℤ) ≤ k)
    linarith [hk_hi]
  omega

/-- **BHK Case 5.1.2 (`k = 3`, `8 < x₁ < 26/3`).**  BHK condition 2.  A triple
    configuration exists at `t = 14/6` (`l = 1`), so `x₄ > 9/10` (eqn (27),
    `span_l1`); with `v₂ > 23/24` this puts `[52/23, 51/20]` in a 1234-gap that
    runner 5 cannot cover (no `i ≥ 3` with `(i−1/6)x₅ < 52/23` and
    `(i+1/6)x₅ > 51/20`). -/
lemma bhk_s5_case51_subcase_512 (speeds : Fin 5 → ℕ) (hmono : StrictMono speeds)
    (hpos : ∀ i, 0 < speeds i) (hgcd : Finset.univ.gcd speeds = 1)
    (hsmall : 3 * speeds ⟨0, by omega⟩ < speeds ⟨2, by omega⟩)
    (hcon : ∀ t : ℝ, ∃ i, circDist ((speeds i : ℝ) * t) < 1 / 6)
    (k D : ℕ) (hk3 : 3 ≤ k)
    (hD : D = speeds ⟨2, by omega⟩ - speeds ⟨1, by omega⟩)
    (hkD : speeds ⟨0, by omega⟩ = D * k)
    (hk : k = 3) (hx1 : 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ))
    (hx1' : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3) :
    False := by
  have hv2lb := bhk_s5_case51_512_v2_lb speeds hmono hpos k D hD hkD hk hx1
  have hx4ub := bhk_s5_case51_512_x4_ub speeds hmono hpos hcon k D hD hkD hk hx1 hx1'
  have hv1 : (0 : ℝ) < (speeds ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  rw [lt_div_iff₀ hv1] at hx1
  rw [div_lt_iff₀ hv1] at hx1'
  have hx1hi : 3 * (speeds ⟨2, by omega⟩ : ℝ) < 26 * (speeds ⟨0, by omega⟩ : ℝ) := by
    linarith [hx1']
  have hgap := bhk_s5_case51_512_gap1234 speeds hmono hpos hv2lb hx4ub hx1 hx1hi
  exact bhk_s5_case51_512_no_cover speeds hmono hpos hcon hgap

/-- **Case 5.1 main argument.**  For Case-5.1 speeds (`v₁ = k·D`, `k ≥ 3`,
    `D = v₃ − v₂`, `3 v₁ < v₃`, `gcd = 1`), there is a time at which every runner
    is `≥ 1/6` from the origin.  Dispatches on `x₁ = v₃/v₁`: the generic
    `l ≥ i` configuration (`config_bounds` → `x4_incompatible`) when no
    exceptional condition holds, else the explicit sub-cases 5.1.1 (`x₁ < 14/3`,
    conditions 1/3/4) and 5.1.2 (`k = 3 ∧ 8 < x₁ < 26/3`, condition 2). -/
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
  -- `hcon : ∀ t, ∃ i, circDist (vᵢ t) < 1/6` — the covering assumption.
  -- Dispatch on `x₁ = v₃/v₁` (BHK conditions 1–4 vs the generic `l ≥ i` config).
  by_cases h511 : (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 14 / 3
  · -- Case 5.1.1 (covers conditions 1, 3, 4).
    exact bhk_s5_case51_subcase_511 speeds hmono hpos hgcd hsmall hcon k D hk3 hD hkD h511
  · push_neg at h511
    by_cases h512 : k = 3 ∧ 8 < (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ)
        ∧ (speeds ⟨2, by omega⟩ : ℝ) / (speeds ⟨0, by omega⟩ : ℝ) < 26 / 3
    · -- Case 5.1.2 (condition 2).
      exact bhk_s5_case51_subcase_512 speeds hmono hpos hgcd hsmall hcon k D hk3 hD hkD
        h512.1 h512.2.1 h512.2.2
    · -- Generic case: an `l ≥ i` configuration exists; `x4_incompatible` closes it.
      obtain ⟨i, l, hil, h30, h33⟩ := bhk_s5_case51_config_bounds speeds hmono hpos hgcd
        hsmall hcon k D hk3 hD hkD h511 h512
      exact bhk_s5_case51_x4_incompatible _ i l hil h30 h33

end BHK
