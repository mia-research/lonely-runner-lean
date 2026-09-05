import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas

/-!
# n = 7 (Barajas–Serra) — Lemmas 7 and 9(ii)

Source: `sources_barajas_serra_2008.txt`, lines 444–506.

Split out from `Lemmas.lean` (which holds Lemmas 5, 6, 4(i), 9(i) and Remark 8)
to keep each file ≤ ~300 lines. These are the §6 retargeting tools that the
`|A|=5` case analysis (`five_compress`) consumes:

- **Lemma 7 (i)/(ii)** (L444): given `X` with `ℓ(X) ≤ 4` (resp. the `ν = m`
  edge), a `Λ_h` multiplier pushes `ẽ(λd, λd') ∉ X`. Needs `m > 1` for (ii).
- **Lemma 9 (ii)** (L491): for `B = {b₁,b₂,b₃}` equal-residue, level 0, with
  `ν(x)=ν(y)=h<m` and `r(y)=j·r(x)`, a multiplier compresses `ℓ(λ·B) ≤ j`,
  `j ∈ {2,3}`.

All four are **open stubs**. See `docs/n7_bs/SECTION6_PLAN.md` for the gap notes
(the `ẽ = 1` subtlety in BS's 9(ii), j=2 case).
-/

open Finset

namespace IntLRC7BS

/-- **Lemma 7 (i) (BS L450), `r(d')=2r(d)` case.** `X ⊂ ZMod 7` with `ℓ(X) ≤ 4`
(i.e. X fits in a length-4 interval), and `d, d'` at level 0 with `r(d') = 2r(d)`.
If `ν(2d − d') = h < m`, then some `λ ∈ Λ_h` sends `ẽ(λd, λd') = 2q(λd) − q(λd') ∉ X`.

BS proof (L450): pick `t ∈ ZMod 7 \ (X + {-1,0,1})` (exists since ℓ(X) ≤ 4 ⇒
`(X+{-1,0,1})` spans ≤ 6 consecutive values); retarget `q(λ(2d−d')) = t`; then
`qz_2xsuby_carry` gives `ẽ ∈ {t−1,t,t+1}`, all ∉ X.

NOTE: The correct hypothesis is `∃ a, fitsInterval X a 4` (not merely `X.card ≤ 4` —
e.g. `X={0,2,4,6}` has card 4 but `X+{-1,0,1}` covers all of ZMod 7). The
`five_compress` caller always supplies an interval-shaped X because it comes from
the §6 case-structure (q-values in a BS-assigned window).

**Open stub.** Lean sketch: obtain `t` from `fitsInterval` gap (`decide` on the
7-element case once the interval start `a` is known); `qz_retarget m h hh e hν' t`
for `e = 2*d - d'`; combine with `qz_2xsuby_carry` and case-split on the carry
`c ∈ {0,1,6}`; finite `decide` on ZMod 7 membership. -/
theorem lemma7_i (m h : ℕ) (hh : h < m) (d d' : ℤ)
    (hd : ¬ (7 : ℤ) ∣ d) (hd' : ¬ (7 : ℤ) ∣ d')
    (hr : (d' : ZMod 7) = 2 * (d : ZMod 7))
    (X : Finset (ZMod 7)) (hX : ∃ a, fitsInterval X a 4)
    (hν : (7 : ℤ) ^ h ∣ (2 * d - d')) (hν' : ¬ (7 : ℤ) ^ (h + 1) ∣ (2 * d - d')) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (lam : ZMod 7) = 1 ∧
      (2 * qz m (lam * d) - qz m (lam * d')) ∉ X := by
  obtain ⟨a, ha⟩ := hX
  -- Retarget e = 2d - d' so that q(λ e) = a - 2.
  obtain ⟨k, hqe, hk⟩ := qz_retarget m h hh (2 * d - d') hν hν' (a - 2)
  set lam : ℤ := 1 + k * 7 ^ (m - h) with hlam_def
  have hlam_res : (lam : ZMod 7) = 1 := by
    simp [hlam_def, show (7 : ZMod 7) = 0 from by decide, zero_pow (show m - h ≠ 0 from by omega)]
  refine ⟨lam, hk, hlam_res, ?_⟩
  -- Carry bound: q(λ(2d-d')) = 2 q(λd) - q(λd') + c, c ∈ {0,1,6}.
  obtain ⟨c, hc, hcarry⟩ := qz_2xsuby_carry m (lam * d) (lam * d')
  -- Rewrite λ(2d-d') = 2(λd) - (λd').
  have hlin : lam * (2 * d - d') = 2 * (lam * d) - lam * d' := by ring
  rw [hlin] at hqe
  -- So 2 q(λd) - q(λd') = (a - 2) - c.
  have hval : 2 * qz m (lam * d) - qz m (lam * d') = (a - 2) - c := by
    rw [hcarry] at hqe; linear_combination hqe
  rw [hval]
  intro hmem
  obtain ⟨j, hj⟩ := ha _ hmem
  -- a - 2 - c = a + j with c ∈ {0,1,6}, j ∈ Fin 4: impossible in ZMod 7.
  have hjlt := j.isLt
  -- a - 2 - c = a + j  ⟺  -2 - c = j (cancel a); false for c∈{0,1,6}, j∈{0,1,2,3}.
  have hj' : (-2 : ZMod 7) - c = (j.val : ZMod 7) := by
    have := hj; linear_combination this
  interval_cases (j.val) <;>
    rcases hc with hc | hc | hc <;> subst hc <;>
      revert hj' <;> decide

/-- **Lemma 7 (ii) (BS L455), `ν(2d − d') = m` edge.** Needs `m > 1`. With
`r(2d−d') ∉ X ∩ (X+1)`, a `Λ₁` multiplier (sending `q(λ(7d)) ∈ {0,6}`) forces
`q(2λd) = 2q(λd)`, whence `ẽ(λd, λd') = q(λ(2d−d')) = r(2d−d') ∉ X`.

The clean proof uses three ingredients: (1) `qz_sub_mul_pow` — since `7^m | (2d-d')`,
`qz(λd') = qz(2λd) - qz(λe)` where `e = 2d-d'`; (2) `qz_double_no_carry` /
`qz_double_carry_one` — retargeting `q(7λd)` to `0` or `6` pins the doubling carry;
(3) `qz_higher_inert` — `qz(λe) = qz(e)` since `ν(e) = m ≥ 2` and `λ ∈ Λ₁`. -/
theorem lemma7_ii (m h : ℕ) (hm : 1 < m) (d d' : ℤ)
    (hd : ¬ (7 : ℤ) ∣ d) (hd' : ¬ (7 : ℤ) ∣ d')
    (hr : (d' : ZMod 7) = 2 * (d : ZMod 7))
    (X : Finset (ZMod 7))
    (hν : (7 : ℤ) ^ m ∣ (2 * d - d'))
    (hXX : qz m (2 * d - d') ∉ (X ∩ (X.image (· + 1)))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (lam : ZMod 7) = 1 ∧
      (2 * qz m (lam * d) - qz m (lam * d')) ∉ X := by
  set e := 2 * d - d' with he_def
  set qe := qz m e with hqe_def
  -- Split hypothesis: qe ∉ X or qe ∉ X.image (· + 1)
  simp only [Finset.mem_inter, not_and_or] at hXX
  -- 7d has level 1: 7^1 | 7d and ¬ 7^2 | 7d (from ¬ 7 | d)
  have h7d_dvd : (7 : ℤ) ^ 1 ∣ 7 * d := ⟨d, by ring⟩
  have h7d_ndvd : ¬ (7 : ℤ) ^ (1 + 1) ∣ 7 * d := by
    simp only [pow_succ, pow_one]; intro ⟨c, hc⟩; exact hd ⟨c, by linarith⟩
  -- Key identity: for any unit lam = 1 + k*7^(m-1),
  -- ẽ = 2*qz(lam*d) - qz(lam*d') = qz(e) - c₂ where c₂ is the doubling carry.
  -- Proof: lam*d' = 2*(lam*d) - lam*e, and 7^m | lam*e, so
  -- qz(lam*d') = qz(2*(lam*d)) - qz(lam*e) by qz_sub_mul_pow.
  -- qz(lam*e) = qz(e) by qz_higher_inert (j=1, 7^2 | e since m ≥ 2).
  have he_dvd2 : (7 : ℤ) ^ (1 + 1) ∣ e := dvd_trans (pow_dvd_pow 7 (by omega)) hν
  -- Helper: for any lam coprime to 7, ẽ = qz(e) - (qz(2*(lam*d)) - 2*qz(lam*d))
  have etilde_eq (k : ℤ) :
      let lam := 1 + k * 7 ^ (m - 1)
      2 * qz m (lam * d) - qz m (lam * d') =
        qe - (qz m (2 * (lam * d)) - 2 * qz m (lam * d)) := by
    intro lam
    -- qz(lam*e) = qz(e) by inertness (j=1, 7^2 | e)
    have hinert : qz m (lam * e) = qe := by
      show qz m ((1 + k * 7 ^ (m - 1)) * e) = qz m e
      exact qz_higher_inert m 1 (by omega) k e he_dvd2
    -- lam*d' = 2*(lam*d) - lam*e
    have hld' : lam * d' = 2 * (lam * d) - lam * e := by rw [he_def]; ring
    -- 7^m | lam*e
    obtain ⟨w, hw⟩ := hν.mul_left lam
    have hw' : lam * e = (7 : ℤ) ^ m * w := by linarith
    -- qz(lam*d') = qz(2*(lam*d)) - (w : ZMod 7)
    have hqd' : qz m (lam * d') = qz m (2 * (lam * d)) - (w : ZMod 7) := by
      rw [hld', hw', qz_sub_mul_pow]
    -- (w : ZMod 7) = qz(lam*e) = qe
    have hw_cast : (w : ZMod 7) = qe := by
      have h1 : qz m (lam * e) = (w : ZMod 7) := by
        simp only [qz]
        rw [hw', Int.mul_ediv_cancel_left w (pow_ne_zero m (show (7:ℤ) ≠ 0 by decide))]
      rw [← h1, hinert]
    rw [hqd', hw_cast]; ring
  rcases hXX with hcase1 | hcase2
  · -- Case 1: qe ∉ X. Retarget 7d to q = 0 (no doubling carry).
    obtain ⟨k, hqk, hku⟩ := qz_retarget m 1 (by omega) (7 * d) h7d_dvd h7d_ndvd 0
    set lam := 1 + k * 7 ^ (m - 1) with hlam_def
    have hlam_res : (lam : ZMod 7) = 1 := by
      simp [hlam_def, show (7 : ZMod 7) = 0 from by decide, zero_pow (show m - 1 ≠ 0 from by omega)]
    refine ⟨lam, hku, hlam_res, ?_⟩
    rw [etilde_eq k]
    -- q(7*(lam*d)) = q(lam*(7*d)) = 0
    have hq7 : qz m (7 * (lam * d)) = 0 := by
      rw [show (7 : ℤ) * (lam * d) = lam * (7 * d) from by ring]; exact hqk
    -- No doubling carry: qz(2*(lam*d)) = 2*qz(lam*d)
    have hno_carry := qz_double_no_carry m (lam * d) hq7
    rw [hno_carry, sub_self, sub_zero]
    exact hcase1
  · -- Case 2: qe ∉ X.image (· + 1), i.e. qe - 1 ∉ X. Retarget 7d to q = 6 (carry = 1).
    have hcase2' : qe - 1 ∉ X := by
      intro hmem
      exact hcase2 (Finset.mem_image.mpr ⟨qe - 1, hmem, by ring⟩)
    obtain ⟨k, hqk, hku⟩ := qz_retarget m 1 (by omega) (7 * d) h7d_dvd h7d_ndvd 6
    set lam := 1 + k * 7 ^ (m - 1) with hlam_def
    have hlam_res : (lam : ZMod 7) = 1 := by
      simp [hlam_def, show (7 : ZMod 7) = 0 from by decide, zero_pow (show m - 1 ≠ 0 from by omega)]
    refine ⟨lam, hku, hlam_res, ?_⟩
    rw [etilde_eq k]
    -- q(7*(lam*d)) = 6
    have hq7 : qz m (7 * (lam * d)) = 6 := by
      rw [show (7 : ℤ) * (lam * d) = lam * (7 * d) from by ring]; exact hqk
    -- Doubling carry = 1: qz(2*(lam*d)) = 2*qz(lam*d) + 1
    have hcarry := qz_double_carry_one m (by omega) (lam * d) hq7
    rw [hcarry, show qe - (2 * qz m (lam * d) + 1 - 2 * qz m (lam * d)) = qe - 1 from by ring]
    exact hcase2'

/-- **Lemma 9 (ii) (BS L491), `j = 2` case.** `B = {b₁,b₂,b₃}` at level 0, equal
residue, with `x = b₁−b₃`, `y = b₂−b₃` of equal valuation `h < m` and
`r(y) = 2·r(x)`. Then a multiplier compresses `ℓ(λ·B) ≤ 2`.

BS proof (L493): set `e = 2x − y`; retarget `q(λe) = 0` via `Λ_h`; Lemma 4 gives
`ẽ(λx,λy) ∈ {0,1,6}`; a second `Λ_h` step sends `q(λ'λy) ∈ {0,6}`, so
`q(λ'λ(B−B)) ⊂ {0,6}` and Remark 8(i) gives `ℓ ≤ 2`.

**Open stub.** NOTE: BS's argument has a gap when `ẽ = 1` (it lands `q(λ'λx) = 0`
but `q(λ'λy) = 1 ∉ {0,6}`); see `SECTION6_PLAN.md`. The repair routes `ẽ = 1`
through the `j = 3` / explicit-table branch. Lean sketch: `qz_retarget` on `e`,
`lemma4_i`, then a second `qz_retarget`, then `remark8_i_int`. -/
theorem lemma9_ii_j2 (m h : ℕ) (hh : h < m) (b₁ b₂ b₃ : ℤ)
    (hs1 : (b₁ : ZMod 7) = (b₃ : ZMod 7)) (hs2 : (b₂ : ZMod 7) = (b₃ : ZMod 7))
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃)) (hy' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 2 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 2 := by
  -- Two-stage Λ-retarget (the documented `ẽ = 1` gap is closed by the carry implication
  -- `qz_combined_carry`). Set `x = b₁−b₃`, `y = b₂−b₃`, `e = 2x−y`; `r(y)=2r(x)` forces
  -- `ν₇(e) ≥ h+1 > h`. STAGE 1 sets `q(λ₁·e) = se ∈ {0,6}` (a `Λ_{h'}`/`Λ_m` retarget at
  -- the exact level of `e`, or `λ₁=1` if `7^{m+1}∣e`). STAGE 2 applies a `Λ_h` factor on
  -- `λ₁·x` to a target `t = f(se, c₃)`: `ẽ = 2q(λ₁x)−q(λ₁y) = se − c₃` is `Λ_h`-invariant
  -- (Lemma 4(i)) and `e` is inert under `Λ_h` (higher level), so in the final frame all
  -- three pairwise `q`-differences land in `{0,6}` and `remark8_i_int` gives `ℓ ≤ 2`. The
  -- carry implication `c₃=6⇒c₁=6`, `c₃=1⇒c₁=0` (`qz_combined_carry`) is exactly what
  -- rules out the bad `(c₃,c₁)` combos a single retarget cannot avoid.
  classical
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  set x : ℤ := b₁ - b₃ with hxdef
  set y : ℤ := b₂ - b₃ with hydef
  set e : ℤ := 2 * x - y with hedef
  -- Step 1: `r(y) = 2·r(x)` forces `7^{h+1} ∣ e` (the level-h terms of `2x−y` cancel).
  have he_lo : (7 : ℤ) ^ (h + 1) ∣ e := by
    have he_dvd : (7 : ℤ) ^ h ∣ e := by
      rw [hedef]; exact dvd_sub (Dvd.dvd.mul_left hx 2) hy
    have hres : (((e) / 7 ^ h : ℤ) : ZMod 7) = 0 := by
      rw [hedef, Int.sub_ediv_of_dvd _ hy, Int.mul_ediv_assoc 2 hx]
      push_cast; rw [hr]; ring
    have h7 : (7 : ℤ) ∣ (e / 7 ^ h) := by rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hres
    obtain ⟨c, hc⟩ := h7
    obtain ⟨w, hw⟩ := he_dvd
    refine ⟨c, ?_⟩
    have hwc : w = 7 * c := by
      have : e / 7 ^ h = w := by rw [hw]; exact Int.mul_ediv_cancel_left w (by positivity)
      rw [← this, hc]
    rw [hw, hwc, pow_succ]; ring
  -- STAGE 1: a unit `λ₁` and `se ∈ {0,6}` with `q(λ₁·e) = se`; `e` stays at level ≥ h+1.
  obtain ⟨lam₁, se, hlam₁, hse, hse_eq, he_high⟩ :
      ∃ (lam₁ : ℤ) (se : ZMod 7), ¬ (7 : ℤ) ∣ lam₁ ∧ (se = 0 ∨ se = 6) ∧
        qz m (lam₁ * e) = se ∧ (7 : ℤ) ^ (h + 1) ∣ lam₁ * e := by
    by_cases htop : (7 : ℤ) ^ (m + 1) ∣ e
    · -- `e ≡ 0 (mod 7^{m+1})`: `λ₁ = 1`, `q(e) = 0`.
      refine ⟨1, 0, by norm_num, Or.inl rfl, ?_, by rw [one_mul]; exact he_lo⟩
      rw [one_mul]; unfold qz
      obtain ⟨c, hc⟩ := htop
      rw [hc, pow_succ, show (7 : ℤ) ^ m * 7 * c = 7 ^ m * (7 * c) from by ring,
        Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨c, by ring⟩
    · -- extract the exact level `h'` of `e` (`h+1 ≤ h' ≤ m`)
      obtain ⟨h', hh'lo, hh'hi, hh'd, hh'd'⟩ :
          ∃ h' : ℕ, h + 1 ≤ h' ∧ h' ≤ m ∧ (7 : ℤ) ^ h' ∣ e ∧ ¬ (7 : ℤ) ^ (h' + 1) ∣ e := by
        have hex : ∃ j, ¬ (7 : ℤ) ^ (j + 1) ∣ e := ⟨m, htop⟩
        set j₀ := Nat.find hex with hj0
        have hspec : ¬ (7 : ℤ) ^ (j₀ + 1) ∣ e := Nat.find_spec hex
        have hle : j₀ ≤ m := Nat.find_le htop
        have hge : h + 1 ≤ j₀ := by
          by_contra hc; rw [not_le] at hc
          exact hspec (dvd_trans (pow_dvd_pow 7 (by omega)) he_lo)
        have hprev : ¬ ¬ (7 : ℤ) ^ ((j₀ - 1) + 1) ∣ e :=
          Nat.find_min hex (by omega : j₀ - 1 < j₀)
        rw [not_not] at hprev
        exact ⟨j₀, hge, hle, by rwa [show (j₀ - 1) + 1 = j₀ from by omega] at hprev, hspec⟩
      by_cases hh'm : h' < m
      · -- `Λ_{h'}` retarget of `e` to `0`
        obtain ⟨k, hqk, hku⟩ := qz_retarget m h' hh'm e hh'd hh'd' 0
        exact ⟨1 + k * 7 ^ (m - h'), 0, hku, Or.inl rfl, hqk, Dvd.dvd.mul_left he_lo _⟩
      · -- `h' = m`: top-level retarget of `e` to `6` (`0` unreachable at level `m`)
        have hh'eq : h' = m := by omega
        rw [hh'eq] at hh'd hh'd'
        obtain ⟨j, hju, hjq⟩ := qz_retarget_top m e hh'd hh'd' 6 (by decide)
        exact ⟨j, 6, hju, Or.inr rfl, hjq, Dvd.dvd.mul_left he_lo _⟩
  -- `ν(λ₁·x) = h` still (`λ₁` a unit), so STAGE 2's `Λ_h` retarget is available on `λ₁·x`.
  have hl1x_dvd : (7 : ℤ) ^ h ∣ lam₁ * x := Dvd.dvd.mul_left hx lam₁
  have hl1y_dvd : (7 : ℤ) ^ h ∣ lam₁ * y := Dvd.dvd.mul_left hy lam₁
  have hl1x_ndvd : ¬ (7 : ℤ) ^ (h + 1) ∣ lam₁ * x := by
    intro hdvd; refine hx' ?_
    have hcop : IsCoprime ((7 : ℤ) ^ (h + 1)) lam₁ :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp7).mpr hlam₁)
    exact hcop.dvd_of_dvd_mul_left hdvd
  -- carries on the STAGE-1 frame `(λ₁·x, λ₁·y)`, with the `2x−y ⇒ x−y` implication
  obtain ⟨c₃, c₁, hc3, hc1, hcarry3, hcarry1, himp6, himp1⟩ :=
    qz_combined_carry m (lam₁ * x) (lam₁ * y)
  have hle_eq : lam₁ * e = 2 * (lam₁ * x) - lam₁ * y := by rw [hedef]; ring
  -- `ẽ := 2q(λ₁x) − q(λ₁y) = se − c₃` (since `q(λ₁·e) = se` and `e = 2x−y`)
  have hetilde1 : 2 * qz m (lam₁ * x) - qz m (lam₁ * y) = se - c₃ := by
    have := hcarry3; rw [← hle_eq, hse_eq] at this; linear_combination -this
  -- choose the STAGE-2 target `t` so all three final differences land in `{0,6}`
  obtain ⟨t, htA, htB, htC⟩ :
      ∃ t : ZMod 7, t ∈ ({0, 6} : Finset (ZMod 7)) ∧
        (2 * t - (se - c₃)) ∈ ({0, 6} : Finset (ZMod 7)) ∧
        (- t + (se - c₃) + c₁) ∈ ({0, 6} : Finset (ZMod 7)) := by
    rcases hse with rfl | rfl <;> rcases hc3 with rfl | rfl | rfl
    · exact ⟨0, by rcases hc1 with rfl | rfl <;> decide⟩
    · have : c₁ = 0 := himp1 rfl; subst this; exact ⟨6, by decide⟩
    · have : c₁ = 6 := himp6 rfl; subst this; exact ⟨0, by decide⟩
    · exact ⟨6, by rcases hc1 with rfl | rfl <;> decide⟩
    · have : c₁ = 0 := himp1 rfl; subst this; exact ⟨6, by decide⟩
    · have : c₁ = 6 := himp6 rfl; subst this; exact ⟨0, by decide⟩
  -- STAGE 2: `Λ_h` factor on `λ₁·x` sending `q(λ·x) = t`; `λ = (1 + k₂·7^{m-h})·λ₁`.
  obtain ⟨k₂, hk₂x, hk₂u⟩ := qz_retarget m h hh (lam₁ * x) hl1x_dvd hl1x_ndvd t
  set lam : ℤ := (1 + k₂ * 7 ^ (m - h)) * lam₁ with hlam_def
  have hlam_u : ¬ (7 : ℤ) ∣ lam := by
    rw [hlam_def]; exact mt (Prime.dvd_mul hp7 |>.mp) (by tauto)
  have e1 : lam * x = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * x) := by rw [hlam_def]; ring
  have e2 : lam * y = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * y) := by rw [hlam_def]; ring
  have e3 : lam * x - lam * y = (1 + k₂ * 7 ^ (m - h)) * (lam₁ * x - lam₁ * y) := by
    rw [hlam_def]; ring
  have hfx : qz m (lam * x) = t := by rw [e1]; exact hk₂x
  -- `ẽ` is `Λ_h`-invariant (Lemma 4(i)) ⇒ `q(λ·y) = 2t − (se − c₃)`
  have hetilde_inv : 2 * qz m (lam * x) - qz m (lam * y)
      = 2 * qz m (lam₁ * x) - qz m (lam₁ * y) := by
    have hr2 : ((lam₁ * y / 7 ^ h : ℤ) : ZMod 7) = 2 * ((lam₁ * x / 7 ^ h : ℤ) : ZMod 7) := by
      rw [Int.mul_ediv_assoc lam₁ hy, Int.mul_ediv_assoc lam₁ hx]; push_cast; rw [hr]; ring
    have hlemma4 := lemma4_i m h (le_of_lt hh) k₂ (lam₁ * x) (lam₁ * y) hl1x_dvd hl1y_dvd hr2
    rw [e1, e2]; exact hlemma4
  have hfy : qz m (lam * y) = 2 * t - (se - c₃) := by
    rw [hetilde1] at hetilde_inv; rw [hfx] at hetilde_inv; linear_combination -hetilde_inv
  -- the `x−y` carry `c₁` is `Λ_h`-invariant ⇒ `q(λ·(x−y)) = q(λ·x) − q(λ·y) + c₁`
  have hcarry1' : qz m (lam * x - lam * y) = qz m (lam * x) - qz m (lam * y) + c₁ := by
    have hl1xy : (7 : ℤ) ^ h ∣ (lam₁ * x - lam₁ * y) := dvd_sub hl1x_dvd hl1y_dvd
    have hgx := qz_lambda m h (le_of_lt hh) k₂ (lam₁ * x) hl1x_dvd
    have hgy := qz_lambda m h (le_of_lt hh) k₂ (lam₁ * y) hl1y_dvd
    have hgxy := qz_lambda m h (le_of_lt hh) k₂ (lam₁ * x - lam₁ * y) hl1xy
    have hslope : (((lam₁ * x - lam₁ * y) / 7 ^ h : ℤ) : ZMod 7)
        = ((lam₁ * x / 7 ^ h : ℤ) : ZMod 7) - ((lam₁ * y / 7 ^ h : ℤ) : ZMod 7) := by
      rw [Int.sub_ediv_of_dvd _ hl1y_dvd]; push_cast; ring
    rw [e3, e1, e2, hgx, hgy, hgxy, hslope, hcarry1]; ring
  -- all three pairwise `q`-differences are in `{0,6}`: Remark 8(i) gives `ℓ ≤ 2`.
  refine ⟨lam, hlam_u, remark8_i_int m (lam * b₁) (lam * b₂) (lam * b₃) ?_ ?_ ?_⟩
  · rw [show lam * b₁ - lam * b₂ = lam * x - lam * y from by rw [hxdef, hydef]; ring,
      hcarry1', hfx, hfy]
    rw [show t - (2 * t - (se - c₃)) + c₁ = - t + (se - c₃) + c₁ from by ring]; exact htC
  · rw [show lam * b₁ - lam * b₃ = lam * x from by rw [hxdef]; ring, hfx]; exact htA
  · rw [show lam * b₂ - lam * b₃ = lam * y from by rw [hydef]; ring, hfy]; exact htB

/-- **Lemma 9 (ii) (BS L491), `j = 3` case.** As `lemma9_ii_j2` but `r(y)=3·r(x)`,
giving `ℓ(λ·B) ≤ 3` with `λ ∈ Λ_h`. BS chooses `q(λy)` by the explicit table on
`3q(y)+5q(x)` so that `q(λy) ∈ {0,5,6}`, `q(λx) ∈ {0,1,5,6}`; Lemma 4 then puts
`q(λ(y−x)) ∈ {0,1,5,6}` and Remark 8(ii) gives `ℓ ≤ 3`.

**Open stub.** Lean sketch: case-split on `3·q(y)+5·q(x)` (`decide`-friendly once
`q(λy)`/`q(λx)` levels are fixed by `qz_retarget`), then `remark8_ii_int`. -/
theorem lemma9_ii_j3 (m h : ℕ) (hh : h < m) (b₁ b₂ b₃ : ℤ)
    (hs1 : (b₁ : ZMod 7) = (b₃ : ZMod 7)) (hs2 : (b₂ : ZMod 7) = (b₃ : ZMod 7))
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃)) (hy' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 3 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 3) ∧
      (qz m (lam * b₁ - lam * b₂) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        qz m (lam * b₁ - lam * b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        qz m (lam * b₂ - lam * b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) ∧
      (∀ e : ℤ, (7 : ℤ) ^ (h + 1) ∣ e → qz m (lam * e) = qz m e) := by
  set x : ℤ := b₁ - b₃ with hx_def
  set y : ℤ := b₂ - b₃ with hy_def
  set rx : ZMod 7 := ((x / 7 ^ h : ℤ) : ZMod 7) with hrx_def
  -- residue facts: r(y) = 3·rx, r(x−y) = −2·rx
  have hry : ((y / 7 ^ h : ℤ) : ZMod 7) = 3 * rx := hr
  have hxy_dvd : (7 : ℤ) ^ h ∣ (x - y) := dvd_sub hx hy
  have hrxy : (((x - y) / 7 ^ h : ℤ) : ZMod 7) = rx - 3 * rx := by
    rw [Int.sub_ediv_of_dvd _ hy]; push_cast; rw [← hrx_def, hry]
  -- the carry on q(x − y): q(x−y) = q(x) − q(y) + c, c ∈ {0,6}
  obtain ⟨c, hc, hcarry⟩ := qz_subxy_carry m x y
  -- finite selection of a good target t (BS explicit table)
  obtain ⟨t, htA, htB, htC⟩ :
      ∃ t : ZMod 7, t ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        (qz m y + 3 * (t - qz m x)) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        ((qz m x - qz m y + c) - 2 * (t - qz m x)) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    clear hcarry hrxy hxy_dvd hry hr hrx_def
    generalize qz m x = p
    generalize qz m y = s
    rcases hc with rfl | rfl <;> revert p s <;> decide
  -- retarget q(λ x) = t
  obtain ⟨k, hqx, hk⟩ := qz_retarget m h hh x hx hx' t
  set lam : ℤ := 1 + k * 7 ^ (m - h) with hlam_def
  have hkrx : (k : ZMod 7) * rx = t - qz m x := by
    have := qz_lambda m h (le_of_lt hh) k x hx
    rw [← hrx_def] at this; rw [hqx] at this; linear_combination -this
  have h12 : qz m (lam * b₁ - lam * b₂) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    rw [show lam * b₁ - lam * b₂ = lam * (x - y) from by rw [hx_def, hy_def]; ring,
      qz_lambda m h (le_of_lt hh) k (x - y) hxy_dvd, hrxy]
    have : qz m (x - y) + (k : ZMod 7) * (rx - 3 * rx)
        = (qz m x - qz m y + c) - 2 * (t - qz m x) := by
      rw [hcarry]; linear_combination (-2 : ZMod 7) * hkrx
    rw [this]; exact htC
  have h13 : qz m (lam * b₁ - lam * b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    rw [show lam * b₁ - lam * b₃ = lam * x from by rw [hx_def]; ring, hqx]; exact htA
  have h23 : qz m (lam * b₂ - lam * b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by
    rw [show lam * b₂ - lam * b₃ = lam * y from by rw [hy_def]; ring,
      qz_lambda m h (le_of_lt hh) k y hy, hry]
    have : qz m y + (k : ZMod 7) * (3 * rx) = qz m y + 3 * (t - qz m x) := by
      linear_combination (3 : ZMod 7) * hkrx
    rw [this]; exact htB
  exact ⟨lam, hk, remark8_ii_int m (lam * b₁) (lam * b₂) (lam * b₃) h12 h13 h23,
    ⟨h12, h13, h23⟩, fun e he => qz_higher_inert m h (le_of_lt hh) k e he⟩

/-- **Two-level control (BS §6.3/6.5, case (ii.2.a)).** Compress a ratio-3 triple
`B = {b₁,b₂,b₃}` — differences at level `h < m` — to `ℓ(λ·B) ≤ 3`, while
simultaneously forcing `q(λ·f) = t` for a combination `f` at a *different* level
`μ < m` (`μ ≠ h`). Because the two structures live at distinct 7-adic levels, the
lower-level multiplier is inert on the higher-level target (`qz_higher_inert`), so
the operations compose: apply the higher level first, then the lower.

- `h < μ` (`f` higher): retarget `f` first (`Λ_μ`), then compress `B` (`Λ_h`); the
  compression is inert on `f` (level `μ ≥ h+1`), preserving `q(λ·f)`.
- `μ < h` (`B` higher): compress `B` first (`Λ_h`), then retarget `f` (`Λ_μ`); the
  retarget is inert on the level-`h` pairwise differences of `B`, so the exposed
  difference-arc facts of `lemma9_ii_j3` transfer and `remark8_ii_int` rebuilds
  the window. -/
theorem j3_control (m h μ : ℕ) (hh : h < m) (hμ : μ < m) (hne : h ≠ μ)
    (b₁ b₂ b₃ : ℤ)
    (hs1 : (b₁ : ZMod 7) = (b₃ : ZMod 7)) (hs2 : (b₂ : ZMod 7) = (b₃ : ZMod 7))
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃)) (hy' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 3 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7))
    (f : ℤ) (hf : (7 : ℤ) ^ μ ∣ f) (hf' : ¬ (7 : ℤ) ^ (μ + 1) ∣ f) (t : ZMod 7) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 3) ∧ qz m (lam * f) = t := by
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  have hcop : ∀ (u z : ℤ) (n : ℕ), ¬ (7 : ℤ) ∣ u → ¬ (7 : ℤ) ^ n ∣ z → ¬ (7 : ℤ) ^ n ∣ (u * z) :=
    fun u z n hu hz hdvd =>
      hz ((hp7.irreducible.coprime_pow_of_not_dvd n hu).symm.dvd_of_dvd_mul_left hdvd)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- h < μ: `f` is higher. Retarget `f` (Λ_μ) first, then compress `B` (Λ_h).
    obtain ⟨k₀, hqf, hk₀⟩ := qz_retarget m μ hμ f hf hf' t
    set lam0 : ℤ := 1 + k₀ * 7 ^ (m - μ) with hlam0
    -- transfer the ratio-3 hypotheses to `λ₀·B`
    have hs1' : ((lam0 * b₁ : ℤ) : ZMod 7) = ((lam0 * b₃ : ℤ) : ZMod 7) := by
      push_cast; rw [hs1]
    have hs2' : ((lam0 * b₂ : ℤ) : ZMod 7) = ((lam0 * b₃ : ℤ) : ZMod 7) := by
      push_cast; rw [hs2]
    have hx_t : (7 : ℤ) ^ h ∣ (lam0 * b₁ - lam0 * b₃) := by
      rw [show lam0 * b₁ - lam0 * b₃ = lam0 * (b₁ - b₃) from by ring]; exact hx.mul_left lam0
    have hx_t' : ¬ (7 : ℤ) ^ (h + 1) ∣ (lam0 * b₁ - lam0 * b₃) := by
      rw [show lam0 * b₁ - lam0 * b₃ = lam0 * (b₁ - b₃) from by ring]
      exact hcop lam0 (b₁ - b₃) (h + 1) hk₀ hx'
    have hy_t : (7 : ℤ) ^ h ∣ (lam0 * b₂ - lam0 * b₃) := by
      rw [show lam0 * b₂ - lam0 * b₃ = lam0 * (b₂ - b₃) from by ring]; exact hy.mul_left lam0
    have hy_t' : ¬ (7 : ℤ) ^ (h + 1) ∣ (lam0 * b₂ - lam0 * b₃) := by
      rw [show lam0 * b₂ - lam0 * b₃ = lam0 * (b₂ - b₃) from by ring]
      exact hcop lam0 (b₂ - b₃) (h + 1) hk₀ hy'
    have hr_t : (((lam0 * b₂ - lam0 * b₃) / 7 ^ h : ℤ) : ZMod 7)
        = 3 * (((lam0 * b₁ - lam0 * b₃) / 7 ^ h : ℤ) : ZMod 7) := by
      rw [show lam0 * b₂ - lam0 * b₃ = lam0 * (b₂ - b₃) from by ring,
          show lam0 * b₁ - lam0 * b₃ = lam0 * (b₁ - b₃) from by ring,
          Int.mul_ediv_assoc lam0 hy, Int.mul_ediv_assoc lam0 hx]
      push_cast; rw [hr]; ring
    obtain ⟨lam1, hlam1, ⟨a, hfit⟩, _, hinert⟩ :=
      lemma9_ii_j3 m h hh (lam0 * b₁) (lam0 * b₂) (lam0 * b₃) hs1' hs2' hx_t hx_t' hy_t hy_t' hr_t
    refine ⟨lam1 * lam0, ?_, ⟨a, ?_⟩, ?_⟩
    · intro hdvd; rcases hp7.dvd_mul.mp hdvd with h' | h'
      · exact hlam1 h'
      · exact hk₀ h'
    · simpa only [mul_assoc] using hfit
    · rw [show lam1 * lam0 * f = lam1 * (lam0 * f) from by ring,
          hinert (lam0 * f) (dvd_trans (pow_dvd_pow 7 (by omega : h + 1 ≤ μ)) (hf.mul_left lam0))]
      exact hqf
  · -- μ < h: `B` is higher. Compress `B` (Λ_h) first, then retarget `f` (Λ_μ).
    obtain ⟨lam1, hlam1, _, ⟨hf12, hf13, hf23⟩, _⟩ :=
      lemma9_ii_j3 m h hh b₁ b₂ b₃ hs1 hs2 hx hx' hy hy' hr
    have hf_l : (7 : ℤ) ^ μ ∣ (lam1 * f) := hf.mul_left lam1
    have hf_l' : ¬ (7 : ℤ) ^ (μ + 1) ∣ (lam1 * f) := hcop lam1 f (μ + 1) hlam1 hf'
    obtain ⟨k₀, hqf, hk₀⟩ := qz_retarget m μ hμ (lam1 * f) hf_l hf_l' t
    set lam0 : ℤ := 1 + k₀ * 7 ^ (m - μ) with hlam0
    -- pairwise differences of B live at level ≥ h ≥ μ+1, so Λ_μ is inert on them
    have hdvd12 : (7 : ℤ) ^ (μ + 1) ∣ (b₁ - b₂) :=
      dvd_trans (pow_dvd_pow 7 (by omega : μ + 1 ≤ h))
        (by rw [show b₁ - b₂ = (b₁ - b₃) - (b₂ - b₃) from by ring]; exact dvd_sub hx hy)
    have hdvd13 : (7 : ℤ) ^ (μ + 1) ∣ (b₁ - b₃) :=
      dvd_trans (pow_dvd_pow 7 (by omega : μ + 1 ≤ h)) hx
    have hdvd23 : (7 : ℤ) ^ (μ + 1) ∣ (b₂ - b₃) :=
      dvd_trans (pow_dvd_pow 7 (by omega : μ + 1 ≤ h)) hy
    refine ⟨lam0 * lam1, ?_,
      remark8_ii_int m (lam0 * lam1 * b₁) (lam0 * lam1 * b₂) (lam0 * lam1 * b₃) ?_ ?_ ?_, ?_⟩
    · intro hdvd; rcases hp7.dvd_mul.mp hdvd with h' | h'
      · exact hk₀ h'
      · exact hlam1 h'
    · rw [show lam0 * lam1 * b₁ - lam0 * lam1 * b₂ = lam0 * (lam1 * (b₁ - b₂)) from by ring,
          qz_higher_inert m μ (le_of_lt hμ) k₀ (lam1 * (b₁ - b₂)) (hdvd12.mul_left lam1),
          show lam1 * (b₁ - b₂) = lam1 * b₁ - lam1 * b₂ from by ring]
      exact hf12
    · rw [show lam0 * lam1 * b₁ - lam0 * lam1 * b₃ = lam0 * (lam1 * (b₁ - b₃)) from by ring,
          qz_higher_inert m μ (le_of_lt hμ) k₀ (lam1 * (b₁ - b₃)) (hdvd13.mul_left lam1),
          show lam1 * (b₁ - b₃) = lam1 * b₁ - lam1 * b₃ from by ring]
      exact hf13
    · rw [show lam0 * lam1 * b₂ - lam0 * lam1 * b₃ = lam0 * (lam1 * (b₂ - b₃)) from by ring,
          qz_higher_inert m μ (le_of_lt hμ) k₀ (lam1 * (b₂ - b₃)) (hdvd23.mul_left lam1),
          show lam1 * (b₂ - b₃) = lam1 * b₂ - lam1 * b₃ from by ring]
      exact hf23
    · rw [show lam0 * lam1 * f = lam0 * (lam1 * f) from by ring]; exact hqf

/-- **Two-level control, top-level target (`μ = m`).** The `μ = m` boundary of
`j3_control`: compress a ratio-3 triple `B` to `ℓ ≤ 3` while forcing `q(λ·f) = t`
for a combination `f` at the *top* level `m`. Since `m > h`, retarget `f` first
(via `qz_retarget_top`, which needs `t ≠ 0`), then compress `B`; the compression
(`Λ_h`) is inert on `f` (level `m ≥ h+1`), preserving `q(λ·f)`. -/
theorem j3_control_top (m h : ℕ) (hh : h < m) (b₁ b₂ b₃ : ℤ)
    (hs1 : (b₁ : ZMod 7) = (b₃ : ZMod 7)) (hs2 : (b₂ : ZMod 7) = (b₃ : ZMod 7))
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃)) (hy' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 3 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7))
    (f : ℤ) (hf : (7 : ℤ) ^ m ∣ f) (hf' : ¬ (7 : ℤ) ^ (m + 1) ∣ f) (t : ZMod 7) (ht : t ≠ 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ (∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 3) ∧ qz m (lam * f) = t := by
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  have hcop : ∀ (u z : ℤ) (n : ℕ), ¬ (7 : ℤ) ∣ u → ¬ (7 : ℤ) ^ n ∣ z → ¬ (7 : ℤ) ^ n ∣ (u * z) :=
    fun u z n hu hz hdvd =>
      hz ((hp7.irreducible.coprime_pow_of_not_dvd n hu).symm.dvd_of_dvd_mul_left hdvd)
  obtain ⟨j, hj, hqf⟩ := qz_retarget_top m f hf hf' t ht
  have hs1' : ((j * b₁ : ℤ) : ZMod 7) = ((j * b₃ : ℤ) : ZMod 7) := by push_cast; rw [hs1]
  have hs2' : ((j * b₂ : ℤ) : ZMod 7) = ((j * b₃ : ℤ) : ZMod 7) := by push_cast; rw [hs2]
  have hx_t : (7 : ℤ) ^ h ∣ (j * b₁ - j * b₃) := by
    rw [show j * b₁ - j * b₃ = j * (b₁ - b₃) from by ring]; exact hx.mul_left j
  have hx_t' : ¬ (7 : ℤ) ^ (h + 1) ∣ (j * b₁ - j * b₃) := by
    rw [show j * b₁ - j * b₃ = j * (b₁ - b₃) from by ring]; exact hcop j (b₁ - b₃) (h + 1) hj hx'
  have hy_t : (7 : ℤ) ^ h ∣ (j * b₂ - j * b₃) := by
    rw [show j * b₂ - j * b₃ = j * (b₂ - b₃) from by ring]; exact hy.mul_left j
  have hy_t' : ¬ (7 : ℤ) ^ (h + 1) ∣ (j * b₂ - j * b₃) := by
    rw [show j * b₂ - j * b₃ = j * (b₂ - b₃) from by ring]; exact hcop j (b₂ - b₃) (h + 1) hj hy'
  have hr_t : (((j * b₂ - j * b₃) / 7 ^ h : ℤ) : ZMod 7)
      = 3 * (((j * b₁ - j * b₃) / 7 ^ h : ℤ) : ZMod 7) := by
    rw [show j * b₂ - j * b₃ = j * (b₂ - b₃) from by ring,
        show j * b₁ - j * b₃ = j * (b₁ - b₃) from by ring,
        Int.mul_ediv_assoc j hy, Int.mul_ediv_assoc j hx]
    push_cast; rw [hr]; ring
  obtain ⟨lam1, hlam1, ⟨a, hfit⟩, _, hinert⟩ :=
    lemma9_ii_j3 m h hh (j * b₁) (j * b₂) (j * b₃) hs1' hs2' hx_t hx_t' hy_t hy_t' hr_t
  refine ⟨lam1 * j, ?_, ⟨a, ?_⟩, ?_⟩
  · intro hdvd; rcases hp7.dvd_mul.mp hdvd with h' | h'
    · exact hlam1 h'
    · exact hj h'
  · simpa only [mul_assoc] using hfit
  · rw [show lam1 * j * f = lam1 * (j * f) from by ring,
        hinert (j * f) (dvd_trans (pow_dvd_pow 7 (by omega : h + 1 ≤ m)) (hf.mul_left j))]
    exact hqf

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 4000 in
/-- **`(3,1,1)` ratio-3 h<m, `ν(e₄₅)=ν(e₁₃)` diff-arc decide** (BS L607–632, `+`-sign).
Everything is at level `h`, so a `Λ_h` shift `k` moves the four diff-arcs linearly:
`X=q(e₁₃)↦X+3k`, `Y=q(e₂₃)↦Y+k`, `Z=q(e₁₂)↦Z+2k`, `W=q(e₄₅)↦W+3k`. The
`f=e₄₅−e₁₃` retarget pins `ẽ' = q(e₁₃)−q(e₄₅) ∈ {0,1}` (so `W ∈ {X, X−1}`), and
`Z ∈ {X−Y, X−Y+6}` (the `q(e₁₂)` carry). Except at BS's exceptional `ũ=3∧ẽ'=0`
(`3X+5Y=3 ∧ W=X`), some `k` lands either all three `A₁` diff-arcs in `{0,6}`
(`ℓ(A₁)≤2`, Lemma 5 needs no carve) or in `{0,1,5,6}` with `W+3k∈{0,6}` (`ℓ≤3` and
`ẽ(d₄,d₅)∉{2,4}`). -/
theorem ii2b_shift (X Y Z W : ZMod 7)
    (hZ : Z = X - Y ∨ Z = X - Y + 6) (hW : W = X ∨ W = X - 1)
    (hexc : ¬ (3 * X + 5 * Y = 3 ∧ W = X)) :
    ∃ k : ZMod 7,
      (X + 3 * k ∈ ({0, 6} : Finset (ZMod 7)) ∧ Y + k ∈ ({0, 6} : Finset (ZMod 7)) ∧
        Z + 2 * k ∈ ({0, 6} : Finset (ZMod 7))) ∨
      (X + 3 * k ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        Y + k ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        Z + 2 * k ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) ∧
        W + 3 * k ∈ ({0, 6} : Finset (ZMod 7))) := by
  -- Split `Z,W` off first (`decide`'s instance synthesis chokes on the full 4-∀ nesting).
  rcases hZ with rfl | rfl <;> rcases hW with hw | hw <;> subst W <;> revert hexc X Y <;> decide

/-- `6 = -1` in `ZMod 7` (carry-normalization constant). -/
private theorem six_eq_neg_one_z7 : (6 : ZMod 7) = -1 := by decide

/-- Exceptional-column landing: the shift `k = 5(3−x)` sends `x ↦ x + 3k = 3`. -/
private theorem ii2b_exc_X : ∀ x : ZMod 7, x + 3 * (5 * (3 - x)) = 3 := by decide

/-- On the `ũ = 3` column the same shift sends `y ↦ y + k = 3`. -/
private theorem ii2b_exc_Y : ∀ x y : ZMod 7, 3 * x + 5 * y = 3 → y + 5 * (3 - x) = 3 := by
  decide

/-- On the `ũ = 3` column the `q(e₁₂)` arc lands in `{0,6}`. -/
private theorem ii2b_exc_Z : ∀ x y z : ZMod 7,
    (z = x - y ∨ z = x - y + 6) → 3 * x + 5 * y = 3 →
    (z + 2 * (5 * (3 - x)) = 0 ∨ z + 2 * (5 * (3 - x)) = 6) := by decide

/-- Doubling an arc at `3`: `2·3 + ε ∈ {0,6}` for `ε ∈ {0,1}`. -/
private theorem ii2b_dbl6 : ∀ ε : ZMod 7, (ε = 0 ∨ ε = 1) →
    2 * 3 + ε ∈ ({0, 6} : Finset (ZMod 7)) := by decide

/-- Doubling an arc at `3`, into the wide set. -/
private theorem ii2b_dbl6' : ∀ ε : ZMod 7, (ε = 0 ∨ ε = 1) →
    2 * 3 + ε ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by decide

/-- Doubling an arc in `{0,6}` lands in `{0,1,5,6}`. -/
private theorem ii2b_dblC : ∀ z ε : ZMod 7, (ε = 0 ∨ ε = 1) → (z = 0 ∨ z = 6) →
    2 * z + ε ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) := by decide

/-- **Case (ii.2.b) two-stage control (BS L607–635).** Given a ratio-3 pair of
level-`h` differences `A = b₂−b₃`, `B = b₁−b₃` (`r(A) = 3·r(B)`, BS's
`e₁₃`/`e₂₃`) and a companion `E` at the same level with the *same leading
residue* as `A` (BS: `r(e₄₅) = r(e₁₃)`, arranged via `lemma11_s` with
`s := r(e₄₅)`), some multiplier `λ` coprime to 7 places the arcs of
`{b₁,b₂,b₃}` in a window of length 2, or in a window of length 3 with
`q(λE) ∈ {0,6}` (which carves `ẽ(d₄,d₅) ∉ {2,4}` downstream).

Stage 1 (BS: "Set `f = e₄₅ − e₁₃` ... by Lemma 2 we may assume `q(f) = 0` (or
`f = N/7` with the same consequences)"): `f := A − E` has `ν(f) > h`; a
retarget at level `ν(f) < m` pins `q(λ₀f) = 0` and the subtraction carry gives
`q(λ₀E) ∈ {q(λ₀A), q(λ₀A) − 1}`; at `ν(f) = m` a top retarget `q(jf) = 1`
makes `jf ≡ 7^m` exactly and `qz_sub_mul_pow` gives `q(jE) = q(jA) − 1`;
at `ν(f) ≥ m+1` (incl. `f = 0`) the relation `q(E) = q(A)` is free.

Stage 2 (BS ũ-table): the diff-arc decide `ii2b_shift` picks the `Λ_h` shift.
The exceptional column `ũ = 3 ∧ ẽ' = 0` is closed by doubling
(`qz_double_pin`): the shift `k = 5(3−X)` lands `q(e₁₃)=q(e₂₃)=q(e₄₅)=3`,
`q(e₁₂) ∈ {0,6}`, which double into `{0,6}`/`{0,1,5,6}` arcs (BS L633–635). -/
theorem ii2b_control (m h : ℕ) (hh : h < m) (b₁ b₂ b₃ E : ℤ)
    (hx : (7 : ℤ) ^ h ∣ (b₁ - b₃)) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ (b₁ - b₃))
    (hy : (7 : ℤ) ^ h ∣ (b₂ - b₃))
    (hr : (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7) = 3 * (((b₁ - b₃) / 7 ^ h : ℤ) : ZMod 7))
    (hE : (7 : ℤ) ^ h ∣ E)
    (hrE : ((E / 7 ^ h : ℤ) : ZMod 7) = (((b₂ - b₃) / 7 ^ h : ℤ) : ZMod 7)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      ((∃ a : ZMod 7, fitsInterval
          ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)} : Finset (ZMod 7)) a 2) ∨
       ((∃ a : ZMod 7, fitsInterval
          ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)} : Finset (ZMod 7)) a 3) ∧
        qz m (lam * E) ∈ ({0, 6} : Finset (ZMod 7)))) := by
  haveI h7p : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  set A : ℤ := b₂ - b₃ with hA_def
  set B : ℤ := b₁ - b₃ with hB_def
  set C : ℤ := b₂ - b₁ with hC_def
  -- leading residue of `B` is a unit
  set ρ : ZMod 7 := ((B / 7 ^ h : ℤ) : ZMod 7) with hρ_def
  have hρ_ne : ρ ≠ 0 := by
    intro h0
    rw [hρ_def, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    obtain ⟨c, hc⟩ := h0
    exact hx' ⟨c, by rw [← Int.mul_ediv_cancel' hx, hc, pow_succ]; ring⟩
  -- `C = A − B` at level `h` with `r(C) = 2ρ`
  have hCsub : C = A - B := by rw [hA_def, hB_def, hC_def]; ring
  have hC_dvd : (7 : ℤ) ^ h ∣ C := by rw [hCsub]; exact dvd_sub hy hx
  have hCr : ((C / 7 ^ h : ℤ) : ZMod 7) = 2 * ρ := by
    rw [hCsub, Int.sub_ediv_of_dvd _ hx]
    push_cast
    rw [hr, ← hρ_def]; ring
  -- Stage 1: a multiplier `lam₀` pinning `q(λ₀E) ∈ {q(λ₀A), q(λ₀A) − 1}`.
  set f : ℤ := A - E with hf_def
  have hf_dvd : (7 : ℤ) ^ h ∣ f := by rw [hf_def]; exact dvd_sub hy hE
  have hf_high : (7 : ℤ) ^ (h + 1) ∣ f := by
    have hq0 : ((f / 7 ^ h : ℤ) : ZMod 7) = 0 := by
      rw [hf_def, Int.sub_ediv_of_dvd _ hE]
      push_cast
      rw [hrE]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hq0
    obtain ⟨c, hc⟩ := hq0
    exact ⟨c, by rw [← Int.mul_ediv_cancel' hf_dvd, hc, pow_succ]; ring⟩
  obtain ⟨lam₀, hlam₀, hWX⟩ :
      ∃ lam₀ : ℤ, ¬ (7 : ℤ) ∣ lam₀ ∧
        (qz m (lam₀ * E) = qz m (lam₀ * A) ∨
         qz m (lam₀ * E) = qz m (lam₀ * A) - 1) := by
    by_cases hftop : (7 : ℤ) ^ (m + 1) ∣ f
    · -- `f` invisible mod `7^{m+1}`: `q(E) = q(A)` outright.
      obtain ⟨c, hc⟩ := hftop
      refine ⟨1, by norm_num, Or.inl ?_⟩
      have hEeq : (1 : ℤ) * E = 1 * A - 7 ^ m * (7 * c) := by
        rw [one_mul, one_mul, show E = A - f from by rw [hf_def]; ring, hc, pow_succ]; ring
      rw [hEeq, qz_sub_mul_pow]
      have h7c : ((7 * c : ℤ) : ZMod 7) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact Dvd.intro c rfl
      rw [h7c]; ring
    · have hfne : f ≠ 0 := fun h0 => hftop (h0 ▸ dvd_zero _)
      set μ : ℕ := padicValInt 7 f with hμ_def
      have hfd : (7 : ℤ) ^ μ ∣ f := padicValInt_dvd f
      have hfd' : ¬ (7 : ℤ) ^ (μ + 1) ∣ f := by
        intro hdvd
        have hle : μ + 1 ≤ padicValInt 7 f :=
          ((padicValInt_dvd_iff (μ + 1) f).mp hdvd).resolve_left hfne
        omega
      have hμ_le : μ ≤ m := by
        by_contra hgt
        exact hftop (dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ μ)) hfd)
      rcases lt_or_eq_of_le hμ_le with hμm | hμm
      · -- `h < ν(f) < m`: retarget `q(λ₀f) = 0`, then the subtraction carry.
        obtain ⟨k₀, hqf0, hk₀⟩ := qz_retarget m μ hμm f hfd hfd' 0
        refine ⟨1 + k₀ * 7 ^ (m - μ), hk₀, ?_⟩
        obtain ⟨c, hc, hcarry⟩ := qz_subxy_carry m ((1 + k₀ * 7 ^ (m - μ)) * A)
          ((1 + k₀ * 7 ^ (m - μ)) * f)
        have hEsub : (1 + k₀ * 7 ^ (m - μ)) * E
            = (1 + k₀ * 7 ^ (m - μ)) * A - (1 + k₀ * 7 ^ (m - μ)) * f := by
          rw [show E = A - f from by rw [hf_def]; ring]; ring
        rw [hEsub, hcarry, hqf0]
        rcases hc with rfl | rfl
        · exact Or.inl (by ring)
        · refine Or.inr ?_
          rw [six_eq_neg_one_z7]; ring
      · -- `ν(f) = m`: top retarget `q(jf) = 1` makes `jf ≡ 7^m` exactly.
        rw [hμm] at hfd hfd'
        obtain ⟨j, hj, hjq⟩ := qz_retarget_top m f hfd hfd' 1 one_ne_zero
        obtain ⟨u, hu⟩ := hfd
        have hjf : j * f = 7 ^ m * (j * u) := by rw [hu]; ring
        have hq_ju : ((j * u : ℤ) : ZMod 7) = 1 := by
          rw [← hjq]
          simp only [qz]
          rw [hjf, Int.mul_ediv_cancel_left _ (by positivity : (7 : ℤ) ^ m ≠ 0)]
        refine ⟨j, hj, Or.inr ?_⟩
        rw [show j * E = j * A - 7 ^ m * (j * u) from by
              rw [show E = A - f from by rw [hf_def]; ring, hu]; ring,
            qz_sub_mul_pow, hq_ju]
  -- Stage 2: transfer structure to the `lam₀`-dilated tuple.
  have hA0 : (7 : ℤ) ^ h ∣ (lam₀ * A) := hy.mul_left lam₀
  have hB0 : (7 : ℤ) ^ h ∣ (lam₀ * B) := hx.mul_left lam₀
  have hC0 : (7 : ℤ) ^ h ∣ (lam₀ * C) := hC_dvd.mul_left lam₀
  have hE0 : (7 : ℤ) ^ h ∣ (lam₀ * E) := hE.mul_left lam₀
  have hres : ∀ x : ℤ, (7 : ℤ) ^ h ∣ x → (((lam₀ * x) / 7 ^ h : ℤ) : ZMod 7)
      = (lam₀ : ZMod 7) * ((x / 7 ^ h : ℤ) : ZMod 7) := by
    intro x hxd
    rw [Int.mul_ediv_assoc lam₀ hxd]; push_cast; ring
  set ρ' : ZMod 7 := (lam₀ : ZMod 7) * ρ with hρ'_def
  have hρ'_ne : ρ' ≠ 0 := by
    refine mul_ne_zero (fun h0 => hlam₀ ?_) hρ_ne
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd lam₀ 7).mp h0
  have hrA : (((lam₀ * A) / 7 ^ h : ℤ) : ZMod 7) = 3 * ρ' := by
    rw [hres A hy, hr, hρ'_def]; ring
  have hrB : (((lam₀ * B) / 7 ^ h : ℤ) : ZMod 7) = ρ' := by
    rw [hres B hx, hρ'_def, hρ_def]
  have hrC : (((lam₀ * C) / 7 ^ h : ℤ) : ZMod 7) = 2 * ρ' := by
    rw [hres C hC_dvd, hCr, hρ'_def]; ring
  have hrE0 : (((lam₀ * E) / 7 ^ h : ℤ) : ZMod 7) = 3 * ρ' := by
    rw [hres E hE, hrE, hr, hρ'_def]; ring
  set X : ZMod 7 := qz m (lam₀ * A) with hX_def
  set Y : ZMod 7 := qz m (lam₀ * B) with hY_def
  set Z : ZMod 7 := qz m (lam₀ * C) with hZv_def
  set W : ZMod 7 := qz m (lam₀ * E) with hWv_def
  have hZrel : Z = X - Y ∨ Z = X - Y + 6 := by
    obtain ⟨c, hc, hcarry⟩ := qz_subxy_carry m (lam₀ * A) (lam₀ * B)
    have hCeq : lam₀ * C = lam₀ * A - lam₀ * B := by rw [hCsub]; ring
    rw [hZv_def, hCeq, hcarry]
    rcases hc with rfl | rfl
    · exact Or.inl (by ring)
    · exact Or.inr (by ring)
  -- The `Λ_h` shift realization: any target `kt` moves the arcs by `(3kt, kt, 2kt, 3kt)`.
  have shift_arcs : ∀ kt : ZMod 7, ∃ lam₁ : ℤ, ¬ (7 : ℤ) ∣ lam₁ ∧
      qz m (lam₁ * (lam₀ * A)) = X + 3 * kt ∧
      qz m (lam₁ * (lam₀ * B)) = Y + kt ∧
      qz m (lam₁ * (lam₀ * C)) = Z + 2 * kt ∧
      qz m (lam₁ * (lam₀ * E)) = W + 3 * kt := by
    intro kt
    set kk : ℤ := (((kt * ρ'⁻¹ : ZMod 7)).val : ℤ) with hkk_def
    have hkk : (kk : ZMod 7) = kt * ρ'⁻¹ := by simp [hkk_def, ZMod.natCast_val]
    have h1kk : (kk : ZMod 7) * ρ' = kt := by
      rw [hkk, show kt * ρ'⁻¹ * ρ' = kt * (ρ'⁻¹ * ρ') from by ring,
          inv_mul_cancel₀ hρ'_ne, mul_one]
    refine ⟨1 + kk * 7 ^ (m - h), ?_, ?_, ?_, ?_, ?_⟩
    · intro hdvd
      have h7d : (7 : ℤ) ∣ kk * 7 ^ (m - h) :=
        Dvd.dvd.mul_left (dvd_pow_self 7 (by omega : m - h ≠ 0)) kk
      have h1 : (7 : ℤ) ∣ 1 := by
        have := dvd_sub hdvd h7d
        simpa using this
      norm_num at h1
    · rw [qz_lambda m h (le_of_lt hh) kk (lam₀ * A) hA0, hrA, ← hX_def,
          show (kk : ZMod 7) * (3 * ρ') = 3 * ((kk : ZMod 7) * ρ') from by ring, h1kk]
    · rw [qz_lambda m h (le_of_lt hh) kk (lam₀ * B) hB0, hrB, ← hY_def, h1kk]
    · rw [qz_lambda m h (le_of_lt hh) kk (lam₀ * C) hC0, hrC, ← hZv_def,
          show (kk : ZMod 7) * (2 * ρ') = 2 * ((kk : ZMod 7) * ρ') from by ring, h1kk]
    · rw [qz_lambda m h (le_of_lt hh) kk (lam₀ * E) hE0, hrE0, ← hWv_def,
          show (kk : ZMod 7) * (3 * ρ') = 3 * ((kk : ZMod 7) * ρ') from by ring, h1kk]
  -- Window builders from the three shifted diff-arcs.
  have window2 : ∀ lam : ℤ, qz m (lam * A) ∈ ({0, 6} : Finset (ZMod 7)) →
      qz m (lam * B) ∈ ({0, 6} : Finset (ZMod 7)) →
      qz m (lam * C) ∈ ({0, 6} : Finset (ZMod 7)) →
      ∃ a : ZMod 7, fitsInterval
        ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)} : Finset (ZMod 7)) a 2 := by
    intro lam hA' hB' hC'
    obtain ⟨a, hfit⟩ := remark8_i_int m (lam * b₂) (lam * b₁) (lam * b₃)
      (by rw [show lam * b₂ - lam * b₁ = lam * C from by rw [hC_def]; ring]; exact hC')
      (by rw [show lam * b₂ - lam * b₃ = lam * A from by rw [hA_def]; ring]; exact hA')
      (by rw [show lam * b₁ - lam * b₃ = lam * B from by rw [hB_def]; ring]; exact hB')
    exact ⟨a, by rwa [Finset.insert_comm] at hfit⟩
  have window3 : ∀ lam : ℤ, qz m (lam * A) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) →
      qz m (lam * B) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) →
      qz m (lam * C) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)) →
      ∃ a : ZMod 7, fitsInterval
        ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)} : Finset (ZMod 7)) a 3 := by
    intro lam hA' hB' hC'
    obtain ⟨a, hfit⟩ := remark8_ii_int m (lam * b₂) (lam * b₁) (lam * b₃)
      (by rw [show lam * b₂ - lam * b₁ = lam * C from by rw [hC_def]; ring]; exact hC')
      (by rw [show lam * b₂ - lam * b₃ = lam * A from by rw [hA_def]; ring]; exact hA')
      (by rw [show lam * b₁ - lam * b₃ = lam * B from by rw [hB_def]; ring]; exact hB')
    exact ⟨a, by rwa [Finset.insert_comm] at hfit⟩
  by_cases hexc : 3 * X + 5 * Y = 3 ∧ W = X
  · -- Exceptional column `ũ = 3 ∧ ẽ' = 0`: land on the all-`3` column, then double.
    obtain ⟨lam₁, hl₁, hqA, hqB, hqC, hqE⟩ := shift_arcs (5 * (3 - X))
    -- the landed arcs (finite `ZMod 7` facts, file-level decides)
    have hqA3 : qz m (lam₁ * (lam₀ * A)) = 3 := by rw [hqA, ii2b_exc_X X]
    have hqB3 : qz m (lam₁ * (lam₀ * B)) = 3 := by rw [hqB, ii2b_exc_Y X Y hexc.1]
    have hqC06 : qz m (lam₁ * (lam₀ * C)) = 0 ∨ qz m (lam₁ * (lam₀ * C)) = 6 := by
      rw [hqC]; exact ii2b_exc_Z X Y Z hZrel hexc.1
    have hqE3 : qz m (lam₁ * (lam₀ * E)) = 3 := by rw [hqE, hexc.2, ii2b_exc_X X]
    -- double
    have hm1 : 1 ≤ m := by omega
    obtain ⟨εA, hεA, hdA, -, -⟩ := qz_double_pin m hm1 (lam₁ * (lam₀ * A))
    obtain ⟨εB, hεB, hdB, -, -⟩ := qz_double_pin m hm1 (lam₁ * (lam₀ * B))
    obtain ⟨εC, hεC, hdC', -, -⟩ := qz_double_pin m hm1 (lam₁ * (lam₀ * C))
    obtain ⟨εE, hεE, hdE, -, -⟩ := qz_double_pin m hm1 (lam₁ * (lam₀ * E))
    refine ⟨2 * (lam₁ * lam₀), ?_, Or.inr ⟨?_, ?_⟩⟩
    · intro hdvd
      rcases hp7.dvd_mul.mp hdvd with h' | h'
      · norm_num at h'
      · rcases hp7.dvd_mul.mp h' with h'' | h''
        · exact hl₁ h''
        · exact hlam₀ h''
    · refine window3 (2 * (lam₁ * lam₀)) ?_ ?_ ?_
      · rw [show 2 * (lam₁ * lam₀) * A = 2 * (lam₁ * (lam₀ * A)) from by ring, hdA, hqA3]
        exact ii2b_dbl6' εA hεA
      · rw [show 2 * (lam₁ * lam₀) * B = 2 * (lam₁ * (lam₀ * B)) from by ring, hdB, hqB3]
        exact ii2b_dbl6' εB hεB
      · rw [show 2 * (lam₁ * lam₀) * C = 2 * (lam₁ * (lam₀ * C)) from by ring, hdC']
        exact ii2b_dblC _ εC hεC hqC06
    · rw [show 2 * (lam₁ * lam₀) * E = 2 * (lam₁ * (lam₀ * E)) from by ring, hdE, hqE3]
      exact ii2b_dbl6 εE hεE
  · -- Generic column: the diff-arc decide picks the shift.
    obtain ⟨k, hk⟩ := ii2b_shift X Y Z W hZrel hWX hexc
    obtain ⟨lam₁, hl₁, hqA, hqB, hqC, hqE⟩ := shift_arcs k
    have hndvd : ¬ (7 : ℤ) ∣ (lam₁ * lam₀) := by
      intro hdvd
      rcases hp7.dvd_mul.mp hdvd with h' | h'
      · exact hl₁ h'
      · exact hlam₀ h'
    rcases hk with ⟨hA6, hB6, hC6⟩ | ⟨hA4, hB4, hC4, hW6⟩
    · refine ⟨lam₁ * lam₀, hndvd, Or.inl (window2 (lam₁ * lam₀) ?_ ?_ ?_)⟩
      · rw [show lam₁ * lam₀ * A = lam₁ * (lam₀ * A) from by ring, hqA]; exact hA6
      · rw [show lam₁ * lam₀ * B = lam₁ * (lam₀ * B) from by ring, hqB]; exact hB6
      · rw [show lam₁ * lam₀ * C = lam₁ * (lam₀ * C) from by ring, hqC]; exact hC6
    · refine ⟨lam₁ * lam₀, hndvd, Or.inr ⟨window3 (lam₁ * lam₀) ?_ ?_ ?_, ?_⟩⟩
      · rw [show lam₁ * lam₀ * A = lam₁ * (lam₀ * A) from by ring, hqA]; exact hA4
      · rw [show lam₁ * lam₀ * B = lam₁ * (lam₀ * B) from by ring, hqB]; exact hB4
      · rw [show lam₁ * lam₀ * C = lam₁ * (lam₀ * C) from by ring, hqC]; exact hC4
      · rw [show lam₁ * lam₀ * E = lam₁ * (lam₀ * E) from by ring, hqE]; exact hW6

end IntLRC7BS
