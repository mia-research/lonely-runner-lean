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
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
      (2 * qz m (lam * d) - qz m (lam * d')) ∉ X := by
  obtain ⟨a, ha⟩ := hX
  -- Retarget e = 2d - d' so that q(λ e) = a - 2.
  obtain ⟨k, hqe, hk⟩ := qz_retarget m h hh (2 * d - d') hν hν' (a - 2)
  set lam : ℤ := 1 + k * 7 ^ (m - h) with hlam_def
  refine ⟨lam, hk, ?_⟩
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
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧
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
    refine ⟨lam, hku, ?_⟩
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
    refine ⟨lam, hku, ?_⟩
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
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 3 := by
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
  refine ⟨lam, hk, remark8_ii_int m (lam * b₁) (lam * b₂) (lam * b₃) ?_ ?_ ?_⟩
  · -- q(λ b₁ − λ b₂) = q(λ(x − y)) ∈ {0,1,5,6}
    rw [show lam * b₁ - lam * b₂ = lam * (x - y) from by rw [hx_def, hy_def]; ring,
      qz_lambda m h (le_of_lt hh) k (x - y) hxy_dvd, hrxy]
    have hkrx : (k : ZMod 7) * rx = t - qz m x := by
      have := qz_lambda m h (le_of_lt hh) k x hx
      rw [← hrx_def] at this; rw [hqx] at this; linear_combination -this
    have : qz m (x - y) + (k : ZMod 7) * (rx - 3 * rx)
        = (qz m x - qz m y + c) - 2 * (t - qz m x) := by
      rw [hcarry]; linear_combination (-2 : ZMod 7) * hkrx
    rw [this]; exact htC
  · -- q(λ b₁ − λ b₃) = q(λ x) = t ∈ {0,1,5,6}
    rw [show lam * b₁ - lam * b₃ = lam * x from by rw [hx_def]; ring, hqx]; exact htA
  · -- q(λ b₂ − λ b₃) = q(λ y) ∈ {0,1,5,6}
    rw [show lam * b₂ - lam * b₃ = lam * y from by rw [hy_def]; ring,
      qz_lambda m h (le_of_lt hh) k y hy, hry]
    have hkrx : (k : ZMod 7) * rx = t - qz m x := by
      have := qz_lambda m h (le_of_lt hh) k x hx
      rw [← hrx_def] at this; rw [hqx] at this; linear_combination -this
    have : qz m y + (k : ZMod 7) * (3 * rx) = qz m y + 3 * (t - qz m x) := by
      linear_combination (3 : ZMod 7) * hkrx
    rw [this]; exact htB

end IntLRC7BS
