import LonelyRunner.LRC.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic

/-!
# n = 7 (Barajas–Serra 2008) — `p = 7` apparatus

Source: `sources_barajas_serra_2008.txt`, §1–§4 (lines 40–264).

7-adic apparatus shared by the whole n = 7 proof. We work with `p = 7` fixed.

- `nu x`     : 7-adic valuation `ν₇(x)` (mathlib `padicValNat 7`).
- `qval m x` : the arc index `q(x) = ⌊(x mod N)/7^m⌋ ∈ {0,…,6}` where
  `N = 7^(m+1)` (the top 7-ary digit of `x mod N`).
- `circDist_ge_of_qval` : the **q-language correspondence** — `q(x) ∉ {0,6}`
  forces `circDist(x/N) ≥ 1/7`. This lets the entire discrete argument be run
  in terms of arc indices `q ∈ {1,…,5}`.

Reuse `LonelyRunner.LRC.Defs` (circDist, badSet, goodSet, intLRC).
See `docs/n7_bs/ROADMAP.md`.
-/

namespace IntLRC7BS

/-- 7-adic valuation `ν₇(x)`. -/
def nu (x : ℕ) : ℕ := padicValNat 7 x

/-- Arc index `q(x) = ⌊(x mod N) / 7^m⌋ ∈ {0,…,6}`, where `N = 7^(m+1)`.
This is the top 7-ary digit of the residue `(x)_N`; `q(x) = k` iff
`(x)_N ∈ [k·7^m, (k+1)·7^m)`. -/
def qval (m : ℕ) (x : ℤ) : ℤ := (x % (7 ^ (m + 1) : ℤ)) / (7 ^ m : ℤ)

/-- Arc index as an element of `ZMod 7`: `q(x) = (⌊x/7^m⌋ : ZMod 7)`. This is the
natural target of Barajas–Serra's equation (3); `(qval m x : ZMod 7) = qz m x`
on the representative range (proved in `qz_eq_qval`). The advantage: the
multiplier identity (3) is *additive in `ZMod 7`*. -/
def qz (m : ℕ) (x : ℤ) : ZMod 7 := ((x / (7 : ℤ) ^ m : ℤ) : ZMod 7)

/-- **Equation (3) — the multiplier identity (unified form).** For a multiplier
`λ = 1 + k·7^{m-j}` and any `x` divisible by `7^j` (`j ≤ m`),
`q(λx) = q(x) + k · (x / 7^j)` in `ZMod 7`.

This unifies both cases of Barajas–Serra (3): if `ν(x) = j` then `x/7^j` is a unit
(`= r(x) ≠ 0`), giving `q(λx) = q(x) + k·r(x)`; if `ν(x) > j` then `7 ∣ x/7^j`, so
the increment vanishes and `q(λx) = q(x)`. The engine behind Lemma 2 / Cor 3. -/
theorem qz_lambda (m j : ℕ) (hjm : j ≤ m) (k x : ℤ) (hdvd : (7 : ℤ) ^ j ∣ x) :
    qz m ((1 + k * 7 ^ (m - j)) * x)
      = qz m x + (k : ZMod 7) * ((x / 7 ^ j : ℤ) : ZMod 7) := by
  obtain ⟨w, hw⟩ := hdvd
  have h7 : (7 : ℤ) ≠ 0 := by norm_num
  have hexp : (7 : ℤ) ^ m = 7 ^ (m - j) * 7 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjm]
  have hstep : (1 + k * 7 ^ (m - j)) * x = x + (k * w) * 7 ^ m := by
    rw [hw, hexp]; ring
  have hwq : x / 7 ^ j = w := by
    rw [hw]; exact Int.mul_ediv_cancel_left w (pow_ne_zero j h7)
  rw [hstep]
  unfold qz
  rw [Int.add_mul_ediv_right x (k * w) (pow_ne_zero m h7), hwq]
  push_cast
  ring

/-- **One filtering step, factored.** Multiplying `lam·d` by `1 + K·7^{m-j}`
(with `7^j ∣ d`) shifts the arc index by `K · (lam · (d/7^j))` in `ZMod 7`:
`qz m ((1+K·7^{m-j})·(lam·d)) = qz m (lam·d) + K · (lam · (d/7^j))`. The slope
`lam · (d/7^j)` is a unit exactly when `d` has valuation `j` and `7 ∤ lam`. This
is `qz_lambda` specialized to a base already multiplied by `lam`. -/
theorem qz_step (m j : ℕ) (hjm : j ≤ m) (K lam d : ℤ) (hjd : (7 : ℤ) ^ j ∣ d) :
    qz m ((1 + K * 7 ^ (m - j)) * (lam * d))
      = qz m (lam * d) + (K : ZMod 7) * ((lam : ZMod 7) * ((d / 7 ^ j : ℤ) : ZMod 7)) := by
  have hdvd : (7 : ℤ) ^ j ∣ lam * d := hjd.mul_left lam
  rw [qz_lambda m j hjm K (lam * d) hdvd, Int.mul_ediv_assoc lam hjd]
  push_cast
  ring

/-- The `ZMod 7` arc index agrees with the cast of the integer `qval`:
`qz m x = (qval m x : ZMod 7)`. (The top 7-ary digit of `x` and of `x mod 7^(m+1)`
agree mod 7 since they differ by a multiple of 7.) -/
theorem qz_eq_qval (m : ℕ) (x : ℤ) : qz m x = ((qval m x : ℤ) : ZMod 7) := by
  have h7 : (7 : ℤ) ≠ 0 := by norm_num
  have hxe : x % (7 ^ (m + 1) : ℤ) + (7 * (x / (7 ^ (m + 1) : ℤ))) * 7 ^ m = x := by
    conv_rhs => rw [← Int.emod_add_ediv x (7 ^ (m + 1) : ℤ)]
    ring
  unfold qz qval
  conv_lhs => rw [← hxe]
  rw [Int.add_mul_ediv_right _ (7 * (x / (7 ^ (m + 1) : ℤ))) (pow_ne_zero m h7)]
  push_cast
  rw [show (7 : ZMod 7) = 0 from by decide]
  ring

/-- **Good-criterion in q-language.** If `q(x) ∉ {0, 6}` in `ZMod 7`, the residue
`(x)_N` lies in the central band `[7^m, 6·7^m]` (in fact `[7^m, 6·7^m)`). This is
the bridge from the filtered conclusion of Lemma 2 / Cor 3 (stated as
`q(λd) ∉ {0,6}`) to the achievable target of `bs_discrete_q`. -/
theorem band_of_qz_ne (m : ℕ) (x : ℤ) (h0 : qz m x ≠ 0) (h6 : qz m x ≠ 6) :
    (7 ^ m : ℤ) ≤ x % (7 ^ (m + 1) : ℤ) ∧ x % (7 ^ (m + 1) : ℤ) ≤ 6 * 7 ^ m := by
  have hPpos : (0 : ℤ) < 7 ^ m := by positivity
  have hNpos : (0 : ℤ) < 7 ^ (m + 1) := by positivity
  set R : ℤ := x % (7 ^ (m + 1) : ℤ) with hR
  have hR0 : 0 ≤ R := Int.emod_nonneg x (by positivity)
  have hRN : R < 7 ^ (m + 1) := Int.emod_lt_of_pos x hNpos
  set qq : ℤ := R / (7 ^ m : ℤ) with hqq
  have hdm : (7 ^ m : ℤ) * qq + R % (7 ^ m : ℤ) = R := by
    rw [hqq]; exact Int.ediv_add_emod R (7 ^ m)
  have hs0 : 0 ≤ R % (7 ^ m : ℤ) := Int.emod_nonneg R (by positivity)
  have hsP : R % (7 ^ m : ℤ) < 7 ^ m := Int.emod_lt_of_pos R hPpos
  have hN7 : (7 ^ (m + 1) : ℤ) = 7 * 7 ^ m := by ring
  have hq0 : 0 ≤ qq := Int.ediv_nonneg hR0 (le_of_lt hPpos)
  have hq6 : qq ≤ 6 := by nlinarith [hdm, hs0, hRN, hN7, hPpos]
  have hqe : qval m x = qq := by rw [qval, ← hR, ← hqq]
  have hne0 : qq ≠ 0 := fun h => h0 (by rw [qz_eq_qval, hqe, h]; simp)
  have hne6 : qq ≠ 6 := fun h => h6 (by rw [qz_eq_qval, hqe, h]; decide)
  have hq1 : 1 ≤ qq := by omega
  have hq5 : qq ≤ 5 := by omega
  refine ⟨?_, ?_⟩
  · have h1 : (7 ^ m : ℤ) * 1 ≤ (7 ^ m : ℤ) * qq :=
      mul_le_mul_of_nonneg_left hq1 (le_of_lt hPpos)
    linarith [hdm, hs0]
  · have h5 : (7 ^ m : ℤ) * qq ≤ (7 ^ m : ℤ) * 5 :=
      mul_le_mul_of_nonneg_left hq5 (le_of_lt hPpos)
    linarith [hdm, hsP]

/-- **Master good-criterion.** If the residue `(x)_N = x mod 7^(m+1)` lies in the
central band `[7^m, 6·7^m]`, then `x/N` is at circle distance ≥ 1/7
(`N = 7^(m+1)`). This is the discrete "good" criterion `|x|_N ≥ N/7` of
Barajas–Serra, phrased via `circDist`. The band is **inclusive** at both ends:
the boundary points `7^m` and `6·7^m` give `|x|_N = N/7` exactly, which BS's
construction may produce for `D₇(m)` elements. -/
theorem circDist_ge_of_residue (m : ℕ) (x : ℤ)
    (hlo : (7 ^ m : ℤ) ≤ x % (7 ^ (m + 1) : ℤ))
    (hhi : x % (7 ^ (m + 1) : ℤ) ≤ 6 * 7 ^ m) :
    (1 : ℝ) / 7 ≤ circDist ((x : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ)) := by
  have hNRpos : (0 : ℝ) < ((7 ^ (m + 1) : ℕ) : ℝ) := by positivity
  have hNval : ((7 ^ (m + 1) : ℕ) : ℝ) = 7 * (7 : ℝ) ^ m := by push_cast; ring
  have hRlo' : ((7 : ℝ) ^ m) ≤ ((x % (7 ^ (m + 1) : ℤ) : ℤ) : ℝ) := by exact_mod_cast hlo
  have hRhi' : ((x % (7 ^ (m + 1) : ℤ) : ℤ) : ℝ) ≤ 6 * (7 : ℝ) ^ m := by exact_mod_cast hhi
  have hfract : Int.fract ((x : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ))
      = ((x % (7 ^ (m + 1) : ℤ) : ℤ) : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ) := by
    have h := Int.fract_div_intCast_eq_div_intCast_mod (k := ℝ) (m := x) (n := (7 ^ (m + 1) : ℕ))
    rw [h]; push_cast; ring_nf
  unfold circDist
  rw [hfract]
  have hub : ((x % (7 ^ (m + 1) : ℤ) : ℤ) : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ) ≤ 6 / 7 := by
    rw [div_le_iff₀ hNRpos, hNval]; nlinarith [hRhi']
  apply le_min
  · rw [le_div_iff₀ hNRpos, hNval]; nlinarith [hRlo']
  · linarith [hub]

/-- **q-language sufficient condition.** Avoiding the two forbidden arcs
`q(x) ∉ {0, 6}` puts the residue in `[7^m, 6·7^m)`, hence (by
`circDist_ge_of_residue`) at circle distance ≥ 1/7. This is the criterion used
for the filtered elements `d ∈ D \ D₇(m)` (where `F_d = {0,6}`). -/
theorem circDist_ge_of_qval (m : ℕ) (x : ℤ)
    (h0 : qval m x ≠ 0) (h6 : qval m x ≠ 6) :
    (1 : ℝ) / 7 ≤ circDist ((x : ℝ) / ((7 ^ (m + 1) : ℕ) : ℝ)) := by
  have hPpos : (0 : ℤ) < 7 ^ m := by positivity
  have hNpos : (0 : ℤ) < 7 ^ (m + 1) := by positivity
  set R : ℤ := x % (7 ^ (m + 1) : ℤ) with hR
  have hR0 : 0 ≤ R := Int.emod_nonneg x (by positivity)
  have hRN : R < 7 ^ (m + 1) := Int.emod_lt_of_pos x hNpos
  set q : ℤ := R / (7 ^ m : ℤ) with hq
  have hqe : qval m x = q := by rw [qval, ← hR, ← hq]
  have hdm : (7 ^ m : ℤ) * q + R % (7 ^ m : ℤ) = R := by
    rw [hq]; exact Int.ediv_add_emod R (7 ^ m)
  have hs0 : 0 ≤ R % (7 ^ m : ℤ) := Int.emod_nonneg R (by positivity)
  have hsP : R % (7 ^ m : ℤ) < 7 ^ m := Int.emod_lt_of_pos R hPpos
  have hN7 : (7 ^ (m + 1) : ℤ) = 7 * 7 ^ m := by ring
  rw [hqe] at h0 h6
  have hq0 : 0 ≤ q := Int.ediv_nonneg hR0 (le_of_lt hPpos)
  have hq1 : 1 ≤ q := by omega
  have hPq5 : (7 ^ m : ℤ) * q ≤ (7 ^ m : ℤ) * 5 := by
    have hq6 : q ≤ 6 := by nlinarith [hdm, hs0, hRN, hN7, hPpos]
    have hq5 : q ≤ 5 := by omega
    exact mul_le_mul_of_nonneg_left hq5 (le_of_lt hPpos)
  have hP1q : (7 ^ m : ℤ) * 1 ≤ (7 ^ m : ℤ) * q :=
    mul_le_mul_of_nonneg_left hq1 (le_of_lt hPpos)
  have hRlo : (7 ^ m : ℤ) ≤ R := by linarith [hdm, hs0, hP1q]
  have hRhi : R ≤ 6 * (7 ^ m : ℤ) := by linarith [hdm, hsP, hPq5]
  exact circDist_ge_of_residue m x hRlo hRhi

/-- **Carry lemma.** For non-negative integers, `qz m (x + y)` is either
`qz m x + qz m y` or `qz m x + qz m y + 1` in `ZMod 7`. This is the
formalization of equation (9)'s carry term. -/
theorem qz_add_carry (m : ℕ) (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    qz m (x + y) = qz m x + qz m y ∨
    qz m (x + y) = qz m x + qz m y + 1 := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hPne : (7 : ℤ) ^ m ≠ 0 := ne_of_gt hP
  -- Write x = P·qx + rx, y = P·qy + ry (Euclidean)
  set P := (7 : ℤ) ^ m
  set qx := x / P; set qy := y / P
  have hxe : P * qx + x % P = x := Int.ediv_add_emod x P
  have hye : P * qy + y % P = y := Int.ediv_add_emod y P
  have hrx0 : 0 ≤ x % P := Int.emod_nonneg x hPne
  have hry0 : 0 ≤ y % P := Int.emod_nonneg y hPne
  have hrxP : x % P < P := Int.emod_lt_of_pos x hP
  have hryP : y % P < P := Int.emod_lt_of_pos y hP
  -- x + y = P·(qx + qy) + (rx + ry); the remainder may overflow
  have hsum : x + y = P * (qx + qy) + (x % P + y % P) := by linarith
  rcases le_or_gt (x % P + y % P) (P - 1) with hlt | hge
  · -- no carry: rx + ry < P
    left
    have hlt' : x % P + y % P < P := by omega
    have hq : (x + y) / P = qx + qy := by
      rw [hsum, show P * (qx + qy) + (x % P + y % P)
            = x % P + y % P + P * (qx + qy) by ring]
      rw [Int.add_mul_ediv_left _ _ hPne]
      rw [Int.ediv_eq_zero_of_lt (by linarith) hlt', zero_add]
    unfold qz; rw [hq]; push_cast; ring
  · -- carry: rx + ry ≥ P
    right
    have hge' : P ≤ x % P + y % P := by omega
    have hlt2 : x % P + y % P - P < P := by omega
    have hq : (x + y) / P = qx + qy + 1 := by
      rw [hsum, show P * (qx + qy) + (x % P + y % P)
            = (x % P + y % P - P) + P * (qx + qy + 1) by ring]
      rw [Int.add_mul_ediv_left _ _ hPne]
      rw [Int.ediv_eq_zero_of_lt (by omega) hlt2, zero_add]
    unfold qz; rw [hq]; push_cast; ring

end IntLRC7BS
