import LonelyRunner.LRC.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

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

/-- **Carry lemma.** `qz m (x + y)` is either `qz m x + qz m y` or
`qz m x + qz m y + 1` in `ZMod 7`, for **any** integers (Euclidean `ediv`
always yields `0 ≤ remainder < 7^m`). Formalizes equation (9)'s carry term. -/
theorem qz_add_carry (m : ℕ) (x y : ℤ) :
    qz m (x + y) = qz m x + qz m y ∨
    qz m (x + y) = qz m x + qz m y + 1 := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hPne : (7 : ℤ) ^ m ≠ 0 := ne_of_gt hP
  -- Write x = P·qx + rx, y = P·qy + ry (Euclidean)
  set P := (7 : ℤ) ^ m
  set qx := x / P; set qy := y / P
  have hxe : P * qx + x % P = x := Int.mul_ediv_add_emod x P
  have hye : P * qy + y % P = y := Int.mul_ediv_add_emod y P
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

/-- **Multiplicative carry bound — equation (9) engine.** For `n ≥ 1` and a
non-negative integer `x`, `qz m (n·x) = n · qz m x + c` in `ZMod 7`, where the
carry `c` is the cast of a natural number `cn < n`.

This is Barajas–Serra (9) in multiplicative form: since `λ'_j · d = j · (λ'_1 · d)`,
applying it with `x = λ'_1 · d` gives `q(λ'_j·d) ∈ j·q(λ'_1·d) + {0,…,j-1}`. -/
theorem qz_mul_carry (m : ℕ) (n : ℕ) (hn : 1 ≤ n) (x : ℤ) :
    ∃ cn : ℕ, cn < n ∧ qz m ((n : ℤ) * x) = (n : ZMod 7) * qz m x + (cn : ZMod 7) := by
  induction n, hn using Nat.le_induction with
  | base =>
    exact ⟨0, by norm_num, by push_cast; ring_nf⟩
  | succ k hk ih =>
    obtain ⟨cn, hcnlt, hcneq⟩ := ih
    have hsplit : ((k + 1 : ℕ) : ℤ) * x = (k : ℤ) * x + x := by push_cast; ring
    rw [hsplit]
    rcases qz_add_carry m ((k : ℤ) * x) x with h | h
    · -- no carry: same cn
      refine ⟨cn, by omega, ?_⟩
      rw [h, hcneq]; push_cast; ring
    · -- carry of 1: cn + 1
      refine ⟨cn + 1, by omega, ?_⟩
      rw [h, hcneq]; push_cast; ring

/-- **Additive carry across multiplier steps (the `hadd` provider).** For the
q-sequence `Q j := qz m (j·x)`, any split `j + l` satisfies the carry relation
`Q(j+l) ∈ {Q j + Q l, +1}`, since `(j+l)·x = j·x + l·x` and `qz_add_carry` applies.
This is exactly the hypothesis consumed by the §5 Case 1/2/3 compression lemmas. -/
theorem qz_seq_hadd (m : ℕ) (x : ℤ) (j l : ℕ) :
    qz m (((j + l : ℕ) : ℤ) * x) = qz m ((j : ℤ) * x) + qz m ((l : ℤ) * x)
      ∨ qz m (((j + l : ℕ) : ℤ) * x) = qz m ((j : ℤ) * x) + qz m ((l : ℤ) * x) + 1 := by
  have hsplit : ((j + l : ℕ) : ℤ) * x = (j : ℤ) * x + (l : ℤ) * x := by push_cast; ring
  rw [hsplit]
  exact qz_add_carry m ((j : ℤ) * x) ((l : ℤ) * x)

/-- **Equation (10) — the `Λ₀` shift.** The multiplier `1 + k·7^m` shifts the arc
index of `y` by `k · r(y)` where `r(y) = (y : ZMod 7)`:
`q((1 + k·7^m)·y) = q(y) + k·(y : ZMod 7)`. This is `qz_lambda` at level `j = 0`.
For the §5 assembly: applied to `y = j·x`, the shift `k·(j·x mod 7)` is uniform
across a residue class and ranges over all of `ZMod 7` (since `j·x mod 7` is a unit),
so the abstract `∃ t` (the case lemmas) becomes the integer multiplier `∃ k`. -/
theorem qz_shift0 (m : ℕ) (k y : ℤ) :
    qz m ((1 + k * 7 ^ m) * y) = qz m y + (k : ZMod 7) * (y : ZMod 7) := by
  have h := qz_lambda m 0 (Nat.zero_le m) k y (one_dvd y)
  simpa using h

/-- **Lemma 4 (ii) carry bound, `e = 2x − y` (BS L368).** The arc index of the
combination `2x − y` agrees with `2·q(x) − q(y)` up to a carry `c ∈ {−1,0,1}`
(here `6 = −1` in `ZMod 7`). Pure integer-floor fact: the carry is
`⌊(2·(x%7^m) − y%7^m)/7^m⌋`, and `2·rx − ry ∈ (−7^m, 2·7^m)`. -/
theorem qz_2xsuby_carry (m : ℕ) (x y : ℤ) :
    ∃ c : ZMod 7, (c = 0 ∨ c = 1 ∨ c = 6) ∧
      qz m (2 * x - y) = 2 * qz m x - qz m y + c := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hPne : (7 : ℤ) ^ m ≠ 0 := ne_of_gt hP
  set P := (7 : ℤ) ^ m
  set rx := x % P; set ry := y % P
  have hrx0 : 0 ≤ rx := Int.emod_nonneg x hPne
  have hry0 : 0 ≤ ry := Int.emod_nonneg y hPne
  have hrxP : rx < P := Int.emod_lt_of_pos x hP
  have hryP : ry < P := Int.emod_lt_of_pos y hP
  set s : ℤ := (2 * rx - ry) / P with hs_def
  -- s ∈ {−1,0,1}
  have hs_hi : s ≤ 1 := by
    have : s < 2 := by rw [hs_def, Int.ediv_lt_iff_lt_mul hP]; linarith
    omega
  have hs_lo : -1 ≤ s := by
    rw [hs_def, Int.le_ediv_iff_mul_le hP]; linarith
  -- (2x − y)/P = 2(x/P) − (y/P) + s
  have hdecomp : (2 * x - y) / P = 2 * (x / P) - y / P + s := by
    have ex : (rx : ℤ) = x - P * (x / P) := Int.emod_def x P
    have ey : (ry : ℤ) = y - P * (y / P) := Int.emod_def y P
    have hcomb : 2 * x - y = (2 * rx - ry) + P * (2 * (x / P) - y / P) := by
      rw [ex, ey]; ring
    rw [hcomb, Int.add_mul_ediv_left _ _ hPne, ← hs_def]; ring
  refine ⟨((s : ZMod 7)), ?_, ?_⟩
  · interval_cases s
    · right; right; decide
    · left; decide
    · right; left; decide
  · unfold qz; rw [hdecomp]; push_cast; ring

/-- **Lemma 4 (ii) carry bound, `e = x − y` (BS L368).** For equal-residue pairs
`r(x) = r(y)`, the arc index of `x − y` agrees with `q(x) − q(y)` up to a carry
`c ∈ {−1,0}` (`6 = −1`): `x − y = P·(qx−qy) + (rx−ry)` with `rx−ry ∈ (−P,P)`. -/
theorem qz_subxy_carry (m : ℕ) (x y : ℤ) :
    ∃ c : ZMod 7, (c = 0 ∨ c = 6) ∧
      qz m (x - y) = qz m x - qz m y + c := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hPne : (7 : ℤ) ^ m ≠ 0 := ne_of_gt hP
  set P := (7 : ℤ) ^ m
  set rx := x % P; set ry := y % P
  have hrx0 : 0 ≤ rx := Int.emod_nonneg x hPne
  have hry0 : 0 ≤ ry := Int.emod_nonneg y hPne
  have hrxP : rx < P := Int.emod_lt_of_pos x hP
  have hryP : ry < P := Int.emod_lt_of_pos y hP
  set s : ℤ := (rx - ry) / P with hs_def
  have hs_hi : s ≤ 0 := by
    have : s < 1 := by rw [hs_def, Int.ediv_lt_iff_lt_mul hP]; linarith
    omega
  have hs_lo : -1 ≤ s := by
    rw [hs_def, Int.le_ediv_iff_mul_le hP]; linarith
  have hdecomp : (x - y) / P = x / P - y / P + s := by
    have ex : (rx : ℤ) = x - P * (x / P) := Int.emod_def x P
    have ey : (ry : ℤ) = y - P * (y / P) := Int.emod_def y P
    have hcomb : x - y = (rx - ry) + P * (x / P - y / P) := by rw [ex, ey]; ring
    rw [hcomb, Int.add_mul_ediv_left _ _ hPne, ← hs_def]; ring
  refine ⟨((s : ZMod 7)), ?_, ?_⟩
  · interval_cases s
    · right; decide
    · left; decide
  · unfold qz; rw [hdecomp]; push_cast; ring

/-- **Single-element q-retargeting (BS Lemma 2, one element).** For `x` with
`ν₇(x) = h < m`, a multiplier `1 + k·7^{m-h} ∈ Λ_h` sends the arc index `q(x)` to
ANY target `t ∈ ZMod 7`: the slope `x/7^h` is a unit, so `q(λx) = q(x) + k·(x/7^h)`
is surjective in `k`. The multiplier is coprime to 7. This is the engine behind
every "by Lemma 2 we may assume `q(λx) = …`" step of the §6 case analysis. -/
theorem qz_retarget (m h : ℕ) (hhm : h < m) (x : ℤ)
    (hx : (7 : ℤ) ^ h ∣ x) (hx' : ¬ (7 : ℤ) ^ (h + 1) ∣ x) (t : ZMod 7) :
    ∃ k : ℤ, qz m ((1 + k * 7 ^ (m - h)) * x) = t ∧ ¬ (7 : ℤ) ∣ (1 + k * 7 ^ (m - h)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨d, hd⟩ := id hx
  have hxdiv : x / 7 ^ h = d := by rw [hd]; exact Int.mul_ediv_cancel_left d (by positivity)
  set r : ZMod 7 := ((x / 7 ^ h : ℤ) : ZMod 7) with hr_def
  have hr_ne : r ≠ 0 := by
    rw [hr_def, hxdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro ⟨c, hc⟩; exact hx' ⟨c, by rw [hd, hc, pow_succ]; ring⟩
  -- In ZMod 7, r⁻¹ = r^5 (Fermat: r^6 = 1), so we use r^5 and avoid inverses.
  have hr6 : r ^ 6 = 1 := ZMod.pow_card_sub_one_eq_one hr_ne
  refine ⟨((t - qz m x) * r ^ 5).val, ?_, ?_⟩
  · rw [qz_lambda m h (le_of_lt hhm) _ x hx, ← hr_def]
    have hk : (((((t - qz m x) * r ^ 5).val : ℤ)) : ZMod 7) = (t - qz m x) * r ^ 5 := by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
    rw [hk, mul_assoc, show r ^ 5 * r = r ^ 6 from by ring, hr6, mul_one, add_sub_cancel]
  · intro hdvd
    have h7 : (7 : ℤ) ∣ 7 ^ (m - h) := dvd_pow_self 7 (by omega : m - h ≠ 0)
    have h1 : (7 : ℤ) ∣ 1 := by
      have := dvd_sub hdvd (Dvd.dvd.mul_left h7 (((t - qz m x) * r ^ 5).val : ℤ))
      simpa using this
    norm_num at h1

/-- **Top-level q-retargeting (BS `Λ_m`, one element).** For `x` with `ν₇(x) = m`,
a constant multiplier `j` (coprime to 7) sends the arc index `q(x) = x/7^m mod 7`
to ANY NONZERO target `t`: `q(j·x) = j·(x/7^m)` and `x/7^m` is a unit. (Unlike
`qz_retarget` this is the level-`m` mechanism — multiply by a constant, not a
`Λ_h` element — and `0` is unreachable since `j·unit ≠ 0`.) -/
theorem qz_retarget_top (m : ℕ) (x : ℤ) (hx : (7 : ℤ) ^ m ∣ x)
    (hx' : ¬ (7 : ℤ) ^ (m + 1) ∣ x) (t : ZMod 7) (ht : t ≠ 0) :
    ∃ j : ℤ, ¬ (7 : ℤ) ∣ j ∧ qz m (j * x) = t := by
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := id hx
  have hxdiv : x / 7 ^ m = u := by rw [hu]; exact Int.mul_ediv_cancel_left u (by positivity)
  set r : ZMod 7 := ((x / 7 ^ m : ℤ) : ZMod 7) with hr_def
  have hr_ne : r ≠ 0 := by
    rw [hr_def, hxdiv, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro ⟨c, hc⟩; exact hx' ⟨c, by rw [hu, hc, pow_succ]; ring⟩
  have hr6 : r ^ 6 = 1 := ZMod.pow_card_sub_one_eq_one hr_ne
  have hjcast : (((t * r ^ 5).val : ℤ) : ZMod 7) = t * r ^ 5 := by
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  refine ⟨(t * r ^ 5).val, ?_, ?_⟩
  · intro hdvd
    have hz : (((t * r ^ 5).val : ℤ) : ZMod 7) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hdvd
    rw [hjcast] at hz
    exact (mul_ne_zero ht (pow_ne_zero 5 hr_ne)) hz
  · show qz m (((t * r ^ 5).val : ℤ) * x) = t
    unfold qz
    rw [show ((t * r ^ 5).val : ℤ) * x = 7 ^ m * ((t * r ^ 5).val * u) from by rw [hu]; ring,
      Int.mul_ediv_cancel_left _ (pow_ne_zero m (by norm_num : (7 : ℤ) ≠ 0))]
    have hu_r : ((u : ℤ) : ZMod 7) = r := by rw [hr_def, hxdiv]
    push_cast [hjcast]
    rw [hu_r, mul_assoc, show r ^ 5 * r = r ^ 6 from by ring, hr6, mul_one]

/-- **General `ẽ`-invariance (BS Lemma 4(i), master form).** Any `ZMod 7`-linear
combination `a·q(x) + b·q(y)` is invariant under a level-`h` multiplier
`1 + k·7^{m-h}`, provided the corresponding combination of slopes vanishes:
`a·(x/7^h) + b·(y/7^h) = 0`. The three cases of `ẽ` in BS eq (13) are the
instances `(a,b) = (2,-1)`, `(-1,2)`, `(1,-1)` under the residue relations
`r(y)=2r(x)`, `r(x)=2r(y)`, `r(y)=r(x)`. -/
theorem qz_lin_invariant (m h : ℕ) (hhm : h ≤ m) (k x y : ℤ) (a b : ZMod 7)
    (hx : (7 : ℤ) ^ h ∣ x) (hy : (7 : ℤ) ^ h ∣ y)
    (hab : a * ((x / 7 ^ h : ℤ) : ZMod 7) + b * ((y / 7 ^ h : ℤ) : ZMod 7) = 0) :
    a * qz m ((1 + k * 7 ^ (m - h)) * x) + b * qz m ((1 + k * 7 ^ (m - h)) * y)
      = a * qz m x + b * qz m y := by
  rw [qz_lambda m h hhm k x hx, qz_lambda m h hhm k y hy]
  linear_combination (k : ZMod 7) * hab

/-- **`Λ_j` is inert on higher-level elements.** If `7^{j+1} ∣ x` (i.e. `ν(x) > j`),
the multiplier `1 + k·7^{m-j}` leaves the arc index `q(x)` unchanged: its slope
`x/7^j ≡ 0 (mod 7)`. This is what lets retargeting at a low level not disturb the
q-values already set at higher levels. -/
theorem qz_higher_inert (m j : ℕ) (hjm : j ≤ m) (k x : ℤ) (hx : (7 : ℤ) ^ (j + 1) ∣ x) :
    qz m ((1 + k * 7 ^ (m - j)) * x) = qz m x := by
  rw [qz_lambda m j hjm k x (dvd_trans (pow_dvd_pow 7 (Nat.le_succ j)) hx)]
  have hz : ((x / 7 ^ j : ℤ) : ZMod 7) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    push_cast
    rw [hc, pow_succ, show 7 ^ j * 7 * c = 7 ^ j * (7 * c) from by ring,
      Int.mul_ediv_cancel_left _ (pow_ne_zero j (by norm_num))]
  rw [hz, mul_zero, add_zero]

/-- **Two-level simultaneous q-retargeting.** Two elements `x, y` at distinct
levels `h₂ < h₁ < m` can have BOTH arc indices set to arbitrary targets `s, t`
by one unit multiplier: retarget the higher level first (`qz_retarget` on `x`),
then the lower (`qz_retarget` on `λ₁·y`); the lower-level factor is inert on `x`
(`qz_higher_inert`). The engine for Lemma 9 and the multi-element §6 cases. -/
theorem qz_retarget_two (m h₁ h₂ : ℕ) (hh₁ : h₁ < m) (hlt : h₂ < h₁)
    (x y : ℤ) (hx : (7 : ℤ) ^ h₁ ∣ x) (hx' : ¬ (7 : ℤ) ^ (h₁ + 1) ∣ x)
    (hy : (7 : ℤ) ^ h₂ ∣ y) (hy' : ¬ (7 : ℤ) ^ (h₂ + 1) ∣ y) (s t : ZMod 7) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ qz m (lam * x) = s ∧ qz m (lam * y) = t := by
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  obtain ⟨k₁, hk₁x, hk₁u⟩ := qz_retarget m h₁ hh₁ x hx hx' s
  set lam1 : ℤ := 1 + k₁ * 7 ^ (m - h₁) with hlam1_def
  -- ν(lam1·y) = h₂ still (lam1 is a unit)
  have hl1y_dvd : (7 : ℤ) ^ h₂ ∣ lam1 * y := Dvd.dvd.mul_left hy lam1
  have hl1y_ndvd : ¬ (7 : ℤ) ^ (h₂ + 1) ∣ lam1 * y := by
    intro hdvd
    refine hy' ?_
    have hcop : IsCoprime ((7 : ℤ) ^ (h₂ + 1)) lam1 :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp7).mpr hk₁u)
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨k₂, hk₂y, hk₂u⟩ := qz_retarget m h₂ (by omega) (lam1 * y) hl1y_dvd hl1y_ndvd t
  set lam2 : ℤ := 1 + k₂ * 7 ^ (m - h₂) with hlam2_def
  refine ⟨lam2 * lam1, ?_, ?_, ?_⟩
  · exact mt (Prime.dvd_mul hp7 |>.mp) (by tauto)
  · -- lam2 inert on lam1·x (ν(lam1·x) = h₁ > h₂)
    have hl1x_high : (7 : ℤ) ^ (h₂ + 1) ∣ lam1 * x :=
      Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 7 (by omega)) hx) lam1
    rw [show lam2 * lam1 * x = lam2 * (lam1 * x) from by ring, hlam2_def,
      qz_higher_inert m h₂ (by omega) k₂ (lam1 * x) hl1x_high]
    exact hk₁x
  · rw [show lam2 * lam1 * y = lam2 * (lam1 * y) from by ring, hlam2_def, hk₂y]

/-- **Two-level retargeting with one element at the top level `m`.** `x` at level
`m` (target `s ≠ 0`) and `y` at level `h < m` (target `t`, any): one unit
multiplier hits both. Retarget `x` with a constant `j` (`qz_retarget_top`), then
`y` with a `Λ_h` factor on `j·y`; the `Λ_h` factor is inert on `j·x` (level
`m > h`). The `ν=m` analogue of `qz_retarget_two`, for the `ν=m` edges of §6. -/
theorem qz_retarget_two_top (m h : ℕ) (hh : h < m) (x y : ℤ)
    (hx : (7 : ℤ) ^ m ∣ x) (hx' : ¬ (7 : ℤ) ^ (m + 1) ∣ x)
    (hy : (7 : ℤ) ^ h ∣ y) (hy' : ¬ (7 : ℤ) ^ (h + 1) ∣ y)
    (s t : ZMod 7) (hs : s ≠ 0) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ qz m (lam * x) = s ∧ qz m (lam * y) = t := by
  have hp7 : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
  obtain ⟨j, hju, hjx⟩ := qz_retarget_top m x hx hx' s hs
  have hjy_dvd : (7 : ℤ) ^ h ∣ j * y := Dvd.dvd.mul_left hy j
  have hjy_ndvd : ¬ (7 : ℤ) ^ (h + 1) ∣ j * y := by
    intro hdvd
    refine hy' ?_
    have hcop : IsCoprime ((7 : ℤ) ^ (h + 1)) j :=
      IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp7).mpr hju)
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨k, hky, hku⟩ := qz_retarget m h hh (j * y) hjy_dvd hjy_ndvd t
  set lam2 : ℤ := 1 + k * 7 ^ (m - h) with hlam2_def
  refine ⟨lam2 * j, ?_, ?_, ?_⟩
  · exact mt (Prime.dvd_mul hp7 |>.mp) (by tauto)
  · -- lam2 inert on j·x (ν(j·x) = m > h)
    have hjx_high : (7 : ℤ) ^ (h + 1) ∣ j * x :=
      Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow 7 (by omega)) hx) j
    rw [show lam2 * j * x = lam2 * (j * x) from by ring, hlam2_def,
      qz_higher_inert m h (by omega) k (j * x) hjx_high]
    exact hjx
  · rw [show lam2 * j * y = lam2 * (j * y) from by ring, hlam2_def, hky]

/-- **Subtracting a multiple of `7^m` shifts `qz` by the multiplier.** Since
`qz m x = (x / 7^m : ZMod 7)`, subtracting `7^m · w` from `x` shifts the integer
quotient by exactly `w`. This is the key to the carry analysis in Lemma 7(ii). -/
theorem qz_sub_mul_pow (m : ℕ) (a w : ℤ) :
    qz m (a - (7 : ℤ) ^ m * w) = qz m a - (w : ZMod 7) := by
  simp only [qz]
  have h7 : (7 : ℤ) ^ m ≠ 0 := pow_ne_zero m (show (7:ℤ) ≠ 0 by decide)
  have heq : a - (7 : ℤ) ^ m * w = a + (-w) * (7 : ℤ) ^ m := by ring
  rw [heq, Int.add_mul_ediv_right _ _ h7]
  push_cast; ring

/-- **No doubling carry when `q(7a) = 0`.** If the top 7-ary digit of `7a` is 0,
the low part of `a` is `< 7^{m-1}`, so doubling stays below `7^m` and the carry
vanishes: `q(2a) = 2·q(a)`. -/
theorem qz_double_no_carry (m : ℕ) (a : ℤ) (h : qz m (7 * a) = 0) :
    qz m (2 * a) = 2 * qz m a := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [qz, pow_zero, Int.ediv_one]; push_cast; ring
  simp only [qz] at *
  have h7m : (7 : ℤ) ^ m = 7 * 7 ^ (m - 1) := by
    cases m with | zero => omega | succ n => simp [pow_succ']
  rw [h7m, Int.mul_ediv_mul_of_pos a ((7 : ℤ) ^ (m - 1)) (by norm_num : (0:ℤ) < 7)] at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hdvd : (7 : ℤ) ∣ a / (7 : ℤ) ^ (m - 1) := by exact_mod_cast h
  obtain ⟨c, hc⟩ := hdvd
  set P := (7 : ℤ) ^ m
  set Pm1 := (7 : ℤ) ^ (m - 1)
  have hPm1_pos : (0 : ℤ) < Pm1 := pow_pos (by norm_num : (0:ℤ) < 7) _
  have hP_pos : (0 : ℤ) < P := pow_pos (by norm_num : (0:ℤ) < 7) _
  have hPeq : P = 7 * Pm1 := h7m
  have hrm1 : 0 ≤ a % Pm1 := Int.emod_nonneg a (ne_of_gt hPm1_pos)
  have hrm1P : a % Pm1 < Pm1 := Int.emod_lt_of_pos a hPm1_pos
  have ha_decomp : a = P * c + a % Pm1 := by
    have h1 : Pm1 * (a / Pm1) + a % Pm1 = a := Int.ediv_add_emod a Pm1
    have h2 : Pm1 * (7 * c) = P * c := by rw [hPeq]; ring
    rw [hc] at h1; linarith
  have h2r_nn : 0 ≤ 2 * (a % Pm1) := by linarith
  have h2r_lt : 2 * (a % Pm1) < P := by nlinarith [hPeq]
  have h2adiv : 2 * a / P = 2 * c := by
    have h2a : 2 * a = 2 * (a % Pm1) + P * (2 * c) := by linarith [ha_decomp]
    rw [h2a, Int.add_mul_ediv_left _ _ (ne_of_gt hP_pos),
      Int.ediv_eq_zero_of_lt h2r_nn h2r_lt, zero_add]
  have hadiv : a / P = c := by
    have ha2 : a = a % Pm1 + P * c := by linarith [ha_decomp]
    rw [ha2, Int.add_mul_ediv_left _ _ (ne_of_gt hP_pos),
      Int.ediv_eq_zero_of_lt hrm1 (by linarith [hPeq]), zero_add]
  rw [h2adiv, hadiv]; push_cast; ring

/-- **Doubling carry = 1 when `q(7a) = 6`.** If the top 7-ary digit of `7a` is 6,
the low part of `a` is `≥ 6·7^{m-1}`, so doubling overflows by exactly `7^m`:
`q(2a) = 2·q(a) + 1`. -/
theorem qz_double_carry_one (m : ℕ) (hm : 1 ≤ m) (a : ℤ) (h : qz m (7 * a) = 6) :
    qz m (2 * a) = 2 * qz m a + 1 := by
  simp only [qz] at *
  have h7m : (7 : ℤ) ^ m = 7 * 7 ^ (m - 1) := by
    cases m with | zero => omega | succ n => simp [pow_succ']
  rw [h7m, Int.mul_ediv_mul_of_pos a ((7 : ℤ) ^ (m - 1)) (by norm_num : (0:ℤ) < 7)] at h
  set P := (7 : ℤ) ^ m
  set Pm1 := (7 : ℤ) ^ (m - 1)
  have hPm1_pos : (0 : ℤ) < Pm1 := pow_pos (by norm_num : (0:ℤ) < 7) _
  have hP_pos : (0 : ℤ) < P := pow_pos (by norm_num : (0:ℤ) < 7) _
  have hPeq : P = 7 * Pm1 := h7m
  set Q := a / Pm1
  have hQmod : Q % 7 = 6 := by
    have := ZMod.intCast_zmod_eq_zero_iff_dvd (Q - 6) 7
    simp only [Int.cast_sub, h] at this
    obtain ⟨k, hk⟩ := this.mp rfl; omega
  have eQ : Q = 7 * (Q / 7) + 6 := by omega
  have hrm1 : 0 ≤ a % Pm1 := Int.emod_nonneg a (ne_of_gt hPm1_pos)
  have hrm1P : a % Pm1 < Pm1 := Int.emod_lt_of_pos a hPm1_pos
  have h1 : Pm1 * Q + a % Pm1 = a := Int.ediv_add_emod a Pm1
  set r := 6 * Pm1 + a % Pm1 with hr_def
  have ha_decomp : a = P * (Q / 7) + r := by
    have h2 : Pm1 * (7 * (Q / 7) + 6) = P * (Q / 7) + 6 * Pm1 := by rw [hPeq]; ring
    rw [eQ] at h1; linarith
  have hr_nn : 0 ≤ r := by linarith [hr_def]
  have hr_lt : r < P := by linarith [hr_def, hPeq]
  have h2r_ge : P ≤ 2 * r := by linarith [hr_def, hPeq]
  have h2adiv : 2 * a / P = 2 * (Q / 7) + 1 := by
    have h2a : 2 * a = (2 * r - P) + P * (2 * (Q / 7) + 1) := by linarith [ha_decomp]
    rw [h2a, Int.add_mul_ediv_left _ _ (ne_of_gt hP_pos),
      Int.ediv_eq_zero_of_lt (by linarith) (by linarith), zero_add]
  have hadiv : a / P = Q / 7 := by
    have ha2 : a = r + P * (Q / 7) := by linarith [ha_decomp]
    rw [ha2, Int.add_mul_ediv_left _ _ (ne_of_gt hP_pos),
      Int.ediv_eq_zero_of_lt hr_nn hr_lt, zero_add]
  rw [h2adiv, hadiv]; push_cast; ring

/-- **Combined carry with the `2x−y` ⇒ `x−y` implication (BS L368, refined).**
Produces BOTH the `2x−y` carry `c₃ ∈ {−1,0,1}` and the `x−y` carry `c₁ ∈ {−1,0}`
on the SAME pair `(x,y)`, together with the integer-forced links
`c₃ = −1 ⇒ c₁ = −1` and `c₃ = 1 ⇒ c₁ = 0` (`6 = −1` in `ZMod 7`). The links are
honest facts about the shared low parts `rx = x%7^m`, `ry = y%7^m ∈ [0,7^m)`:
`2rx < ry ⇒ rx ≤ 2rx < ry ⇒ rx < ry`, and `2rx ≥ ry+7^m > 2ry ⇒ rx > ry`. These
links are exactly what lets the `j=2` length-2 compression (`lemma9_ii_j2`) close:
a single carry pair cannot, but the implication rules out the bad `(c₃,c₁)` combos. -/
theorem qz_combined_carry (m : ℕ) (x y : ℤ) :
    ∃ c₃ c₁ : ZMod 7,
      (c₃ = 0 ∨ c₃ = 1 ∨ c₃ = 6) ∧ (c₁ = 0 ∨ c₁ = 6) ∧
      qz m (2 * x - y) = 2 * qz m x - qz m y + c₃ ∧
      qz m (x - y) = qz m x - qz m y + c₁ ∧
      (c₃ = 6 → c₁ = 6) ∧ (c₃ = 1 → c₁ = 0) := by
  have hP : (0 : ℤ) < 7 ^ m := by positivity
  have hPne : (7 : ℤ) ^ m ≠ 0 := ne_of_gt hP
  set P := (7 : ℤ) ^ m
  set rx := x % P; set ry := y % P
  have hrx0 : 0 ≤ rx := Int.emod_nonneg x hPne
  have hry0 : 0 ≤ ry := Int.emod_nonneg y hPne
  have hrxP : rx < P := Int.emod_lt_of_pos x hP
  have hryP : ry < P := Int.emod_lt_of_pos y hP
  set s₃ : ℤ := (2 * rx - ry) / P with hs3_def
  have hs3_hi : s₃ ≤ 1 := by
    have : s₃ < 2 := by rw [hs3_def, Int.ediv_lt_iff_lt_mul hP]; linarith
    omega
  have hs3_lo : -1 ≤ s₃ := by rw [hs3_def, Int.le_ediv_iff_mul_le hP]; linarith
  have hdecomp3 : (2 * x - y) / P = 2 * (x / P) - y / P + s₃ := by
    have ex : (rx : ℤ) = x - P * (x / P) := Int.emod_def x P
    have ey : (ry : ℤ) = y - P * (y / P) := Int.emod_def y P
    have hcomb : 2 * x - y = (2 * rx - ry) + P * (2 * (x / P) - y / P) := by rw [ex, ey]; ring
    rw [hcomb, Int.add_mul_ediv_left _ _ hPne, ← hs3_def]; ring
  set s₁ : ℤ := (rx - ry) / P with hs1_def
  have hs1_hi : s₁ ≤ 0 := by
    have : s₁ < 1 := by rw [hs1_def, Int.ediv_lt_iff_lt_mul hP]; linarith
    omega
  have hs1_lo : -1 ≤ s₁ := by rw [hs1_def, Int.le_ediv_iff_mul_le hP]; linarith
  have hdecomp1 : (x - y) / P = x / P - y / P + s₁ := by
    have ex : (rx : ℤ) = x - P * (x / P) := Int.emod_def x P
    have ey : (ry : ℤ) = y - P * (y / P) := Int.emod_def y P
    have hcomb : x - y = (rx - ry) + P * (x / P - y / P) := by rw [ex, ey]; ring
    rw [hcomb, Int.add_mul_ediv_left _ _ hPne, ← hs1_def]; ring
  -- integer carry links
  have himp6 : s₃ = -1 → s₁ = -1 := by
    intro _h3
    have h2 : 2 * rx - ry < 0 := by
      by_contra hc; rw [not_lt] at hc
      have : 0 ≤ s₃ := by rw [hs3_def]; exact Int.ediv_nonneg hc (le_of_lt hP)
      omega
    have hlt : rx - ry < 0 := by linarith
    have hneg : s₁ < 0 := by rw [hs1_def]; exact Int.ediv_neg_of_neg_of_pos hlt hP
    omega
  have himp1 : s₃ = 1 → s₁ = 0 := by
    intro h3
    have h2 : P ≤ 2 * rx - ry := by
      have hmod := Int.emod_add_mul_ediv (2 * rx - ry) P
      have hnn : 0 ≤ (2 * rx - ry) % P := Int.emod_nonneg _ hPne
      rw [← hs3_def] at hmod; nlinarith [hmod, hnn]
    have hge : 0 ≤ rx - ry := by linarith
    have : 0 ≤ s₁ := by rw [hs1_def]; exact Int.ediv_nonneg hge (le_of_lt hP)
    omega
  have hq3 : qz m (2 * x - y) = 2 * qz m x - qz m y + (s₃ : ZMod 7) := by
    unfold qz; rw [hdecomp3]; push_cast; ring
  have hq1 : qz m (x - y) = qz m x - qz m y + (s₁ : ZMod 7) := by
    unfold qz; rw [hdecomp1]; push_cast; ring
  refine ⟨(s₃ : ZMod 7), (s₁ : ZMod 7), ?_, ?_, hq3, hq1, ?_, ?_⟩
  · interval_cases s₃
    · right; right; decide
    · left; decide
    · right; left; decide
  · interval_cases s₁
    · right; decide
    · left; decide
  · intro h
    interval_cases s₃
    · rw [himp6 rfl]; decide
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · intro h
    interval_cases s₃
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rw [himp1 rfl]; decide

/-- **q-equivalence under high divisibility.** If `7^(m+1) ∣ (a − b)`, then
`qz m (λ·a) = qz m (λ·b)` for ALL `λ`: the elements `a, b` are indistinguishable
at resolution `m`. Proof: `a − b = 7·c · 7^m`, so `qz_sub_mul_pow` gives
`qz(λa) − qz(λb) = (7·λc : ZMod 7) = 0`. -/
theorem qz_eq_of_high_dvd (m : ℕ) (a b lam : ℤ) (h : (7 : ℤ) ^ (m + 1) ∣ (a - b)) :
    qz m (lam * a) = qz m (lam * b) := by
  obtain ⟨k, hk⟩ := h
  have hPne : (7 : ℤ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hlin : lam * a = lam * b - (7 : ℤ) ^ m * (-(7 * lam * k)) := by
    have : a = b + 7 ^ (m + 1) * k := by linarith
    rw [this, pow_succ]; ring
  rw [hlin, qz_sub_mul_pow]
  simp only [Int.cast_neg, sub_neg_eq_add]
  suffices h : (↑(7 * lam * k) : ZMod 7) = 0 by rw [h, add_zero]
  push_cast
  have h7 : (7 : ZMod 7) = 0 := by decide
  rw [h7]; ring

end IntLRC7BS
