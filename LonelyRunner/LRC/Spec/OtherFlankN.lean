import LonelyRunner.LRC.Spec.SelfSimilarN

/-!
# P6: the construction at a flank that need not be the largest

2026-09-21.  `lonely_iff_exists_flank` permits **any** flank, not only the largest.  Every set in
the order-5 residue contains a disparity divisible by 5; taking that as the flank puts us in the
`n ∣ e` case even when it is not the maximum.

With `a = k·e + 1` and `d = c·e + s` (`c = d/e`, `s = d % e`),

    d·a  =  e·(d·k + c) + s,     so    d·a mod n·e  =  e·((d·k + c) mod n) + s,

which is in `[e, (n−1)e]` exactly when `(d·k + d/e) mod n ∈ {1,…,n−2}`, or `= n−1` with `e ∣ d`.
For `d < e` the offset vanishes and this is `flankWorks_of_prime_dvd`; the offset is precisely
what makes a non-maximal flank usable.

Measured at `n = 5`: **49.5%** of all primitive card-4 sets, and **77.4%** of what P1′–P5 leave,
taking total coverage from 80.9% to **96.1%**.  Soundness checked: no claimed set fails.

Note the pigeonhole is weaker here.  With `c = 0` each `d` forbids one `k`; with `c ≠ 0` it can
forbid two (the residues `0` and `n−1`), so existence of a good `k` is a hypothesis, not free.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace LRC.OtherFlank

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **P6: the `k`-construction at a flank that need NOT be the largest.**

With `n ∣ e` and `a = k·e + 1`, writing `d = c·e + s` (`c = d/e`, `s = d % e`),

    d·a = d·k·e + c·e + s = e·(d·k + c) + s,

so `d·a mod n·e = e·((d·k + c) mod n) + s`, which lies in `[e, (n−1)e]` exactly when
`(d·k + d/e) mod n` is in `{1, …, n−2}`, or equals `n−1` with `e ∣ d`.

When `d < e` the offset `c` vanishes and this is `flankWorks_of_prime_dvd`.  When `d > e` the
offset is what lets a non-maximal flank be used — and `lonely_iff_exists_flank` allows any flank,
so this is legitimate.  Measured at `n = 5`: **49.5%** of all primitive card-4 sets, and
**77.4%** of what the other criteria leave. -/
theorem flankWorks_of_shifted (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (k : ℕ) (hk0 : 0 < k) (hkn : k < n)
    (hgood : ∀ d ∈ L, 1 ≤ (d * k + d / e) % n ∧
              ((d * k + d / e) % n ≤ n - 2 ∨ ((d * k + d / e) % n = n - 1 ∧ d % e = 0))) :
    flankWorks n L e = true := by
  have hn2 : 2 ≤ n := Fact.out
  obtain ⟨E, hE⟩ := hen
  set j : ℕ := k * E with hj
  have hkey : n * j + 1 = k * e + 1 := by rw [hj, hE]; ring
  have hjlt : j < e := by
    have hE0 : 0 < E := by
      rcases Nat.eq_zero_or_pos E with h | h
      · exfalso; rw [h, Nat.mul_zero] at hE; omega
      · exact h
    have : k * E < n * E := (Nat.mul_lt_mul_right hE0).mpr hkn
    rw [hj, hE]; omega
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hkey]
  obtain ⟨hlo, hhi⟩ := hgood d hd
  set c : ℕ := d / e with hc
  set s : ℕ := d % e with hs
  set r : ℕ := (d * k + c) % n with hr
  have hslt : s < e := Nat.mod_lt _ he
  have hds : c * e + s = d := by
    rw [hc, hs, Nat.mul_comm]
    exact Nat.div_add_mod d e
  -- d*(k*e+1) = e*(d*k + c) + s
  have hsplit : d * (k * e + 1) = (e * r + s) + (n * e) * ((d * k + c) / n) := by
    have hdm := Nat.div_add_mod (d * k + c) n
    calc d * (k * e + 1) = (d * k) * e + d := by ring
      _ = (d * k) * e + (c * e + s) := by rw [hds]
      _ = e * (d * k + c) + s := by ring
      _ = e * (n * ((d*k+c)/n) + r) + s := by rw [hr, hdm]
      _ = (e * r + s) + (n * e) * ((d * k + c) / n) := by ring
  have hrlt : r < n := Nat.mod_lt _ (by omega)
  have hub : e * r + s < n * e := by nlinarith [hrlt, hslt, he]
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hub]
  constructor
  · nlinarith [hlo, he]
  · rcases hhi with h | ⟨h1, h2⟩
    · have hne : (n - 2) * e + e = (n - 1) * e := by
        have hstep : n - 1 = (n - 2) + 1 := by omega
        rw [hstep, Nat.succ_mul]
      have : e * r ≤ (n - 2) * e := by nlinarith [h, he]
      omega
    · rw [h1, h2, Nat.add_zero, mul_comm]


/-! ## the `t`-generalisation

`a = k·e + 1` samples only `n` of the flank's `e` openings.  Taking `a = k·e + t` with
`t ≡ 1 (mod n)` samples more, and the same algebra applies with `d·t` in place of `d`:

    d·a = e·(d·k) + d·t = e·(d·k + ⌊d·t/e⌋) + (d·t mod e).

Measured at `n = 5`: a budget of four values `t ∈ {1, 6, 11, 16}` lifts coverage of what
P1′–P5 leave from 79.0% to **94.4%** — and it saturates there, so the budget is genuinely
bounded.  Total coverage 96.1% → **99.13%**. -/

theorem flankWorks_of_shifted_t (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (k t : ℕ) (hkn : k < n) (ht0 : 0 < t) (hte : k * e + t < n * e) (htn : t % n = 1 % n)
    (hgood : ∀ d ∈ L, 1 ≤ (d * k + (d * t) / e) % n ∧
              ((d * k + (d * t) / e) % n ≤ n - 2 ∨
               ((d * k + (d * t) / e) % n = n - 1 ∧ (d * t) % e = 0))) :
    flankWorks n L e = true := by
  have hn2 : 2 ≤ n := Fact.out
  -- a = k*e + t is congruent to 1 mod n, so it is n*j+1 for j = (a-1)/n
  obtain ⟨E, hE⟩ := hen
  have hke : (k * e) % n = 0 := by
    rw [hE, show k * (n * E) = n * (k * E) by ring]
    exact Nat.mul_mod_right _ _
  have hamod : (k * e + t) % n = 1 % n := by
    rw [Nat.add_mod, hke, Nat.zero_add]
    simpa using htn
  have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone] at hamod
  set j : ℕ := (k * e + t) / n with hj
  have hkey : n * j + 1 = k * e + t := by
    have h := Nat.div_add_mod (k * e + t) n
    rw [hamod] at h
    rw [hj]; omega
  have hjlt : j < e := by
    have : n * j + 1 ≤ n * e := by rw [hkey]; omega
    nlinarith [this, he, hn2]
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hkey]
  obtain ⟨hlo, hhi⟩ := hgood d hd
  set c : ℕ := (d * t) / e with hc
  set s : ℕ := (d * t) % e with hs
  set r : ℕ := (d * k + c) % n with hr
  have hslt : s < e := Nat.mod_lt _ he
  have hds : c * e + s = d * t := by rw [hc, hs, Nat.mul_comm]; exact Nat.div_add_mod (d * t) e
  have hsplit : d * (k * e + t) = (e * r + s) + (n * e) * ((d * k + c) / n) := by
    have hdm := Nat.div_add_mod (d * k + c) n
    calc d * (k * e + t) = (d * k) * e + d * t := by ring
      _ = (d * k) * e + (c * e + s) := by rw [hds]
      _ = e * (d * k + c) + s := by ring
      _ = e * (n * ((d*k+c)/n) + r) + s := by rw [hr, hdm]
      _ = (e * r + s) + (n * e) * ((d * k + c) / n) := by ring
  have hrlt : r < n := Nat.mod_lt _ (by omega)
  have hub : e * r + s < n * e := by nlinarith [hrlt, hslt, he]
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hub]
  refine ⟨by nlinarith [hlo, he], ?_⟩
  rcases hhi with h | ⟨h1, h2⟩
  · have hne : (n - 2) * e + e = (n - 1) * e := by
      have hstep : n - 1 = (n - 2) + 1 := by omega
      rw [hstep, Nat.succ_mul]
    have : e * r ≤ (n - 2) * e := by nlinarith [h, he]
    omega
  · rw [h1, h2, Nat.add_zero, mul_comm]



/-! ## the `ρ`-construction is a reparametrisation, not a search

**Correction, 2026-09-22.**  I described the `ρ`-construction as "a search, not a rule — one
parameter against `c − 2` constraints, hence the `v`-budget".  That is wrong, and the error is
one already on this project's own list.

With `gcd(e, n) = 1` the Chinese Remainder Theorem makes `ρ ↦ a` a **bijection** between the
residues `ρ < e` and the opening indices `a < n·e` with `a ≡ 1 (mod n)` — which are exactly the
`a = n·j + 1` for `j < e` that `flankWorks` already ranges over (`FlankFiniteN.flankWorks_iff`).
And `v ↦ ρ = m'⁻¹·v mod e` is a bijection on `ℤ/e` whenever `gcd(m', e) = 1`.

So `v` over `[0, e)` **is** `j` over `[0, e)`, reparametrised so that the multiple of `n` sits at
a chosen position instead of the flank.  Ranging over it is not a search: it is the same finite
decidable check, and `flankWorks_iff` proves that check decides the question.

**What was actually wrong was my `v`-budget of 12.**  Truncating an exhaustive finite range and
then reporting the result as the criterion's reach is the error recorded at
`HANDOVER_2026_09_21_v1` §1.5 — a range truncated instead of taken whole.  With the full range,
every applicable set at order five is covered: 18,794 of 18,794
(`experiments/nN/rho_is_determined_v1.out`).

**What remains true**: no *closed form* for `v` is known.  Five natural candidates — `v = ⌊e/2⌋`,
`⌈e/2⌉`, `ρ = ⌊e/2⌋`, `ρ = m'⁻¹` — reach at most 46% of the applicable sets.  So the construction
is a complete decidable criterion without a formula, which is a different thing from a search. -/

/-- **The `ρ`-parametrisation is exhaustive.**  Every residue `ρ < e` is `a mod e` for exactly one
opening index `a < n·e` with `a ≡ 1 (mod n)`, so ranging over `ρ` ranges over every opening the
flank has.  This is why the construction needs no budget. -/
theorem exists_opening_with_residue {e : ℕ} (he : 0 < e) (hcop : Nat.Coprime n e) (ρ : ℕ) :
    ∃ a : ℕ, a < n * e ∧ a % n = 1 % n ∧ a % e = ρ % e := by
  have hn2 : 2 ≤ n := Fact.out
  refine ⟨(Nat.chineseRemainder hcop 1 ρ).val, ?_,
    (Nat.chineseRemainder hcop 1 ρ).prop.1, (Nat.chineseRemainder hcop 1 ρ).prop.2⟩
  simpa using Nat.chineseRemainder_lt_mul hcop 1 ρ (by omega) (by omega)

/-- **And the multiple's position is the parameter.**  With `n ∣ m`, `m = n·m'`, the reading of
`m` at `a` is `n·(m'·a mod e)` — so choosing `a mod e` chooses that reading outright.  Combined
with the bijection above: the construction selects an opening *by naming where the multiple goes*,
and every opening is named exactly once. -/
theorem multiple_reading_at (m' e a : ℕ) : (n * m' * a) % (n * e) = n * ((m' * a) % e) := by
  rw [mul_assoc, Nat.mul_mod_mul_left]

end LRC.OtherFlank

namespace LRC.Witness

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-! ## the general witness certificate

`a = k·e + t` is one way to produce a witness; the `ρ`-construction at a **non-multiple** flank
is another (choose `ρ` so the lone `n`-multiple lands mid-band, then `a = ρ + e·w` with
`w = (1−ρ)·e⁻¹ mod n`).  Rather than a theorem per construction, this is the single bridge from
any produced `a` to `flankWorks`.

Measured at `n = 5`, the `ρ`-construction with a budget of twelve values closes **98.1%** of what
P1′–P6 leave, taking total coverage from 99.13% to **99.986%** — 12 sets of 85,771 remain. -/

/-- **The general witness certificate.**  Any `a ≡ 1 (mod n)` below `n·e` whose readings all sit
in the band certifies the flank.  Every construction in this development — the prime one
`a = e·s`, the shifted one `a = k·e + t`, and the `ρ`-construction at a non-multiple flank — is
an instance: they differ only in how `a` is produced, and this lemma is the single bridge from a
produced `a` to `flankWorks`. -/
theorem flankWorks_of_witness (L : List ℕ) (e : ℕ) (he : 0 < e) (a : ℕ)
    (ha1 : a % n = 1 % n) (halt : a < n * e)
    (hband : ∀ d ∈ L, e ≤ (d * a) % (n * e) ∧ (d * a) % (n * e) ≤ (n - 1) * e) :
    flankWorks n L e = true := by
  have hn2 : 2 ≤ n := Fact.out
  have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone] at ha1
  set j : ℕ := a / n with hj
  have hkey : n * j + 1 = a := by
    have h := Nat.div_add_mod a n
    rw [ha1] at h; rw [hj]; omega
  have hjlt : j < e := by
    have : n * j + 1 ≤ n * e := by rw [hkey]; omega
    nlinarith [this, he, hn2]
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hkey]
  exact hband d hd

/-- **And the real-valued form**, through the bridge. -/
theorem lonely_of_witness (L : List ℕ) (e : ℕ) (he : 0 < e) (a : ℕ)
    (ha1 : a % n = 1 % n) (halt : a < n * e)
    (hband : ∀ d ∈ L, e ≤ (d * a) % (n * e) ∧ (d * a) % (n * e) ≤ (n - 1) * e) :
    ∃ j : ℕ, ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening n (e : ℝ) j) :=
  lonely_of_flankWorks L e he (flankWorks_of_witness L e he a ha1 halt hband)

end LRC.Witness

namespace LRC.OtherFlank

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

/-! ## a worked instance

`ds = (1, 2, 10, 16)` is in the residue — `10` is a non-flank multiple of 5, the ratio `16/1` is
wide, `16 > 15`, and its widest lonely interval is narrower than `1/16`, so P1′–P5 all miss it.
Taking the flank to be **10**, not the largest 16, and `k = 1`: the values `d·k + d/10` are
`1, 2, 11, 17`, with residues `1, 2, 1, 2` mod 5 — all inside `{1,2,3}`. -/

instance : Fact (2 ≤ 5) := ⟨by norm_num⟩

theorem residue_instance_1_2_10_16 :
    ∃ k : ℕ, ∀ d ∈ ([1, 2, 10, 16] : List ℕ),
      ((5 : ℕ) : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening 5 ((10 : ℕ) : ℝ) k) :=
  lonely_of_flankWorks _ 10 (by norm_num)
    (flankWorks_of_shifted (n := 5) [1, 2, 10, 16] 10 (by norm_num) (by norm_num)
      1 (by norm_num) (by norm_num) (by decide))

/-! ## a worked instance for the witness certificate

`ds = (1, 5, 6, 16)` sits in the final 0.87% — one `5`-multiple (namely `5` itself), flank `16`
coprime to 5, and P1′–P6 all miss it.  The `ρ`-construction gives `ρ = 4`, hence `a = 36`, and
the readings `36, 20, 56, 16` all lie in the band `[16, 64]`. -/

theorem residue_instance_1_5_6_16 :
    ∃ j : ℕ, ∀ d ∈ ([1, 5, 6, 16] : List ℕ),
      ((5 : ℕ) : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening 5 ((16 : ℕ) : ℝ) j) :=
  LRC.Witness.lonely_of_witness (n := 5) [1, 5, 6, 16] 16 (by norm_num) 36
    (by norm_num) (by norm_num) (by decide)

end LRC.OtherFlank
