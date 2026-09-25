import LonelyRunner.LRC.Spec.OrderSixPropElevenN

/-!
# BHK Proposition 11 at named instants

`OrderSixPropElevenN` ports BHK's Proposition 11 in BHK's own form: assume the
runners cover every time (`B₀ = ℝ⁺`) and derive `False`. That form concludes by
emptiness, which the framework does not use. This file is the same proof,
lemma for lemma, with the covering removed.

Wherever BHK's argument reads the covering at an instant `τ` it now asks
whether `τ` is lonely (`found_or_blocked`): if it is, `τ` is the named instant
and the case closes; if not, some runner blocks `τ`, and BHK's argument
continues unchanged. So

* a lemma that ended in `False` now ends in `Found w`, a lonely instant, and
  every branch that produces one names it;
* a lemma with conclusion `P` now ends in `Found w ∨ P`.

Part 2 adds BHK's fictional runner of speed `2 w₀` (`Found6`).

The lemmas that do not read the covering are used from `OrderSixPropElevenN`
as they are. The names here are those of the source, in the namespace
`LRC.OrderSixN.S7.Named`. The docstrings are the source's, lightly edited; where
one still speaks of runners covering a gap, read it as: every instant of that
named gap has been read and each is blocked, or the lonely one has been returned.
-/

open MeasureTheory Set

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.show false
set_option linter.style.multiGoal false
set_option linter.style.setOption false
set_option linter.flexible false

namespace LRC.OrderSixN.S7.Named

open LRC.OrderSixN

/-- A lonely instant for the five speeds `w` at `1/6`. -/
def Found (w : Fin 5 → ℕ) : Prop :=
  ∃ t : ℝ, ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * t)

/-- A lonely instant at which BHK's fictional runner `2 w₀` is also clear. -/
def Found6 (w : Fin 5 → ℕ) : Prop :=
  ∃ t : ℝ, (∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * t)) ∧
    (1 : ℝ) / 6 ≤ circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * t))

/-- **The instant `τ` is read.** Either `τ` is lonely, and is the named instant,
    or some runner is within `1/6` of the origin at `τ`. -/
theorem found_or_blocked (w : Fin 5 → ℕ) (τ : ℝ) :
    Found w ∨ ∃ i, circDist ((w i : ℝ) * τ) < 1 / 6 := by
  by_cases h : ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
  · exact Or.inl ⟨τ, h⟩
  · push_neg at h
    exact Or.inr h

/-- **The instant `τ` is read, with the fictional runner.** Either `τ` is
    lonely with `2 w₀` also clear, or some runner (possibly `2 w₀`) blocks `τ`. -/
theorem found6_or_blocked (w : Fin 5 → ℕ) (τ : ℝ) :
    Found6 w ∨ (∃ i, circDist ((w i : ℝ) * τ) < 1 / 6) ∨
      circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ)) < 1 / 6 := by
  by_cases h : ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
  · by_cases h0 : (1 : ℝ) / 6 ≤ circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ))
    · exact Or.inl ⟨τ, h, h0⟩
    · exact Or.inr (Or.inr (not_le.mp h0))
  · push_neg at h
    exact Or.inr (Or.inl h)

/-- **The instants of a named set are read.** Either one of them is lonely, or
    every one is blocked by some runner. Used only on explicit sets (a named
    gap `[a, b]`, or its translates by multiples of `1/g`), never on all times. -/
theorem found_or_blocked_on (w : Fin 5 → ℕ) (S : Set ℝ) :
    Found w ∨ ∀ τ ∈ S, ∃ i, circDist ((w i : ℝ) * τ) < 1 / 6 := by
  by_cases h : ∃ τ ∈ S, ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
  · obtain ⟨τ, -, hτ⟩ := h
    exact Or.inl ⟨τ, hτ⟩
  · push_neg at h
    exact Or.inr h

/-- Six-runner form of `found_or_blocked_on`. -/
theorem found6_or_blocked_on (w : Fin 5 → ℕ) (S : Set ℝ) :
    Found6 w ∨ ∀ τ ∈ S, (∃ i, circDist ((w i : ℝ) * τ) < 1 / 6) ∨
      circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ)) < 1 / 6 := by
  by_cases h : ∃ τ ∈ S, (∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)) ∧
      (1 : ℝ) / 6 ≤ circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ))
  · obtain ⟨τ, -, hτ⟩ := h
    exact Or.inl ⟨τ, hτ⟩
  · refine Or.inr fun τ hτ => ?_
    by_cases h1 : ∀ i, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ)
    · exact Or.inr (not_le.mp fun h2 => h ⟨τ, hτ, h1, h2⟩)
    · push_neg at h1
      exact Or.inl h1

/-- **Covering of a 123-gap.** Unless an instant has been found, every
    123-gap (runners 1, 2, 3 safe) must be covered by runners 4 and 5. -/
lemma bhk_prop11_gap_covered (w : Fin 5 → ℕ)
    {a b : ℝ}
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s)) : Found w ∨
      (Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∪ unsafeOf w ⟨4, by omega⟩) := by
  rcases found_or_blocked_on w (Set.Icc a b) with hF | hblk
  · exact Or.inl hF
  right
  intro s hs
  obtain ⟨i, hi⟩ := hblk s hs
  fin_cases i
  · exact absurd hi (not_lt.mpr (hgap s hs 0))
  · exact absurd hi (not_lt.mpr (hgap s hs 1))
  · exact absurd hi (not_lt.mpr (hgap s hs 2))
  · exact Or.inl ((mem_unsafeOf_iff w _ s).mpr hi)
  · exact Or.inr ((mem_unsafeOf_iff w _ s).mpr hi)

/-- **BHK §5 Part 2 — Corollary 16 (`v₄ < 2`), conditional on a witness time.**
    Given a half-integer time `t` (runner 3 at `1/2`) with runner 1 in
    `[1/6, 1/3]`, unless an instant has been found, BHK force `w₃ < 2 w₂`
    (`v₄ < 2 v₃`). The witness-time existence (BHK Corollary 15, via finite
    equidistribution of the `w₂` half-integer positions of runner 1) is the
    remaining ingredient. Proof: `bhk_prop11_gap123` gives a 123-gap of length
    `1/(3 w₂)`; `bhk_lemma_4` bounds that length by `2/(3 w₃)`. -/
lemma bhk_prop11_v4_lt_2v3_of_time (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ≤ 1 / 3) : Found w ∨
      ((w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ)) := by
  have hw2R : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3R : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  obtain hF | hcov := bhk_prop11_gap_covered w
    (bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi)
  · exact Or.inl hF
  right
  have hab : t ≤ t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
    have : (0 : ℝ) ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by positivity
    linarith
  have hlen := bhk_lemma_4 w hmono hpos t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) hab hcov
  have hkey : 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) < 2 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by
    linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hkey
  linarith

/-- **BHK §5 Part 2 — Corollary 16 (`v₄ < 2`).** Combining the witness-time
    existence (`bhk_prop11_witness_time`) with the conditional bound: under the
    covering assumption, `q = w₂/gcd(w₀,w₂) ≥ 5` forces `w₃ < 2 w₂`. This `q ≥ 5`
    is exactly BHK Lemma 13 — the only remaining structural fact for Cor 16. -/
lemma bhk_prop11_v4_lt_2v3 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found w ∨
      ((w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ)) := by
  obtain ⟨t, h3, h1lo, h1hi⟩ := bhk_prop11_witness_time w hpos hsmall hq5
  exact bhk_prop11_v4_lt_2v3_of_time w hmono hpos hsum hsmall t h3 h1lo h1hi

/-- **BHK §5 Part 2 — Lemma 18 (`q ≥ 18` part): `v₄ ≤ 3/2`.** The sharpening of
    Corollary 16 (`v₄ < 2`). For `q = w₂/gcd(w₀,w₂) ≥ 18`, `bhk_prop11_residue_hit_narrow`
    produces a half-integer time launching (via `bhk_prop11_gap123_long`) a
    0123-gap of time-length `4/(9w₂)` (BHK length `4/9`); `bhk_lemma_4` converts
    the length into `2 w₃ < 3 w₂`. (BHK states `≤ 3/2`; the denominator-`q`
    refinement and the per-`(p,q)` Table 1 entries are only needed in the
    complementary `q < 18` branch.) -/
lemma bhk_prop11_v4_le_3_2 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq18 : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < 3 * (w ⟨2, by omega⟩ : ℝ)) := by
  set a := w ⟨0, by omega⟩ with ha
  set n := w ⟨2, by omega⟩ with hn
  have ha0 : 0 < a := hpos _
  have hn0 : 0 < n := by omega
  set g : ℕ := Nat.gcd a n with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a n
  have hgn : g ∣ n := Nat.gcd_dvd_right a n
  have ha'0 : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hg0
  have h3a' : 3 * (a / g) < n / g := by
    have hmul : 3 * (a / g) * g < n / g * g := by
      calc 3 * (a / g) * g = 3 * a := by rw [mul_assoc, Nat.div_mul_cancel hga]
        _ < n := hsmall
        _ = n / g * g := (Nat.div_mul_cancel hgn).symm
    exact lt_of_mul_lt_mul_right hmul (Nat.zero_le g)
  have hcop' : Nat.Coprime (a / g) (n / g) := Nat.coprime_div_gcd_div_gcd hg0
  obtain ⟨m, hm⟩ := bhk_prop11_residue_hit_narrow (a / g) (n / g) ha'0 h3a' hq18 hcop'
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  have hb'R : (0 : ℝ) < ((n / g : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n / g)
  have haf : (a : ℝ) = (g : ℝ) * ((a / g : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hga]
  have hnf : (n : ℝ) = (g : ℝ) * ((n / g : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hgn]
  set t : ℝ := (2 * (m : ℝ) + 1) / (2 * (n : ℝ)) with ht
  have heq : (a : ℝ) * t
      = ((a / g : ℕ) : ℝ) * ((2 * (m : ℝ) + 1) / (2 * ((n / g : ℕ) : ℝ))) := by
    rw [ht, haf, hnf]; field_simp
  have hw1 : (w ⟨1, by omega⟩ : ℝ) = (n : ℝ) - (a : ℝ) := by
    have : (a : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (n : ℝ) := by exact_mod_cast hsum
    linarith
  -- runner 3 at the half-way point
  have h3half : Int.fract ((n : ℝ) * t) = 1 / 2 := by
    have hh : (n : ℝ) * t = (m : ℝ) + 1 / 2 := by rw [ht]; field_simp
    rw [hh, show (m : ℝ) + 1 / 2 = ((m : ℤ) : ℝ) + 1 / 2 from by push_cast; ring,
      Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  -- endpoint bridges p/(9q) = a/(9n), (q-p)/(9q) = (n-a)/(9n)
  have hep1 : ((a / g : ℕ) : ℝ) / (9 * ((n / g : ℕ) : ℝ)) = (a : ℝ) / (9 * n) := by
    rw [haf, hnf]; field_simp
  have hep2 : (((n / g : ℕ) : ℝ) - ((a / g : ℕ) : ℝ)) / (9 * ((n / g : ℕ) : ℝ))
      = ((n : ℝ) - a) / (9 * n) := by rw [haf, hnf]; field_simp
  have hbridge : Int.fract ((a : ℝ) * t)
      = Int.fract (((a / g : ℕ) : ℝ) * ((2 * (m : ℝ) + 1) / (2 * ((n / g : ℕ) : ℝ)))) := by
    rw [heq]
  have hwlo : 1 / 6 + (a : ℝ) / (9 * n) ≤ Int.fract ((a : ℝ) * t) := by
    rw [hbridge, ← hep1]; exact (Set.mem_Icc.mp hm).1
  have hwhi : Int.fract ((a : ℝ) * t) ≤ 1 / 3 - (w ⟨1, by omega⟩ : ℝ) / (9 * n) := by
    rw [hbridge, hw1, ← hep2]; exact (Set.mem_Icc.mp hm).2
  have hgap := bhk_prop11_gap123_long w hpos hsum hsmall t h3half hwlo hwhi
  obtain hF | hcov := bhk_prop11_gap_covered w hgap
  · exact Or.inl hF
  right
  have hab : t - 1 / (9 * n) ≤ t + 1 / (3 * n) := by
    have h1 : (0 : ℝ) < 1 / (9 * n) := by positivity
    have h2 : (0 : ℝ) < 1 / (3 * n) := by positivity
    linarith
  have hlen := bhk_lemma_4 w hmono hpos (t - 1 / (9 * n)) (t + 1 / (3 * n)) hab hcov
  have hw3R : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have key : 1 / (3 * (n : ℝ)) + 1 / (9 * n) < 2 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by
    linarith [hlen]
  have hcomb : 1 / (3 * (n : ℝ)) + 1 / (9 * n) = 4 / (9 * n) := by field_simp; ring
  rw [hcomb, div_lt_div_iff₀ (by positivity) (by positivity)] at key
  linarith [key]

/-- **Lemma 18 / Table 1 bound from an explicit witness (`q < 18`).** Given a
    half-integer time `t` whose runner-1 position lies in the parametric window
    `[1/6 + ρ·v₁, 1/3 − ρ·v₂]`, the resulting `0123`-gap of length `(1/3 + ρ)/w₂`
    (a `45`-block by the covering) forces, via `bhk_lemma_4`, the bound
    `(1 + 3ρ)·w₃ < 2·w₂` — i.e. `v₄ < 2/(1 + 3ρ)`. With `ρ = 1/9` this is
    `v₄ ≤ 3/2`; the per-`(p,q)` Table-1 entries are the maximal-`ρ` instances used
    to exclude the large-`v₄` triples in `core_q_lt_18`. -/
lemma bhk_prop11_v4_bound_witness (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ6 : ρ ≤ 1 / 6)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 + ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
      ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
      ≤ 1 / 3 - ρ * (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)) : Found w ∨
      ((1 + 3 * ρ) * (w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ)) := by
  have hw2R : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3R : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hgap := bhk_prop11_gap123_long_rho w hpos hsum hsmall ρ hρ0 hρ6 t h3 h1lo h1hi
  obtain hF | hcov := bhk_prop11_gap_covered w hgap
  · exact Or.inl hF
  right
  have hab : t - ρ / (w ⟨2, by omega⟩ : ℝ) ≤ t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
    have h1 : (0 : ℝ) < ρ / (w ⟨2, by omega⟩ : ℝ) := by positivity
    have h2 : (0 : ℝ) < 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by positivity
    linarith
  have hlen := bhk_lemma_4 w hmono hpos _ _ hab hcov
  -- hlen : (t + 1/(3w₂)) - (t - ρ/w₂) < 2/(3 w₃)
  have key : 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) + ρ / (w ⟨2, by omega⟩ : ℝ)
      < 2 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by linarith [hlen]
  have hcomb : 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) + ρ / (w ⟨2, by omega⟩ : ℝ)
      = (1 + 3 * ρ) / (3 * (w ⟨2, by omega⟩ : ℝ)) := by field_simp
  rw [hcomb, div_lt_div_iff₀ (by positivity) (by positivity)] at key
  nlinarith [key]

/-- **Reusable Lemma-18 exclusion kill (`q < 18`).** A maximizing half-integer
    witness `m` with slack `ρ` (runner 1 at `{p(m+½)/q} ∈ [1/6+ρp/q, 1/3-ρ(q-p)/q]`)
    forces `v₄ < 2/(1+3ρ)` via `bhk_prop11_v4_bound_witness`; if the candidate `r`
    has `2q ≤ (1+3ρ)r` (i.e. `r/q ≥ 2/(1+3ρ)`), that is a contradiction. For a
    concrete triple the window facts `h1lo/h1hi` and the bound `hrb` are `norm_num`
    goals. Excludes the large-`v₄` triples (BHK Table 1 / Lemma 18). -/
lemma bhk_prop11_exc_v4kill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r m : ℕ) (ρ : ℝ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (hρ0 : 0 < ρ) (hρ6 : ρ ≤ 1 / 6)
    (h1lo : 1 / 6 + ρ * (p : ℝ) / q ≤ (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ))
    (h1hi : (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)
        ≤ 1 / 3 - ρ * ((q : ℝ) - p) / q)
    (hrb : 2 * (q : ℝ) ≤ (1 + 3 * ρ) * r) : Found w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
  have hw0w2 : (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ) = (p : ℝ) / q := by
    rw [c0, c2]; rw [mul_div_mul_left _ _ hgR.ne']
  have hw1w2 : (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ) = ((q : ℝ) - p) / q := by
    have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - p) := by
      have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
        exact_mod_cast hsum
      rw [show (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) from by
        linarith, c0, c2]; ring
    rw [c1, c2, mul_div_mul_left _ _ hgR.ne']
  set t : ℝ := ((m : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
  have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ) + 1 / 2 := by rw [htdef]; field_simp
  have h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2 := by
    rw [e2, show (m : ℝ) + 1 / 2 = ((m : ℤ) : ℝ) + 1 / 2 from by push_cast; ring,
        Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  have e0t : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((m : ℝ) + 1 / 2) := by
    rw [htdef, c0, c2]; field_simp
  have hCp : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
      = (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) := by
    rw [e0t, bhk_prop11_Cpoint_eval p q m hq]
  have hwlo : 1 / 6 + ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
      ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) := by
    rw [hCp, show ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
          = ρ * ((w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)) from by ring, hw0w2,
        show ρ * ((p : ℝ) / q) = ρ * (p : ℝ) / q from by ring]
    exact h1lo
  have hwhi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
      ≤ 1 / 3 - ρ * (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ) := by
    rw [hCp, show ρ * (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
          = ρ * ((w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)) from by ring, hw1w2,
        show ρ * (((q : ℝ) - p) / q) = ρ * ((q : ℝ) - p) / q from by ring]
    exact h1hi
  obtain hF | hb := bhk_prop11_v4_bound_witness w hmono hpos hsum hsmall ρ hρ0 hρ6 t h3 hwlo hwhi
  · exact hF
  -- hb : (1 + 3ρ) * w₃ < 2 * w₂; with c2,c3 and hrb : 2q ≤ (1+3ρ)r → contradiction
  rw [c2, c3] at hb
  nlinarith [hb, hrb, hgR, mul_pos hgR hqR]

/-- **BHK §5 Part 2 — Lemma 12.** For a `0123`-gap `[a,b]` (runners 1,2,3 safe
    throughout) unless an instant has been found, with `g` dividing the
    speeds of runners 1,2,3: either runner 4 covers the whole gap, or runner 5
    does, or *both* `v₄ = r/q` and `v₅ = s/q` (`g ∣ w₃ ∧ g ∣ w₄`). Use (1)
    (`bhk_prop11_no_double`) forces one denominator to divide `g`; use (2)
    (`bhk_prop11_dvd_of_orbit_covered`) then forces the other. -/
lemma bhk_prop11_lemma12 (w : Fin 5 → ℕ) (g : ℕ) (hg : 0 < g)
    (hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩)
    {a b : ℝ} (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s)) : Found w ∨
      (Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∨ Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
      ∨ (g ∣ w ⟨3, by omega⟩ ∧ g ∣ w ⟨4, by omega⟩)) := by
  obtain hF | hcov45 := bhk_prop11_gap_covered w hgap
  · exact Or.inl hF
  rcases found_or_blocked_on w {τ | ∃ p ∈ Set.Icc a b, ∃ i : ℕ, τ = p + (i : ℝ) * (1 / g)} with hF | hblkT
  · exact Or.inl hF
  right
  by_cases h4 : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩
  · exact Or.inl h4
  by_cases h5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
  · exact Or.inr (Or.inl h5)
  refine Or.inr (Or.inr ?_)
  obtain ⟨u, huIcc, hu4, hu5⟩ := bhk_prop11_overlap w hcov45 h4 h5
  -- Translates of any 0123-safe point are covered by runner 4 or 5.
  have htrans : ∀ (p : ℝ), p ∈ Set.Icc a b → ∀ i : ℕ,
      circDist ((w ⟨3, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)) < 1 / 6 ∨
      circDist ((w ⟨4, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)) < 1 / 6 := by
    intro p hp i
    obtain ⟨k, hk⟩ := hblkT _ ⟨p, hp, i, rfl⟩
    -- runners 1,2,3 stay safe at the translate
    have hsafe012 : ∀ j : Fin 3,
        (1 : ℝ) / 6 ≤ circDist ((w ⟨j.val, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g))) := by
      intro j
      have hjexp : (w ⟨j.val, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g))
          = (w ⟨j.val, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨j.val, by omega⟩ : ℝ) / g) := by
        ring
      rw [hjexp, bhk_prop11_circDist_orbit_dvd _ g hg (hdvd012 j)]
      exact hgap p hp j
    -- so the covering runner k is 4 or 5
    fin_cases k
    · exact absurd hk (not_lt.mpr (hsafe012 0))
    · exact absurd hk (not_lt.mpr (hsafe012 1))
    · exact absurd hk (not_lt.mpr (hsafe012 2))
    · left
      rw [show (w ⟨3, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)
            = (w ⟨3, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g)) from by ring]
      exact hk
    · right
      rw [show (w ⟨4, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)
            = (w ⟨4, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g)) from by ring]
      exact hk
  -- use (1): at least one of runners 4, 5 has its orbit collapse (g ∣ w_a).
  have hua : circDist ((w ⟨3, by omega⟩ : ℝ) * u) < 1 / 6 := (mem_unsafeOf_iff w _ u).mp hu4
  have hub : circDist ((w ⟨4, by omega⟩ : ℝ) * u) < 1 / 6 := (mem_unsafeOf_iff w _ u).mp hu5
  have hor : g ∣ w ⟨3, by omega⟩ ∨ g ∣ w ⟨4, by omega⟩ := by
    by_contra hcon
    rw [not_or] at hcon
    exact bhk_prop11_no_double g hg _ _ hcon.1 hcon.2 _ _ hua hub (htrans u huIcc)
  -- use (2): a point where runner `a` is also safe forces runner `b` to cover all
  -- translates, collapsing its orbit too.
  rcases hor with h3 | h4'
  · -- `g ∣ w₃`; pick a point where runner 4 (`w₃`) is also safe, forcing runner 5.
    refine ⟨h3, ?_⟩
    rw [Set.not_subset] at h4
    obtain ⟨p, hpIcc, hp4⟩ := h4
    rw [mem_unsafeOf_iff, not_lt] at hp4
    apply bhk_prop11_dvd_of_orbit_covered _ g hg ((w ⟨4, by omega⟩ : ℝ) * p)
    intro i
    rcases htrans p hpIcc i with h | h
    · exfalso
      have hsafe3 : (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * p
          + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)) := by
        rw [bhk_prop11_circDist_orbit_dvd _ g hg h3]; exact hp4
      linarith
    · exact h
  · -- `g ∣ w₄`; pick a point where runner 5 (`w₄`) is also safe, forcing runner 4.
    refine ⟨?_, h4'⟩
    rw [Set.not_subset] at h5
    obtain ⟨p, hpIcc, hp5⟩ := h5
    rw [mem_unsafeOf_iff, not_lt] at hp5
    apply bhk_prop11_dvd_of_orbit_covered _ g hg ((w ⟨3, by omega⟩ : ℝ) * p)
    intro i
    rcases htrans p hpIcc i with h | h
    · exact h
    · exfalso
      have hsafe4 : (1 : ℝ) / 6 ≤ circDist ((w ⟨4, by omega⟩ : ℝ) * p
          + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)) := by
        rw [bhk_prop11_circDist_orbit_dvd _ g hg h4']; exact hp5
      linarith

/-- **BHK §5 Part 2 — Lemma 17 (`v₄ = r/q`, `v₅ = s/q`).** Conditional on
    `q = w₂ / gcd(w₀,w₂) ≥ 5` (BHK Lemma 13), the denominators of runners 4 and 5
    both divide `q`: `g ∣ w₃ ∧ g ∣ w₄` with `g = gcd(w₀,w₂)`. Corollary 15
    (`bhk_prop11_witness_time`) produces a `0123`-gap of length `1/(3 w₂)`; since
    `w₃, w₄ > w₂` this exceeds both block widths, so the gap lies in neither `B₄`
    nor `B₅`, and Lemma 12 leaves only the divisibility conclusion. -/
lemma bhk_prop11_lemma17 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found w ∨
      (Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨3, by omega⟩ ∧
      Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨4, by omega⟩) := by
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgdvd0 : g ∣ w ⟨0, by omega⟩ := by rw [hgdef]; exact Nat.gcd_dvd_left _ _
  have hgdvd2 : g ∣ w ⟨2, by omega⟩ := by rw [hgdef]; exact Nat.gcd_dvd_right _ _
  have hgdvd1 : g ∣ w ⟨1, by omega⟩ := by
    have he : w ⟨1, by omega⟩ = w ⟨2, by omega⟩ - w ⟨0, by omega⟩ := by omega
    rw [he]; exact Nat.dvd_sub hgdvd2 hgdvd0
  have hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩ := by
    intro i; fin_cases i
    · exact hgdvd0
    · exact hgdvd1
    · exact hgdvd2
  -- Corollary 15 + the 0123-gap construction.
  obtain ⟨t, h3, h1lo, h1hi⟩ := bhk_prop11_witness_time w hpos hsmall hq5
  have hgap := bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi
  -- The gap (length `1/(3 w₂)`) is too long to fit in `B₄` or `B₅`.
  have hw2 : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos ⟨2, by omega⟩
  have hgaplen : ∀ (j : Fin 5), w ⟨2, by omega⟩ < w j →
      (1 : ℝ) / (3 * (w j : ℝ)) < (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) - t := by
    intro j hj
    rw [add_sub_cancel_left]
    have hwj : (w ⟨2, by omega⟩ : ℝ) < (w j : ℝ) := by exact_mod_cast hj
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hn4 : ¬ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) ⊆ unsafeOf w ⟨3, by omega⟩ :=
    bhk_prop11_not_subset_unsafeOf w ⟨3, by omega⟩ (hpos _)
      (le_add_of_nonneg_right (by positivity))
      (hgaplen ⟨3, by omega⟩ (hmono (Fin.mk_lt_mk.mpr (by omega))))
  have hn5 : ¬ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) ⊆ unsafeOf w ⟨4, by omega⟩ :=
    bhk_prop11_not_subset_unsafeOf w ⟨4, by omega⟩ (hpos _)
      (le_add_of_nonneg_right (by positivity))
      (hgaplen ⟨4, by omega⟩ (hmono (Fin.mk_lt_mk.mpr (by omega))))
  rcases bhk_prop11_lemma12 w g hg0 hdvd012 hgap with hF | hc | hc | hc
  · exact Or.inl hF
  all_goals right
  · exact absurd hc hn4
  · exact absurd hc hn5
  · exact hc

/-- **`1234`-gap span bound.** A `1234`-gap (runners 1,2,3,4 all `≥ 1/6`) is,
    unless an instant has been found, contained in `B₅`, so `block_containment`
    bounds the span of runner 5: `w₄ · (b - a) < 1/3`. The engine of every
    `r`-case of BHK Lemma 13. -/
lemma bhk_prop11_gap1234_b5span (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h4safe : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s)) : Found w ∨
      ((w ⟨4, by omega⟩ : ℝ) * (b - a) < 1 / 3) := by
  obtain hF | hcov45 := bhk_prop11_gap_covered w hgap
  · exact Or.inl hF
  right
  have hsub5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩ := by
    intro s hs
    rcases hcov45 hs with h | h
    · exact absurd ((mem_unsafeOf_iff w _ s).mp h) (not_lt.mpr (h4safe s hs))
    · exact h
  obtain ⟨k, hk1, hk2⟩ := block_containment w ⟨4, by omega⟩ (hpos _) a b hab hsub5
  rw [mul_sub]; linarith

/-- **BHK Lemma 13 (`q ≥ 5`).** Unless an instant has been found, the
    reduced denominator `q = w₂ / gcd(w₀,w₂)` is at least `5`; equivalently the
    case `v₁ = 1/4` (`q = 4`) cannot occur. BHK rule this out via the explicit
    `123`-gaps `I₁ = [2/3, 5/6]` and `I₂ = [13/6, 44/18]` (in normalised time,
    i.e. `[1/(6w₀), 5/(24w₀)]` and `[13/(24w₀), 11/(18w₀)]` here since `w₂ = 4w₀`)
    together with Lemma 4 and the orbit-divisibility Lemma 12. -/
theorem bhk_prop11_lemma13 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    : Found w ∨
      (5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) := by
  rw [or_iff_not_imp_right]
  intro hq
  push_neg at hq
  -- ## Step 0 — reduce to `q = 4`, `p = 1`, hence `w₂ = 4 w₀`.
  set w0 : ℕ := w ⟨0, by omega⟩ with hw0_def
  set w2 : ℕ := w ⟨2, by omega⟩ with hw2_def
  set g : ℕ := Nat.gcd w0 w2 with hg_def
  have hw0pos : 0 < w0 := hpos _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hw0pos
  have hgw0 : g ∣ w0 := by rw [hg_def]; exact Nat.gcd_dvd_left w0 w2
  have hgw2 : g ∣ w2 := by rw [hg_def]; exact Nat.gcd_dvd_right w0 w2
  obtain ⟨p, hp⟩ := hgw0
  obtain ⟨q, hqe⟩ := hgw2
  have hqval : w2 / g = q := by rw [hqe, Nat.mul_div_cancel_left _ hg0]
  rw [hqval] at hq
  have hppos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, mul_zero] at hp; omega
    · exact h
  have h3pq : 3 * p < q := by
    have key : g * (3 * p) < g * q := by
      have h := hsmall; rw [hp, hqe] at h
      calc g * (3 * p) = 3 * (g * p) := by ring
        _ < g * q := h
    exact Nat.lt_of_mul_lt_mul_left key
  have hq4 : q = 4 := by omega
  have hp1 : p = 1 := by omega
  have hgw0_eq : g = w0 := by rw [hp, hp1, mul_one]
  have hw2_eq : w2 = 4 * w0 := by rw [hqe, hq4, hgw0_eq]; ring
  -- ## Step 1 — real-valued setup and the explicit gap `I₂ = [a, b]`.
  have hw0R : (0 : ℝ) < (w0 : ℝ) := by exact_mod_cast hw0pos
  have hw1_eq : w ⟨1, by omega⟩ = 3 * w0 := by omega
  have hw1R : ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) := by rw [hw1_eq]; push_cast; ring
  have hw2R : ((w2 : ℕ) : ℝ) = 4 * (w0 : ℝ) := by exact_mod_cast hw2_eq
  set a : ℝ := 13 / (24 * (w0 : ℝ)) with ha_def
  set b : ℝ := 11 / (18 * (w0 : ℝ)) with hb_def
  have e0a : (w0 : ℝ) * a = 13 / 24 := by rw [ha_def]; field_simp
  have e0b : (w0 : ℝ) * b = 11 / 18 := by rw [hb_def]; field_simp
  have e1a : (3 * (w0 : ℝ)) * a = 13 / 8 := by rw [ha_def]; field_simp; ring
  have e1b : (3 * (w0 : ℝ)) * b = 11 / 6 := by rw [hb_def]; field_simp; ring
  have e2a : (4 * (w0 : ℝ)) * a = 13 / 6 := by rw [ha_def]; field_simp; ring
  have e2b : (4 * (w0 : ℝ)) * b = 22 / 9 := by rw [hb_def]; field_simp; ring
  have hab : a ≤ b := by
    have h : (w0 : ℝ) * a ≤ (w0 : ℝ) * b := by rw [e0a, e0b]; norm_num
    exact le_of_mul_le_mul_left h hw0R
  -- `I₂` is a 123-gap: runners 1, 2, 3 (Lean indices 0, 1, 2) stay `≥ 1/6`.
  have hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    fin_cases i
    · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
      exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [e0a]; norm_num)
        (by rw [e0b]; norm_num) hw0R.le s hs
    · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
      rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
      exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 1 (by rw [e1a]; norm_num)
        (by rw [e1b]; norm_num) (by positivity) s hs
    · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
      rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
      exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 2 (by rw [e2a]; norm_num)
        (by rw [e2b]; norm_num) (by positivity) s hs
  -- The gap is covered by runners 4 and 5.
  obtain hF | (hcov45 : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∪ unsafeOf w ⟨4, by omega⟩) :=
    bhk_prop11_gap_covered w hgap
  · exact hF
  -- ## Step 2 — BHK (35): `I₂ ⊄ B₄` and `I₂ ⊄ B₅`.
  -- If `[a,b] ⊆ unsafeOf i` then `block_containment` traps it in one block
  -- `m`; since `wᵢ > 4 w₀` the block index is `m ≥ 3`, which together with the
  -- span bound `wᵢ (b-a) < 1/3` is contradictory.
  have h35 : ∀ i : Fin 5, 4 * w0 < w i → ¬ Set.Icc a b ⊆ unsafeOf w i := by
    intro i hwi hsub
    have hwi0 : 0 < w i := by omega
    have hwiR : 4 * (w0 : ℝ) < (w i : ℝ) := by exact_mod_cast hwi
    obtain ⟨m, hm1, hm2⟩ := block_containment w i hwi0 a b hab hsub
    have hva : (w i : ℝ) * a = 13 / 24 * ((w i : ℝ) / (w0 : ℝ)) := by rw [ha_def]; ring
    have hvb : (w i : ℝ) * b = 11 / 18 * ((w i : ℝ) / (w0 : ℝ)) := by rw [hb_def]; ring
    set ρ : ℝ := (w i : ℝ) / (w0 : ℝ) with hρ
    have hρ4 : 4 < ρ := by rw [hρ, lt_div_iff₀ hw0R]; linarith
    rw [hva] at hm1; rw [hvb] at hm2
    have hm3 : (3 : ℤ) ≤ m := by
      by_contra h; push_neg at h
      have hm2' : (m : ℝ) ≤ 2 := by exact_mod_cast (by omega : m ≤ 2)
      linarith [hm2, hρ4, hm2']
    have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    linarith [hm1, hm2, hρ4, hm3R]
  have hw3gt : 4 * w0 < w ⟨3, by omega⟩ := by
    have h := hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega) :
      (⟨2, by omega⟩ : Fin 5) < ⟨3, by omega⟩); omega
  have hw4gt : 4 * w0 < w ⟨4, by omega⟩ := by
    have h := hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega) :
      (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩); omega
  have hn4 := h35 ⟨3, by omega⟩ hw3gt
  have hn5 := h35 ⟨4, by omega⟩ hw4gt
  -- ## Step 3 — Lemma 12 ⟹ `w₀ ∣ w₃` and `w₀ ∣ w₄` (`v₄ = r/4`, `v₅ = s/4`).
  have hd0 : w0 ∣ w ⟨0, by omega⟩ := ⟨1, by rw [mul_one]⟩
  have hd1 : w0 ∣ w ⟨1, by omega⟩ := ⟨3, by rw [hw1_eq]; ring⟩
  have hd2 : w0 ∣ w ⟨2, by omega⟩ := ⟨4, by rw [← hw2_def, hw2_eq]; ring⟩
  have hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩ := by
    rw [hgw0_eq]; intro i; fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
  rcases bhk_prop11_lemma12 w g hg0 hdvd012 hgap with hF | hc | hc | hc
  · exact hF
  · exact False.elim <| hn4 hc
  · exact False.elim <| hn5 hc
  · obtain ⟨hgw3, hgw4⟩ := hc
    rw [hgw0_eq] at hgw3 hgw4
    obtain ⟨r, hr⟩ := hgw3
    obtain ⟨s, hseq⟩ := hgw4
    have hrR : ((w ⟨3, by omega⟩ : ℕ) : ℝ) = (w0 : ℝ) * (r : ℝ) := by rw [hr]; push_cast; ring
    have hseqR : ((w ⟨4, by omega⟩ : ℕ) : ℝ) = (w0 : ℝ) * (s : ℝ) := by
      rw [hseq]; push_cast; ring
    -- ## Step 4 — bounds: `5 ≤ r ≤ 9`, `r < s`, and `6 ∣ r ∨ 6 ∣ s`.
    have hr5 : 5 ≤ r := by
      rcases Nat.lt_or_ge r 5 with h | h
      · exfalso
        have hmul : w0 * r ≤ w0 * 4 := Nat.mul_le_mul le_rfl (by omega)
        omega
      · exact h
    have hsr : r < s := by
      have h34 := hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega) :
        (⟨3, by omega⟩ : Fin 5) < ⟨4, by omega⟩)
      rw [hr, hseq] at h34
      exact Nat.lt_of_mul_lt_mul_left h34
    have hbaW : (w0 : ℝ) * (b - a) = 5 / 72 := by rw [mul_sub, e0b, e0a]; norm_num
    have hr9 : r ≤ 9 := by
      have hl4 := bhk_lemma_4 w hmono hpos a b hab hcov45
      rw [hrR] at hl4
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
      have hD : (0 : ℝ) < 3 * ((w0 : ℝ) * (r : ℝ)) := by positivity
      rw [lt_div_iff₀ hD] at hl4
      have hexp : (b - a) * (3 * ((w0 : ℝ) * (r : ℝ))) = 5 * (r : ℝ) / 24 := by
        have e : (b - a) * (3 * ((w0 : ℝ) * (r : ℝ)))
            = 3 * (r : ℝ) * ((w0 : ℝ) * (b - a)) := by ring
        rw [e, hbaW]; ring
      rw [hexp] at hl4
      have : (r : ℝ) < 10 := by linarith
      have : r < 10 := by exact_mod_cast this
      omega
    obtain hF | ⟨i, hi⟩ := found_or_blocked w (1 / (6 * (w0 : ℝ)))
    · exact hF
    have hobs : 6 ∣ r ∨ 6 ∣ s := by
      set t0 : ℝ := 1 / (6 * (w0 : ℝ)) with ht0
      have et1 : (w0 : ℝ) * t0 = 1 / 6 := by rw [ht0]; field_simp
      have et2 : 3 * (w0 : ℝ) * t0 = 1 / 2 := by rw [ht0]; field_simp; ring
      have et3 : 4 * (w0 : ℝ) * t0 = 2 / 3 := by rw [ht0]; field_simp; ring
      have p3 : (w ⟨3, by omega⟩ : ℝ) * t0 = (r : ℝ) / 6 := by
        rw [hrR, ht0]; field_simp
      have p4 : (w ⟨4, by omega⟩ : ℝ) * t0 = (s : ℝ) / 6 := by
        rw [hseqR, ht0]; field_simp
      have ht0mem : t0 ∈ Set.Icc t0 t0 := ⟨le_refl t0, le_refl t0⟩
      fin_cases i
      · exact absurd hi (not_lt.mpr (bhk_prop11_safe_on_Icc (w0 : ℝ) 0
          (by rw [et1]; norm_num) (by rw [et1]; norm_num) hw0R.le t0 ht0mem))
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
        exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0
          (by rw [et2]; norm_num) (by rw [et2]; norm_num) (by positivity) t0 ht0mem
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
        exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0
          (by rw [et3]; norm_num) (by rw [et3]; norm_num) (by positivity) t0 ht0mem
      · exact Or.inl (bhk_prop11_dvd_six_of_circDist (by rw [← p3]; exact hi))
      · exact Or.inr (bhk_prop11_dvd_six_of_circDist (by rw [← p4]; exact hi))
    -- ## Step 5 — casework on `r ∈ {5,…,9}`.
    interval_cases r
    · -- r = 5: the gap `[13/(24w₀), 17/(30w₀)]` (= `[13/6, 68/30]`) is a 1234-gap,
      -- bounding `s ≤ 13`; with `6 ∣ s` this gives `s ∈ {6, 12}`. For both, the
      -- explicit time `t = 13/(30 w₀)` (runner positions `{1,3,4,5,s}·13/30`) is
      -- lonely, which is the instant.
      set a5 : ℝ := 13 / (24 * (w0 : ℝ)) with ha5
      set b5 : ℝ := 17 / (30 * (w0 : ℝ)) with hb5
      have f0a : (w0 : ℝ) * a5 = 13 / 24 := by rw [ha5]; field_simp
      have f0b : (w0 : ℝ) * b5 = 17 / 30 := by rw [hb5]; field_simp
      have f1a : 3 * (w0 : ℝ) * a5 = 13 / 8 := by rw [ha5]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b5 = 17 / 10 := by rw [hb5]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a5 = 13 / 6 := by rw [ha5]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b5 = 34 / 15 := by rw [hb5]; field_simp; ring
      have f3a : 5 * (w0 : ℝ) * a5 = 65 / 24 := by rw [ha5]; field_simp; ring
      have f3b : 5 * (w0 : ℝ) * b5 = 17 / 6 := by rw [hb5]; field_simp; ring
      have hab5 : a5 ≤ b5 := by
        have h : (w0 : ℝ) * a5 ≤ (w0 : ℝ) * b5 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg5 : ∀ s ∈ Set.Icc a5 b5, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 1 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 2 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a5 b5, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 5 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (5 * (w0 : ℝ)) 2 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab5 hg5 h4safe
      · exact hF
      have hba5W : (w0 : ℝ) * (b5 - a5) = 1 / 40 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b5 - a5) = (s : ℝ) * ((w0 : ℝ) * (b5 - a5)) := by ring
      rw [hseqR, hc, hba5W] at hspan
      have hsR : (s : ℝ) < 14 := by linarith
      have hsle13 : s ≤ 13 := by
        have : s < 14 := by exact_mod_cast hsR
        omega
      have hs612 : s = 6 ∨ s = 12 := by omega
      -- The lonely time `t = 13/(30 w₀)`.
      set tW : ℝ := 13 / (30 * (w0 : ℝ)) with htW
      have gw0 : (w0 : ℝ) * tW = 13 / 30 := by rw [htW]; field_simp
      have gw1 : 3 * (w0 : ℝ) * tW = 13 / 10 := by rw [htW]; field_simp; ring
      have gw2 : 4 * (w0 : ℝ) * tW = 26 / 15 := by rw [htW]; field_simp; ring
      have gw3 : 5 * (w0 : ℝ) * tW = 13 / 6 := by rw [htW]; field_simp; ring
      have gw46 : 6 * (w0 : ℝ) * tW = 13 / 5 := by rw [htW]; field_simp; ring
      have gw412 : 12 * (w0 : ℝ) * tW = 26 / 5 := by rw [htW]; field_simp; ring
      have htWmem : tW ∈ Set.Icc tW tW := ⟨le_refl _, le_refl _⟩
      obtain hF | ⟨i, hi⟩ := found_or_blocked w tW
      · exact hF
      fin_cases i
      · exact absurd hi (not_lt.mpr (bhk_prop11_safe_on_Icc (w0 : ℝ) 0
          (by rw [gw0]; norm_num) (by rw [gw0]; norm_num) hw0R.le tW htWmem))
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
        exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 1 (by rw [gw1]; norm_num)
          (by rw [gw1]; norm_num) (by positivity) tW htWmem
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
        exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 1 (by rw [gw2]; norm_num)
          (by rw [gw2]; norm_num) (by positivity) tW htWmem
      · refine absurd hi (not_lt.mpr ?_)
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 5 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (5 * (w0 : ℝ)) 2 (by rw [gw3]; norm_num)
          (by rw [gw3]; norm_num) (by positivity) tW htWmem
      · refine absurd hi (not_lt.mpr ?_)
        rcases hs612 with rfl | rfl
        · rw [show ((w ⟨4, by omega⟩ : ℕ) : ℝ) = 6 * (w0 : ℝ) from by rw [hseqR]; push_cast; ring]
          exact bhk_prop11_safe_on_Icc (6 * (w0 : ℝ)) 2 (by rw [gw46]; norm_num)
            (by rw [gw46]; norm_num) (by positivity) tW htWmem
        · rw [show ((w ⟨4, by omega⟩ : ℕ) : ℝ) = 12 * (w0 : ℝ) from by rw [hseqR]; push_cast; ring]
          exact bhk_prop11_safe_on_Icc (12 * (w0 : ℝ)) 5 (by rw [gw412]; norm_num)
            (by rw [gw412]; norm_num) (by positivity) tW htWmem
    · -- r = 6: runner 4 = `6 w₀` is also safe on `I₂`, making it a 1234-gap.
      have h4safe : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 6 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        refine bhk_prop11_safe_on_Icc (6 * (w0 : ℝ)) 3 ?_ ?_ (by positivity) s hs
        · rw [show 6 * (w0 : ℝ) * a = 6 * ((w0 : ℝ) * a) from by ring, e0a]; norm_num
        · rw [show 6 * (w0 : ℝ) * b = 6 * ((w0 : ℝ) * b) from by ring, e0b]; norm_num
      obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab hgap h4safe
      · exact hF
      have hc : (w0 : ℝ) * (s : ℝ) * (b - a) = (s : ℝ) * ((w0 : ℝ) * (b - a)) := by ring
      rw [hseqR, hc, hbaW] at hspan
      have hsR : (s : ℝ) < 5 := by linarith
      have : s < 5 := by exact_mod_cast hsR
      omega
    · -- r = 7: `I₁ = [1/(6w₀), 5/(24w₀)]` is a 1234-gap (runner 4 = `7 w₀`).
      set a1 : ℝ := 1 / (6 * (w0 : ℝ)) with ha1
      set b1 : ℝ := 5 / (24 * (w0 : ℝ)) with hb1
      have f0a : (w0 : ℝ) * a1 = 1 / 6 := by rw [ha1]; field_simp
      have f0b : (w0 : ℝ) * b1 = 5 / 24 := by rw [hb1]; field_simp
      have f1a : 3 * (w0 : ℝ) * a1 = 1 / 2 := by rw [ha1]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b1 = 5 / 8 := by rw [hb1]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a1 = 2 / 3 := by rw [ha1]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b1 = 5 / 6 := by rw [hb1]; field_simp; ring
      have f3a : 7 * (w0 : ℝ) * a1 = 7 / 6 := by rw [ha1]; field_simp
      have f3b : 7 * (w0 : ℝ) * b1 = 35 / 24 := by rw [hb1]; field_simp; ring
      have hab1 : a1 ≤ b1 := by
        have h : (w0 : ℝ) * a1 ≤ (w0 : ℝ) * b1 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg1 : ∀ s ∈ Set.Icc a1 b1, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a1 b1, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 7 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (7 * (w0 : ℝ)) 1 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab1 hg1 h4safe
      · exact hF
      have hba1W : (w0 : ℝ) * (b1 - a1) = 1 / 24 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b1 - a1) = (s : ℝ) * ((w0 : ℝ) * (b1 - a1)) := by ring
      rw [hseqR, hc, hba1W] at hspan
      have : (s : ℝ) < 8 := by linarith
      have : s < 8 := by exact_mod_cast this
      omega
    · -- r = 8: as r = 7 but runner 4 = `8 w₀` (window `k = 1`).
      set a1 : ℝ := 1 / (6 * (w0 : ℝ)) with ha1
      set b1 : ℝ := 5 / (24 * (w0 : ℝ)) with hb1
      have f0a : (w0 : ℝ) * a1 = 1 / 6 := by rw [ha1]; field_simp
      have f0b : (w0 : ℝ) * b1 = 5 / 24 := by rw [hb1]; field_simp
      have f1a : 3 * (w0 : ℝ) * a1 = 1 / 2 := by rw [ha1]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b1 = 5 / 8 := by rw [hb1]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a1 = 2 / 3 := by rw [ha1]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b1 = 5 / 6 := by rw [hb1]; field_simp; ring
      have f3a : 8 * (w0 : ℝ) * a1 = 4 / 3 := by rw [ha1]; field_simp; ring
      have f3b : 8 * (w0 : ℝ) * b1 = 5 / 3 := by rw [hb1]; field_simp; ring
      have hab1 : a1 ≤ b1 := by
        have h : (w0 : ℝ) * a1 ≤ (w0 : ℝ) * b1 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg1 : ∀ s ∈ Set.Icc a1 b1, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a1 b1, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 8 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (8 * (w0 : ℝ)) 1 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab1 hg1 h4safe
      · exact hF
      have hba1W : (w0 : ℝ) * (b1 - a1) = 1 / 24 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b1 - a1) = (s : ℝ) * ((w0 : ℝ) * (b1 - a1)) := by ring
      rw [hseqR, hc, hba1W] at hspan
      have : (s : ℝ) < 8 := by linarith
      have : s < 8 := by exact_mod_cast this
      omega
    · -- r = 9: the gap `[1/(6w₀), 11/(54w₀)]` (= `[2/3, 44/54]`) is a 1234-gap.
      set a9 : ℝ := 1 / (6 * (w0 : ℝ)) with ha9
      set b9 : ℝ := 11 / (54 * (w0 : ℝ)) with hb9
      have f0a : (w0 : ℝ) * a9 = 1 / 6 := by rw [ha9]; field_simp
      have f0b : (w0 : ℝ) * b9 = 11 / 54 := by rw [hb9]; field_simp
      have f1a : 3 * (w0 : ℝ) * a9 = 1 / 2 := by rw [ha9]; field_simp; ring
      have f1b : 3 * (w0 : ℝ) * b9 = 11 / 18 := by rw [hb9]; field_simp; ring
      have f2a : 4 * (w0 : ℝ) * a9 = 2 / 3 := by rw [ha9]; field_simp; ring
      have f2b : 4 * (w0 : ℝ) * b9 = 22 / 27 := by rw [hb9]; field_simp; ring
      have f3a : 9 * (w0 : ℝ) * a9 = 3 / 2 := by rw [ha9]; field_simp; ring
      have f3b : 9 * (w0 : ℝ) * b9 = 11 / 6 := by rw [hb9]; field_simp; ring
      have hab9 : a9 ≤ b9 := by
        have h : (w0 : ℝ) * a9 ≤ (w0 : ℝ) * b9 := by rw [f0a, f0b]; norm_num
        exact le_of_mul_le_mul_left h hw0R
      have hg9 : ∀ s ∈ Set.Icc a9 b9, ∀ i : Fin 3,
          (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
        intro s hs i; fin_cases i
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s)
          exact bhk_prop11_safe_on_Icc (w0 : ℝ) 0 (by rw [f0a]; norm_num)
            (by rw [f0b]; norm_num) hw0R.le s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨1, by omega⟩ : ℕ) : ℝ) = 3 * (w0 : ℝ) from hw1R]
          exact bhk_prop11_safe_on_Icc (3 * (w0 : ℝ)) 0 (by rw [f1a]; norm_num)
            (by rw [f1b]; norm_num) (by positivity) s hs
        · change (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s)
          rw [show ((w ⟨2, by omega⟩ : ℕ) : ℝ) = 4 * (w0 : ℝ) from hw2R]
          exact bhk_prop11_safe_on_Icc (4 * (w0 : ℝ)) 0 (by rw [f2a]; norm_num)
            (by rw [f2b]; norm_num) (by positivity) s hs
      have h4safe : ∀ s ∈ Set.Icc a9 b9, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
        intro s hs
        rw [show ((w ⟨3, by omega⟩ : ℕ) : ℝ) = 9 * (w0 : ℝ) from by rw [hrR]; push_cast; ring]
        exact bhk_prop11_safe_on_Icc (9 * (w0 : ℝ)) 1 (by rw [f3a]; norm_num)
          (by rw [f3b]; norm_num) (by positivity) s hs
      obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab9 hg9 h4safe
      · exact hF
      have hba9W : (w0 : ℝ) * (b9 - a9) = 1 / 27 := by rw [mul_sub, f0b, f0a]; norm_num
      have hc : (w0 : ℝ) * (s : ℝ) * (b9 - a9) = (s : ℝ) * ((w0 : ℝ) * (b9 - a9)) := by ring
      rw [hseqR, hc, hba9W] at hspan
      have : (s : ℝ) < 9 := by linarith
      have : s < 9 := by exact_mod_cast this
      omega

/-- **Corollary 16, unconditional.** `v₄ < 2` (`w₃ < 2 w₂`), now that Lemma 13
    discharges the `q ≥ 5` side condition. -/
theorem bhk_prop11_v4_lt_2v3_uncond (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    : Found w ∨
      ((w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ)) := by
  rcases bhk_prop11_lemma13 w hmono hpos hsum hsmall with hF | hq5
  · exact Or.inl hF
  exact bhk_prop11_v4_lt_2v3 w hmono hpos hsum hsmall hq5

/-- **Lemma 17, unconditional.** `v₄ = r/q` and `v₅ = s/q` (`g ∣ w₃ ∧ g ∣ w₄`
    for `g = gcd(w₀,w₂)`), with the `q ≥ 5` side condition discharged by
    Lemma 13. This is the rational structure Part 3 feeds to the main lemma. -/
theorem bhk_prop11_lemma17_uncond (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    : Found w ∨
      (Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨3, by omega⟩ ∧
      Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨4, by omega⟩) := by
  rcases bhk_prop11_lemma13 w hmono hpos hsum hsmall with hF | hq5
  · exact Or.inl hF
  exact bhk_prop11_lemma17 w hmono hpos hsum hsmall hq5

/-- **BHK §5 Part 3 — Pentagon `P`: the long-gap contradiction engine.** Any
    1234-gap `[a, b]` (runners `w₀, w₁, w₂` safe via `hgap`, runner `w₃` via
    `h4safe`) of length `≥ 1/(3w₄) = x₅/3` contains the lonely instant:
    otherwise `bhk_prop11_gap1234_b5span` forces `w₄·(b−a) < 1/3`, while
    `1/(3w₄) ≤ b−a` gives `w₄·(b−a) ≥ 1/3`. Every gap-end sub-case (runner-3
    ends, runner-4 ends) terminates here once its gap length is bounded below. -/
lemma bhk_prop11_long_gap_absurd (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (a b : ℝ) (hab : a ≤ b)
    (hlen : 1 / (3 * (w ⟨4, by omega⟩ : ℝ)) ≤ b - a)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3, 1 / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h4safe : ∀ s ∈ Set.Icc a b, 1 / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s)) : Found w := by
  have hw4 : (0:ℝ) < (w ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab hgap h4safe
  · exact hF
  have hmul : (w ⟨4, by omega⟩ : ℝ) * (1 / (3 * (w ⟨4, by omega⟩ : ℝ)))
      ≤ (w ⟨4, by omega⟩ : ℝ) * (b - a) := mul_le_mul_of_nonneg_left hlen hw4.le
  have heq : (w ⟨4, by omega⟩ : ℝ) * (1 / (3 * (w ⟨4, by omega⟩ : ℝ))) = 1 / 3 := by field_simp
  rw [heq] at hmul
  linarith [hspan, hmul]

/-- **BHK §5 Part 3 — Pentagon `P` no-good-time, runner-3-ends sub-region.** No
    half-integer time `t` (`{w₂t} = 1/2`) satisfies the relaxed pentagon bounds
    (39),(40),(41) on runners 4,1,2 *and* `{w₃t} ≤ 5/6 − v₄/3`: such a `t` makes
    `[t + (1−x₅)/(3w₂), t + 1/(3w₂)]` a 1234-gap of length exactly `1/(3w₄)`,
    forcing `w₄·(b−a) < 1/3` by `bhk_prop11_gap1234_b5span` — but `w₄·(b−a) =
    1/3`. This is the runner-3-ends half of `C ∩ P = ∅`; the runner-4-ends half
    needs BHK's full (42) bound. The lower bounds (39)/(40) and upper (41) are
    the genuine pentagon expansion (they permit `{w₃t} < 1/6`, `{w₀t} < 1/6` and
    `{w₀t} > 1/3`), strengthening the rectangle `bhk_prop11_no_good_time`. -/
theorem bhk_prop11_no_good_time_P_r3 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i) (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h40 : 1 / 6 - (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h41 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
    (h39 : 1 / 6 - (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h42 : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)
            ≤ 5 / 6 - (w ⟨3, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))) : Found w := by
  have hw2 : (0:ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw4 : (0:ℝ) < (w ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hba : (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)))
        - (t + ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
        = 1 / (3 * (w ⟨4, by omega⟩ : ℝ)) := by
    field_simp
    ring
  have hab : t + ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
        / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
      ≤ t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
    have h0 : (0:ℝ) ≤ 1 / (3 * (w ⟨4, by omega⟩ : ℝ)) := by positivity
    linarith [hba]
  have hgap := bhk_prop11_pent_gap123 w hpos hmono hsum hsmall t h3 h40 h41
  have h4safe := bhk_prop11_pent_runner4_safe w hpos t h39 h42
  exact bhk_prop11_long_gap_absurd w hpos _ _ hab (le_of_eq hba.symm) hgap h4safe

set_option maxHeartbeats 800000 in
/-- **BHK §5 Part 3 — Pentagon `P` no-good-time, runner-4-ends sub-region.** The
    complementary half of `C ∩ P = ∅`: when runner 4 reaches `5/6` *before* runner
    3 (`hr4 : 5/6 − v₄/3 ≤ {w₃t}`), the 1234-gap ends at `b' = t + (5/6−{w₃t})/w₃`.
    Its start is the *latest* of the four reach-`1/6` times
    `τ₁,τ₂,τ₃,τ₄` (runners `w₀,w₁,w₂,w₃`); BHK's (42) — here split into the two
    consequences `h42a` (`b'−τ₁ ≥ x₅/3`) and `h42b` (`b'−τ₂ ≥ x₅/3`) — together
    with `b'−τ₃,b'−τ₄ ≥ x₅/3` (the latter `= 2/(3w₃)`, automatic from `w₃ < w₄`)
    make the gap `[a', b']` a 1234-gap of length `≥ 1/(3w₄)`, killed by
    `bhk_prop11_long_gap_absurd`. Using `a' = max(τ₁,τ₂,τ₃,τ₄)` and bounding each
    `b'−τᵢ` separately avoids BHK's three-way "who was last at `1/6`" split. -/
theorem bhk_prop11_no_good_time_P_r4 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i) (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h41 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
    (hxle : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) ≤ 5 / 6)
    (hr4 : 5 / 6 - (w ⟨3, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h42a : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) - 1 / 6) / (w ⟨0, by omega⟩ : ℝ))
    (h42b : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (1 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)) / (w ⟨1, by omega⟩ : ℝ)) : Found w := by
  have hw0 : (0:ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw1 : (0:ℝ) < (w ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0:ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3 : (0:ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw4 : (0:ℝ) < (w ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h12 : (w ⟨1, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega))
  have h23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega))
  have h34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3:ℕ) < 4 by omega))
  have hsmallR : 3 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall
  have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsum
  set w0 : ℝ := (w ⟨0, by omega⟩ : ℝ) with hw0d
  set w1 : ℝ := (w ⟨1, by omega⟩ : ℝ) with hw1d
  set w2 : ℝ := (w ⟨2, by omega⟩ : ℝ) with hw2d
  set w3 : ℝ := (w ⟨3, by omega⟩ : ℝ) with hw3d
  set w4 : ℝ := (w ⟨4, by omega⟩ : ℝ) with hw4d
  have h24 : w2 < w4 := lt_trans h23 h34
  have hw0' : w0 ≠ 0 := ne_of_gt hw0
  have hw1' : w1 ≠ 0 := ne_of_gt hw1
  have hw2' : w2 ≠ 0 := ne_of_gt hw2
  have hw3' : w3 ≠ 0 := ne_of_gt hw3
  set y : ℝ := Int.fract (w0 * t) with hyd
  set x : ℝ := Int.fract (w3 * t) with hxd
  have hf0 : (0:ℝ) ≤ y := Int.fract_nonneg _
  have hf0' : y < 1 := Int.fract_lt_one _
  have hslack : w1 * (w4 - w2) / (3 * w2 * w4) < 1 / 3 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right h12 (show (0:ℝ) < w4 - w2 by linarith), mul_pos hw2 hw2]
  have hy23 : y < 2 / 3 := by linarith [h41, hslack]
  have hsm0 : w0 / (3 * w2) < 1 / 9 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hsm1 : w1 / (3 * w2) < 1 / 3 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hsm2 : w2 / (3 * w2) = 1 / 3 := by field_simp
  have hbt : (5 / 6 - x) / w3 ≤ 1 / (3 * w2) := by
    rw [div_le_iff₀ hw3, show (1:ℝ) / (3 * w2) * w3 = w3 / (3 * w2) from by ring]; linarith [hr4]
  have hbtpos : (0:ℝ) ≤ (5 / 6 - x) / w3 := div_nonneg (by linarith [hxle]) hw3.le
  have key : ∀ v : ℝ, 0 ≤ v → v * ((5 / 6 - x) / w3) ≤ v / (3 * w2) := by
    intro v hv
    calc v * ((5 / 6 - x) / w3) ≤ v * (1 / (3 * w2)) := mul_le_mul_of_nonneg_left hbt hv
      _ = v / (3 * w2) := by ring
  have h1w : 1 / (3 * w4) ≤ 1 / (3 * w2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  set b' : ℝ := t + (5 / 6 - x) / w3 with hb'd
  have hb't : b' - t = (5 / 6 - x) / w3 := by rw [hb'd]; ring
  set a' : ℝ := max (t + (1 / 6 - y) / w0)
      (max (t + (y - 1 / 3) / w1) (max (t - 1 / (3 * w2)) (t + (1 / 6 - x) / w3))) with ha'd
  have hb1 : t + (1 / 6 - y) / w0 ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t + (1 / 6 - y) / w0) = (5 / 6 - x) / w3 + (y - 1 / 6) / w0 := by rw [hb'd]; ring
    linarith [h42a, e]
  have hb2 : t + (y - 1 / 3) / w1 ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t + (y - 1 / 3) / w1) = (5 / 6 - x) / w3 + (1 / 3 - y) / w1 := by rw [hb'd]; ring
    linarith [h42b, e]
  have hb3 : t - 1 / (3 * w2) ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t - 1 / (3 * w2)) = (5 / 6 - x) / w3 + 1 / (3 * w2) := by rw [hb'd]; ring
    linarith [hbtpos, h1w, e]
  have hb4 : t + (1 / 6 - x) / w3 ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t + (1 / 6 - x) / w3) = (2 / 3) / w3 := by rw [hb'd]; ring
    have h2w : 1 / (3 * w4) ≤ (2 / 3) / w3 := by
      rw [le_div_iff₀ hw3, show (1:ℝ) / (3 * w4) * w3 = w3 / (3 * w4) from by ring,
        div_le_iff₀ (show (0:ℝ) < 3 * w4 by positivity)]
      linarith
    linarith [h2w, e]
  have ha'le : a' ≤ b' - 1 / (3 * w4) := by
    rw [ha'd]; exact max_le hb1 (max_le hb2 (max_le hb3 hb4))
  have hlen : 1 / (3 * w4) ≤ b' - a' := by linarith [ha'le]
  have hab' : a' ≤ b' := by
    have h0 : (0:ℝ) < 1 / (3 * w4) := by positivity
    linarith [ha'le]
  have hτ1 : t + (1 / 6 - y) / w0 ≤ a' := by rw [ha'd]; exact le_max_left _ _
  have hτ2 : t + (y - 1 / 3) / w1 ≤ a' := by
    rw [ha'd]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hτ3 : t - 1 / (3 * w2) ≤ a' := by
    rw [ha'd]; exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hτ4 : t + (1 / 6 - x) / w3 ≤ a' := by
    rw [ha'd]; exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hw1cast : w1 = w2 - w0 := by linarith [hsumR]
  have hf1base : Int.fract (w1 * t) = Int.fract (1 / 2 - y) := by
    have h0 : w1 * t = ((⌊w2 * t⌋ - ⌊w0 * t⌋ : ℤ) : ℝ) + (1 / 2 - y) := by
      have e2 := Int.floor_add_fract (w2 * t)
      have e0 := Int.floor_add_fract (w0 * t)
      rw [h3] at e2
      rw [hw1cast, sub_mul, Int.cast_sub]; linarith [e2, e0]
    rw [h0, Int.fract_intCast_add]
  -- runner 1 (w₀): reaches 1/6 at τ₁, k = 0
  have safe0 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w0 * s) :=
    bhk_prop11_pent_reach_safe w0 t a' b' 0 (t + (1 / 6 - y) / w0) hw0.le hτ1
      (by have e : w0 * ((t + (1 / 6 - y) / w0) - t) = 1 / 6 - y := by
            rw [show (t + (1 / 6 - y) / w0) - t = (1 / 6 - y) / w0 from by ring]; field_simp
          rw [e]; push_cast; ring)
      (by rw [hb't]; push_cast; have hk := key w0 hw0.le; linarith [hk, hsm0, hy23])
  -- runner 3 (w₂): at 1/2, reached 1/6 at τ₃ = t − 1/(3w₂), k = 0
  have safe2 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w2 * s) :=
    bhk_prop11_pent_reach_safe w2 t a' b' 0 (t - 1 / (3 * w2)) hw2.le hτ3
      (by rw [h3]
          have e : w2 * ((t - 1 / (3 * w2)) - t) = -(1 / 3) := by
            rw [show (t - 1 / (3 * w2)) - t = -(1 / (3 * w2)) from by ring]; field_simp
          rw [e]; push_cast; ring)
      (by rw [h3, hb't]; push_cast; have hk := key w2 hw2.le; rw [hsm2] at hk; linarith [hk])
  -- runner 4 (w₃): at x, reaches 1/6 at τ₄, reaches 5/6 at b', k = 0
  have safe3 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w3 * s) :=
    bhk_prop11_pent_reach_safe w3 t a' b' 0 (t + (1 / 6 - x) / w3) hw3.le hτ4
      (by have e : w3 * ((t + (1 / 6 - x) / w3) - t) = 1 / 6 - x := by
            rw [show (t + (1 / 6 - x) / w3) - t = (1 / 6 - x) / w3 from by ring]; field_simp
          rw [e]; push_cast; ring)
      (by rw [hb't]
          have e : w3 * ((5 / 6 - x) / w3) = 5 / 6 - x := by field_simp
          rw [e]; push_cast; linarith)
  -- runner 2 (w₁): position frac(1/2 − y); k = 0 if y ≤ 1/2, k = 1 (wrap) otherwise
  have safe1 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w1 * s) := by
    by_cases hle : y ≤ 1 / 2
    · have hf1 : Int.fract (w1 * t) = 1 / 2 - y := by
        rw [hf1base]; exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      exact bhk_prop11_pent_reach_safe w1 t a' b' 0 (t + (y - 1 / 3) / w1) hw1.le hτ2
        (by rw [hf1]
            have e : w1 * ((t + (y - 1 / 3) / w1) - t) = y - 1 / 3 := by
              rw [show (t + (y - 1 / 3) / w1) - t = (y - 1 / 3) / w1 from by ring]; field_simp
            rw [e]; push_cast; ring)
        (by rw [hf1, hb't]; push_cast; have hk := key w1 hw1.le; linarith [hk, hsm1, hf0])
    · have hgt : 1 / 2 < y := not_le.mp hle
      have hf1 : Int.fract (w1 * t) = 3 / 2 - y := by
        rw [hf1base, show (1:ℝ) / 2 - y = ((-1 : ℤ) : ℝ) + (3 / 2 - y) from by push_cast; ring,
          Int.fract_intCast_add]
        exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      exact bhk_prop11_pent_reach_safe w1 t a' b' 1 (t + (y - 1 / 3) / w1) hw1.le hτ2
        (by rw [hf1]
            have e : w1 * ((t + (y - 1 / 3) / w1) - t) = y - 1 / 3 := by
              rw [show (t + (y - 1 / 3) / w1) - t = (y - 1 / 3) / w1 from by ring]; field_simp
            rw [e]; push_cast; ring)
        (by rw [hf1, hb't]; push_cast; have hk := key w1 hw1.le; linarith [hk, hsm1, hgt])
  have hgap : ∀ s ∈ Set.Icc a' b', ∀ i : Fin 3, 1 / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    fin_cases i
    · exact safe0 s hs
    · exact safe1 s hs
    · exact safe2 s hs
  exact bhk_prop11_long_gap_absurd w hpos a' b' hab' hlen hgap safe3

/-- **BHK §5 Part 3 — Pentagon `P` no-good-time (`C ∩ P = ∅`).** Combines the two
    gap-end sub-cases: no half-integer time `t` (`{w₂t} = 1/2`) satisfies the
    pentagon lower bounds (39) (`h39`), (40) (`h40`), the upper bound (41)
    (`h41`), the bound `{w₃t} ≤ 5/6` (`hxle`), and (42) — supplied as its two
    consequences `h42a`, `h42b` (`b'−τ₁, b'−τ₂ ≥ x₅/3`). Dispatches on whether
    runner 3 or runner 4 reaches `5/6` first (`{w₃t} ≶ 5/6 − v₄/3`) to the
    `_r3` / `_r4` halves. This is the full pentagon strengthening of the
    rectangle `bhk_prop11_no_good_time`. -/
theorem bhk_prop11_no_good_time_P (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i) (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h39 : 1 / 6 - (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h40 : 1 / 6 - (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h41 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
    (hxle : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) ≤ 5 / 6)
    (h42a : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) - 1 / 6) / (w ⟨0, by omega⟩ : ℝ))
    (h42b : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (1 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)) / (w ⟨1, by omega⟩ : ℝ)) : Found w := by
  by_cases hx : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)
      ≤ 5 / 6 - (w ⟨3, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))
  · exact bhk_prop11_no_good_time_P_r3 w hmono hpos hsum hsmall t h3 h40 h41 h39 hx
  · exact bhk_prop11_no_good_time_P_r4 w hmono hpos hsum hsmall t h3 h41 hxle
      (le_of_lt (not_le.mp hx)) h42a h42b

/-- **Pentagon avoidance in reduced coordinates (`C ∩ P = ∅`).** Transports
    `bhk_prop11_no_good_time_P` to the coset coordinates: at no half-integer index
    `l` does the C-point `(X,Y) = ({v₄(l+½)}, {v₁(l+½)}) = (fract(r/q(l+½)),
    fract(p/q(l+½)))` lie in the pentagon `P` (the six conditions h39/h40/h41/hxle/
    h42a/h42b, correction terms kept in `w`-form since `w₁`/`w₄` need no reduction).
    This is the pentagon analog of the `h_nogood` fact built in `core_q18`; the
    Case 5.2.3 / `(1,±2)` kills exhibit an `l` *in* `P`, contradicting it. -/
theorem bhk_prop11_pent_no_good (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r : ℕ) (hgpos : 0 < g) (hqpos : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) : Found w ∨
      (∀ l : ℤ, ¬ (
      1 / 6 - (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
        ≤ Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∧
      1 / 6 - (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
        ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∧
      Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))
        ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) ∧
      Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ 5 / 6 ∧
      1 / (3 * (w ⟨4, by omega⟩ : ℝ))
        ≤ (5 / 6 - Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))) / (w ⟨3, by omega⟩ : ℝ)
          + (Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) - 1 / 6) / (w ⟨0, by omega⟩ : ℝ) ∧
      1 / (3 * (w ⟨4, by omega⟩ : ℝ))
        ≤ (5 / 6 - Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))) / (w ⟨3, by omega⟩ : ℝ)
          + (1 / 3 - Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))) / (w ⟨1, by omega⟩ : ℝ))) := by
  rw [or_iff_not_imp_right]
  intro hQ
  obtain ⟨l, hl⟩ := not_forall_not.mp hQ
  obtain ⟨h39, h40, h41, hxle, h42a, h42b⟩ := hl
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  set t : ℝ := ((l : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; exact mul_ne_zero hgR hqR
  have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (l : ℝ) + 1 / 2 := by rw [htdef]; field_simp
  have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by
    rw [htdef, c0, c2]; field_simp
  have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by
    rw [htdef, c3, c2]; field_simp
  refine bhk_prop11_no_good_time_P w hmono hpos hsum hsmall t ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  · rw [e3]; exact h39
  · rw [e0]; exact h40
  · rw [e0]; exact h41
  · rw [e3]; exact hxle
  · rw [e3, e0]; exact h42a
  · rw [e3, e0]; exact h42b

/-- **BHK §5 Part 3 — the no-good-time fact (eq. (36)–(37)).** Under the
    covering assumption, there is *no* half-integer time `t` (`{w₂ t} = 1/2`)
    with runner 1 in `[1/6, 1/3]` *and* runner 4 in `[1/6, 1/2]`. Such a `t`
    would extend the `123`-gap `[t, t + 1/(3w₂)]` to a `1234`-gap
    `[t, t + 1/(3w₃)]` (runner 4 stays within `[1/6, 5/6]` across it), which
    runner 5 cannot cover (`bhk_prop11_gap1234_b5span` would force `w₄ < w₃`).
    Equivalently: the set `S = {({v₄(l+½)}, {v₁(l+½)})}` avoids the `1/3 × 1/6`
    rectangle `R`, the hypothesis of the main-lemma application. -/
theorem bhk_prop11_no_good_time (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ≤ 1 / 3)
    (h4lo : 1 / 6 ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h4hi : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) ≤ 1 / 2) : Found w := by
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3pos : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega))
  have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
  have hgap2 := bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi
  set b3 : ℝ := t + 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) with hb3
  have hab3 : t ≤ b3 := by rw [hb3]; exact le_add_of_nonneg_right (by positivity)
  have hlen_le : 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  -- The `123`-gap restricted to the shorter interval.
  have hgap_sub : ∀ s ∈ Set.Icc t b3, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    exact hgap2 s ⟨hs.1, by rw [hb3] at hs; linarith [hs.2]⟩ i
  -- Runner 4 stays safe across `[t, b3]`.
  have h4safe : ∀ s ∈ Set.Icc t b3, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
    intro s hs
    have hd0 : 0 ≤ s - t := by linarith [hs.1]
    have hdu : (w ⟨3, by omega⟩ : ℝ) * (s - t) ≤ 1 / 3 := by
      have h1 : (w ⟨3, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨3, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left (by rw [hb3] at hs; linarith [hs.2]) hw3pos.le
      have h2 : (w ⟨3, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) = 1 / 3 := by
        field_simp
      linarith [h1, h2]
    have hbnn : 0 ≤ (w ⟨3, by omega⟩ : ℝ) * (s - t) := mul_nonneg hw3pos.le hd0
    have hfs : Int.fract ((w ⟨3, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) + (w ⟨3, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨3, by omega⟩ : ℝ) * s
            = (w ⟨3, by omega⟩ : ℝ) * t + (w ⟨3, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by linarith) (by linarith)]
    simp only [circDist]; rw [hfs]; exact le_min (by linarith) (by linarith)
  obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab3 hgap_sub h4safe
  · exact hF
  rw [hb3, add_sub_cancel_left, mul_one_div, div_lt_iff₀ (by positivity)] at hspan
  -- hspan : w₄ < 1/3 * (3 * w₃) = w₃, contradicting w₃ < w₄.
  nlinarith [hspan, hw34]

/-- **BHK §5 Part 3 — the exceptional pair (`q ≥ 18` branch).** Wiring the
    no-good-time fact into the main-lemma application. Writing `g = gcd(w₀,w₂)`,
    `p = w₀/g`, `q = w₂/g`, `r = w₃/g`, `s = w₄/g` (Lemma 17 gives `g ∣ w₃, w₄`),
    the set `S = {({v₄(l+½)}, {v₁(l+½)})}` avoids the `1/3 × 1/6` rectangle `R`,
    so `bhk_corollary_6` (its hypothesis `αβ = 1/18 ≥ 1/q` holding iff `q ≥ 18`)
    yields a nonzero *exceptional generator pair* `(i,j)` in the cone
    `0 ≤ i < 6`, `|j| < 3 + i/2`. Parts 4–6 then rule out every such pair. -/
theorem bhk_prop11_exceptional_q18 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq18 : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found w ∨
      (∃ g p q r s : ℕ, 0 < g ∧
      w ⟨0, by omega⟩ = g * p ∧ w ⟨2, by omega⟩ = g * q ∧
      w ⟨3, by omega⟩ = g * r ∧ w ⟨4, by omega⟩ = g * s ∧
      Nat.gcd p q = 1 ∧ 18 ≤ q ∧
      ∃ ij : ℤ × ℤ, ij ≠ (0, 0) ∧
        (∃ k : ℤ, Int.fract ((ij.1 : ℝ) / q) = Int.fract ((k : ℝ) * r / q) ∧
                  Int.fract ((ij.2 : ℝ) / q) = Int.fract ((k : ℝ) * p / q)) ∧
        0 ≤ ij.1 ∧ (ij.1 : ℝ) < 6 ∧
        -3 - 1 / 2 * (ij.1 : ℝ) < (ij.2 : ℝ) ∧ (ij.2 : ℝ) < 3 + 1 / 2 * (ij.1 : ℝ) ∧
        (ij.1 ≠ 0 → ij.2 ≠ 0 → (ij.1.natAbs + 1) * (ij.2.natAbs + 1) - 2 ≤ q)) := by
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgw0 : g ∣ w ⟨0, by omega⟩ := Nat.gcd_dvd_left _ _
  have hgw2 : g ∣ w ⟨2, by omega⟩ := Nat.gcd_dvd_right _ _
  obtain hF | ⟨hgw3, hgw4⟩ := bhk_prop11_lemma17_uncond w hmono hpos hsum hsmall
  · exact Or.inl hF
  set p : ℕ := w ⟨0, by omega⟩ / g with hpdef
  set q : ℕ := w ⟨2, by omega⟩ / g with hqdef
  set r : ℕ := w ⟨3, by omega⟩ / g with hrdef
  set s : ℕ := w ⟨4, by omega⟩ / g with hsdef
  have hp : w ⟨0, by omega⟩ = g * p := (Nat.mul_div_cancel' hgw0).symm
  have hq : w ⟨2, by omega⟩ = g * q := (Nat.mul_div_cancel' hgw2).symm
  have hr : w ⟨3, by omega⟩ = g * r := (Nat.mul_div_cancel' hgw3).symm
  have hs : w ⟨4, by omega⟩ = g * s := (Nat.mul_div_cancel' hgw4).symm
  have hcop : Nat.gcd p q = 1 := Nat.coprime_div_gcd_div_gcd hg_pos
  have hqpos : 0 < q := by omega
  -- Cast helpers.
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hqne : (q : ℝ) ≠ 0 := hqR.ne'
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * (p : ℝ) := by exact_mod_cast hp
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hq
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * (r : ℝ) := by exact_mod_cast hr
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
  -- The no-good-time fact transported to `(r/q, p/q)` ratios.
  obtain hF | h_nogood : Found w ∨ (∀ k : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((k : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((k : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) := by
    rw [or_iff_not_imp_right]
    intro hQ
    obtain ⟨k, hk⟩ := not_forall_not.mp hQ
    obtain ⟨hrmem, hpmem⟩ := hk
    set t : ℝ := ((k : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
    have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (k : ℝ) + 1 / 2 := by
      rw [htdef]; field_simp
    have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((k : ℝ) + 1 / 2) := by
      rw [htdef, c0, c2]; field_simp
    have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((k : ℝ) + 1 / 2) := by
      rw [htdef, c3, c2]; field_simp
    refine bhk_prop11_no_good_time w hmono hpos hsum hsmall t ?_ ?_ ?_ ?_ ?_
    · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    · rw [e0]; exact hpmem.1
    · rw [e0]; exact hpmem.2
    · rw [e3]; exact hrmem.1
    · rw [e3]; exact hrmem.2
  · exact Or.inl hF
  right
  obtain ⟨_G, _hGlift, ij, hne, hmem, h0, h1β, hc1, hc2, _hmin, h14⟩ :=
    bhk_part3_exceptional_minimal_bound r p q (by omega) hcop h_nogood
  exact ⟨g, p, q, r, s, hg_pos, hp, hq, hr, hs, hcop, by omega, ij, hne, hmem, h0, h1β, hc1, hc2,
    h14⟩

set_option maxHeartbeats 800000 in
/-- **BHK §5 Case 5.2.11 — `(1, 2)U` pentagon kill, non-special branch `s ≥ q + 3`.**
    Under rigidity `2r = 2q + p` the cone points `({r(l+½)/q}, {p(l+½)/q})` lie on the
    line `Y = {2X}`, which (as `gcd(r,q) = 1`) is an `1/q`-spaced grid in `X`. For
    `s ≥ q+3` the horizontal segment `l = (line) ∩ P` has length `(s−q)/(2s) ≥ 1/q`,
    so the grid lands a point in `P`, contradicting `bhk_prop11_pent_no_good`
    (`C ∩ P = ∅`). Here `g·p, g·q, g·r, g·s` are `w₀, w₂, w₃, w₄`. -/
lemma bhk_prop11_exc_1_2_pentkill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hrig : 2 * r = 2 * q + p) (hs3 : q + 3 ≤ s) : Found w := by
  obtain hF | hpent := bhk_prop11_pent_no_good w hmono hpos hsum hsmall g p q r hg hq c0 c2 c3
  · exact hF
  -- positivity facts on the reduced reals
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hpq : (p : ℝ) < q := by exact_mod_cast (show p < q by omega)
  have hsq : (q : ℝ) < s := by exact_mod_cast (show q < s by omega)
  have hg0 : (g : ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
  have hrr : (p : ℝ) = 2 * r - 2 * q := by
    have h : (2 : ℝ) * r = 2 * q + p := by exact_mod_cast hrig
    linarith
  -- gcd(r,q) = 1: any common divisor divides 2q + p = 2r, hence p (coprime to q)
  have hcop_rq : Nat.Coprime r q := by
    have h1 : Nat.gcd r q ∣ r := Nat.gcd_dvd_left r q
    have h2 : Nat.gcd r q ∣ q := Nat.gcd_dvd_right r q
    have h2q : Nat.gcd r q ∣ 2 * q := h2.mul_left 2
    have h2r : Nat.gcd r q ∣ 2 * q + p := by rw [← hrig]; exact h1.mul_left 2
    have hd : Nat.gcd r q ∣ p := (Nat.dvd_add_right h2q).mp h2r
    have hg1 : Nat.gcd r q ∣ 1 := hcop ▸ Nat.dvd_gcd hd (Nat.gcd_dvd_right r q)
    exact Nat.dvd_one.mp hg1
  -- the shared pentagon margin factor M = (s - q)/(3 q s)
  set M : ℝ := ((s : ℝ) - q) / (3 * (q : ℝ) * (s : ℝ)) with hM
  have hMpos : 0 < M := by
    rw [hM]; exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hqR) hsR)
  -- the three margins of `pent_no_good` in reduced form
  have hmw3 : (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (r : ℝ) * M := by
    rw [c2, c3, c4, hM]; field_simp
  have hmw0 : (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (p : ℝ) * M := by
    rw [c0, c2, c4, hM]; field_simp
  have hmw1 : (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = ((q : ℝ) - p) * M := by
    have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - p) := by
      have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
        exact_mod_cast hsum
      have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by
        linarith
      rw [hs1, c0, c2]; ring
    rw [c1, c2, c4, hM]; field_simp
  -- window endpoint and feasibility (s ≥ q+3 ⟹ length ≥ 1/q)
  set Xv : ℝ := 1 / 6 + ((q : ℝ) - p) * M / 2 with hXv
  have hwin : 1 / (q : ℝ) ≤ ((q : ℝ) - p) * M / 2 + (r : ℝ) * M := by
    have hkey : ((q : ℝ) - p) * M / 2 + (r : ℝ) * M = ((s : ℝ) - q) / (2 * s) := by
      rw [hrr, hM]; field_simp; ring
    rw [hkey, div_le_div_iff₀ hqR (by linarith [hsR])]
    have hq18R : (18 : ℝ) ≤ q := by exact_mod_cast hq18
    have hs3R : (q : ℝ) + 3 ≤ s := by exact_mod_cast hs3
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (s:ℝ) - (q + 3) by linarith)
      (show (0:ℝ) ≤ (q:ℝ) - 2 by linarith)]
  have hE1_lt : ((q : ℝ) - p) * M < 1 / 3 := by
    have hlt : ((q : ℝ) - p) * M < (q : ℝ) * M := mul_lt_mul_of_pos_right (by linarith) hMpos
    have hqM : (q : ℝ) * M = ((s : ℝ) - q) / (3 * s) := by rw [hM]; field_simp
    rw [hqM] at hlt
    have hfrac : ((s : ℝ) - q) / (3 * s) < 1 / 3 := by
      rw [div_lt_div_iff₀ (by linarith [hsR]) (by norm_num)]; linarith [hqR]
    linarith
  have hE0_nn : 0 ≤ (p : ℝ) * M := mul_nonneg (by positivity) hMpos.le
  have hE1_nn : 0 ≤ ((q : ℝ) - p) * M := mul_nonneg (by linarith) hMpos.le
  -- place a grid point in the X-window [Xv - 1/q, Xv]
  obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq r hcop_rq
    ((r : ℝ) / (2 * q)) (Xv - 1 / q) (1 / q) (le_refl _)
    (by
      have hq18R : (18 : ℝ) ≤ q := by exact_mod_cast hq18
      have hq118 : 1 / (q : ℝ) ≤ 1 / 18 := by
        rw [div_le_div_iff₀ hqR (by norm_num)]; linarith
      rw [hXv]; linarith [hE1_nn])
    (by rw [hXv]; linarith [hE1_lt])
  have harg : (r : ℝ) / (2 * q) + (l : ℝ) * (r : ℝ) / (q : ℝ)
      = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
  rw [harg] at hl
  set X : ℝ := Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) with hXdef
  have hX_lo : Xv - 1 / q ≤ X := hl.1
  have hX_hi : X ≤ Xv := by have := hl.2; linarith
  have hXlt12 : X < 1 / 2 := by have h := hX_hi; rw [hXv] at h; linarith [hE1_lt]
  -- Y = {2X}: from p = 2r - 2q, the second coordinate folds onto twice the first
  set Y : ℝ := Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) with hYdef
  have hXnn : 0 ≤ X := by rw [hXdef]; exact Int.fract_nonneg _
  have hYeq : Y = 2 * X := by
    have hYarg : (p : ℝ) / q * ((l : ℝ) + 1 / 2)
        = 2 * ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) - ((2 * l + 1 : ℤ) : ℝ) := by
      rw [hrr]; push_cast; field_simp
    rw [hYdef, hYarg, Int.fract_sub_intCast]
    have hsplit : 2 * ((r : ℝ) / q * ((l : ℝ) + 1 / 2))
        = ((2 * ⌊(r : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ : ℤ) : ℝ) + 2 * X := by
      have hfa := Int.floor_add_fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))
      rw [hXdef]; push_cast; linarith [hfa]
    rw [hsplit, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith [hXnn], by linarith [hXlt12]⟩
  -- shared bounds for the six pentagon conditions
  have hr0 : (r : ℝ) ≠ 0 := hrR.ne'
  have hp0 : (p : ℝ) ≠ 0 := hpR0.ne'
  have hqp : (0 : ℝ) < (q : ℝ) - p := by linarith [hpq]
  have hqp0 : ((q : ℝ) - p) ≠ 0 := hqp.ne'
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - p) := by
    have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast hsum
    have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
    rw [hs1, c0, c2]; ring
  have hq118 : 1 / (q : ℝ) ≤ 1 / 18 := by
    rw [div_le_div_iff₀ hqR (by norm_num)]
    have : (18 : ℝ) ≤ q := by exact_mod_cast hq18
    linarith
  have hq6 : 2 / (q : ℝ) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ hqR (by norm_num)]
    have : (18 : ℝ) ≤ q := by exact_mod_cast hq18
    linarith
  have hsumM : ((q : ℝ) - p) * M + (p : ℝ) * M = (q : ℝ) * M := by ring
  have hrsR : (r : ℝ) < s := by exact_mod_cast hrs
  have hr3qR : 2 * (r : ℝ) < 3 * q := by exact_mod_cast hr32
  have hX13 : X < 1 / 3 := by linarith [hX_hi, hXv, hE1_lt]
  have hX112 : (1 : ℝ) / 12 < X := by linarith [hX_lo, hXv, hE1_nn, hq118]
  have ht1 : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by linarith [hsR]) hrR]
    nlinarith [hrsR, hsR, mul_pos (show (0:ℝ) < 1 / 3 - X by linarith [hX13]) hsR]
  have htq : 1 / (3 * (q : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by linarith [hqR]) hrR]
    nlinarith [hr3qR, hqR, mul_pos (show (0:ℝ) < 1 / 3 - X by linarith [hX13]) hqR]
  have hMq : 1 / (3 * (s : ℝ)) + M = 1 / (3 * (q : ℝ)) := by rw [hM]; field_simp; ring
  have key5 : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r + (2 * X - 1 / 6) / p := by
    have ht2 : 0 ≤ (2 * X - 1 / 6) / p := div_nonneg (by linarith [hX112]) hpR0.le
    linarith [ht1, ht2]
  have key6 : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r + (1 / 3 - 2 * X) / ((q : ℝ) - p) := by
    rcases le_total (2 * X) (1 / 3) with hc | hc
    · have ht2 : 0 ≤ (1 / 3 - 2 * X) / ((q : ℝ) - p) := div_nonneg (by linarith) hqp.le
      linarith [ht1, ht2]
    · have hub : 2 * X - 1 / 3 ≤ ((q : ℝ) - p) * M := by linarith [hX_hi, hXv]
      have hle : (2 * X - 1 / 3) / ((q : ℝ) - p) ≤ M := by
        rw [div_le_iff₀ hqp]; linarith [hub, mul_comm ((q : ℝ) - p) M]
      have hterm : -M ≤ (1 / 3 - 2 * X) / ((q : ℝ) - p) := by
        rw [show (1 : ℝ) / 3 - 2 * X = -(2 * X - 1 / 3) by ring, neg_div]; linarith [hle]
      linarith [htq, hterm, hMq]
  have e5 : (5 / 6 - X) / ((g : ℝ) * r) + (2 * X - 1 / 6) / ((g : ℝ) * p)
      = (1 / (g : ℝ)) * ((5 / 6 - X) / r + (2 * X - 1 / 6) / p) := by field_simp
  have e6 : (5 / 6 - X) / ((g : ℝ) * r) + (1 / 3 - 2 * X) / ((g : ℝ) * ((q : ℝ) - p))
      = (1 / (g : ℝ)) * ((5 / 6 - X) / r + (1 / 3 - 2 * X) / ((q : ℝ) - p)) := by field_simp
  have egs : (1 : ℝ) / (3 * ((g : ℝ) * s)) = (1 / (g : ℝ)) * (1 / (3 * s)) := by field_simp
  -- discharge the six pentagon conditions
  refine False.elim <| hpent l ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmw3, ← hXdef]; linarith [hX_lo, hwin, hXv]
  · rw [hmw0, ← hYdef, hYeq]
    linarith [hX_lo, hXv, hsumM, mul_pos hqR hMpos, hq6]
  · rw [hmw1, ← hYdef, hYeq]; linarith [hX_hi, hXv]
  · rw [← hXdef]; linarith [hX_hi, hXv, hE1_lt]
  · rw [← hXdef, ← hYdef, hYeq, c4, c3, c0, e5, egs]
    exact mul_le_mul_of_nonneg_left key5 (by positivity)
  · rw [← hXdef, ← hYdef, hYeq, c4, c3, c1, e6, egs]
    exact mul_le_mul_of_nonneg_left key6 (by positivity)

/-- **BHK §5 Case 5.2.11 — `(1, 2)U` special case `p = 2` (`s = q + 2`, `r = q + 1`).**
    Here the horizontal pigeonhole fails (`H = 1/(q+2) < 1/q`); BHK's direct witness
    applies instead. With speeds `2, q−2, q, q+1, q+2` (times `g`), pick an odd `m` with
    `1/6 ≤ m/q ≤ 1/3` (exists for `q ≥ 9`) and set `t = m/(2qg)`; then every
    `circDist(wᵢ t) ≥ 1/6` (a `012345`-gap), which is the instant. -/
lemma bhk_prop11_exc_1_2_special (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (g q : ℕ) (hg : 0 < g) (hq9 : 9 ≤ q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * 2)
    (c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - 2))
    (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 1))
    (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 2)) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hg0 : (g : ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  -- an odd `m` with `1/6 ≤ m/q ≤ 1/3`
  obtain ⟨m, hmodd, hm6, hm3⟩ : ∃ m : ℕ, Odd m ∧ q ≤ 6 * m ∧ 3 * m ≤ q := by
    rcases Nat.even_or_odd (q / 6 + 1) with ⟨k, hk⟩ | ho
    · exact ⟨q / 6 + 2, ⟨k, by omega⟩, by omega, by omega⟩
    · exact ⟨q / 6 + 1, ho, by omega, by omega⟩
  obtain ⟨j, hj⟩ := hmodd
  have hmjR : (m : ℝ) = 2 * (j : ℝ) + 1 := by exact_mod_cast hj
  have hm6R : (q : ℝ) ≤ 6 * m := by exact_mod_cast hm6
  have hm3R : 3 * (m : ℝ) ≤ q := by exact_mod_cast hm3
  have hmq_lo : (1 : ℝ) / 6 ≤ (m : ℝ) / q := by rw [le_div_iff₀ hqR]; linarith
  have hmq_hi : (m : ℝ) / q ≤ 1 / 3 := by rw [div_le_iff₀ hqR]; linarith
  set t : ℝ := (m : ℝ) / (2 * q * g) with htdef
  -- fract in [1/6,5/6] ⟹ circDist ≥ 1/6, after stripping the integer part `n`
  have key : ∀ (W y : ℝ) (n : ℤ), W = (n : ℝ) + y → 1 / 6 ≤ y → y ≤ 5 / 6 →
      1 / 6 ≤ circDist W := by
    intro W y n hW hlo hhi
    have hyfr : Int.fract y = y := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hWeq : W = y + (n : ℝ) := by rw [hW]; ring
    rw [hWeq, bhk_prop11_circDist_add_int]
    unfold circDist; rw [le_min_iff, hyfr]; exact ⟨hlo, by linarith⟩
  -- the five runner positions at `t`
  have e0 : (w ⟨0, by omega⟩ : ℝ) * t = ((0 : ℤ) : ℝ) + (m : ℝ) / q := by
    rw [c0, htdef]; push_cast; field_simp; ring
  have e1 : (w ⟨1, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + (1 / 2 - (m : ℝ) / q) := by
    rw [c1, htdef, hmjR]; push_cast; field_simp; ring
  have e2 : (w ⟨2, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + 1 / 2 := by
    rw [c2, htdef, hmjR]; push_cast; field_simp
  have e3 : (w ⟨3, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + (1 / 2 + (m : ℝ) / q / 2) := by
    rw [c3, htdef, hmjR]; push_cast; field_simp; ring
  have e4 : (w ⟨4, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + (1 / 2 + (m : ℝ) / q) := by
    rw [c4, htdef, hmjR]; push_cast; field_simp; ring
  obtain hF | ⟨i, hi⟩ := found_or_blocked w t
  · exact hF
  refine absurd hi (not_lt.mpr ?_)
  fin_cases i
  · exact key _ _ 0 e0 hmq_lo (by linarith [hmq_hi])
  · exact key _ _ (j : ℤ) e1 (by linarith [hmq_hi]) (by linarith [hmq_lo])
  · exact key _ _ (j : ℤ) e2 (by norm_num) (by norm_num)
  · exact key _ _ (j : ℤ) e3 (by linarith [hmq_lo]) (by linarith [hmq_hi])
  · exact key _ _ (j : ℤ) e4 (by linarith [hmq_lo]) (by linarith [hmq_hi])

/-- **BHK §5 Case 5.2.11 — `(1, 2)U` dispatcher.** Splits on `s`: the special
    `s = q + 2` (forcing `r = q + 1`, `p = 2`; `bhk_prop11_exc_1_2_special`) versus the
    generic `s ≥ q + 3` horizontal pigeonhole (`bhk_prop11_exc_1_2_pentkill`). -/
lemma bhk_prop11_exc_1_2_kill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hrig : 2 * r = 2 * q + p) : Found w := by
  rcases Nat.lt_or_ge s (q + 3) with hs2 | hs3
  · -- special branch: s = q + 2 forces r = q + 1, p = 2
    have hsq2 : s = q + 2 := by omega
    have hr1 : r = q + 1 := by omega
    have hp2 : p = 2 := by omega
    have c0' : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * 2 := by rw [c0, hp2]; push_cast; ring
    have c1' : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - 2) := by
      have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
        exact_mod_cast hsum
      have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by
        linarith
      rw [hs1, c0, c2, hp2]; push_cast; ring
    have c3' : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 1) := by rw [c3, hr1]; push_cast; ring
    have c4' : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 2) := by rw [c4, hsq2]; push_cast; ring
    exact bhk_prop11_exc_1_2_special w hpos g q hg (by omega) c0' c1' c2 c3' c4'
  · -- generic branch: s ≥ q + 3
    exact bhk_prop11_exc_1_2_pentkill w hmono hpos hsum hsmall g p q r s hg hq
      c0 c2 c3 c4 hcop hp h3p hrq hr32 hrs hq18 hrig (by omega)

/-- **`pent_no_good` in reduced coordinates.** The six pentagon conditions written in terms of
    `p, q, r, s` (with `w₀=g·p, w₂=g·q, w₃=g·r, w₄=g·s`, margin `M=(s-q)/(3qs)`), bridged to
    the `w`-form of `bhk_prop11_pent_no_good` (the slants `×1/g`). -/
lemma bhk_prop11_pent_no_good_red (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hpqlt : p < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (l : ℤ)
    (h39 : 1/6 - (r:ℝ)*(((s:ℝ)-q)/(3*q*s)) ≤ Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)))
    (h40 : 1/6 - (p:ℝ)*(((s:ℝ)-q)/(3*q*s)) ≤ Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)))
    (h41 : Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)) ≤ 1/3 + ((q:ℝ)-p)*(((s:ℝ)-q)/(3*q*s)))
    (hxle : Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)) ≤ 5/6)
    (h42a : 1/(3*(s:ℝ)) ≤ (5/6 - Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)))/r
        + (Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)) - 1/6)/p)
    (h42b : 1/(3*(s:ℝ)) ≤ (5/6 - Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)))/r
        + (1/3 - Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)))/((q:ℝ)-p)) : Found w := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hpR0 : (0:ℝ) < p := by exact_mod_cast hp
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  have hg0 : (g:ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q:ℝ) ≠ 0 := hqR.ne'
  have hs0 : (s:ℝ) ≠ 0 := hsR.ne'
  have hr0 : (r:ℝ) ≠ 0 := hrR.ne'
  have hp0 : (p:ℝ) ≠ 0 := hpR0.ne'
  have hpqR : (p:ℝ) < q := by exact_mod_cast hpqlt
  have hqp : (0:ℝ) < (q:ℝ) - p := by linarith
  set X : ℝ := Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)) with hXdef
  set Y : ℝ := Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)) with hYdef
  have hmw3 : (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (r:ℝ)*(((s:ℝ)-q)/(3*q*s)) := by
    rw [c2, c3, c4]; field_simp
  have hmw0 : (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (p:ℝ)*(((s:ℝ)-q)/(3*q*s)) := by
    rw [c0, c2, c4]; field_simp
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g:ℝ) * ((q:ℝ) - p) := by
    have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast hsum
    have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
    rw [hs1, c0, c2]; ring
  have hmw1 : (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = ((q:ℝ)-p)*(((s:ℝ)-q)/(3*q*s)) := by
    rw [c1, c2, c4]; field_simp
  have e5 : (5/6 - X)/((g:ℝ)*r) + (Y - 1/6)/((g:ℝ)*p)
      = (1/(g:ℝ)) * ((5/6 - X)/r + (Y - 1/6)/p) := by field_simp
  have e6 : (5/6 - X)/((g:ℝ)*r) + (1/3 - Y)/((g:ℝ)*((q:ℝ)-p))
      = (1/(g:ℝ)) * ((5/6 - X)/r + (1/3 - Y)/((q:ℝ)-p)) := by field_simp
  have egs : (1:ℝ)/(3*((g:ℝ)*s)) = (1/(g:ℝ)) * (1/(3*s)) := by field_simp
  rcases bhk_prop11_pent_no_good w hmono hpos hsum hsmall g p q r hg hq c0 c2 c3 with hF | hpent
  · exact hF
  refine False.elim <| hpent l
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmw3]; exact h39
  · rw [hmw0]; exact h40
  · rw [hmw1]; exact h41
  · exact hxle
  · rw [c4, c3, c0, e5, egs]; exact mul_le_mul_of_nonneg_left h42a (by positivity)
  · rw [c4, c3, c1, e6, egs]; exact mul_le_mul_of_nonneg_left h42b (by positivity)

set_option maxHeartbeats 800000 in
/-- **`(2,1)/(4,2)` pentagon six-condition discharge.** Given a grid index `l` whose
    `p`-coordinate `Y = {p/q(l+½)}` lies in `[1/4, 5/12)` with `Y ≥ 1/3 − rM/2` (h39, passed
    folded as `h39Y`) and `Y ≤ 1/3 + (q−p)M` (h41), the cone point `({r/q(l+½)}, Y)` lies in
    the pentagon `P`: rigidity `r = 2p+q` folds `X = {r/q(l+½)} = {2Y+½} = 2Y − 1/2`, and the
    remaining four conditions (`h40`, `hxle`, `h42a`, `h42b`) follow from `X < 1/3` and
    `Y ≥ 1/4`. Contradicts `bhk_prop11_pent_no_good_red`. -/
lemma bhk_prop11_pent_six_from_Y (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hpqlt : p < q) (hr32 : 2 * r < 3 * q) (hrs : r < s)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hrig : r = 2 * p + q) (l : ℤ)
    (hYlo : 1 / 4 ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)))
    (hYhi : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) < 5 / 12)
    (h39Y : 1 / 6 - (r : ℝ) * (((s : ℝ) - q) / (3 * q * s))
        ≤ 2 * Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) - 1 / 2)
    (h41 : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))
        ≤ 1 / 3 + ((q : ℝ) - p) * (((s : ℝ) - q) / (3 * q * s))) : Found w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpqlt
  have hqp : (0 : ℝ) < (q : ℝ) - p := by linarith
  have hp0 : (p : ℝ) ≠ 0 := hpR0.ne'
  have hrigR : (r : ℝ) = 2 * (p : ℝ) + q := by exact_mod_cast hrig
  have hrsR : (r : ℝ) < s := by exact_mod_cast hrs
  have hr32R : 2 * (r : ℝ) < 3 * q := by exact_mod_cast hr32
  set Y : ℝ := Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) with hYdef
  set X : ℝ := Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) with hXdef
  -- fold X = 2Y − 1/2 (rigidity r = 2p+q ⟹ r/q(l+½) = 2·(p/q(l+½)) + (l+½))
  have hXeq : X = 2 * Y - 1 / 2 := by
    have hXarg : (r : ℝ) / q * ((l : ℝ) + 1 / 2)
        = 2 * ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) + ((l : ℤ) : ℝ) + 1 / 2 := by
      rw [hrigR]; push_cast; field_simp; ring
    rw [hXdef, hXarg]
    have hfa := Int.floor_add_fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))
    have hsplit : 2 * ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) + ((l : ℤ) : ℝ) + 1 / 2
        = ((2 * ⌊(p : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ + l + 1 : ℤ) : ℝ) + (2 * Y - 1 / 2) := by
      rw [hYdef] at *; push_cast; linarith [hfa]
    rw [hsplit, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith [hYlo], by linarith [hYhi]⟩
  have hX13 : X < 1 / 3 := by rw [hXeq]; linarith [hYhi]
  have hsq : (q : ℝ) < s := by linarith [hrsR, hrigR, hpR0]
  have hEpos : 0 < ((s : ℝ) - q) / (3 * q * s) := div_pos (by linarith [hsq]) (by positivity)
  have ht1 : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by positivity) hrR]
    nlinarith [hrsR, hsR, mul_pos (show (0 : ℝ) < 1 / 3 - X by linarith [hX13]) hsR]
  have htq : 1 / (3 * (q : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by positivity) hrR]
    nlinarith [hr32R, hqR, mul_pos (show (0 : ℝ) < 1 / 3 - X by linarith [hX13]) hqR]
  have hMq : 1 / (3 * (s : ℝ)) + ((s : ℝ) - q) / (3 * q * s) = 1 / (3 * (q : ℝ)) := by
    field_simp; ring
  refine bhk_prop11_pent_no_good_red w hmono hpos hsum hsmall g p q r s hg hq hp hr hs
    hpqlt c0 c2 c3 c4 l ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hXdef, hXeq]; exact h39Y
  · rw [← hYdef]; nlinarith [hYlo, hEpos, mul_nonneg (le_of_lt hpR0) (le_of_lt hEpos)]
  · rw [← hYdef]; exact h41
  · rw [← hXdef, hXeq]; linarith [hYhi]
  · rw [← hXdef, ← hYdef]
    have h2 : 0 ≤ (Y - 1 / 6) / p := div_nonneg (by linarith [hYlo]) hpR0.le
    linarith [ht1, h2]
  · rw [← hXdef, ← hYdef]
    rcases le_total Y (1 / 3) with hc | hc
    · have h2 : 0 ≤ (1 / 3 - Y) / ((q : ℝ) - p) := div_nonneg (by linarith) hqp.le
      linarith [ht1, h2]
    · have hub : Y - 1 / 3 ≤ ((q : ℝ) - p) * (((s : ℝ) - q) / (3 * q * s)) := by linarith [h41]
      have hle : (Y - 1 / 3) / ((q : ℝ) - p) ≤ ((s : ℝ) - q) / (3 * q * s) := by
        rw [div_le_iff₀ hqp]; linarith [hub, mul_comm ((q : ℝ) - p) (((s : ℝ) - q) / (3 * q * s))]
      have hterm : -(((s : ℝ) - q) / (3 * q * s)) ≤ (1 / 3 - Y) / ((q : ℝ) - p) := by
        rw [show (1 : ℝ) / 3 - Y = -(Y - 1 / 3) by ring, neg_div]; linarith [hle]
      linarith [htq, hterm, hMq]

set_option maxHeartbeats 800000 in
/-- **BHK §5 `(2,1)` (and `(4,2)` c=2) pentagon kill.** Rigidity `r = 2p+q` puts the cone
    points `({r/q(l+½)}, {p/q(l+½)})` on the line `X = {2Y+½}` (a `1/q`-grid in `Y`, as
    `gcd(p,q)=1`). The pentagon segment splits into two regimes by `rM ⋛ 1/6`
    (`M = (s−q)/(3qs)`): for `rM ≤ 1/6` the window `[1/3−rM/2, +1/q]` (the box bottom h39
    to top h41, width `(s−q)/(2s) ≥ 1/q` since `s ≥ q+3`); for `rM > 1/6` the window
    `[1/4, +1/q]` (anchored at the X-branch cutoff). A grid `Y` in either window lands the
    cone point in `P` via `bhk_prop11_pent_six_from_Y`. -/
lemma bhk_prop11_exc_2_1_pentkill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hrig : r = 2 * p + q) : Found w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqlt : p < q := by omega
  have hs3 : q + 3 ≤ s := by omega
  have hq18R : (18 : ℝ) ≤ q := by exact_mod_cast hq18
  have h1q18 : 1 / (q : ℝ) ≤ 1 / 18 := by
    rw [div_le_div_iff₀ hqR (by norm_num)]; linarith
  have hrigR : (r : ℝ) = 2 * (p : ℝ) + q := by exact_mod_cast hrig
  have hsq : (q : ℝ) < s := by
    have hrsR : (r : ℝ) < s := by exact_mod_cast hrs
    linarith [hrsR, hrigR, hpR0]
  set M : ℝ := ((s : ℝ) - q) / (3 * q * s) with hM
  have hMpos : 0 < M := by
    rw [hM]; exact div_pos (by linarith [hsq]) (by positivity)
  have hwin : 1 / (q : ℝ) ≤ ((s : ℝ) - q) / (2 * s) := by
    rw [div_le_div_iff₀ hqR (by linarith [hsR])]
    have hs3R : (q : ℝ) + 3 ≤ s := by exact_mod_cast hs3
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (s : ℝ) - (q + 3) by linarith)
      (show (0 : ℝ) ≤ (q : ℝ) - 2 by linarith)]
  have hid : ((q : ℝ) - p) * M + (r : ℝ) * M / 2 = ((s : ℝ) - q) / (2 * s) := by
    rw [hM, hrigR]; field_simp; ring
  by_cases hreg : (r : ℝ) * M ≤ 1 / 6
  · -- regime A: window [1/3 − rM/2, +1/q]
    obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq p hcop
      ((p : ℝ) / (2 * q)) (1 / 3 - (r : ℝ) * M / 2) (1 / q) (le_refl _)
      (by linarith [hreg]) (by nlinarith [hMpos, hrR, h1q18])
    have harg : (p : ℝ) / (2 * q) + (l : ℝ) * (p : ℝ) / (q : ℝ)
        = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
    rw [harg] at hl
    have hY_lo : 1 / 3 - (r : ℝ) * M / 2 ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) := hl.1
    have hY_hi : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ 1 / 3 - (r : ℝ) * M / 2 + 1 / q := by
      have := hl.2; linarith
    exact bhk_prop11_pent_six_from_Y w hmono hpos hsum hsmall g p q r s hg hq hp
      (by omega) (by omega) hpqlt hr32 hrs c0 c2 c3 c4 hrig l
      (by linarith [hY_lo, hreg])
      (by linarith [hY_hi, mul_pos hrR hMpos, h1q18])
      (by rw [← hM]; linarith [hY_lo])
      (by rw [← hM]; linarith [hY_hi, hwin, hid])
  · -- regime B: window [1/4, +1/q]
    have hreg' : 1 / 6 < (r : ℝ) * M := not_le.mp hreg
    obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq p hcop
      ((p : ℝ) / (2 * q)) (1 / 4) (1 / q) (le_refl _)
      (by norm_num) (by linarith [h1q18])
    have harg : (p : ℝ) / (2 * q) + (l : ℝ) * (p : ℝ) / (q : ℝ)
        = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
    rw [harg] at hl
    have hY_lo : 1 / 4 ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) := hl.1
    have hY_hi : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ 1 / 4 + 1 / q := by
      have := hl.2; linarith
    exact bhk_prop11_pent_six_from_Y w hmono hpos hsum hsmall g p q r s hg hq hp
      (by omega) (by omega) hpqlt hr32 hrs c0 c2 c3 c4 hrig l
      hY_lo
      (by linarith [hY_hi, h1q18])
      (by rw [← hM]; linarith [hY_lo, hreg'])
      (by rw [← hM]; nlinarith [hY_hi, h1q18, hMpos, mul_nonneg (show (0:ℝ) ≤ (q:ℝ) - p by linarith [show (p:ℝ)<q from by exact_mod_cast hpqlt]) hMpos.le])

set_option maxHeartbeats 800000 in
/-- **`(4,2)` c=1 pentagon six-condition discharge (odd-`l` fold).** For the c=1 line
    `2r = 4p+q` (`r = 2p + q/2`), at an **odd** index `l = 2m+1` the cone point folds as
    `X = {r/q(l+½)} = {2Y + 3/4} = 2Y − 1/4` (valid for `1/8 ≤ Y < 7/24`). The three
    `M`-dependent `Y`-inequalities (h39c, h40c, h41c) are supplied; the slant conditions
    (h42a, h42b) and `hxle` are derived here from `Y ∈ [1/8, 7/24)`, `q < 4p` and `r < s`
    (slant h42a reduces to `s(9p−q)/4 + (3/2)qsY ≥ pr`, true as `9p > q` and `s > r`).
    Contradicts `bhk_prop11_pent_no_good_red`. -/
lemma bhk_prop11_pent_six_from_Y_c1 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hpqlt : p < q) (hq4p : q < 4 * p) (hrs : r < s)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hrig2 : 2 * r = 4 * p + q) (m : ℤ)
    (hYlo : 1 / 8 ≤ Int.fract ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)))
    (hYhi : Int.fract ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)) < 7 / 24)
    (h39c : 1 / 6 - (r : ℝ) * (((s : ℝ) - q) / (3 * q * s))
        ≤ 2 * Int.fract ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)) - 1 / 4)
    (h40c : 1 / 6 - (p : ℝ) * (((s : ℝ) - q) / (3 * q * s))
        ≤ Int.fract ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)))
    (h41c : Int.fract ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2))
        ≤ 1 / 3 + ((q : ℝ) - p) * (((s : ℝ) - q) / (3 * q * s))) : Found w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpqlt
  have hq4pR : (q : ℝ) < 4 * p := by exact_mod_cast hq4p
  have hrsR : (r : ℝ) < s := by exact_mod_cast hrs
  have hrig2R : 2 * (r : ℝ) = 4 * p + q := by exact_mod_cast hrig2
  set Y : ℝ := Int.fract ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)) with hYdef
  set X : ℝ := Int.fract ((r : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)) with hXdef
  -- fold X = 2Y − 1/4 (rigidity 2r = 4p+q, l odd ⟹ r/q(l+½) = 2·(p/q(l+½)) + m + 3/4)
  have hXeq : X = 2 * Y - 1 / 4 := by
    have hXarg : (r : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)
        = 2 * ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)) + (m : ℝ) + 3 / 4 := by
      rw [show (r : ℝ) = (4 * (p : ℝ) + q) / 2 from by linarith [hrig2R]]
      push_cast; field_simp; ring
    rw [hXdef, hXarg]
    have hfa := Int.floor_add_fract ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2))
    have hsplit : 2 * ((p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)) + (m : ℝ) + 3 / 4
        = ((2 * ⌊(p : ℝ) / q * (((2 * m + 1 : ℤ) : ℝ) + 1 / 2)⌋ + m + 1 : ℤ) : ℝ)
          + (2 * Y - 1 / 4) := by
      rw [hYdef] at *; push_cast at hfa ⊢; linarith [hfa]
    rw [hsplit, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith [hYlo], by linarith [hYhi]⟩
  have hX13 : X < 1 / 3 := by rw [hXeq]; linarith [hYhi]
  -- slant slack: 1/(3s) ≤ (5/6 − X)/r  (from X < 1/3 and r < s)
  have ht1 : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by positivity) hrR]
    nlinarith [hX13, hrsR, hsR, mul_pos (show (0 : ℝ) < 5 / 6 - X by linarith [hX13]) hsR]
  refine bhk_prop11_pent_no_good_red w hmono hpos hsum hsmall g p q r s hg hq hp hr hs
    hpqlt c0 c2 c3 c4 (2 * m + 1) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hXdef, hXeq]; exact h39c
  · rw [← hYdef]; exact h40c
  · rw [← hYdef]; exact h41c
  · rw [← hXdef, hXeq]; linarith [hYhi]
  · rw [← hXdef, ← hYdef]
    -- h42a : 1/(3s) ≤ (5/6 − X)/r + (Y − 1/6)/p ; clears to s(9p−q)/4 + (3/2)qsY ≥ pr
    have e : (5 / 6 - X) / r + (Y - 1 / 6) / p
        = ((5 / 6 - X) * p + (Y - 1 / 6) * r) / (r * p) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity), hXeq,
      show (r : ℝ) = (4 * (p : ℝ) + q) / 2 from by linarith [hrig2R]]
    nlinarith [mul_pos (show (0 : ℝ) < 2 * (s : ℝ) - (4 * p + q) by linarith [hrsR, hrig2R])
        (show (0 : ℝ) < 9 * (p : ℝ) - q by linarith [hq4pR]),
      mul_pos (show (0 : ℝ) < 5 * (p : ℝ) - q by linarith [hq4pR])
        (show (0 : ℝ) < 4 * (p : ℝ) + q by positivity),
      mul_nonneg (mul_nonneg hsR.le hqR.le) (show (0 : ℝ) ≤ Y by linarith [hYlo]),
      hsR.le, hpR0.le, hqR.le, hYlo]
  · rw [← hXdef, ← hYdef]
    -- h42b : easy — (1/3 − Y)/(q−p) ≥ 0 (Y < 7/24 < 1/3) and ht1
    have h2 : 0 ≤ (1 / 3 - Y) / ((q : ℝ) - p) :=
      div_nonneg (by linarith [hYhi]) (by linarith [hpqR])
    linarith [ht1, h2]

set_option maxHeartbeats 1600000 in
/-- **BHK §5 `(4,2)` c=1 pentagon kill.** The c=1 line `2r = 4p+q` (`q` even,
    `r = 2p + q/2`, `q/4 < p < q/3`) only arises in the five-runner `core_q18` (the
    six-runner `6p < q` rules it out). Cone points fold onto `X = {2Y − 1/4}` at **odd**
    `l = 2m+1`; `Y = {p/q(l+½)}` lives on a `2/q`-spaced grid (`gcd(2p,q)=2`, generator
    `p` mod `q' = q/2`). Two regimes by `rM ⋛ 1/6` (`M = (s−q)/(3qs)`): window
    `[5/24 − rM/2, +2/q]` (`rM ≤ 1/6`) or `[1/8, +2/q]` (`rM > 1/6`); width `2/q` fits the
    feasible window for `q ≥ 30`. A grid `Y` lands the cone point in `P` via
    `bhk_prop11_pent_six_from_Y_c1`. -/
lemma bhk_prop11_exc_4_2_c1_pentkill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq30 : 30 ≤ q) (hrig2 : 2 * r = 4 * p + q) : Found w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqlt : p < q := by omega
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpqlt
  have hrqR : (q : ℝ) < r := by exact_mod_cast hrq
  have hrsR : (r : ℝ) < s := by exact_mod_cast hrs
  have hqs : (q : ℝ) < s := by linarith [hrqR, hrsR]
  have hrig2R : 2 * (r : ℝ) = 4 * p + q := by exact_mod_cast hrig2
  have hq4p : q < 4 * p := by omega
  have hq4pR : (q : ℝ) < 4 * p := by exact_mod_cast hq4p
  have hr4pR : (r : ℝ) < 4 * p := by linarith [hrig2R, hq4pR]
  set M : ℝ := ((s : ℝ) - q) / (3 * q * s) with hM
  have hMpos : 0 < M := div_pos (by linarith [hqs]) (by positivity)
  have hrMnn : 0 ≤ (r : ℝ) * M := mul_nonneg hrR.le hMpos.le
  -- q' = q/2, the modulus of the odd-`l` grid (generator `p`, coprime to `q'`)
  obtain ⟨q', hq'⟩ : ∃ q', q = 2 * q' := ⟨r - 2 * p, by omega⟩
  have hq'pos : 0 < q' := by omega
  have hq'15 : 15 ≤ q' := by omega
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'pos
  have hqq'R : (q : ℝ) = 2 * (q' : ℝ) := by rw [hq']; push_cast; ring
  have hq'ne : (q' : ℝ) ≠ 0 := hq'R.ne'
  have hcop' : Nat.Coprime p q' := Nat.Coprime.coprime_dvd_right ⟨2, by omega⟩ hcop
  have h1q'15 : (1 : ℝ) / (q' : ℝ) ≤ 1 / 15 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hq'15)
  -- the grid connection: `{p/q(l+½)}` at `l = 2t+1` equals the coset value
  have harg : ∀ t : ℤ, (p : ℝ) / q * (((2 * t + 1 : ℤ) : ℝ) + 1 / 2)
      = (3 * (p : ℝ)) / (4 * (q' : ℝ)) + (t : ℝ) * (p : ℝ) / (q' : ℝ) := by
    intro t; rw [hqq'R]; push_cast; field_simp; ring
  -- `M`-identities: `pM = rM/2 − qM/4` (from `4p = 2r − q`) and `qM ≤ rM`
  have h4p_eq : (4 : ℝ) * p = 2 * r - q := by linarith [hrig2R]
  have hpM_eq : 4 * ((p : ℝ) * M) = 2 * ((r : ℝ) * M) - (q : ℝ) * M := by
    rw [show 4 * ((p : ℝ) * M) = ((4 : ℝ) * p) * M from by ring, h4p_eq]; ring
  have hqM_le : (q : ℝ) * M ≤ (r : ℝ) * M := mul_le_mul_of_nonneg_right hrqR.le hMpos.le
  have hqpMnn : 0 ≤ ((q : ℝ) - p) * M := mul_nonneg (by linarith [hpqR]) hMpos.le
  by_cases hreg : (r : ℝ) * M ≤ 1 / 6
  · -- regime A: window [5/24 − rM/2, +1/q']
    have hlo_pos : (0 : ℝ) ≤ 5 / 24 - (r : ℝ) * M / 2 := by linarith [hreg]
    obtain ⟨t, ht⟩ := bhk_prop11_grid_hit_coset_step q' hq'pos p hcop'
      ((3 * (p : ℝ)) / (4 * (q' : ℝ))) (5 / 24 - (r : ℝ) * M / 2) (1 / (q' : ℝ)) (le_refl _)
      hlo_pos (by linarith [hrMnn, h1q'15])
    rw [← harg t, Set.mem_Icc] at ht
    have hY_lo : 5 / 24 - (r : ℝ) * M / 2
        ≤ Int.fract ((p : ℝ) / q * (((2 * t + 1 : ℤ) : ℝ) + 1 / 2)) := ht.1
    have hY_hi : Int.fract ((p : ℝ) / q * (((2 * t + 1 : ℤ) : ℝ) + 1 / 2))
        ≤ 5 / 24 - (r : ℝ) * M / 2 + 1 / (q' : ℝ) := ht.2
    exact bhk_prop11_pent_six_from_Y_c1 w hmono hpos hsum hsmall g p q r s hg hq hp
      (by omega) (by omega) hpqlt hq4p hrs c0 c2 c3 c4 hrig2 t
      (by linarith [hY_lo, hreg])
      (by linarith [hY_hi, hrMnn, h1q'15])
      (by rw [← hM]; linarith [hY_lo])
      (by rw [← hM]; linarith [hY_lo, hpM_eq, hqM_le, hreg])
      (by rw [← hM]; linarith [hY_hi, hqpMnn, hrMnn, h1q'15])
  · -- regime B: window [1/8, +1/q']
    have hreg' : 1 / 6 < (r : ℝ) * M := not_le.mp hreg
    have hrM_lt_4pM : (r : ℝ) * M < 4 * ((p : ℝ) * M) := by
      have h := mul_lt_mul_of_pos_right hr4pR hMpos
      rw [show (4 * (p : ℝ)) * M = 4 * ((p : ℝ) * M) from by ring] at h; exact h
    obtain ⟨t, ht⟩ := bhk_prop11_grid_hit_coset_step q' hq'pos p hcop'
      ((3 * (p : ℝ)) / (4 * (q' : ℝ))) (1 / 8) (1 / (q' : ℝ)) (le_refl _)
      (by norm_num) (by linarith [h1q'15])
    rw [← harg t, Set.mem_Icc] at ht
    have hY_lo : (1 : ℝ) / 8 ≤ Int.fract ((p : ℝ) / q * (((2 * t + 1 : ℤ) : ℝ) + 1 / 2)) := ht.1
    have hY_hi : Int.fract ((p : ℝ) / q * (((2 * t + 1 : ℤ) : ℝ) + 1 / 2))
        ≤ 1 / 8 + 1 / (q' : ℝ) := ht.2
    exact bhk_prop11_pent_six_from_Y_c1 w hmono hpos hsum hsmall g p q r s hg hq hp
      (by omega) (by omega) hpqlt hq4p hrs c0 c2 c3 c4 hrig2 t
      hY_lo
      (by linarith [hY_hi, h1q'15])
      (by rw [← hM]; linarith [hY_lo, hreg'])
      (by rw [← hM]; linarith [hY_lo, hrM_lt_4pM, hreg'])
      (by rw [← hM]; linarith [hY_hi, hqpMnn, h1q'15])

set_option maxHeartbeats 400000 in
/-- **Reusable P-witness kill (`q < 18`, `s`-free).** A witness index `m` whose
    explicit C-coordinates `(X, Y)` lie in the pentagon `P` for *every* valid
    runner-5 speed `s > r` contradicts `bhk_prop11_pent_no_good_red`. The pentagon
    conditions depend on `s` through the margin `(s-q)/(3qs)` and the slant slack
    `1/(3s)`, both monotone in `s`, so it suffices to verify them at the worst case
    `s = r+1`: the six hypotheses `h39w…h42bw` are `s`-free rational inequalities
    closed by `norm_num` for a concrete triple. Handles the 33 P-killable
    Table-4/6/8 small-`q` cases. -/
lemma bhk_prop11_exc_Pkill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s m : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hpqlt : p < q)
    (hrq : q < r) (hrs : r < s)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (h39w : 1 / 6 - (r : ℝ) * (((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1)))
        ≤ (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ))
    (h40w : 1 / 6 - (p : ℝ) * (((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1)))
        ≤ (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ))
    (h41w : (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)
        ≤ 1 / 3 + ((q : ℝ) - p) * (((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1))))
    (hxlew : (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) ≤ 5 / 6)
    (h42aw : 1 / (3 * ((r : ℝ) + 1))
        ≤ (5 / 6 - (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)) / r
          + ((((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) - 1 / 6) / p)
    (h42bw : 1 / (3 * ((r : ℝ) + 1))
        ≤ (5 / 6 - (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)) / r
          + (1 / 3 - (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)) / ((q : ℝ) - p)) : Found w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hr1R : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hrsR : (r : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast (by omega : r + 1 ≤ s)
  have hqpR : (0 : ℝ) ≤ (q : ℝ) - p := by
    have : (p : ℝ) < q := by exact_mod_cast hpqlt
    linarith
  -- the two monotonicity facts (margin and slant slack are worst at s = r+1)
  have hcorr : ((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1)) ≤ ((s : ℝ) - q) / (3 * q * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hqR.le hqR.le) (show (0 : ℝ) ≤ (s : ℝ) - ((r : ℝ) + 1) from by linarith)]
  have hrecip : 1 / (3 * (s : ℝ)) ≤ 1 / (3 * ((r : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  -- rewrite the C-coordinates to explicit rationals
  have hXrw : Int.fract ((r : ℝ) / q * (((m : ℤ) : ℝ) + 1 / 2))
      = (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) := by
    rw [show ((m : ℤ) : ℝ) = ((m : ℕ) : ℝ) from by push_cast; ring,
        bhk_prop11_Cpoint_eval r q m hq]
  have hYrw : Int.fract ((p : ℝ) / q * (((m : ℤ) : ℝ) + 1 / 2))
      = (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) := by
    rw [show ((m : ℤ) : ℝ) = ((m : ℕ) : ℝ) from by push_cast; ring,
        bhk_prop11_Cpoint_eval p q m hq]
  refine bhk_prop11_pent_no_good_red w hmono hpos hsum hsmall g p q r s hg hq hp hr0 hs0
    hpqlt c0 c2 c3 c4 (m : ℤ) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hXrw]; nlinarith [h39w, mul_le_mul_of_nonneg_left hcorr hrR.le]
  · rw [hYrw]
    have hp0R : (0 : ℝ) ≤ (p : ℝ) := by positivity
    nlinarith [h40w, mul_le_mul_of_nonneg_left hcorr hp0R]
  · rw [hYrw]; nlinarith [h41w, mul_le_mul_of_nonneg_left hcorr hqpR]
  · rw [hXrw]; exact hxlew
  · rw [hXrw, hYrw]; linarith [h42aw, hrecip]
  · rw [hXrw, hYrw]; linarith [h42bw, hrecip]

-- grid-witness on a slant-bound window: large rational-arithmetic proof
set_option maxHeartbeats 3200000 in
/-- **BHK §5 Case 5.2.9 — `(1,-2)S` pentagon kill, wide window (`hwb : 36s ≤ r(5s-4r)`).**
    Rigidity `2r+p=3q` puts the cone points on the line `Y={3/2-2X}` (branch `X∈(1/4,3/4)`), a
    `1/q`-grid in `X`. The two *slants* of `P` bind (not the box); their linear-in-`X` cuts `Xlo`
    (h42b) and `Xhi` (h42a) span width `r(5s-4r)/(36qs)`, which is `≥ 1/q` exactly when
    `5rs-4r²-36s ≥ 0` (the hypothesis `hwb`). A grid point in `[Xlo,Xhi] ⊆ P` contradicts
    `pent_no_good`. `hwb` holds whenever `q ≥ 25` (then `r≥34, s≥r+1`); the finite set of
    instances with `36s > r(5s-4r)` (`q∈{19,21,23}`) goes to `bhk_prop11_exc_1_neg2_small`. -/
lemma bhk_prop11_exc_1_neg2_pentkill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hwb : 36 * (s : ℝ) ≤ (r : ℝ) * (5 * s - 4 * r))
    (hrig : 2 * r + p = 3 * q) : Found w := by
  obtain hF | hpent := bhk_prop11_pent_no_good w hmono hpos hsum hsmall g p q r hg hq c0 c2 c3
  · exact hF
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpR0 : (0:ℝ) < p := by exact_mod_cast hp
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  have hpq : (p:ℝ) < q := by exact_mod_cast (show p < q by omega)
  have hsq : (q:ℝ) < s := by exact_mod_cast (show q < s by omega)
  have hg0 : (g:ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q:ℝ) ≠ 0 := hqR.ne'
  have hs0 : (s:ℝ) ≠ 0 := hsR.ne'
  have hr0 : (r:ℝ) ≠ 0 := hrR.ne'
  have hp0 : (p:ℝ) ≠ 0 := hpR0.ne'
  have hqp : (0:ℝ) < (q:ℝ) - p := by linarith [hpq]
  have hqp0 : ((q:ℝ) - p) ≠ 0 := hqp.ne'
  have hsr1R : (r:ℝ) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
  have hrrR : (p:ℝ) = 3 * q - 2 * r := by
    have h : (2:ℝ) * r + p = 3 * q := by exact_mod_cast hrig
    linarith
  have hqpR : (q:ℝ) - p = 2 * ((r:ℝ) - q) := by rw [hrrR]; ring
  have hrgtq : (q:ℝ) < r := by exact_mod_cast hrq
  -- gcd(r,q)=1
  have hcop_rq : Nat.Coprime r q := by
    have h1 : Nat.gcd r q ∣ r := Nat.gcd_dvd_left r q
    have h2 : Nat.gcd r q ∣ q := Nat.gcd_dvd_right r q
    have h2r : Nat.gcd r q ∣ 2 * r := h1.mul_left 2
    have h2rp : Nat.gcd r q ∣ 2 * r + p := by rw [hrig]; exact h2.mul_left 3
    have hd : Nat.gcd r q ∣ p := (Nat.dvd_add_right h2r).mp h2rp
    have hg1 : Nat.gcd r q ∣ 1 := hcop ▸ Nat.dvd_gcd hd (Nat.gcd_dvd_right r q)
    exact Nat.dvd_one.mp hg1
  -- pentagon box margin and slant-cut endpoints (roots of the slants with Y=3/2-2X)
  set M : ℝ := ((s:ℝ) - q) / (3 * (q:ℝ) * (s:ℝ)) with hM
  have hMpos : 0 < M := by
    rw [hM]; exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hqR) hsR)
  set Da : ℝ := 1/(r:ℝ) + 2/(p:ℝ) with hDa
  set Na : ℝ := 5/(6*(r:ℝ)) + 4/(3*(p:ℝ)) - 1/(3*(s:ℝ)) with hNa
  set Db : ℝ := 2/((q:ℝ)-p) - 1/(r:ℝ) with hDb
  set Nb : ℝ := 1/(3*(s:ℝ)) - 5/(6*(r:ℝ)) + 7/(6*((q:ℝ)-p)) with hNb
  have hDapos : 0 < Da := by rw [hDa]; exact add_pos (div_pos one_pos hrR) (div_pos (by norm_num) hpR0)
  have hDbpos : 0 < Db := by
    rw [hDb, sub_pos, div_lt_div_iff₀ hrR hqp]; rw [hqpR]; nlinarith [hrgtq, hrR]
  set Xhi : ℝ := Na / Da with hXhi
  set Xlo : ℝ := Nb / Db with hXlo
  -- the width simplifies to r(5s-4r)/(36 q s) (sympy-verified identity, uses p=3q-2r)
  -- collapse Xhi, Xlo to single fractions (pure identities), then use p+2r = 3q
  have hpp2r : (0:ℝ) < (p:ℝ) + 2*r := by linarith [hpR0, hrR]
  have h2rqp : (0:ℝ) < 2*(r:ℝ) - ((q:ℝ)-p) := by
    have h := hDbpos; rw [hDb, sub_pos, div_lt_div_iff₀ hrR hqp] at h; linarith [h]
  have hXhi_eq : Xhi = (5*(p:ℝ)*s + 8*r*s - 2*r*p) / (6*s*((p:ℝ)+2*r)) := by
    rw [hXhi, hNa, hDa]; field_simp; ring
  have hXlo_eq : Xlo = (2*(r:ℝ)*((q:ℝ)-p) - 5*s*((q:ℝ)-p) + 7*r*s) / (6*s*(2*(r:ℝ)-((q:ℝ)-p))) := by
    rw [hXlo, hNb, hDb]; field_simp; ring
  have hwidth : Xhi - Xlo = (r:ℝ) * (5*s - 4*r) / (36 * q * s) := by
    rw [hXhi_eq, hXlo_eq]
    have e1 : (p:ℝ) + 2*r = 3*q := by rw [hrrR]; ring
    have e2 : 2*(r:ℝ) - ((q:ℝ)-p) = 2*q := by rw [hrrR]; ring
    rw [e1, e2, hrrR]; field_simp; ring
  -- 1/q ≤ width  ⟺  5rs - 4r² - 36s ≥ 0  (the hypothesis `hwb`)
  have hw : 1 / (q:ℝ) ≤ Xhi - Xlo := by
    rw [hwidth, div_le_div_iff₀ hqR (by positivity)]
    nlinarith [hwb, hqR, hsR, hrR]
  -- 4r > 3q and p < 2r and 3r < 7q (regime), used for the endpoint locations
  have h4r3q : 3*(q:ℝ) < 4*r := by
    have : (8:ℝ)*q + 1 ≤ 6*r := by exact_mod_cast (show 8*q + 1 ≤ 6*r by omega)
    linarith
  have hp2r : (p:ℝ) < 2*r := by rw [hrrR]; linarith [h4r3q]
  have h3r7q : 3*(r:ℝ) < 7*q := by
    have : (2:ℝ)*r < 3*q := by exact_mod_cast hr32
    linarith
  -- endpoint location: 1/4 < Xlo ≤ Xhi < 3/4 (so X is on the Y=3/2-2X branch)
  have hXhi34 : Xhi < 3/4 := by
    have hid : (3:ℝ)/4 * Da - Na = 1/(3*s) - 1/(12*r) + 1/(6*p) := by
      rw [hNa, hDa]; field_simp; ring
    have hpos' : 0 < (3:ℝ)/4 * Da - Na := by
      rw [hid]
      have h1 : 1/(12*(r:ℝ)) < 1/(6*p) := by
        rw [div_lt_div_iff₀ (by linarith [hrR]) (by linarith [hpR0])]; nlinarith [hp2r]
      have h2 : (0:ℝ) < 1/(3*s) := by positivity
      linarith [h1, h2]
    rw [hXhi, div_lt_iff₀ hDapos]; linarith [hpos']
  have hXlo14 : 1/4 < Xlo := by
    have hid : Nb - (1:ℝ)/4 * Db = 1/(3*s) - 7/(12*r) + 2/(3*((q:ℝ)-p)) := by
      rw [hNb, hDb]; field_simp; ring
    have hpos' : 0 < Nb - (1:ℝ)/4 * Db := by
      rw [hid]
      have h1 : 7/(12*(r:ℝ)) < 2/(3*((q:ℝ)-p)) := by
        rw [div_lt_div_iff₀ (by linarith [hrR]) (by linarith [hqp]), hqpR]; nlinarith [h3r7q]
      have h2 : (0:ℝ) < 1/(3*s) := by positivity
      linarith [h1, h2]
    rw [hXlo, lt_div_iff₀ hDbpos]; linarith [hpos']
  have hXloXhi : Xlo ≤ Xhi := by linarith [hw, one_div_pos.mpr hqR]
  -- box bounds: the slant window [Xlo,Xhi] sits inside the box (factored numerators)
  have hbox_hi : Xhi ≤ 2/3 + (p:ℝ)*M/2 := by
    have hkey : (2:ℝ)/3 + (p:ℝ)*M/2 - Xhi = ((p:ℝ)*(2*s+2*r-3*q)) / (18*q*s) := by
      rw [hXhi_eq, hM, show (6:ℝ)*s*((p:ℝ)+2*r) = 18*q*s from by rw [hrrR]; ring, hrrR]
      field_simp; ring
    have hnn : 0 ≤ ((p:ℝ)*(2*s+2*r-3*q)) / (18*q*s) := by
      apply div_nonneg (mul_nonneg hpR0.le (by nlinarith [hsr1R, h4r3q])) (by positivity)
    linarith [hkey, hnn]
  have hbox_lo : 7/12 - ((q:ℝ)-p)*M/2 ≤ Xlo := by
    have hkey : Xlo - (7/12 - ((q:ℝ)-p)*M/2) = (((r:ℝ)-q)*(4*r-4*q+s)) / (12*q*s) := by
      rw [hXlo_eq, hM, show (6:ℝ)*s*(2*(r:ℝ)-((q:ℝ)-p)) = 12*q*s from by rw [hrrR]; ring, hrrR]
      field_simp; ring
    have hnn : 0 ≤ (((r:ℝ)-q)*(4*r-4*q+s)) / (12*q*s) := by
      apply div_nonneg (mul_nonneg (by linarith [hrgtq]) (by nlinarith [hrgtq, hsR])) (by positivity)
    linarith [hkey, hnn]
  -- the reduced pentagon margins
  have hmw3 : (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (r : ℝ) * M := by
    rw [c2, c3, c4, hM]; field_simp
  have hmw0 : (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (p : ℝ) * M := by
    rw [c0, c2, c4, hM]; field_simp
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - p) := by
    have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast hsum
    have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
    rw [hs1, c0, c2]; ring
  have hmw1 : (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = ((q : ℝ) - p) * M := by
    rw [c1, c2, c4, hM]; field_simp
  -- place a grid point in the slant window [Xlo, Xhi]
  obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq r hcop_rq
    ((r : ℝ) / (2 * q)) Xlo (Xhi - Xlo) hw (by linarith [hXlo14]) (by linarith [hXhi34])
  have harg : (r : ℝ) / (2 * q) + (l : ℝ) * (r : ℝ) / (q : ℝ)
      = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
  rw [harg] at hl
  set X : ℝ := Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) with hXdef
  have hX_lo : Xlo ≤ X := hl.1
  have hX_hi : X ≤ Xhi := by have h := hl.2; linarith
  have hX14 : 1/4 < X := lt_of_lt_of_le hXlo14 hX_lo
  have hX34 : X < 3/4 := lt_of_le_of_lt hX_hi hXhi34
  -- Y = {3/2 - 2X} on the branch X ∈ (1/4, 3/4)
  set Y : ℝ := Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) with hYdef
  have hYeq : Y = 3/2 - 2*X := by
    have hYarg : (p : ℝ) / q * ((l : ℝ) + 1 / 2)
        = ((3*l + 1 : ℤ) : ℝ) + (1/2 - 2*((r : ℝ) / q * ((l : ℝ) + 1 / 2))) := by
      rw [hrrR]; push_cast; field_simp; ring
    rw [hYdef, hYarg, Int.fract_intCast_add]
    have hsplit : (1:ℝ)/2 - 2*((r : ℝ) / q * ((l : ℝ) + 1 / 2))
        = ((-2*⌊(r : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ : ℤ) : ℝ) + (1/2 - 2*X) := by
      have hfa := Int.floor_add_fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))
      rw [hXdef]; push_cast; linarith [hfa]
    rw [hsplit, Int.fract_intCast_add,
        show (1:ℝ)/2 - 2*X = (3/2 - 2*X) + ((-1 : ℤ) : ℝ) from by push_cast; ring,
        Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith [hX34], by linarith [hX14]⟩
  -- reduced slant conditions, via Da·Xhi = Na (h42a) and Db·Xlo = Nb (h42b)
  have key_a : 1/(3*(s:ℝ)) ≤ (5/6 - X)/r + (Y - 1/6)/p := by
    rw [hYeq]
    have h2 : Da * Xhi = Na := by rw [hXhi]; field_simp [hDapos.ne']
    have h3 : Na - Da*X = (5/6 - X)/r + (3/2 - 2*X - 1/6)/p - 1/(3*s) := by rw [hNa, hDa]; ring
    nlinarith [mul_le_mul_of_nonneg_left hX_hi hDapos.le, h2, h3]
  have key_b : 1/(3*(s:ℝ)) ≤ (5/6 - X)/r + (1/3 - Y)/((q:ℝ) - p) := by
    rw [hYeq]
    have h2 : Db * Xlo = Nb := by rw [hXlo]; field_simp [hDbpos.ne']
    have h3 : Db*X - Nb = (5/6 - X)/r + (1/3 - (3/2 - 2*X))/((q:ℝ) - p) - 1/(3*s) := by
      rw [hNb, hDb]; field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hX_lo hDbpos.le, h2, h3]
  -- bridge w-form to reduced form (× 1/g)
  have e5 : (5/6 - X)/((g:ℝ)*r) + (Y - 1/6)/((g:ℝ)*p)
      = (1/(g:ℝ)) * ((5/6 - X)/r + (Y - 1/6)/p) := by field_simp
  have e6 : (5/6 - X)/((g:ℝ)*r) + (1/3 - Y)/((g:ℝ)*((q:ℝ)-p))
      = (1/(g:ℝ)) * ((5/6 - X)/r + (1/3 - Y)/((q:ℝ)-p)) := by field_simp
  have egs : (1:ℝ)/(3*((g:ℝ)*s)) = (1/(g:ℝ)) * (1/(3*s)) := by field_simp
  -- discharge the six pentagon conditions
  refine False.elim <| hpent l ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmw3, ← hXdef]; linarith [hX14, mul_nonneg hrR.le hMpos.le]
  · rw [hmw0, ← hYdef, hYeq]; linarith [hX_hi, hbox_hi]
  · rw [hmw1, ← hYdef, hYeq]; linarith [hX_lo, hbox_lo]
  · rw [← hXdef]; linarith [hX34]
  · rw [← hXdef, ← hYdef, c4, c3, c0, e5, egs]
    exact mul_le_mul_of_nonneg_left key_a (by positivity)
  · rw [← hXdef, ← hYdef, c4, c3, c1, e6, egs]
    exact mul_le_mul_of_nonneg_left key_b (by positivity)

/-- **Pentagon grid-witness applicator.** Given a witness index `l` whose cone point
    `(X, Y) = ({r(l+½)/q}, {p(l+½)/q})` is supplied in closed rational form (`hX`, `hY`),
    discharge the six `pent_no_good_red` conditions (rewritten from `Int.fract` to `X, Y`).
    Used by the ten explicit narrow-window `(1,-2)` instances. -/
lemma bhk_prop11_exc_1_neg2_witness (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hpqlt : p < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (l : ℤ) (X Y : ℝ)
    (hX : Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) = X)
    (hY : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) = Y)
    (h39 : 1 / 6 - (r : ℝ) * (((s : ℝ) - q) / (3 * q * s)) ≤ X)
    (h40 : 1 / 6 - (p : ℝ) * (((s : ℝ) - q) / (3 * q * s)) ≤ Y)
    (h41 : Y ≤ 1 / 3 + ((q : ℝ) - p) * (((s : ℝ) - q) / (3 * q * s)))
    (hxle : X ≤ 5 / 6)
    (h42a : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r + (Y - 1 / 6) / p)
    (h42b : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r + (1 / 3 - Y) / ((q : ℝ) - p)) : Found w := by
  refine bhk_prop11_pent_no_good_red w hmono hpos hsum hsmall g p q r s hg hq hp hr hs
    hpqlt c0 c2 c3 c4 l ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hX]; exact h39
  · rw [hY]; exact h40
  · rw [hY]; exact h41
  · rw [hX]; exact hxle
  · rw [hX, hY]; exact h42a
  · rw [hX, hY]; exact h42b

-- finite narrow-window enumeration: `interval_cases` over `q, r, p` (≈600 leaves, each
-- closed by `omega`/`decide`) followed by ten explicit grid-witness `norm_num` checks
set_option maxHeartbeats 4000000 in
/-- **BHK §5 Case 5.2.9 — `(1,-2)S` narrow-window tail.** The finite complement of the
    wide-window `pentkill`: instances with `r(5s-4r) < 36s`. The narrow inequality forces
    `r ≤ 32` (since `r² < 31r + 36`) hence `q ≤ 23`; with `q` odd (even `q` fail coprimality)
    this pins `(q, r, p, s)` to one of ten tuples (`q ∈ {19,21,23}`). Each is killed by an
    explicit grid witness `l` placing a cone point in the pentagon `P`
    (`bhk_prop11_exc_1_neg2_witness` → `bhk_prop11_pent_no_good_red`). -/
lemma bhk_prop11_exc_1_neg2_small (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hnar : (r : ℝ) * (5 * s - 4 * r) < 36 * s)
    (hrig : 2 * r + p = 3 * q) : Found w := by
  -- nat form of the narrow inequality (5s > 4r since s > r)
  have hnar_nat : 5 * r * s < 4 * r * r + 36 * s := by
    have hsr : (r : ℝ) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
    have hR : ((5 * r * s : ℕ) : ℝ) < ((4 * r * r + 36 * s : ℕ) : ℝ) := by
      push_cast; nlinarith [hnar]
    exact_mod_cast hR
  have h4q3r : 4 * q < 3 * r := by omega
  -- r ≤ 32 (narrow forces r² < 31r + 36), hence q ≤ 23
  have hr_ub : r ≤ 32 := by
    by_contra h
    have h33 : 33 ≤ r := by omega
    have hrR : (33 : ℝ) ≤ r := by exact_mod_cast h33
    have hsR : (r : ℝ) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
    nlinarith [hnar, mul_nonneg (show (0 : ℝ) ≤ (s : ℝ) - ((r : ℝ) + 1) by linarith)
        (show (0 : ℝ) ≤ 5 * (r : ℝ) - 36 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (r : ℝ) - 33 by linarith) (show (0 : ℝ) ≤ (r : ℝ) by positivity)]
  have hq_ub : q ≤ 23 := by omega
  have hp_ub : p ≤ 7 := by omega
  -- enumerate q, r, p; impossible leaves die by arithmetic (omega) or coprimality (decide)
  interval_cases q <;> interval_cases r <;> interval_cases p <;>
    (first | omega | (exfalso; revert hcop; decide) | skip)
  -- the seven surviving coprime triples (q, r, p); the witness (l, X, Y) is shared across s
  · -- (19, 26, 5): s ∈ {27, 28}
    have hs_ub : s ≤ 28 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness w hmono hpos hsum hsmall g 5 19 26 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-26) (2 / 19) (11 / 38)
        (by rw [show ((26 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-26 : ℤ) : ℝ) + 1 / 2)
                = ((-35 : ℤ) : ℝ) + 2 / 19 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-26 : ℤ) : ℝ) + 1 / 2)
                = ((-7 : ℤ) : ℝ) + 11 / 38 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- (19, 27, 3): s ∈ {28, 29}
    have hs_ub : s ≤ 29 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness w hmono hpos hsum hsmall g 3 19 27 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-37) (5 / 38) (9 / 38)
        (by rw [show ((27 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-52 : ℤ) : ℝ) + 5 / 38 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-6 : ℤ) : ℝ) + 9 / 38 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- (19, 28, 1): s ∈ {29, 30}
    have hs_ub : s ≤ 30 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness w hmono hpos hsum hsmall g 1 19 28 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-35) (3 / 19) (7 / 38)
        (by rw [show ((28 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-35 : ℤ) : ℝ) + 1 / 2)
                = ((-51 : ℤ) : ℝ) + 3 / 19 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-35 : ℤ) : ℝ) + 1 / 2)
                = ((-2 : ℤ) : ℝ) + 7 / 38 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- (21, 29, 5): s = 30
    have hs_ub : s ≤ 30 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness w hmono hpos hsum hsmall g 5 21 29 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-33) (5 / 42) (11 / 42)
        (by rw [show ((29 : ℕ) : ℝ) / ((21 : ℕ) : ℝ) * (((-33 : ℤ) : ℝ) + 1 / 2)
                = ((-45 : ℤ) : ℝ) + 5 / 42 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((5 : ℕ) : ℝ) / ((21 : ℕ) : ℝ) * (((-33 : ℤ) : ℝ) + 1 / 2)
                = ((-8 : ℤ) : ℝ) + 11 / 42 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- (21, 31, 1): s = 32
    have hs_ub : s ≤ 32 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness w hmono hpos hsum hsmall g 1 21 31 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-37) (5 / 42) (11 / 42)
        (by rw [show ((31 : ℕ) : ℝ) / ((21 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-54 : ℤ) : ℝ) + 5 / 42 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((1 : ℕ) : ℝ) / ((21 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-2 : ℤ) : ℝ) + 11 / 42 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- (23, 31, 7): s = 32
    have hs_ub : s ≤ 32 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness w hmono hpos hsum hsmall g 7 23 31 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-39) (5 / 46) (13 / 46)
        (by rw [show ((31 : ℕ) : ℝ) / ((23 : ℕ) : ℝ) * (((-39 : ℤ) : ℝ) + 1 / 2)
                = ((-52 : ℤ) : ℝ) + 5 / 46 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((7 : ℕ) : ℝ) / ((23 : ℕ) : ℝ) * (((-39 : ℤ) : ℝ) + 1 / 2)
                = ((-12 : ℤ) : ℝ) + 13 / 46 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · -- (23, 32, 5): s = 33
    have hs_ub : s ≤ 33 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness w hmono hpos hsum hsmall g 5 23 32 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-27) (3 / 23) (11 / 46)
        (by rw [show ((32 : ℕ) : ℝ) / ((23 : ℕ) : ℝ) * (((-27 : ℤ) : ℝ) + 1 / 2)
                = ((-37 : ℤ) : ℝ) + 3 / 23 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((5 : ℕ) : ℝ) / ((23 : ℕ) : ℝ) * (((-27 : ℤ) : ℝ) + 1 / 2)
                = ((-6 : ℤ) : ℝ) + 11 / 46 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **BHK §5 Case 5.2.9 — `(1,-2)S` dispatcher.** Splits on the slant width bound:
    `36s ≤ r(5s-4r)` (wide, any `q`) → `bhk_prop11_exc_1_neg2_pentkill`; its complement
    (narrow, `q ∈ {19,21,23}`) → `bhk_prop11_exc_1_neg2_small`. -/
lemma bhk_prop11_exc_1_neg2_kill (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hrig : 2 * r + p = 3 * q) : Found w := by
  by_cases hwb : 36 * (s : ℝ) ≤ (r : ℝ) * (5 * s - 4 * r)
  · exact bhk_prop11_exc_1_neg2_pentkill w hmono hpos hsum hsmall g p q r s hg hq
      c0 c2 c3 c4 hcop hp h3p hrq hr32 hrs hwb hrig
  · exact bhk_prop11_exc_1_neg2_small w hmono hpos hsum hsmall g p q r s hg hq
      c0 c2 c3 c4 hcop hp h3p hrq hr32 hrs hq18 (not_le.mp hwb) hrig

/-- **BHK Part 6 — Claim 19 conclusion (the `v₅ < 2v₄` span bound).** A `1234`-gap
    `[a,b]` (runners `w₀,w₁,w₂` via `Fin 3` and `w₃` all safe) of length at least
    `x₄/6 = 1/(6 w₃)` forces `w₄ < 2 w₃`: runner 5 must cover the gap
    (`gap1234_b5span` gives `w₄·(b-a) < 1/3`), and `b - a ≥ 1/(6 w₃)` then pins
    `w₄ < 2 w₃`. This is the free half of BHK's Claim 19 (Part 6); the gap
    construction at `t = x₁(k+1/6)` is the remaining work. -/
lemma bhk_prop11_part6_claim19_span (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h4safe : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s))
    (hlen : 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) ≤ b - a) : Found w ∨
      (w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) := by
  obtain hF | hspan := bhk_prop11_gap1234_b5span w hpos hab hgap h4safe
  · exact Or.inl hF
  right
  have hw4 : (0 : ℝ) ≤ (w ⟨4, by omega⟩ : ℝ) := by positivity
  have hstep : (w ⟨4, by omega⟩ : ℝ) * (1 / (6 * (w ⟨3, by omega⟩ : ℝ))) < 1 / 3 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlen hw4) hspan
  have hw3 : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h6 : (0 : ℝ) < 6 * (w ⟨3, by omega⟩ : ℝ) := by positivity
  rw [mul_one_div, div_lt_iff₀ h6] at hstep
  have hreal : (w ⟨4, by omega⟩ : ℝ) < 2 * (w ⟨3, by omega⟩ : ℝ) := by linarith [hstep]
  exact_mod_cast hreal

/-- **BHK Part 6 — Claim 19 (`v₅ < 2v₄`), gap construction.** In the diagonal
    case `w₃ = w₀ + w₂` (`v₄ = 1 + v₁`): if at some time `t₀` runner 4 (`w₃`) is at
    `2/3` and runner 1 (`w₀`) lies in `[1/6, 1/4]` — BHK's (55), the realised
    `{w₀t₀} = 1/6 + (w₀/w₃)δ` with `δ ≤ 1/12 + q/(12p) = w₃/(12w₀)` — then
    `w₄ < 2w₃`. Using `w₂ = w₃ − w₀` and `w₁ = w₃ − 2w₀` (from `hsum` + `hdiag`),
    the four runner positions at `t₀` are `{w₀t₀} ∈ [1/6,1/4]`,
    `{w₁t₀} = 2/3 − 2{w₀t₀} ∈ [1/6,1/3]`, `{w₂t₀} = 2/3 − {w₀t₀} ∈ [5/12,1/2]`,
    `{w₃t₀} = 2/3`; each advances `< 1/6` across `[t₀, t₀ + 1/(6w₃)]`, making it a
    `1234`-gap of length `1/(6w₃)`. `part6_claim19_span` then forces `w₄ < 2w₃`.
    The existence of such a `t₀` (the (55) pigeonhole) is supplied separately. -/
lemma bhk_prop11_part6_claim19_gap (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (t0 : ℝ)
    (h3 : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t0) = 2 / 3)
    (h0lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0))
    (h0hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0) ≤ 1 / 4) : Found w ∨
      (w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) := by
  have hw0 : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw1 : (0 : ℝ) < (w ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3 : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsum
  have hdiagR : (w ⟨3, by omega⟩ : ℝ) = (w ⟨0, by omega⟩ : ℝ) + (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hdiag
  have hw1_eq : (w ⟨1, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - 2 * (w ⟨0, by omega⟩ : ℝ) := by
    linarith
  have hw2_eq : (w ⟨2, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by
    linarith
  have hw0lt : (w ⟨0, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  have hw1lt : (w ⟨1, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  have hw2lt : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  -- runner positions at t₀, via the integer relations w₂ = w₃ − w₀ and w₁ = w₃ − 2w₀
  have hf2 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t0)
      = 2 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0) := by
    have key : (w ⟨2, by omega⟩ : ℝ) * t0
        = ((⌊(w ⟨3, by omega⟩ : ℝ) * t0⌋ - ⌊(w ⟨0, by omega⟩ : ℝ) * t0⌋ : ℤ) : ℝ)
          + (2 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0)) := by
      have e3 := Int.floor_add_fract ((w ⟨3, by omega⟩ : ℝ) * t0)
      have e0 := Int.floor_add_fract ((w ⟨0, by omega⟩ : ℝ) * t0)
      rw [h3] at e3
      rw [hw2_eq, sub_mul, Int.cast_sub]
      linarith [e3, e0]
    rw [key, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hf1 : Int.fract ((w ⟨1, by omega⟩ : ℝ) * t0)
      = 2 / 3 - 2 * Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0) := by
    have key : (w ⟨1, by omega⟩ : ℝ) * t0
        = ((⌊(w ⟨3, by omega⟩ : ℝ) * t0⌋ - ⌊(w ⟨0, by omega⟩ : ℝ) * t0⌋
              - ⌊(w ⟨0, by omega⟩ : ℝ) * t0⌋ : ℤ) : ℝ)
          + (2 / 3 - 2 * Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0)) := by
      have e3 := Int.floor_add_fract ((w ⟨3, by omega⟩ : ℝ) * t0)
      have e0 := Int.floor_add_fract ((w ⟨0, by omega⟩ : ℝ) * t0)
      rw [h3] at e3
      rw [hw1_eq, sub_mul, mul_assoc, Int.cast_sub, Int.cast_sub]
      linarith [e3, e0]
    rw [key, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  -- the gap interval [t₀, b], b = t₀ + 1/(6 w₃)
  set b : ℝ := t0 + 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) with hb
  have hbt : b - t0 = 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) := by rw [hb]; ring
  have hab : t0 ≤ b := by rw [hb]; have : (0:ℝ) < 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) := by positivity
                          linarith
  have h6w3 : (0 : ℝ) < 6 * (w ⟨3, by omega⟩ : ℝ) := by positivity
  have hadv0 : (w ⟨0, by omega⟩ : ℝ) * (b - t0) ≤ 1 / 6 := by
    rw [hbt, mul_one_div, div_le_iff₀ h6w3]; linarith
  have hadv1 : (w ⟨1, by omega⟩ : ℝ) * (b - t0) ≤ 1 / 6 := by
    rw [hbt, mul_one_div, div_le_iff₀ h6w3]; linarith
  have hadv2 : (w ⟨2, by omega⟩ : ℝ) * (b - t0) ≤ 1 / 6 := by
    rw [hbt, mul_one_div, div_le_iff₀ h6w3]; linarith
  have hadv3 : (w ⟨3, by omega⟩ : ℝ) * (b - t0) = 1 / 6 := by
    rw [hbt, mul_one_div, div_eq_iff h6w3.ne']; ring
  -- each runner is ≥ 1/6 from the origin throughout [t₀, b]
  have safe0 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨0, by omega⟩ : ℝ) t0 t0 b hw0.le
    · rw [sub_self, mul_zero, add_zero]; exact h0lo
    · linarith
  have safe1 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨1, by omega⟩ : ℝ) t0 t0 b hw1.le
    · rw [hf1, sub_self, mul_zero, add_zero]; linarith
    · rw [hf1]; linarith
  have safe2 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨2, by omega⟩ : ℝ) t0 t0 b hw2.le
    · rw [hf2, sub_self, mul_zero, add_zero]; linarith
    · rw [hf2]; linarith
  have safe3 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨3, by omega⟩ : ℝ) t0 t0 b hw3.le
    · rw [sub_self, mul_zero, add_zero, h3]; norm_num
    · rw [h3]; linarith
  have hgap : ∀ s ∈ Set.Icc t0 b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    fin_cases i
    · exact safe0 s hs
    · exact safe1 s hs
    · exact safe2 s hs
  exact bhk_prop11_part6_claim19_span w hpos hab hgap safe3 (le_of_eq hbt.symm)

/-- **BHK Part 6 — Claim 19 (full): `v₅ < 2v₄` in the diagonal case.** Combines the
    (55)-witness existence (`part6_claim19_witness`) with the gap construction
    (`part6_claim19_gap`): under `hsum`, `hdiag : w₃ = w₀ + w₂`, and the reduced
    structure `w₀ = g·p`, `w₃ = g·r` with `gcd(p,r) = 1` and `r ≥ 12` (always true here,
    `r = p + q ≥ q ≥ 18`), the covering runners force `w₄ < 2w₃`. This is the upper half
    of BHK's Part 6 squeeze; the lower half (`2w₃ < w₄`, Claim 20) is separate. -/
lemma bhk_prop11_part6_claim19 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (g p r : ℕ) (hg : 0 < g) (hp : 0 < p) (hr : 12 ≤ r)
    (hw0 : w ⟨0, by omega⟩ = g * p) (hw3 : w ⟨3, by omega⟩ = g * r)
    (hcop : Nat.Coprime p r) : Found w ∨
      (w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) := by
  obtain ⟨t0, h3, hlo, hhi⟩ :=
    bhk_prop11_part6_claim19_witness w g p r hg hp hr hw0 hw3 hcop
  exact bhk_prop11_part6_claim19_gap w hpos hsum hdiag t0 h3 hlo hhi

/-- **BHK Part 6 — generic lower-bound engine.** Abstracts `part6_claim20_span` over the
    block speed `b` (the runner whose `1/(3b)`-wide block sits inside a `0123`-gap). If the
    interval `[p, q]` has width `q − p = 1/(3b)` with both endpoints `1234`-safe (runners
    `0,1,2,3` all `≥ 1/6`), then the covering assumption forces **runner 5** unsafe at both
    `p` and `q`. Hence `w₄p`, `w₄q` each lie within `1/6` of an integer, so their difference
    `D = w₄(q−p) = w₄/(3b)` lies within `1/3` of the integer `k₂ − k₁`. With `b < w₄` we get
    `D > 1/3`, so that integer is `≥ 1`, forcing `D > 2/3`, i.e. `2b < w₄`. Claim 20
    instantiates `b = w₃`; Claim 21 instantiates `b = w₂`. -/
lemma bhk_prop11_part6_lower_span (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (b : ℝ) (hbpos : 0 < b) (hbw4 : b < (w ⟨4, by omega⟩ : ℝ))
    (p q : ℝ) (hpq : q - p = 1 / (3 * b))
    (hp : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * p))
    (hq : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * q)) : Found w ∨
      (2 * b < (w ⟨4, by omega⟩ : ℝ)) := by
  -- runner 5 (`w₄`) is the only runner that can witness the cover at the edges
  obtain hF | ⟨i, hi⟩ := found_or_blocked w p
  · exact Or.inl hF
  have hp5 : circDist ((w ⟨4, by omega⟩ : ℝ) * p) < 1 / 6 := by
    fin_cases i
    · exact absurd hi (not_lt.mpr (hp 0))
    · exact absurd hi (not_lt.mpr (hp 1))
    · exact absurd hi (not_lt.mpr (hp 2))
    · exact absurd hi (not_lt.mpr (hp 3))
    · exact hi
  obtain hF | ⟨i, hi⟩ := found_or_blocked w q
  · exact Or.inl hF
  right
  have hq5 : circDist ((w ⟨4, by omega⟩ : ℝ) * q) < 1 / 6 := by
    fin_cases i
    · exact absurd hi (not_lt.mpr (hq 0))
    · exact absurd hi (not_lt.mpr (hq 1))
    · exact absurd hi (not_lt.mpr (hq 2))
    · exact absurd hi (not_lt.mpr (hq 3))
    · exact hi
  -- each `w₄`-image lies within `1/6` of an integer
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℤ, |(w ⟨4, by omega⟩ : ℝ) * p - (k : ℝ)| < 1 / 6 :=
    (mem_bhkB_iff _).mpr hp5
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℤ, |(w ⟨4, by omega⟩ : ℝ) * q - (k : ℝ)| < 1 / 6 :=
    (mem_bhkB_iff _).mpr hq5
  rw [abs_lt] at hk₁ hk₂
  have hDeq : (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p
      = (w ⟨4, by omega⟩ : ℝ) / (3 * b) := by
    rw [show (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p
        = (w ⟨4, by omega⟩ : ℝ) * (q - p) from by ring, hpq]; ring
  have hDpos : (1 : ℝ) / 3 < (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p := by
    rw [hDeq, lt_div_iff₀ (by positivity)]; linarith
  have hd1 : (1 : ℤ) ≤ k₂ - k₁ := by
    have hpos' : (0 : ℝ) < ((k₂ - k₁ : ℤ) : ℝ) := by
      push_cast; linarith [hk₁.1, hk₂.2, hDpos]
    have : (0 : ℤ) < k₂ - k₁ := by exact_mod_cast hpos'
    omega
  have hD23 : (2 : ℝ) / 3 < (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p := by
    have hdR : (1 : ℝ) ≤ ((k₂ - k₁ : ℤ) : ℝ) := by exact_mod_cast hd1
    push_cast at hdR; linarith [hk₁.2, hk₂.1]
  rw [hDeq, lt_div_iff₀ (by positivity)] at hD23
  linarith

/-- **BHK Part 6 — Claim 20 (`v₅ > 2v₄`), lower-bound engine.** The dual of
    `gap1234_b5span`. Let `[p, q]` be the closure of a `4`-block (runner 4 within
    `1/6`), so its width is exactly `q − p = 1/(3w₃)` and at each edge runner 4 sits
    at `circDist = 1/6` (safe). If both edges are also `123`-safe (runners 1,2,3
    `≥ 1/6`) — i.e. the `4`-block lies in a `0123`-gap — then both edges are
    `1234`-safe, so the covering assumption forces **runner 5** unsafe at `p` and `q`.
    Hence `w₄p` and `w₄q` each lie within `1/6` of an integer, so their difference
    `D = w₄(q−p) = w₄/(3w₃)` lies within `1/3` of the integer `k₂ − k₁`. Since
    `v₅ > v₄` gives `D > 1/3`, that integer must be `≥ 1`, forcing `D > 2/3`, i.e.
    `2w₃ < w₄`. With Claim 19's `w₄ < 2w₃` this is the Part-6 contradiction. -/
lemma bhk_prop11_part6_claim20_span (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (p q : ℝ) (hpq : q - p = 1 / (3 * (w ⟨3, by omega⟩ : ℝ)))
    (hp : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * p))
    (hq : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * q)) : Found w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
  bhk_prop11_part6_lower_span w hpos (w ⟨3, by omega⟩ : ℝ)
    (by exact_mod_cast hpos _) hw34 p q hpq hp hq

/-- **BHK Part 6 — Claim 20 (`v₅ > 2v₄`), gap construction.** Feeds the engine
    `part6_claim20_span`. At a `(56)`-witness time `t` (runner 1 at `1/3`,
    `w₀t = N + 1/3`; runner 4 within `1/6` of integer `m`, `|w₃t − m| ≤ 1/6`), the
    `4`-block containing `t` has closure `[pe, qe]`, `pe = (m−1/6)/w₃`,
    `qe = (m+1/6)/w₃`, width `qe − pe = 1/(3w₃)`. Using the integer relations
    `w₁ = w₃ − 2w₀`, `w₂ = w₃ − w₀` (from `hsum` + `hdiag`) and `4w₀ < w₃`
    (`hsmall`+`hdiag`, the `v₁ < v₄/4` condition), runner 1's small drift over the
    block (`< 1/12`) keeps `{w₀·}` in `[1/4, 5/12]`, so runners 1,2,3 stay `≥ 1/6`
    across `[pe, qe]` (`safe_on_Icc` with block-indices `N`, `m−2N−1`, `m−N−1`),
    while runner 4 sits at `circDist = 1/6` at each edge. Both edges are then
    `1234`-safe and the engine gives `2w₃ < w₄`. -/
lemma bhk_prop11_part6_claim20_gap (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (t : ℝ) (N m : ℤ)
    (h0 : (w ⟨0, by omega⟩ : ℝ) * t = (N : ℝ) + 1 / 3)
    (hm : |(w ⟨3, by omega⟩ : ℝ) * t - (m : ℝ)| ≤ 1 / 6) : Found w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) := by
  have hw0 : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw1 : (0 : ℝ) < (w ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3 : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3ne : (w ⟨3, by omega⟩ : ℝ) ≠ 0 := hw3.ne'
  have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsum
  have hdiagR : (w ⟨3, by omega⟩ : ℝ) = (w ⟨0, by omega⟩ : ℝ) + (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hdiag
  have hsmallR : 3 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall
  have hw1eq : (w ⟨1, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - 2 * (w ⟨0, by omega⟩ : ℝ) := by
    linarith
  have hw2eq : (w ⟨2, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
  have h4w0 : 4 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hm
  -- the 4-block edges
  set pe : ℝ := ((m : ℝ) - 1 / 6) / (w ⟨3, by omega⟩ : ℝ) with hpe
  set qe : ℝ := ((m : ℝ) + 1 / 6) / (w ⟨3, by omega⟩ : ℝ) with hqe
  have hw3pe : (w ⟨3, by omega⟩ : ℝ) * pe = (m : ℝ) - 1 / 6 := by rw [hpe]; field_simp
  have hw3qe : (w ⟨3, by omega⟩ : ℝ) * qe = (m : ℝ) + 1 / 6 := by rw [hqe]; field_simp
  have hpq : qe - pe = 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by rw [hpe, hqe]; field_simp; ring
  have hpeqe : pe ≤ qe := by
    have h0lt : (0 : ℝ) < qe - pe := by rw [hpq]; positivity
    linarith
  -- runner-0 position at the edges (bare-real arithmetic helper)
  obtain ⟨hw0pe_lo, hw0pe_hi, hw0qe_lo, hw0qe_hi⟩ :=
    bhk_prop11_part6_edge_arith (w ⟨0, by omega⟩ : ℝ) (w ⟨3, by omega⟩ : ℝ) hw0 hw3 h4w0
      t N m h0 hmlo hmhi pe qe hw3pe hw3qe
  -- runners 0,1,2 are safe across the whole block `[pe, qe]`
  have safe0 : ∀ s ∈ Set.Icc pe qe, (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s) :=
    bhk_prop11_safe_on_Icc (w ⟨0, by omega⟩ : ℝ) N hw0pe_lo hw0qe_hi hw0.le
  have safe2 : ∀ s ∈ Set.Icc pe qe, (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_safe_on_Icc (w ⟨2, by omega⟩ : ℝ) (m - N - 1) ?_ ?_ hw2.le
    · have hcast : ((m - N - 1 : ℤ) : ℝ) = (m : ℝ) - (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨2, by omega⟩ : ℝ) * pe = ((m : ℝ) - 1 / 6) - (w ⟨0, by omega⟩ : ℝ) * pe := by
        rw [hw2eq, ← hw3pe]; ring
      rw [hcast, hval]; linarith [hw0pe_hi]
    · have hcast : ((m - N - 1 : ℤ) : ℝ) = (m : ℝ) - (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨2, by omega⟩ : ℝ) * qe = ((m : ℝ) + 1 / 6) - (w ⟨0, by omega⟩ : ℝ) * qe := by
        rw [hw2eq, ← hw3qe]; ring
      rw [hcast, hval]; linarith [hw0qe_lo]
  have safe1 : ∀ s ∈ Set.Icc pe qe, (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_safe_on_Icc (w ⟨1, by omega⟩ : ℝ) (m - 2 * N - 1) ?_ ?_ hw1.le
    · have hcast : ((m - 2 * N - 1 : ℤ) : ℝ) = (m : ℝ) - 2 * (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨1, by omega⟩ : ℝ) * pe
          = ((m : ℝ) - 1 / 6) - 2 * ((w ⟨0, by omega⟩ : ℝ) * pe) := by rw [hw1eq, ← hw3pe]; ring
      rw [hcast, hval]; linarith [hw0pe_hi]
    · have hcast : ((m - 2 * N - 1 : ℤ) : ℝ) = (m : ℝ) - 2 * (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨1, by omega⟩ : ℝ) * qe
          = ((m : ℝ) + 1 / 6) - 2 * ((w ⟨0, by omega⟩ : ℝ) * qe) := by rw [hw1eq, ← hw3qe]; ring
      rw [hcast, hval]; linarith [hw0qe_lo]
  -- runner 3 sits at `circDist = 1/6` at each edge
  have hfrpe : Int.fract ((m : ℝ) - 1 / 6) = 5 / 6 := by
    rw [show ((m : ℝ) - 1 / 6) = ((m - 1 : ℤ) : ℝ) + 5 / 6 from by push_cast; ring,
      Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have hfrqe : Int.fract ((m : ℝ) + 1 / 6) = 1 / 6 := by
    rw [show ((m : ℝ) + 1 / 6) = ((m : ℤ) : ℝ) + 1 / 6 from by push_cast; ring,
      Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have safe3pe : (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * pe) := by
    rw [hw3pe]; simp only [circDist]; rw [hfrpe]; exact le_min (by norm_num) (by norm_num)
  have safe3qe : (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * qe) := by
    rw [hw3qe]; simp only [circDist]; rw [hfrqe]; exact le_min (by norm_num) (by norm_num)
  -- both edges are `1234`-safe → apply the engine
  have hp : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * pe) := by
    intro i; fin_cases i
    · exact safe0 pe ⟨le_refl _, hpeqe⟩
    · exact safe1 pe ⟨le_refl _, hpeqe⟩
    · exact safe2 pe ⟨le_refl _, hpeqe⟩
    · exact safe3pe
  have hq : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * qe) := by
    intro i; fin_cases i
    · exact safe0 qe ⟨hpeqe, le_refl _⟩
    · exact safe1 qe ⟨hpeqe, le_refl _⟩
    · exact safe2 qe ⟨hpeqe, le_refl _⟩
    · exact safe3qe
  exact bhk_prop11_part6_claim20_span w hpos hw34 pe qe hpq hp hq

/-- **BHK Part 6 — Claim 20 (`v₅ > 2v₄`), `p ≥ 3` case.** Combines the `(56)`-witness with
    the gap construction: the diagonal config with `p ≥ 3` forces `2w₃ < w₄`. -/
lemma bhk_prop11_part6_claim20 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g p r : ℕ) (hg : 0 < g) (hp : 3 ≤ p) (hr : 0 < r)
    (hw0 : w ⟨0, by omega⟩ = g * p) (hw3 : w ⟨3, by omega⟩ = g * r)
    (hcop : Nat.Coprime p r) : Found w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) := by
  obtain ⟨t, N, m, h0, hm⟩ := bhk_prop11_part6_claim20_witness w g p r hg hp hr hw0 hw3 hcop
  exact bhk_prop11_part6_claim20_gap w hpos hsum hdiag hsmall hw34 t N m h0 hm

/-- **BHK Part 6 — Claim 21 (`p = 1`), lower bound `2w₂ < w₄`.** With the `(57)`-witness the
    `w₂`-block edges are `1234`-safe (`claim21_edges`), so the generic engine
    `part6_lower_span` with `b = w₂` forces `2w₂ < w₄`. -/
lemma bhk_prop11_part6_claim21_lower (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g q : ℕ) (hg : 0 < g) (hq : 0 < q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (t : ℝ) (m : ℤ) (hbt : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ))
    (h0lo : (1 : ℝ) / 3 + 1 / (6 * (q : ℝ)) ≤ (w ⟨0, by omega⟩ : ℝ) * t)
    (h0hi : (w ⟨0, by omega⟩ : ℝ) * t ≤ 5 / 12 - 1 / (6 * (q : ℝ))) : Found w ∨
      (2 * (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) := by
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := hw2pos.ne'
  set pe : ℝ := ((m : ℝ) - 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hpedef
  set qe : ℝ := ((m : ℝ) + 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hqedef
  have hpe : (w ⟨2, by omega⟩ : ℝ) * pe = (m : ℝ) - 1 / 6 := by rw [hpedef]; field_simp
  have hqe : (w ⟨2, by omega⟩ : ℝ) * qe = (m : ℝ) + 1 / 6 := by rw [hqedef]; field_simp
  have hpq : qe - pe = 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by rw [hpedef, hqedef]; field_simp; ring
  obtain ⟨hsafeP, hsafeQ⟩ := bhk_prop11_part6_claim21_edges w hpos hsum hdiag g q hg hq hw0 hw2
    t m hbt h0lo h0hi pe qe hpe hqe
  exact bhk_prop11_part6_lower_span w hpos (w ⟨2, by omega⟩ : ℝ) hw2pos hw24 pe qe hpq
    hsafeP hsafeQ

/-- **BHK Part 6 — Claim 21 (`p = 1`), `s = 2q+1` lonely exclusion.** Given `w₄ = 2w₂ + w₀`
    (the squeeze `2w₂ < w₄ < 2w₃ = 2w₂ + 2w₀` forces this for `p = 1`), the `(57)`-witness's
    right edge `qe` is a lonely time: runners `0,1,2,3` are safe (`claim21_edges`) and runner
    `4 = 2w₂ + w₀` sits at `circDist = 2/3 − w₀t − 1/(6q) ≥ 1/4 > 1/6`. This contradicts the
    cover. -/
lemma bhk_prop11_part6_claim21_lonely (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hs : w ⟨4, by omega⟩ = 2 * w ⟨2, by omega⟩ + w ⟨0, by omega⟩)
    (g q : ℕ) (hg : 0 < g) (hq : 0 < q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (t : ℝ) (m : ℤ) (hbt : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ))
    (h0lo : (1 : ℝ) / 3 + 1 / (6 * (q : ℝ)) ≤ (w ⟨0, by omega⟩ : ℝ) * t)
    (h0hi : (w ⟨0, by omega⟩ : ℝ) * t ≤ 5 / 12 - 1 / (6 * (q : ℝ))) : Found w := by
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := hw2pos.ne'
  have hw0R : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) := by exact_mod_cast hw0
  have hw2R : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hw2
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hδ : (0 : ℝ) < 1 / (6 * (q : ℝ)) := one_div_pos.mpr (by linarith)
  have hsR : (w ⟨4, by omega⟩ : ℝ)
      = 2 * (w ⟨2, by omega⟩ : ℝ) + (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hs
  set pe : ℝ := ((m : ℝ) - 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hpedef
  set qe : ℝ := ((m : ℝ) + 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hqedef
  have hpe : (w ⟨2, by omega⟩ : ℝ) * pe = (m : ℝ) - 1 / 6 := by rw [hpedef]; field_simp
  have hqe : (w ⟨2, by omega⟩ : ℝ) * qe = (m : ℝ) + 1 / 6 := by rw [hqedef]; field_simp
  obtain ⟨_, hsafeQ⟩ := bhk_prop11_part6_claim21_edges w hpos hsum hdiag g q hg hq hw0 hw2
    t m hbt h0lo h0hi pe qe hpe hqe
  -- runner 0 at qe:  w₀·qe = w₀·t + 1/(6q)
  have e_qe0 : (w ⟨0, by omega⟩ : ℝ) * qe = (w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)) := by
    apply mul_left_cancel₀ hw2ne
    have l : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * qe)
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * qe) := by ring
    have r : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)))
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * t)
          + (w ⟨2, by omega⟩ : ℝ) / (6 * (q : ℝ)) := by ring
    rw [l, r, hqe, hbt, hw0R, hw2R]; field_simp
  -- runner 4 = 2w₂ + w₀ is ALSO safe at qe
  have hw4qe : (w ⟨4, by omega⟩ : ℝ) * qe
      = ((2 * m : ℤ) : ℝ) + (1 / 3 + ((w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)))) := by
    rw [hsR]
    have hdistr : (2 * (w ⟨2, by omega⟩ : ℝ) + (w ⟨0, by omega⟩ : ℝ)) * qe
        = 2 * ((w ⟨2, by omega⟩ : ℝ) * qe) + (w ⟨0, by omega⟩ : ℝ) * qe := by ring
    rw [hdistr, hqe, e_qe0]; push_cast; ring
  have hfr : Int.fract ((w ⟨4, by omega⟩ : ℝ) * qe)
      = 1 / 3 + ((w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ))) := by
    rw [hw4qe, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have safe4qe : (1 : ℝ) / 6 ≤ circDist ((w ⟨4, by omega⟩ : ℝ) * qe) := by
    simp only [circDist]; rw [hfr]; exact le_min (by linarith) (by linarith)
  obtain hF | ⟨i, hi⟩ := found_or_blocked w qe
  · exact hF
  fin_cases i
  · exact absurd hi (not_lt.mpr (hsafeQ 0))
  · exact absurd hi (not_lt.mpr (hsafeQ 1))
  · exact absurd hi (not_lt.mpr (hsafeQ 2))
  · exact absurd hi (not_lt.mpr (hsafeQ 3))
  · exact absurd hi (not_lt.mpr safe4qe)

/-- **BHK Part 6 — Claim 21 (`p = 1`) with the `(57)`-witness supplied explicitly.** Same
    as `bhk_prop11_part6_p1` but takes the half-integer `(57)`-witness `(t, m)` as a
    hypothesis instead of constructing it via the `q ≥ 16` grid argument
    (`claim21_witness`). This handles the small-`q` diagonals `(1, q)` with
    `q ∈ {11, 13, 15}` (where the `1/q`-grid still meets the window `[1/3+1/(6q),
    5/12−1/(6q)]` even though its length dips below `1/q`), needing only `q ≥ 11` for
    Claim 19's `r = q+1 ≥ 12`. -/
lemma bhk_prop11_part6_p1_wit (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g q s : ℕ) (hg : 0 < g) (hq11 : 11 ≤ q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (hw4 : w ⟨4, by omega⟩ = g * s)
    (t : ℝ) (m : ℤ) (hbt : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ))
    (h0lo : (1 : ℝ) / 3 + 1 / (6 * (q : ℝ)) ≤ (w ⟨0, by omega⟩ : ℝ) * t)
    (h0hi : (w ⟨0, by omega⟩ : ℝ) * t ≤ 5 / 12 - 1 / (6 * (q : ℝ))) : Found w := by
  have hq0 : 0 < q := by omega
  have hw0' : w ⟨0, by omega⟩ = g * 1 := by omega
  have hw3' : w ⟨3, by omega⟩ = g * (q + 1) := by rw [hdiag, hw0, hw2]; ring
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19 w hpos hsum hdiag g 1 (q + 1) hg (by norm_num) (by omega)
      hw0' hw3' (Nat.coprime_one_left _)
  · exact hF
  obtain hF | (h21 : 2 * (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
    bhk_prop11_part6_claim21_lower w hpos hsum hdiag hw24 g q hg hq0 hw0 hw2 t m hbt h0lo h0hi
  · exact hF
  have h21n : 2 * w ⟨2, by omega⟩ < w ⟨4, by omega⟩ := by exact_mod_cast h21
  have hsqueeze : s = 2 * q + 1 := by
    have a1 : 2 * q < s := by
      have h := h21n
      rw [hw2, hw4] at h
      have h' : g * (2 * q) = 2 * (g * q) := by ring
      exact lt_of_mul_lt_mul_left (h'.trans_lt h) (Nat.zero_le g)
    have a2 : s < 2 * q + 2 := by
      have h := h19
      rw [hw4, hw3'] at h
      have h' : 2 * (g * (q + 1)) = g * (2 * q + 2) := by ring
      exact lt_of_mul_lt_mul_left (h.trans_le h'.le) (Nat.zero_le g)
    omega
  have hs : w ⟨4, by omega⟩ = 2 * w ⟨2, by omega⟩ + w ⟨0, by omega⟩ := by
    rw [hw4, hw2, hw0, hsqueeze]; ring
  exact bhk_prop11_part6_claim21_lonely w hpos hsum hdiag hs g q hg hq0 hw0 hw2 t m hbt h0lo h0hi

/-- **BHK Part 6 — `p = 1` diagonal case.** Combines Claim 19 (`w₄ < 2w₃`), Claim 21's lower
    bound (`2w₂ < w₄`), and the `s = 2q+1` lonely exclusion. The squeeze
    `2w₂ < w₄ < 2w₃ = 2w₂ + 2w₀` plus the `p = 1` structure (`w₀ = g`, `w₂ = gq`, `w₄ = gs`)
    forces `w₄ = 2w₂ + w₀`, which `claim21_lonely` rules out. -/
lemma bhk_prop11_part6_p1 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g q s : ℕ) (hg : 0 < g) (hq16 : 16 ≤ q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hq0 : 0 < q := by omega
  obtain ⟨t, m, hbt, h0lo, h0hi⟩ := bhk_prop11_part6_claim21_witness w g q hg hq16 hw0 hw2
  -- Claim 19:  w₄ < 2w₃  (p = 1, r = q+1 ≥ 12)
  have hw0' : w ⟨0, by omega⟩ = g * 1 := by omega
  have hw3' : w ⟨3, by omega⟩ = g * (q + 1) := by rw [hdiag, hw0, hw2]; ring
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19 w hpos hsum hdiag g 1 (q + 1) hg (by norm_num) (by omega)
      hw0' hw3' (Nat.coprime_one_left _)
  · exact hF
  -- Claim 21:  2w₂ < w₄
  obtain hF | (h21 : 2 * (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
    bhk_prop11_part6_claim21_lower w hpos hsum hdiag hw24 g q hg hq0 hw0 hw2 t m hbt h0lo h0hi
  · exact hF
  -- squeeze:  w₄ = 2w₂ + w₀
  have h21n : 2 * w ⟨2, by omega⟩ < w ⟨4, by omega⟩ := by exact_mod_cast h21
  have hsqueeze : s = 2 * q + 1 := by
    have a1 : 2 * q < s := by
      have h := h21n
      rw [hw2, hw4] at h
      have h' : g * (2 * q) = 2 * (g * q) := by ring
      exact lt_of_mul_lt_mul_left (h'.trans_lt h) (Nat.zero_le g)
    have a2 : s < 2 * q + 2 := by
      have h := h19
      rw [hw4, hw3'] at h
      have h' : 2 * (g * (q + 1)) = g * (2 * q + 2) := by ring
      exact lt_of_mul_lt_mul_left (h.trans_le h'.le) (Nat.zero_le g)
    omega
  have hs : w ⟨4, by omega⟩ = 2 * w ⟨2, by omega⟩ + w ⟨0, by omega⟩ := by
    rw [hw4, hw2, hw0, hsqueeze]; ring
  exact bhk_prop11_part6_claim21_lonely w hpos hsum hdiag hs g q hg hq0 hw0 hw2 t m hbt h0lo h0hi

/-- **BHK Part 6 — diagonal case `w₃ = w₀ + w₂` (`r = p + q`).** Closes every diagonal
    exceptional config. Claim 19 always gives `w₄ < 2w₃`; the matching lower bound
    contradicts it. The `p`-split: `p ≥ 3` → `claim20` (`2w₃ < w₄`); `p = 2` (so `q`, hence
    `r = q+2`, odd from `Coprime 2 q`) → `claim20` via the two-point `witness_p2`; `p = 1` →
    `part6_p1` (`2w₂ < w₄` + the `s = 2q+1` lonely exclusion). -/
lemma bhk_prop11_part6 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g p q r s : ℕ) (hg : 0 < g) (hp_pos : 0 < p) (hq18 : 18 ≤ q)
    (hgp : w ⟨0, by omega⟩ = g * p) (hgq : w ⟨2, by omega⟩ = g * q)
    (hgr : w ⟨3, by omega⟩ = g * r) (hgs : w ⟨4, by omega⟩ = g * s)
    (hcop : Nat.Coprime p q) : Found w := by
  -- diagonal ⟹ r = p + q
  have hrpq : r = p + q := by
    have h : g * r = g * (p + q) := by rw [← hgr, hdiag, hgp, hgq]; ring
    exact Nat.eq_of_mul_eq_mul_left hg h
  have hr12 : 12 ≤ r := by omega
  have hcopr : Nat.Coprime p r := by
    show Nat.gcd p r = 1
    rw [hrpq, Nat.add_comm p q, Nat.gcd_add_self_right]; exact hcop
  -- Claim 19 (always): w₄ < 2w₃
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19 w hpos hsum hdiag g p r hg hp_pos hr12 hgp hgr hcopr
  · exact hF
  have h19R : (w ⟨4, by omega⟩ : ℝ) < 2 * (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast h19
  -- w₂ < w₄ (for the p = 1 branch)
  have hw23 : w ⟨2, by omega⟩ < w ⟨3, by omega⟩ := by rw [hgq, hgr, hrpq]; nlinarith [hg, hp_pos]
  have hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) :=
    lt_trans (by exact_mod_cast hw23) hw34
  rcases lt_or_ge p 3 with hp3 | hp3
  · interval_cases p
    · -- p = 1
      have hw0g : w ⟨0, by omega⟩ = g := by omega
      exact bhk_prop11_part6_p1 w hpos hsum hdiag hw24 g q s hg (by omega) hw0g hgq hgs
    · -- p = 2  (q, r odd)
      have hqodd : q % 2 = 1 := by
        have h2 : ¬ (2 ∣ q) := by
          intro hdvd
          have hg2 : Nat.gcd 2 q = 2 := Nat.gcd_eq_left hdvd
          have hc1 : Nat.gcd 2 q = 1 := hcop
          omega
        omega
      have hrodd : r % 2 = 1 := by omega
      obtain ⟨t, N, m, h0, hm⟩ := bhk_prop11_part6_claim20_witness_p2 w g r hg hrodd hgp hgr
      obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
        bhk_prop11_part6_claim20_gap w hpos hsum hdiag hsmall hw34 t N m h0 hm
      · exact hF
      linarith
  · -- p ≥ 3
    obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
      bhk_prop11_part6_claim20 w hpos hsum hdiag hsmall hw34 g p r hg hp3 (by omega)
        hgp hgr hcopr
    · exact hF
    linarith

/-- **BHK Part 6 — diagonal case, `q`-free form (`p ≥ 2`, `r = p+q ≥ 12`).** The
    `p ≥ 2` branches of `bhk_prop11_part6` use `q ≥ 18` only to get `r ≥ 12` (the
    hypothesis of Claim 19); Claim 20 needs only `r > 0`. Taking `r ≥ 12` directly
    lifts the `q ≥ 18` restriction, closing every diagonal `(p,q)` with `p ≥ 2` and
    `p + q ≥ 12` — including the `q < 18` ones. (The `p = 1` diagonals still go
    through `part6_p1`, which genuinely needs `q ≥ 16` for `claim21_lonely`.) -/
lemma bhk_prop11_part6_ge12 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g p q r s : ℕ) (hg : 0 < g) (hp2 : 2 ≤ p) (hr12 : 12 ≤ r)
    (hgp : w ⟨0, by omega⟩ = g * p) (hgq : w ⟨2, by omega⟩ = g * q)
    (hgr : w ⟨3, by omega⟩ = g * r) (hgs : w ⟨4, by omega⟩ = g * s)
    (hcop : Nat.Coprime p q) : Found w := by
  have hp_pos : 0 < p := by omega
  have hrpq : r = p + q := by
    have h : g * r = g * (p + q) := by rw [← hgr, hdiag, hgp, hgq]; ring
    exact Nat.eq_of_mul_eq_mul_left hg h
  have hcopr : Nat.Coprime p r := by
    show Nat.gcd p r = 1
    rw [hrpq, Nat.add_comm p q, Nat.gcd_add_self_right]; exact hcop
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19 w hpos hsum hdiag g p r hg hp_pos hr12 hgp hgr hcopr
  · exact hF
  have h19R : (w ⟨4, by omega⟩ : ℝ) < 2 * (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast h19
  rcases lt_or_ge p 3 with hp3 | hp3
  · interval_cases p
    · -- p = 2  (q, r odd)
      have hqodd : q % 2 = 1 := by
        have h2 : ¬ (2 ∣ q) := by
          intro hdvd
          have hg2 : Nat.gcd 2 q = 2 := Nat.gcd_eq_left hdvd
          have hc1 : Nat.gcd 2 q = 1 := hcop
          omega
        omega
      have hrodd : r % 2 = 1 := by omega
      obtain ⟨t, N, m, h0, hm⟩ := bhk_prop11_part6_claim20_witness_p2 w g r hg hrodd hgp hgr
      obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
        bhk_prop11_part6_claim20_gap w hpos hsum hdiag hsmall hw34 t N m h0 hm
      · exact hF
      linarith
  · -- p ≥ 3
    obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
      bhk_prop11_part6_claim20 w hpos hsum hdiag hsmall hw34 g p r hg hp3 (by omega)
        hgp hgr hcopr
    · exact hF
    linarith

set_option maxHeartbeats 40000000 in
/-- **Transversal slivers `q ∈ [18,30)` — finite R/P dispatch.** Every exceptional
    config with `q ∈ [18,30)`, `3p<q`, `gcd(p,q)=1`, `q<r<3q/2` (`hr32`), `r≠p+q`
    is killed by an explicit half-integer witness: either the coset hits the
    rectangle `R` (`bhk_prop11_exc_Rkill`, 526 cases) or — when `C∩R=∅` — the
    pentagon `P` (`bhk_prop11_exc_Pkill`, 82 cases, `s`-free worst-case `s=r+1`).
    This is the small-`q` companion that lets `bhk_prop11_exc_open` assume `q≥30`,
    where every transversal read-off applies without slivers. -/
lemma bhk_prop11_exc_q_18_30 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq18 : 18 ≤ q) (hq30 : q < 30)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q)
    (hrq : q < r) (hr32 : 2 * r < 3 * q) (hrs : r < s) (hndiag : r ≠ p + q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (h_nogood : ∀ l : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) : Found w := by
  interval_cases q
  · -- q = 18
    have hpb : p ≤ 5 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 26 := by omega
      interval_cases r
      · omega  -- r=19=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 18 20 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 21 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 22 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 23 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 24 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 25 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 26 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 19 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 20 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 21 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=23=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 24 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 25 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 19
    have hpb : p ≤ 6 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 28 := by omega
      interval_cases r
      · omega  -- r=20=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 19 21 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 23 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 25 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 19 26 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 19 28 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 19 20 s 12 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega  -- r=21=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 22 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 19 23 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 19 24 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 25 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 26 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 27 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 28 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 20 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 21 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=22=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 19 23 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 24 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 19 25 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 26 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 19 27 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 28 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 20 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 19 21 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 19 22 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega  -- r=23=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 24 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 25 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 26 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 19 27 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 28 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 19 20 s 12 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 21 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=24=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 25 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 19 26 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 28 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 6
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 20 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 21 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 6 19 22 s 10 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 23 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 24 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=25=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 26 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 27 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 28 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 20
    have hpb : p ≤ 6 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 29 := by omega
      interval_cases r
      · omega  -- r=21=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 20 22 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 26 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 27 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 29 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 21 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 22 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=23=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 24 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 25 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 20 26 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 27 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 28 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 29 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
  · -- q = 21
    have hpb : p ≤ 6 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 31 := by omega
      interval_cases r
      · omega  -- r=22=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 21 23 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 24 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 27 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 28 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 2
      have hru : r ≤ 31 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 21 22 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega  -- r=23=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 24 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 27 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 28 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 29 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 4
      have hru : r ≤ 31 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 22 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 23 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 24 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=25=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 26 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 27 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 28 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 29 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 31 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 31 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 22 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 23 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 24 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 25 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=26=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 27 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 28 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 29 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 21 31 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact absurd hcop (by decide)
  · -- q = 22
    have hpb : p ≤ 7 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 32 := by omega
      interval_cases r
      · omega  -- r=23=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 22 24 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 25 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 22 27 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 28 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 32 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 32 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 23 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 24 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=25=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 26 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 27 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 22 28 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 22 29 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 30 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 31 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 32 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 32 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 23 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 24 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 25 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=27=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 28 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 31 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 22 32 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 32 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 23 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 24 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 25 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 26 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 27 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 28 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=29=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 31 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 32 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 23
    have hpb : p ≤ 7 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 34 := by omega
      interval_cases r
      · omega  -- r=24=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 23 25 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 31 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 23 34 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 23 24 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega  -- r=25=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 26 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 23 27 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 28 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 29 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 30 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 31 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 33 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 34 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 24 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 25 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=26=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 23 27 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 28 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 23 29 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 30 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 31 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 23 33 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 34 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 24 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 23 25 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 26 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=27=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 28 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 29 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 30 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 23 31 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 23 33 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 34 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 24 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 25 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 27 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=28=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 29 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 31 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 23 32 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 23 33 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 34 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 6
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 24 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 25 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 6 23 26 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=29=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 30 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 31 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 34 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 7
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 24 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 25 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 26 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 27 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 28 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 29 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=30=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 7 23 31 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 33 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 34 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 24
    have hpb : p ≤ 7 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 35 := by omega
      interval_cases r
      · omega  -- r=25=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 24 26 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 27 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 31 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 32 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 35 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 35 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 25 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 26 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 27 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 28 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=29=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 30 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 31 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 32 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 33 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 24 34 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 35 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 35 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 25 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 26 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 27 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=31=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 32 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 35 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 25
    have hpb : p ≤ 8 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 37 := by omega
      interval_cases r
      · omega  -- r=26=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 25 27 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 28 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 31 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 32 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 35 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 25 37 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 25 26 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega  -- r=27=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 28 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 25 29 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 30 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 33 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 34 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 36 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 37 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 26 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 27 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=28=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 29 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 30 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 25 31 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 33 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 34 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 25 36 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 37 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 26 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 25 27 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 28 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=29=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 30 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 31 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 32 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 25 33 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 34 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 35 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 25 36 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 37 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 6
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 26 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 27 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 6 25 28 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 30 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=31=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 32 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 35 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 36 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 6 25 37 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 7
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 26 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 27 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 28 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 31 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=32=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 33 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 7 25 34 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 35 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 37 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 8
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 26 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 27 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 28 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 8 25 29 s 10 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 31 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 32 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=33=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 34 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 35 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 36 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 37 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 26
    have hpb : p ≤ 8 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 38 := by omega
      interval_cases r
      · omega  -- r=27=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 26 28 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 33 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 35 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 38 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 38 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 27 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 28 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=29=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 30 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 31 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 26 32 s 11 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 33 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 34 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 36 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 37 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 38 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 38 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 27 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 28 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=31=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 32 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 33 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 34 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 35 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 26 36 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 37 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 38 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 38 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 27 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 28 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 29 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 32 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=33=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 34 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 35 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 38 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
  · -- q = 27
    have hpb : p ≤ 8 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 40 := by omega
      interval_cases r
      · omega  -- r=28=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 27 29 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 34 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 35 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 36 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 27 40 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 27 28 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega  -- r=29=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 30 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 33 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 34 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 36 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 40 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 4
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 28 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 29 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 30 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=31=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 32 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 33 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 34 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 35 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 36 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 37 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 38 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 39 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 40 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 28 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 29 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 31 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=32=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 33 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 34 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 35 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 36 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 27 37 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 27 38 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 39 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 40 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 28 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 29 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 30 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=34=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 35 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 36 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 40 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 8
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 28 24 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 29 24 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 34 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=35=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 36 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 40 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 28
    have hpb : p ≤ 9 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 41 := by omega
      interval_cases r
      · omega  -- r=29=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 28 30 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 31 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 32 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 34 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 35 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 36 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 37 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 38 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 39 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 40 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 41 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 41 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 29 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 30 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=31=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 32 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 33 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 28 34 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 35 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 36 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 38 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 39 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 40 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 41 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 41 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 29 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 30 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 31 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 32 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=33=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 34 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 35 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 36 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 37 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 28 38 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 39 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 40 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 41 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- p = 9
      have hru : r ≤ 41 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 29 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 30 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 31 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 32 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 33 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 34 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 35 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 36 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=37=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 38 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 39 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 40 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 41 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 29
    have hpb : p ≤ 9 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 43 := by omega
      interval_cases r
      · omega  -- r=30=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 29 31 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 32 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 35 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 36 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 37 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 38 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 39 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 40 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 41 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 42 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 29 43 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 29 30 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega  -- r=31=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 32 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 29 33 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 35 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 36 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 38 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 39 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 40 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 41 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 42 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 43 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 30 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 31 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=32=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 33 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 34 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 29 35 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 36 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 38 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 39 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 40 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 41 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 29 42 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 43 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 30 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 29 31 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 32 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=33=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 34 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 35 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 36 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 29 37 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 38 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 39 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 40 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 41 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 42 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 43 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 30 24 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 31 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 33 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=34=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 35 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 36 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 37 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 38 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 29 39 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 40 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 29 41 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 42 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 43 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 6
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 30 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 31 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 6 29 32 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 33 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 34 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=35=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 36 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 37 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 38 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 39 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 40 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 6 29 41 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 42 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 43 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 7
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 30 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 31 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 32 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 35 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=36=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 37 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 38 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 39 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 7 29 40 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 41 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 42 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 7 29 43 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 8
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 30 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 31 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 32 26 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 8 29 33 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 35 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 36 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=37=p+q (diagonal, excluded by hndiag)
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 38 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 39 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 40 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 41 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 42 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 43 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 9
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 30 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 31 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 33 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 34 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 35 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 36 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 37 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega  -- r=38=p+q (diagonal, excluded by hndiag)
      · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 9 29 39 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 40 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 41 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 42 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 43 26 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

/-- **Proposition 11 — indirect core, `q ≥ 18` branch.** Extracts the exceptional
    cone pair (`exceptional_q18`), reconstructs the readout bounds and no-good-time
    fact the `exc_*` kills consume, and dispatches. (Stage 1: routes the whole
    pair to `bhk_prop11_exc_open`; the per-pair `interval_cases` wiring of the 21
    closed kills is added incrementally.) -/
theorem bhk_prop11_core_q18 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq18 : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found w := by
  obtain hF | ⟨g, p, q, r, s, hg_pos, hgp, hgq, hgr, hgs, hcop, hq18', ⟨i, j⟩, hne,
      ⟨k, hk1, hk2⟩, h0, h1β, hc1, hc2, h14⟩ :=
    bhk_prop11_exceptional_q18 w hmono hpos hsum hsmall hq18
  · exact hF
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * (p : ℝ) := by exact_mod_cast hgp
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hgq
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * (r : ℝ) := by exact_mod_cast hgr
  have hp_pos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.mul_zero] at hgp
      have h0' := hpos ⟨0, by omega⟩
      omega
    · exact h
  have h3p : 3 * p < q := by
    have h : g * (3 * p) < g * q := by
      rw [show g * (3 * p) = 3 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  have hrq : q < r := by
    have hw23 : w ⟨2, by omega⟩ < w ⟨3, by omega⟩ := hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega))
    have h : g * q < g * r := by rw [← hgq, ← hgr]; exact hw23
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  obtain hF | hreal := bhk_prop11_v4_le_3_2 w hmono hpos hsum hsmall hq18
  · exact hF
  have hr32 : 2 * r < 3 * q := by
    have hgR : (0:ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
    rw [c3, c2] at hreal
    have hcancel : (g : ℝ) * (2 * (r : ℝ)) < (g : ℝ) * (3 * (q : ℝ)) := by nlinarith [hreal]
    have hR : (2 * (r : ℝ)) < 3 * (q : ℝ) := lt_of_mul_lt_mul_left hcancel hgR.le
    exact_mod_cast hR
  obtain hF | h_nogood : Found w ∨ (∀ l : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) := by
    rw [or_iff_not_imp_right]
    intro hQ
    obtain ⟨l, hl⟩ := not_forall_not.mp hQ
    obtain ⟨hrmem, hpmem⟩ := hl
    set t : ℝ := ((l : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
    have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
    have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (l : ℝ) + 1 / 2 := by rw [htdef]; field_simp
    have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c0, c2]; field_simp
    have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c3, c2]; field_simp
    refine bhk_prop11_no_good_time w hmono hpos hsum hsmall t ?_ ?_ ?_ ?_ ?_
    · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    · rw [e0]; exact hpmem.1
    · rw [e0]; exact hpmem.2
    · rw [e3]; exact hrmem.1
    · rw [e3]; exact hrmem.2
  · exact hF
  -- diagonal configs (`w₃ = w₀ + w₂`, i.e. `r = p + q`) route to Part 6; the rest to the
  -- residual exceptional-pair dispatch.
  by_cases hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩
  · have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
      have h34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
        hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
      exact_mod_cast h34
    exact bhk_prop11_part6 w hpos hsum hsmall hdiag hw34 g p q r s hg_pos hp_pos hq18'
      hgp hgq hgr hgs hcop
  · by_cases h12 : i = 1 ∧ j = 2
    · -- (1, 2)U exceptional pair: peel to the dedicated dispatcher (needs the speeds)
      obtain ⟨hi1, hj2⟩ := h12
      subst hi1; subst hj2
      have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
      have hrs : r < s := by
        have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
          hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
        have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
        exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
      have hrig : 2 * r = 2 * q + p :=
        bhk_prop11_exc_1_2 p q r hp_pos h3p hrq hr32 k hk1 hk2
      exact bhk_prop11_exc_1_2_kill w hmono hpos hsum hsmall g p q r s hg_pos
        (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq18' hrig
    · by_cases h1n2 : i = 1 ∧ j = -2
      · -- (1,-2)S exceptional pair: peel to the dedicated dispatcher (needs the speeds)
        obtain ⟨hi1, hjn2⟩ := h1n2
        subst hi1; subst hjn2
        have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
        have hrs : r < s := by
          have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
            hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
          have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
          exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
        have hrig : 2 * r + p = 3 * q :=
          bhk_prop11_exc_1_neg2 p q r hp_pos h3p hrq hr32 k hk1 hk2
        exact bhk_prop11_exc_1_neg2_kill w hmono hpos hsum hsmall g p q r s hg_pos
          (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq18' hrig
      · by_cases h21 : i = 2 ∧ j = 1
        · -- (2,1) exceptional pair: peel to the pentagon kill (needs the speeds)
          obtain ⟨hi2, hj1⟩ := h21
          subst hi2; subst hj1
          have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
          have hrs : r < s := by
            have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
              hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
            have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
            exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
          have hrig : r = 2 * p + q :=
            bhk_prop11_exc_2_1 p q r hp_pos h3p hrq hr32 k hk1 hk2
          exact bhk_prop11_exc_2_1_pentkill w hmono hpos hsum hsmall g p q r s hg_pos
            (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq18' hrig
        · by_cases hq30 : 30 ≤ q
          · by_cases h42 : i = 4 ∧ j = 2
            · -- (4,2) exceptional pair: c-split, both branches pentagon-killed (q ≥ 30)
              obtain ⟨hi4, hj2⟩ := h42
              subst hi4; subst hj2
              have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
              have hrs : r < s := by
                have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
                  hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
                have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
                exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
              rcases bhk_prop11_exc_4_2 p q r hp_pos h3p hrq hr32 k hk1 hk2 with hrig | hrig2
              · exact bhk_prop11_exc_2_1_pentkill w hmono hpos hsum hsmall g p q r s hg_pos
                  (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs (by omega) hrig
              · exact bhk_prop11_exc_4_2_c1_pentkill w hmono hpos hsum hsmall g p q r s hg_pos
                  (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq30 hrig2
            · exact False.elim <| bhk_prop11_exc_open p q r hq30 hcop hp_pos h3p hrq hr32 i j k h0 h1β hc1 hc2 hne
                hk1 hk2 h_nogood h14 h12 h1n2 h21 h42 (fun h => hdiag (by rw [hgr, hgp, hgq, h]; ring))
          · have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
            have hrs : r < s := by
              have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
                hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
              have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
              exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
            exact bhk_prop11_exc_q_18_30 w hmono hpos hsum hsmall g p q r s hg_pos hq18'
              (by omega) hcop hp_pos h3p hrq hr32 hrs
              (fun h => hdiag (by rw [hgr, hgp, hgq, h]; ring)) c0 c2 c3 c4 h_nogood

/-- **Diagonal `s`-upper-bound engine (BHK 5.2.12 "Step A").** If `[a, b]` is a
    `0123`-gap (runners `0,1,2,3` all `≥ 1/6` from the origin throughout), then the
    covering assumption forces `[a, b] ⊆ unsafeOf w₄`, and `not_subset_unsafeOf`
    bounds the gap length: `b - a ≤ 1/(3 w₄)`. -/
lemma bhk_diag_sbound (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (a b : ℝ) (hab : a ≤ b)
    (h0 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * τ))
    (h1 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * τ))
    (h2 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * τ))
    (h3 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * τ)) : Found w ∨
      (b - a ≤ 1 / (3 * (w ⟨4, by omega⟩ : ℝ))) := by
  rw [or_iff_not_imp_right]
  intro hcon
  push_neg at hcon
  -- a point of `[a, b]` outside runner 5's zone: every runner is clear there
  obtain ⟨τ, hτ, hτ4⟩ := Set.not_subset.mp
    (bhk_prop11_not_subset_unsafeOf w ⟨4, by omega⟩ (hpos _) hab hcon)
  rw [mem_unsafeOf_iff, not_lt] at hτ4
  refine ⟨τ, fun i => ?_⟩
  fin_cases i
  · exact h0 τ hτ
  · exact h1 τ hτ
  · exact h2 τ hτ
  · exact h3 τ hτ
  · exact hτ4

/-- **Lonely-time contradiction (5 runners, BHK 5.2.12 "Step B").** If at a single
    time `τ` every runner sits in `[1/6, 5/6]` of the circle (`wᵢτ = Kᵢ + fᵢ`,
    `fᵢ ∈ [1/6, 5/6]`), then `circDist (wᵢτ) ≥ 1/6` for all `i`, contradicting the
    covering assumption. -/
lemma bhk_lonely5 (w : Fin 5 → ℕ)
    (τ : ℝ)
    (f0 f1 f2 f3 f4 : ℝ) (K0 K1 K2 K3 K4 : ℤ)
    (e0 : (w ⟨0, by omega⟩ : ℝ) * τ = (K0 : ℝ) + f0)
    (e1 : (w ⟨1, by omega⟩ : ℝ) * τ = (K1 : ℝ) + f1)
    (e2 : (w ⟨2, by omega⟩ : ℝ) * τ = (K2 : ℝ) + f2)
    (e3 : (w ⟨3, by omega⟩ : ℝ) * τ = (K3 : ℝ) + f3)
    (e4 : (w ⟨4, by omega⟩ : ℝ) * τ = (K4 : ℝ) + f4)
    (h0 : f0 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6)) (h1 : f1 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6))
    (h2 : f2 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6)) (h3 : f3 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6))
    (h4 : f4 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6)) : Found w := by
  have key : ∀ (j : Fin 5) (K : ℤ) (f : ℝ), (w j : ℝ) * τ = (K : ℝ) + f →
      f ∈ Set.Icc (1 / 6 : ℝ) (5 / 6) → 1 / 6 ≤ circDist ((w j : ℝ) * τ) := by
    intro j K f he hf
    obtain ⟨hl, hh⟩ := hf
    have hfr : Int.fract ((w j : ℝ) * τ) = f := by
      rw [he, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [circDist, hfr]; exact le_min hl (by linarith)
  obtain hF | ⟨i, hi⟩ := found_or_blocked w τ
  · exact hF
  fin_cases i
  · exact absurd hi (not_lt.mpr (key ⟨0, by omega⟩ K0 f0 e0 h0))
  · exact absurd hi (not_lt.mpr (key ⟨1, by omega⟩ K1 f1 e1 h1))
  · exact absurd hi (not_lt.mpr (key ⟨2, by omega⟩ K2 f2 e2 h2))
  · exact absurd hi (not_lt.mpr (key ⟨3, by omega⟩ K3 f3 e3 h3))
  · exact absurd hi (not_lt.mpr (key ⟨4, by omega⟩ K4 f4 e4 h4))

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12.3 — the diagonal `(p, q, r) = (1, 7, 8)`.** Speeds
    `w₀ = g, w₁ = 6g, w₂ = 7g, w₃ = 8g, w₄ = sg`, diagonal `v₄ = 8/7`.
    **Step A (`s ≤ 9`):** the interval `[7/(36g), 11/(48g)]` (BHK's
    `[7/6 + x₂/6, 7/6 + x₄/2]` in `t = w₂τ` time) is a `0123`-gap — runners
    `0,1,2,3` stay in `[1/6, 5/6]` throughout — so the cover forces it into
    `unsafeOf w₄`; `not_subset_unsafeOf` bounds its length `5/(144g) ≤ 1/(3·gs)`,
    i.e. `s ≤ 9`. With `s > r = 8` this pins `s = 9`. **Step B:** `τ₁ = 1/(5g)` is
    then a lonely time (positions `1/5, 1/5, 2/5, 3/5, 4/5`), contradicting cover. -/
lemma bhk_prop11_exc_diag_1_7 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 8 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 7)
    (hw3 : w ⟨3, by omega⟩ = g * 8) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 6 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 6 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 7 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 8 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  -- ===== Step A: s ≤ 9 via the 0123-gap interval [a, b] =====
  set a : ℝ := (7 : ℝ) / (36 * (g : ℝ)) with ha
  set b : ℝ := (11 : ℝ) / (48 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (11 : ℝ) / (48 * g) - 7 / (36 * g) = 5 / (144 * g) := by field_simp <;> ring
    rw [hid]; positivity
  -- generic "runner i stays in [1/6, 5/6] on [a, b]" via affine no-wrap
  have away : ∀ (i : Fin 5) (K : ℤ) (fa fb : ℝ),
      (w i : ℝ) * a = (K : ℝ) + fa → (w i : ℝ) * b = (K : ℝ) + fb →
      1 / 6 ≤ fa → fb ≤ 5 / 6 → fa ≤ fb →
      ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w i : ℝ) * τ) := by
    intro i K fa fb hA hB hfa hfb _ τ hτ
    obtain ⟨hτa, hτb⟩ := hτ
    have hwi : (0 : ℝ) ≤ (w i : ℝ) := by positivity
    have hm1 : (w i : ℝ) * a ≤ (w i : ℝ) * τ := mul_le_mul_of_nonneg_left hτa hwi
    have hm2 : (w i : ℝ) * τ ≤ (w i : ℝ) * b := mul_le_mul_of_nonneg_left hτb hwi
    have hlo : (K : ℝ) ≤ (w i : ℝ) * τ := by rw [hA] at hm1; linarith
    have hhi : (w i : ℝ) * τ < (K : ℝ) + 1 := by rw [hB] at hm2; linarith
    have hfloor : ⌊(w i : ℝ) * τ⌋ = K := by rw [Int.floor_eq_iff]; exact ⟨hlo, hhi⟩
    have hfr : Int.fract ((w i : ℝ) * τ) = (w i : ℝ) * τ - (K : ℝ) := by
      rw [Int.fract, hfloor]
    have hfrlo : 1 / 6 ≤ (w i : ℝ) * τ - (K : ℝ) := by rw [hA] at hm1; linarith
    have hfrhi : (w i : ℝ) * τ - (K : ℝ) ≤ 5 / 6 := by rw [hB] at hm2; linarith
    rw [circDist, hfr]; exact le_min hfrlo (by linarith)
  have aw0 := away ⟨0, by omega⟩ 0 (7 / 36) (11 / 48)
    (by rw [c0, ha]; push_cast; field_simp <;> ring) (by rw [c0, hb]; push_cast; field_simp <;> ring)
    (by norm_num) (by norm_num) (by norm_num)
  have aw1 := away ⟨1, by omega⟩ 1 (1 / 6) (3 / 8)
    (by rw [c1, ha]; push_cast; field_simp <;> ring) (by rw [c1, hb]; push_cast; field_simp <;> ring)
    (by norm_num) (by norm_num) (by norm_num)
  have aw2 := away ⟨2, by omega⟩ 1 (13 / 36) (29 / 48)
    (by rw [c2, ha]; push_cast; field_simp <;> ring) (by rw [c2, hb]; push_cast; field_simp <;> ring)
    (by norm_num) (by norm_num) (by norm_num)
  have aw3 := away ⟨3, by omega⟩ 1 (5 / 9) (5 / 6)
    (by rw [c3, ha]; push_cast; field_simp <;> ring) (by rw [c3, hb]; push_cast; field_simp <;> ring)
    (by norm_num) (by norm_num) (by norm_num)
  rcases found_or_blocked_on w (Set.Icc a b) with hF | hblk
  · exact hF
  have hsub : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩ := by
    intro τ hτ
    rw [mem_unsafeOf_iff]
    obtain ⟨i, hi⟩ := hblk τ hτ
    fin_cases i
    · exact absurd hi (not_lt.mpr (aw0 τ hτ))
    · exact absurd hi (not_lt.mpr (aw1 τ hτ))
    · exact absurd hi (not_lt.mpr (aw2 τ hτ))
    · exact absurd hi (not_lt.mpr (aw3 τ hτ))
    · exact hi
  have hs9 : s ≤ 9 := by
    by_contra hcon
    have hs10 : (10 : ℝ) ≤ s := by exact_mod_cast (by omega : 10 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    have hlong : 1 / (3 * (w ⟨4, by omega⟩ : ℝ)) < b - a := by
      rw [c4]
      have hba : b - a = 5 / (144 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
      rw [hba, ← sub_pos]
      have hid : (5 : ℝ) / (144 * g) - 1 / (3 * (g * s)) = (15 * s - 144) / (432 * g * s) := by
        field_simp <;> ring
      rw [hid]; apply div_pos (by nlinarith [hs10]) (by positivity)
    exact (bhk_prop11_not_subset_unsafeOf w ⟨4, by omega⟩ (hpos _) hab hlong) hsub
  have hs9eq : s = 9 := by omega
  subst hs9eq
  -- ===== Step B: τ₁ = 1/(5g) is lonely (positions 1/5, 1/5, 2/5, 3/5, 4/5) =====
  have cdfr : ∀ (x f : ℝ), Int.fract x = f → 1 / 6 ≤ f → f ≤ 5 / 6 → 1 / 6 ≤ circDist x := by
    intro x f hf hlo hhi; rw [circDist, hf]; exact le_min hlo (by linarith)
  have mkfr : ∀ (x f : ℝ) (n : ℤ), x = (n : ℝ) + f → 0 ≤ f → f < 1 → Int.fract x = f := by
    intro x f n hx h0 h1; rw [hx, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨h0, h1⟩]
  set τ₁ : ℝ := 1 / (5 * (g : ℝ)) with hτ₁
  have e0 : (w ⟨0, by omega⟩ : ℝ) * τ₁ = 1 / 5 := by rw [c0, hτ₁]; field_simp <;> ring
  have e1 : (w ⟨1, by omega⟩ : ℝ) * τ₁ = 6 / 5 := by rw [c1, hτ₁]; field_simp <;> ring
  have e2 : (w ⟨2, by omega⟩ : ℝ) * τ₁ = 7 / 5 := by rw [c2, hτ₁]; field_simp <;> ring
  have e3 : (w ⟨3, by omega⟩ : ℝ) * τ₁ = 8 / 5 := by rw [c3, hτ₁]; field_simp <;> ring
  have e4 : (w ⟨4, by omega⟩ : ℝ) * τ₁ = 9 / 5 := by rw [c4, hτ₁]; field_simp <;> ring
  have d0 : 1 / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * τ₁) :=
    cdfr _ (1 / 5) (by rw [e0]; exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩)
      (by norm_num) (by norm_num)
  have d1 : 1 / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * τ₁) :=
    cdfr _ (1 / 5) (mkfr _ (1 / 5) 1 (by rw [e1]; norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have d2 : 1 / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * τ₁) :=
    cdfr _ (2 / 5) (mkfr _ (2 / 5) 1 (by rw [e2]; norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have d3 : 1 / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * τ₁) :=
    cdfr _ (3 / 5) (mkfr _ (3 / 5) 1 (by rw [e3]; norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  have d4 : 1 / 6 ≤ circDist ((w ⟨4, by omega⟩ : ℝ) * τ₁) :=
    cdfr _ (4 / 5) (mkfr _ (4 / 5) 1 (by rw [e4]; norm_num) (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
  obtain hF | ⟨i, hi⟩ := found_or_blocked w τ₁
  · exact hF
  fin_cases i
  · exact absurd hi (not_lt.mpr d0)
  · exact absurd hi (not_lt.mpr d1)
  · exact absurd hi (not_lt.mpr d2)
  · exact absurd hi (not_lt.mpr d3)
  · exact absurd hi (not_lt.mpr d4)

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12.5 — the diagonal `(p, q, r) = (1, 12, 13)`.** Speeds
    `w₀ = g, w₁ = 11g, w₂ = 12g, w₃ = 13g, w₄ = sg`, `v₄ = 13/12`. **Step A:** the
    `0123`-gap `[13/(66g), 17/(78g)]` (BHK's `[2 + x₂/3, 2 + 2x₄/3]`) bounds
    `s ≤ 15`; with `s > r = 13` this leaves `s ∈ {14, 15}`. **Step B:** `τ₁ = 1/(5g)`
    is lonely for `s = 14` (positions `1/5,1/5,2/5,3/5,4/5`); `τ₁ = 3/(14g)` for
    `s = 15` (positions `3/14,5/14,4/7,11/14,3/14`). -/
lemma bhk_prop11_exc_diag_1_12 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 13 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 12)
    (hw3 : w ⟨3, by omega⟩ = g * 13) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 11 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 11 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 12 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 13 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (13 : ℝ) / (66 * (g : ℝ)) with ha
  set b : ℝ := (17 : ℝ) / (78 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (17 : ℝ) / (78 * g) - 13 / (66 * g) = 3 / (143 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (13 / 66) (17 / 78)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 2 (1 / 6) (31 / 78)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 2 (4 / 11) (8 / 13)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 2 (37 / 66) (5 / 6)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
  · exact hF
  have hs15 : s ≤ 15 := by
    by_contra hcon
    have hs16 : (16 : ℝ) ≤ s := by exact_mod_cast (by omega : 16 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 3 / (143 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (3 : ℝ) / (143 * g) - 1 / (3 * (g * s)) = (9 * s - 143) / (429 * g * s) := by
      field_simp <;> ring
    have hd : (0 : ℝ) < 3 / (143 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hs16]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely5 w (1 / (5 * (g : ℝ))) (1 / 5) (1 / 5) (2 / 5) (3 / 5) (4 / 5)
      0 2 2 2 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (3 / (14 * (g : ℝ))) (3 / 14) (5 / 14) (4 / 7) (11 / 14) (3 / 14)
      0 2 2 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12.1 — the diagonal `(p, q, r) = (1, 5, 6)`.** Speeds
    `w₀ = g, w₁ = 4g, w₂ = 5g, w₃ = 6g, w₄ = sg`, `v₄ = 6/5`. **Step A:** the
    `0123`-gap `[13/(24g), 17/(30g)]` (BHK's `[5/2 + x₂/6, 5/2 + 1/3]`) bounds
    `s ≤ 13`; with `s > r = 6` this leaves `s ∈ {7,…,13}`. **Step B:** each value
    has an explicit lonely time (`τ₁ = 4/(11g), 4/(9g), 3/(10g)` cyclically). -/
lemma bhk_prop11_exc_diag_1_5 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 6 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 5)
    (hw3 : w ⟨3, by omega⟩ = g * 6) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 4 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 4 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 5 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 6 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (13 : ℝ) / (24 * (g : ℝ)) with ha
  set b : ℝ := (17 : ℝ) / (30 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (17 : ℝ) / (30 * g) - 13 / (24 * g) = 1 / (40 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (13 / 24) (17 / 30)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 2 (1 / 6) (4 / 15)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 2 (17 / 24) (5 / 6)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 3 (1 / 4) (2 / 5)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
  · exact hF
  have hs13 : s ≤ 13 := by
    by_contra hcon
    have hs14 : (14 : ℝ) ≤ s := by exact_mod_cast (by omega : 14 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 1 / (40 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (1 : ℝ) / (40 * g) - 1 / (3 * (g * s)) = (3 * s - 40) / (120 * g * s) := by
      field_simp <;> ring
    have hd : (0 : ℝ) < 1 / (40 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hs14]) (by positivity)
    linarith
  interval_cases s
  · -- s = 7, τ₁ = 4/(11g)
    exact bhk_lonely5 w (4 / (11 * (g : ℝ))) (4 / 11) (5 / 11) (9 / 11) (2 / 11) (6 / 11)
      0 1 1 2 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- s = 8, τ₁ = 4/(9g)
    exact bhk_lonely5 w (4 / (9 * (g : ℝ))) (4 / 9) (7 / 9) (2 / 9) (2 / 3) (5 / 9)
      0 1 2 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- s = 9, τ₁ = 3/(10g)
    exact bhk_lonely5 w (3 / (10 * (g : ℝ))) (3 / 10) (1 / 5) (1 / 2) (4 / 5) (7 / 10)
      0 1 1 1 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- s = 10, τ₁ = 4/(9g)
    exact bhk_lonely5 w (4 / (9 * (g : ℝ))) (4 / 9) (7 / 9) (2 / 9) (2 / 3) (4 / 9)
      0 1 2 2 4 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- s = 11, τ₁ = 3/(10g)
    exact bhk_lonely5 w (3 / (10 * (g : ℝ))) (3 / 10) (1 / 5) (1 / 2) (4 / 5) (3 / 10)
      0 1 1 1 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- s = 12, τ₁ = 4/(9g)
    exact bhk_lonely5 w (4 / (9 * (g : ℝ))) (4 / 9) (7 / 9) (2 / 9) (2 / 3) (1 / 3)
      0 1 2 2 5 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- s = 13, τ₁ = 4/(9g)
    exact bhk_lonely5 w (4 / (9 * (g : ℝ))) (4 / 9) (7 / 9) (2 / 9) (2 / 3) (7 / 9)
      0 1 2 2 5 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12.2 — the diagonal `(p, q, r) = (1, 6, 7)`.** Speeds
    `w₀ = g, w₁ = 5g, w₂ = 6g, w₃ = 7g, w₄ = sg`. `0123`-gap `[7/(30g), 11/(42g)]`
    bounds `s ≤ 11`; `s > r = 7` leaves `s ∈ {8,…,11}`, each with a lonely time. -/
lemma bhk_prop11_exc_diag_1_6 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 7 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 6)
    (hw3 : w ⟨3, by omega⟩ = g * 7) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 5 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 5 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 6 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 7 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (7 : ℝ) / (30 * (g : ℝ)) with ha
  set b : ℝ := (11 : ℝ) / (42 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (11 : ℝ) / (42 * g) - 7 / (30 * g) = 1 / (35 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (7 / 30) (11 / 42)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 1 (1 / 6) (13 / 42)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 1 (2 / 5) (4 / 7)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 1 (19 / 30) (5 / 6)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
  · exact hF
  have hs11 : s ≤ 11 := by
    by_contra hcon
    have hs12 : (12 : ℝ) ≤ s := by exact_mod_cast (by omega : 12 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 1 / (35 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (1 : ℝ) / (35 * g) - 1 / (3 * (g * s)) = (3 * s - 35) / (105 * g * s) := by
      field_simp <;> ring
    have hd : (0 : ℝ) < 1 / (35 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hs12]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely5 w (5 / (11 * (g : ℝ))) (5 / 11) (3 / 11) (8 / 11) (2 / 11) (7 / 11)
      0 2 2 3 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 4)
      0 1 1 1 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 2)
      0 1 1 1 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (3 / 4)
      0 1 1 1 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12 `(p, q, r) = (2, 7, 9)`** (the `p = 2`, `q = 7` diagonal).
    Speeds `w₀ = 2g, w₁ = 5g, w₂ = 7g, w₃ = 9g, w₄ = sg`. `0123`-gap
    `[13/(54g), 11/(42g)]` bounds `s ≤ 15`; `s > r = 9` leaves `s ∈ {10,…,15}`,
    each with a lonely time. -/
lemma bhk_prop11_exc_diag_2_7 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 9 < s)
    (hw0 : w ⟨0, by omega⟩ = g * 2) (hw2 : w ⟨2, by omega⟩ = g * 7)
    (hw3 : w ⟨3, by omega⟩ = g * 9) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 5 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * 2 := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 5 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 7 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 9 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (13 : ℝ) / (54 * (g : ℝ)) with ha
  set b : ℝ := (11 : ℝ) / (42 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (11 : ℝ) / (42 * g) - 13 / (54 * g) = 4 / (189 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (13 / 27) (11 / 21)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 1 (11 / 54) (13 / 42)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 1 (37 / 54) (5 / 6)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 2 (1 / 6) (5 / 14)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
  · exact hF
  have hs15 : s ≤ 15 := by
    by_contra hcon
    have hs16 : (16 : ℝ) ≤ s := by exact_mod_cast (by omega : 16 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 4 / (189 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (4 : ℝ) / (189 * g) - 1 / (3 * (g * s)) = (4 * s - 63) / (189 * g * s) := by
      field_simp <;> ring
    have hd : (0 : ℝ) < 4 / (189 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hs16]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 2) (1 / 4) (3 / 4) (1 / 4) (1 / 2)
      0 1 1 2 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 2) (1 / 4) (3 / 4) (1 / 4) (3 / 4)
      0 1 1 2 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (4 / (11 * (g : ℝ))) (8 / 11) (9 / 11) (6 / 11) (3 / 11) (4 / 11)
      0 1 2 3 4 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 2) (1 / 4) (3 / 4) (1 / 4) (1 / 4)
      0 1 1 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 2) (1 / 4) (3 / 4) (1 / 4) (1 / 2)
      0 1 1 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 2) (1 / 4) (3 / 4) (1 / 4) (3 / 4)
      0 1 1 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12 `(p, q, r) = (2, 9, 11)`** (the `p = 2`, `q = 9` diagonal).
    Speeds `w₀ = 2g, w₁ = 7g, w₂ = 9g, w₃ = 11g, w₄ = sg`. `0123`-gap
    `[25/(66g), 17/(42g)]` bounds `s ≤ 12`; `s > r = 11` forces `s = 12`, lonely at
    `τ₁ = 1/(5g)`. -/
lemma bhk_prop11_exc_diag_2_9 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 11 < s)
    (hw0 : w ⟨0, by omega⟩ = g * 2) (hw2 : w ⟨2, by omega⟩ = g * 9)
    (hw3 : w ⟨3, by omega⟩ = g * 11) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 7 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * 2 := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 7 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 9 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 11 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (25 : ℝ) / (66 * (g : ℝ)) with ha
  set b : ℝ := (17 : ℝ) / (42 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (17 : ℝ) / (42 * g) - 25 / (66 * g) = 2 / (77 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (25 / 33) (17 / 21)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 2 (43 / 66) (5 / 6)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 3 (9 / 22) (9 / 14)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 4 (1 / 6) (19 / 42)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
  · exact hF
  have hs12 : s ≤ 12 := by
    by_contra hcon
    have hs13 : (13 : ℝ) ≤ s := by exact_mod_cast (by omega : 13 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 2 / (77 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (2 : ℝ) / (77 * g) - 1 / (3 * (g * s)) = (6 * s - 77) / (231 * g * s) := by
      field_simp <;> ring
    have hd : (0 : ℝ) < 2 / (77 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hs13]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely5 w (1 / (5 * (g : ℝ))) (2 / 5) (2 / 5) (4 / 5) (1 / 5) (2 / 5)
      0 1 1 2 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12 `(p, q, r) = (1, 10, 11)`** (`p = 1`, `q = 10`; BHK closes
    this `q ∈ {10,13,15}` value via Claims 19/21). Speeds
    `w₀ = g, w₁ = 9g, w₂ = 10g, w₃ = 11g, w₄ = sg`. `0123`-gap `[13/(54g), 17/(66g)]`
    bounds `s ≤ 19`; `s > r = 11` leaves `s ∈ {12,…,19}`, each with a lonely time. -/
lemma bhk_prop11_exc_diag_1_10 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 11 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 10)
    (hw3 : w ⟨3, by omega⟩ = g * 11) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 9 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 9 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 10 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 11 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (13 : ℝ) / (54 * (g : ℝ)) with ha
  set b : ℝ := (17 : ℝ) / (66 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (17 : ℝ) / (66 * g) - 13 / (54 * g) = 5 / (297 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (13 / 54) (17 / 66)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 2 (1 / 6) (7 / 22)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 2 (11 / 27) (19 / 33)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 2 (35 / 54) (5 / 6)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
  · exact hF
  have hs19 : s ≤ 19 := by
    by_contra hcon
    have hs20 : (20 : ℝ) ≤ s := by exact_mod_cast (by omega : 20 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 5 / (297 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (5 : ℝ) / (297 * g) - 1 / (3 * (g * s)) = (15 * s - 297) / (891 * g * s) := by
      field_simp <;> ring
    have hd : (0 : ℝ) < 5 / (297 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hs20]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely5 w (8 / (17 * (g : ℝ))) (8 / 17) (4 / 17) (12 / 17) (3 / 17) (11 / 17)
      0 4 4 5 5 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 4)
      0 2 2 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 2)
      0 2 2 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (3 / 4)
      0 2 2 2 3 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 2) (2 / 3) (5 / 6) (2 / 3)
      0 1 1 1 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 4)
      0 2 2 2 4 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 2)
      0 2 2 2 4 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely5 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (3 / 4)
      0 2 2 2 4 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **BHK Case 5.2.12.4 — the diagonal `(p, q, r) = (1, 9, 10)`.** Speeds
    `w₀ = g, w₁ = 8g, w₂ = 9g, w₃ = 10g, w₄ = sg` with `v₄ = 10/9` (diagonal) and
    `s > 10`. **Step A:** at `τ = 1/(6g)` (BHK's `t = 3/2`) runners 0–3 sit at
    `1/6, 1/3, 1/2, 2/3` (all `circDist ≥ 1/6`), so the cover forces runner 4 near
    the origin, `circDist(s/6) < 1/6`, i.e. `6 ∣ s`. **Step B:** then
    `τ₁ = (s+1)/(6sg)` is a lonely time — runner 4 sits at `(s+1)/6`, which has
    fractional part `1/6` exactly (as `6 ∣ s`), and the other four are bounded away
    using `s ≥ 12`. No upper bound on `s` is needed (sharper than BHK's gap). -/
lemma bhk_prop11_exc_diag_1_9 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 10 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 9)
    (hw3 : w ⟨3, by omega⟩ = g * 10) (hw4 : w ⟨4, by omega⟩ = g * s) : Found w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hw1 : w ⟨1, by omega⟩ = g * 8 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 8 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 9 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 10 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  have cdfr : ∀ (x f : ℝ), Int.fract x = f → 1 / 6 ≤ f → f ≤ 5 / 6 → 1 / 6 ≤ circDist x := by
    intro x f hf hlo hhi; rw [circDist, hf]; exact le_min hlo (by linarith)
  have mkfr : ∀ (x f : ℝ) (n : ℤ), x = (n : ℝ) + f → 0 ≤ f → f < 1 → Int.fract x = f := by
    intro x f n hx h0 h1; rw [hx, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨h0, h1⟩]
  -- ===== Step A: 6 ∣ s, read at τ = 1/(6g) =====
  obtain hF | ⟨i, hi⟩ := found_or_blocked w (1 / (6 * (g : ℝ)))
  · exact hF
  have h6s : s % 6 = 0 := by
    set τ : ℝ := 1 / (6 * (g : ℝ)) with hτ
    have e0 : (w ⟨0, by omega⟩ : ℝ) * τ = 1 / 6 := by rw [c0, hτ]; field_simp
    have e1 : (w ⟨1, by omega⟩ : ℝ) * τ = 4 / 3 := by rw [c1, hτ]; field_simp; ring
    have e2 : (w ⟨2, by omega⟩ : ℝ) * τ = 3 / 2 := by rw [c2, hτ]; field_simp; ring
    have e3 : (w ⟨3, by omega⟩ : ℝ) * τ = 5 / 3 := by rw [c3, hτ]; field_simp; ring
    have e4 : (w ⟨4, by omega⟩ : ℝ) * τ = (s : ℝ) / 6 := by rw [c4, hτ]; field_simp
    have s0 : 1 / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * τ) :=
      cdfr _ (1 / 6) (by rw [e0]; exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩)
        (by norm_num) (by norm_num)
    have s1 : 1 / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * τ) :=
      cdfr _ (1 / 3) (mkfr _ (1 / 3) 1 (by rw [e1]; norm_num) (by norm_num) (by norm_num))
        (by norm_num) (by norm_num)
    have s2 : 1 / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * τ) :=
      cdfr _ (1 / 2) (mkfr _ (1 / 2) 1 (by rw [e2]; norm_num) (by norm_num) (by norm_num))
        (by norm_num) (by norm_num)
    have s3 : 1 / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * τ) :=
      cdfr _ (2 / 3) (mkfr _ (2 / 3) 1 (by rw [e3]; norm_num) (by norm_num) (by norm_num))
        (by norm_num) (by norm_num)
    have hcd4 : circDist ((w ⟨4, by omega⟩ : ℝ) * τ) < 1 / 6 := by
      fin_cases i
      · exact absurd hi (not_lt.mpr s0)
      · exact absurd hi (not_lt.mpr s1)
      · exact absurd hi (not_lt.mpr s2)
      · exact absurd hi (not_lt.mpr s3)
      · exact hi
    rw [e4] at hcd4
    have hfr : Int.fract ((s : ℝ) / 6) = ((s % 6 : ℕ) : ℝ) / 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) from by norm_num]
      exact Int.fract_div_natCast_eq_div_natCast_mod
    rw [circDist, hfr] at hcd4
    have hk6 : s % 6 < 6 := Nat.mod_lt _ (by norm_num)
    rcases min_lt_iff.mp hcd4 with h | h
    · have h1 : ((s % 6 : ℕ) : ℝ) < 1 := by linarith
      have : s % 6 < 1 := by exact_mod_cast h1
      omega
    · have h1 : (5 : ℝ) < ((s % 6 : ℕ) : ℝ) := by linarith
      have : 5 < s % 6 := by exact_mod_cast h1
      omega
  -- ===== Step B: τ₁ = (s+1)/(6sg) is lonely =====
  obtain ⟨m, hm⟩ : 6 ∣ s := Nat.dvd_of_mod_eq_zero h6s
  have hs12 : 12 ≤ s := by omega
  have hs12R : (12 : ℝ) ≤ s := by exact_mod_cast hs12
  have hmR : (s : ℝ) = 6 * (m : ℝ) := by exact_mod_cast hm
  set τ₁ : ℝ := ((s : ℝ) + 1) / (6 * (s : ℝ) * (g : ℝ)) with hτ₁
  have d0 : 1 / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * τ₁) := by
    refine cdfr _ (((s : ℝ) + 1) / (6 * s)) (mkfr _ _ 0 ?_ ?_ ?_) ?_ ?_
    · rw [c0, hτ₁]; push_cast; field_simp; ring
    · positivity
    · rw [div_lt_one (by positivity)]; nlinarith [hsR]
    · rw [le_div_iff₀ (by positivity)]; nlinarith [hsR]
    · rw [div_le_iff₀ (by positivity)]; nlinarith [hsR]
  have d1 : 1 / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * τ₁) := by
    refine cdfr _ (((s : ℝ) + 4) / (3 * s)) (mkfr _ _ 1 ?_ ?_ ?_) ?_ ?_
    · rw [c1, hτ₁]; push_cast; field_simp; ring
    · positivity
    · rw [div_lt_one (by positivity)]; nlinarith [hsR]
    · rw [le_div_iff₀ (by positivity)]; nlinarith [hsR]
    · rw [div_le_iff₀ (by positivity)]; nlinarith [hsR, hs12R]
  have d2 : 1 / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * τ₁) := by
    refine cdfr _ (((s : ℝ) + 3) / (2 * s)) (mkfr _ _ 1 ?_ ?_ ?_) ?_ ?_
    · rw [c2, hτ₁]; push_cast; field_simp; ring
    · positivity
    · rw [div_lt_one (by positivity)]; nlinarith [hsR]
    · rw [le_div_iff₀ (by positivity)]; nlinarith [hsR]
    · rw [div_le_iff₀ (by positivity)]; nlinarith [hsR, hs12R]
  have d3 : 1 / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * τ₁) := by
    refine cdfr _ ((2 * (s : ℝ) + 5) / (3 * s)) (mkfr _ _ 1 ?_ ?_ ?_) ?_ ?_
    · rw [c3, hτ₁]; push_cast; field_simp; ring
    · positivity
    · rw [div_lt_one (by positivity)]; nlinarith [hsR]
    · rw [le_div_iff₀ (by positivity)]; nlinarith [hsR]
    · rw [div_le_iff₀ (by positivity)]; nlinarith [hsR, hs12R]
  have d4 : 1 / 6 ≤ circDist ((w ⟨4, by omega⟩ : ℝ) * τ₁) := by
    have hmne : (m : ℝ) ≠ 0 := by
      have : 0 < m := by omega
      positivity
    refine cdfr _ (1 / 6) (mkfr _ (1 / 6) (m : ℤ) ?_ (by norm_num) (by norm_num))
      (by norm_num) (by norm_num)
    rw [c4, hτ₁, hmR]; push_cast; field_simp
  obtain hF | ⟨i, hi⟩ := found_or_blocked w τ₁
  · exact hF
  fin_cases i
  · exact absurd hi (not_lt.mpr d0)
  · exact absurd hi (not_lt.mpr d1)
  · exact absurd hi (not_lt.mpr d2)
  · exact absurd hi (not_lt.mpr d3)
  · exact absurd hi (not_lt.mpr d4)

set_option maxHeartbeats 12000000 in
/-- **Proposition 11 — indirect core, `q < 18` branch.** The complementary finite
    case `q = w₂/gcd(w₀,w₂) < 18`: closed by the per-`(p,q)` analysis of BHK's
    Lemma 18 / Table 1 for `q ∈ {5,…,17}` (`q ≥ 5` from `bhk_prop11_lemma13`).

    The extraction (`g, p, q, r, s` via Lemma 17, `q ∈ [5,17]`, `3p < q`,
    `gcd(p,q)=1`, `q < r < 2q` via Cor 16, `r < s`, the rectangle `h_nogood`) is
    complete; the residual `sorry` is the finite `(p,q,r)` dispatch. Every triple
    `(p,q,r)` with `q ∈ {5..17}`, `q < r < 2q` falls into exactly one of:
    diagonal `r = p+q` → `bhk_prop11_part6`; coset hits `R` → `bhk_prop11_exc_Rkill`
    (witness `m` from `experiments/core_q_lt_18_derisk_v2.py`); coset hits `P` →
    `bhk_prop11_exc_Pkill` (witness from `..._pkill_design_v2.py`); or `v₄` exceeds
    the Lemma-18 bound → `bhk_prop11_v4_bound_witness` (per-`(p,q)` `ρ`, witness from
    `..._table1_check_v1.py`). De-risk confirms 0 residual cases (no `gcd(r,q)=1`
    needed). -/
theorem bhk_prop11_core_q_lt_18 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq : w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) < 18) : Found w := by
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgw0 : g ∣ w ⟨0, by omega⟩ := Nat.gcd_dvd_left _ _
  have hgw2 : g ∣ w ⟨2, by omega⟩ := Nat.gcd_dvd_right _ _
  obtain hF | ⟨hgw3, hgw4⟩ := bhk_prop11_lemma17_uncond w hmono hpos hsum hsmall
  · exact hF
  set p : ℕ := w ⟨0, by omega⟩ / g with hpdef
  set q : ℕ := w ⟨2, by omega⟩ / g with hqdef
  set r : ℕ := w ⟨3, by omega⟩ / g with hrdef
  set s : ℕ := w ⟨4, by omega⟩ / g with hsdef
  have hgp : w ⟨0, by omega⟩ = g * p := (Nat.mul_div_cancel' hgw0).symm
  have hgq : w ⟨2, by omega⟩ = g * q := (Nat.mul_div_cancel' hgw2).symm
  have hgr : w ⟨3, by omega⟩ = g * r := (Nat.mul_div_cancel' hgw3).symm
  have hgs : w ⟨4, by omega⟩ = g * s := (Nat.mul_div_cancel' hgw4).symm
  have hcop : Nat.Coprime p q := Nat.coprime_div_gcd_div_gcd hg_pos
  obtain hF | (hq5 : 5 ≤ q) := bhk_prop11_lemma13 w hmono hpos hsum hsmall
  · exact hF
  have hq17 : q < 18 := hq
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * (p : ℝ) := by exact_mod_cast hgp
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hgq
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * (r : ℝ) := by exact_mod_cast hgr
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
  have hp_pos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.mul_zero] at hgp; have h0' := hpos ⟨0, by omega⟩; omega
    · exact h
  have h3p : 3 * p < q := by
    have h : g * (3 * p) < g * q := by
      rw [show g * (3 * p) = 3 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  have hrq : q < r := by
    have hw23 : w ⟨2, by omega⟩ < w ⟨3, by omega⟩ :=
      hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega))
    have h : g * q < g * r := by rw [← hgq, ← hgr]; exact hw23
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  obtain hF | hreal := bhk_prop11_v4_lt_2v3_uncond w hmono hpos hsum hsmall
  · exact hF
  have hr2q : r < 2 * q := by
    have hgR : (0:ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
    rw [c3, c2] at hreal
    have hcancel : (g : ℝ) * (r : ℝ) < (g : ℝ) * (2 * (q : ℝ)) := by nlinarith [hreal]
    have hR : (r : ℝ) < 2 * (q : ℝ) := lt_of_mul_lt_mul_left hcancel hgR.le
    exact_mod_cast hR
  have hrs : r < s := by
    have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
      hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
    have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  obtain hF | h_nogood : Found w ∨ (∀ l : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) := by
    rw [or_iff_not_imp_right]
    intro hQ
    obtain ⟨l, hl⟩ := not_forall_not.mp hQ
    obtain ⟨hrmem, hpmem⟩ := hl
    set t : ℝ := ((l : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
    have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
    have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (l : ℝ) + 1 / 2 := by rw [htdef]; field_simp
    have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c0, c2]; field_simp
    have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c3, c2]; field_simp
    refine bhk_prop11_no_good_time w hmono hpos hsum hsmall t ?_ ?_ ?_ ?_ ?_
    · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    · rw [e0]; exact hpmem.1
    · rw [e0]; exact hpmem.2
    · rw [e3]; exact hrmem.1
    · rw [e3]; exact hrmem.2
  · exact hF
  -- Finite `(p,q,r)` dispatch (q ∈ {5..17}, q < r < 2q): part6 / exc_Rkill / exc_Pkill /
  -- v4_bound_witness. Witnesses tabulated in experiments/core_q_lt_18_*.py.
  clear_value g p q r s
  clear hgdef hpdef hqdef hrdef hsdef hgw0 hgw2 hgw3 hgw4
  by_cases hdiag : r = p + q
  · -- DIAGONAL: r = p+q. part6_ge12 (p≥2,r≥12) / part6_p1 (p=1,q≥16) / exc_Pkill / explicit
    have hdiagw : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩ := by
      rw [hgr, hgp, hgq, hdiag]; ring
    have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
      exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
    have hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
      have h23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by
        exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega))
      linarith
    have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hg_pos.ne'
    interval_cases q
    · -- q = 5
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag_1_5 w hpos hsum g s hg_pos (by omega) (by omega)
            hgq hgr hgs
        · omega  -- r=7 non-diagonal, excluded by hdiag
        · omega  -- r=8 non-diagonal, excluded by hdiag
        · omega  -- r=9 non-diagonal, excluded by hdiag
    · -- q = 6
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag_1_6 w hpos hsum g s hg_pos (by omega) (by omega)
            hgq hgr hgs
        · omega  -- r=8 non-diagonal, excluded by hdiag
        · omega  -- r=9 non-diagonal, excluded by hdiag
        · omega  -- r=10 non-diagonal, excluded by hdiag
        · omega  -- r=11 non-diagonal, excluded by hdiag
    · -- q = 7
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag_1_7 w hpos hsum g s hg_pos (by omega) (by omega)
            hgq hgr hgs
        · omega  -- r=9 non-diagonal, excluded by hdiag
        · omega  -- r=10 non-diagonal, excluded by hdiag
        · omega  -- r=11 non-diagonal, excluded by hdiag
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · omega  -- r=13 non-diagonal, excluded by hdiag
      · -- p = 2
        interval_cases r
        · omega  -- r=8 non-diagonal, excluded by hdiag
        · exact bhk_prop11_exc_diag_2_7 w hpos hsum g s hg_pos (by omega) hgp hgq hgr hgs
        · omega  -- r=10 non-diagonal, excluded by hdiag
        · omega  -- r=11 non-diagonal, excluded by hdiag
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · omega  -- r=13 non-diagonal, excluded by hdiag
    · -- q = 8
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 8 9 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- diag P
        · omega  -- r=10 non-diagonal, excluded by hdiag
        · omega  -- r=11 non-diagonal, excluded by hdiag
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · omega  -- r=13 non-diagonal, excluded by hdiag
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
    · -- q = 9
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · -- (1,9,10) diagonal: BHK Case 5.2.12.4
          exact bhk_prop11_exc_diag_1_9 w hpos hsum g s hg_pos hrs (by omega) hgq hgr hgs
        · omega  -- r=11 non-diagonal, excluded by hdiag
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · omega  -- r=13 non-diagonal, excluded by hdiag
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
      · -- p = 2
        interval_cases r
        · omega  -- r=10 non-diagonal, excluded by hdiag
        · exact bhk_prop11_exc_diag_2_9 w hpos hsum g s hg_pos (by omega) hgp hgq hgr hgs
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · omega  -- r=13 non-diagonal, excluded by hdiag
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
    · -- q = 10
      have hpb : p ≤ 3 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag_1_10 w hpos hsum g s hg_pos (by omega) (by omega)
            hgq hgr hgs
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · omega  -- r=13 non-diagonal, excluded by hdiag
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
      · -- p = 3
        interval_cases r
        · omega  -- r=11 non-diagonal, excluded by hdiag
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 3 10 13 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
    · -- q = 11
      have hpb : p ≤ 3 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · -- (1,11,12) diagonal via part6_p1_wit, (57)-witness m=4
          refine bhk_prop11_part6_p1_wit w hpos hsum hdiagw hw24 g 11 s hg_pos (by norm_num)
            (by omega) hgq hgs ((4 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 4 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((4 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (4 : ℝ) / 11 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((4 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (4 : ℝ) / 11 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=13 non-diagonal, excluded by hdiag
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
      · -- p = 2
        interval_cases r
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 2 11 13 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
      · -- p = 3
        interval_cases r
        · omega  -- r=12 non-diagonal, excluded by hdiag
        · omega  -- r=13 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 3 11 14 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
    · -- q = 12
      have hpb : p ≤ 3 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag_1_12 w hpos hsum g s hg_pos (by omega) (by omega)
            hgq hgr hgs
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
      · exact absurd hcop (by decide)
    · -- q = 13
      have hpb : p ≤ 4 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · -- (1,13,14) diagonal via part6_p1_wit, (57)-witness m=5
          refine bhk_prop11_part6_p1_wit w hpos hsum hdiagw hw24 g 13 s hg_pos (by norm_num)
            (by omega) hgq hgs ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 5 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (5 : ℝ) / 13 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (5 : ℝ) / 13 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
      · -- p = 2
        interval_cases r
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 2 13 15 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
      · -- p = 3
        interval_cases r
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 3 13 16 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
      · -- p = 4
        interval_cases r
        · omega  -- r=14 non-diagonal, excluded by hdiag
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 4 13 17 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
    · -- q = 14
      have hpb : p ≤ 4 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 14 15 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- diag P
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
      · -- p = 3
        interval_cases r
        · omega  -- r=15 non-diagonal, excluded by hdiag
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 3 14 17 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
    · -- q = 15
      have hpb : p ≤ 4 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · -- (1,15,16) diagonal via part6_p1_wit, (57)-witness m=6
          refine bhk_prop11_part6_p1_wit w hpos hsum hdiagw hw24 g 15 s hg_pos (by norm_num)
            (by omega) hgq hgs ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 6 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 15 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 15 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
      · -- p = 2
        interval_cases r
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 2 15 17 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
      · -- p = 4
        interval_cases r
        · omega  -- r=16 non-diagonal, excluded by hdiag
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 4 15 19 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
    · -- q = 16
      have hpb : p ≤ 5 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_part6_p1 w hpos hsum hdiagw hw24 g 16 s hg_pos (by norm_num) (by omega) hgq hgs  -- diag part6_p1
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
      · -- p = 3
        interval_cases r
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 3 16 19 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
      · exact absurd hcop (by decide)
      · -- p = 5
        interval_cases r
        · omega  -- r=17 non-diagonal, excluded by hdiag
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 5 16 21 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
    · -- q = 17
      have hpb : p ≤ 5 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_part6_p1 w hpos hsum hdiagw hw24 g 17 s hg_pos (by norm_num) (by omega) hgq hgs  -- diag part6_p1
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
        · omega  -- r=32 non-diagonal, excluded by hdiag
        · omega  -- r=33 non-diagonal, excluded by hdiag
      · -- p = 2
        interval_cases r
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 2 17 19 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
        · omega  -- r=32 non-diagonal, excluded by hdiag
        · omega  -- r=33 non-diagonal, excluded by hdiag
      · -- p = 3
        interval_cases r
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 3 17 20 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
        · omega  -- r=32 non-diagonal, excluded by hdiag
        · omega  -- r=33 non-diagonal, excluded by hdiag
      · -- p = 4
        interval_cases r
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 4 17 21 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=22 non-diagonal, excluded by hdiag
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
        · omega  -- r=32 non-diagonal, excluded by hdiag
        · omega  -- r=33 non-diagonal, excluded by hdiag
      · -- p = 5
        interval_cases r
        · omega  -- r=18 non-diagonal, excluded by hdiag
        · omega  -- r=19 non-diagonal, excluded by hdiag
        · omega  -- r=20 non-diagonal, excluded by hdiag
        · omega  -- r=21 non-diagonal, excluded by hdiag
        · exact bhk_prop11_part6_ge12 w hpos hsum hsmall hdiagw hw34 g 5 17 22 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- diag part6_ge12
        · omega  -- r=23 non-diagonal, excluded by hdiag
        · omega  -- r=24 non-diagonal, excluded by hdiag
        · omega  -- r=25 non-diagonal, excluded by hdiag
        · omega  -- r=26 non-diagonal, excluded by hdiag
        · omega  -- r=27 non-diagonal, excluded by hdiag
        · omega  -- r=28 non-diagonal, excluded by hdiag
        · omega  -- r=29 non-diagonal, excluded by hdiag
        · omega  -- r=30 non-diagonal, excluded by hdiag
        · omega  -- r=31 non-diagonal, excluded by hdiag
        · omega  -- r=32 non-diagonal, excluded by hdiag
        · omega  -- r=33 non-diagonal, excluded by hdiag
  · -- NON-DIAGONAL: q ∈ {5..17}, q < r < 2q, r ≠ p+q → R / P / v4 exclusion
    interval_cases q
    · -- q = 5
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=6=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 5 7 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=7 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 5 8 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=8 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 5 9 1 (1/24 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=9 v4 excl
    · -- q = 6
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=7=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 6 8 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=8 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 6 9 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=9 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 6 10 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=10 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 6 11 1 (1/10 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=11 v4 excl
    · -- q = 7
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=8=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 7 9 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=9 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 7 10 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=10 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 7 11 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=11 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 7 12 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=12 P
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 7 13 1 (5/36 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=13 v4 excl
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 7 8 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=8 P
        · omega  -- r=9=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 7 10 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=10 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 7 11 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=11 P
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 2 7 12 4 (1/15 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=12 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 2 7 13 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=13 R
    · -- q = 8
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=9=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 8 10 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=10 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 11 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=11 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 12 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=12 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 13 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=13 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 14 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 8 15 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=15 P
      · exact absurd hcop (by decide)  -- p=2, gcd>1
    · -- q = 9
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=10=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 9 11 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=11 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 12 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=12 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 13 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=13 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 14 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 15 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=15 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 16 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 9 17 2 (1/16 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=17 v4 excl
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 9 10 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=10 P
        · omega  -- r=11=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 9 12 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=12 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 9 13 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=13 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 9 14 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 9 15 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=15 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 2 9 16 5 (1/7 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=16 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 2 9 17 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
    · -- q = 10
      have hpb : p ≤ 3 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=11=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 10 12 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=12 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 13 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=13 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 14 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 10 15 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=15 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 10 16 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=16 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 17 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 18 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 10 19 2 (5/54 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=19 v4 excl
      · exact absurd hcop (by decide)  -- p=2, gcd>1
      · -- p = 3
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 3 10 11 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=11 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 10 12 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=12 P
        · omega  -- r=13=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 3 10 14 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 10 15 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=15 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 10 16 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=16 P
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 3 10 17 7 (5/42 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=17 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 3 10 18 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 10 19 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
    · -- q = 11
      have hpb : p ≤ 3 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=12=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 11 13 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=13 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 14 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 15 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=15 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 11 16 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=16 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 17 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 11 18 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=18 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 20 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 11 21 2 (7/60 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=21 v4 excl
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 11 12 s 7 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=12 P
        · omega  -- r=13=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 11 14 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 11 15 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=15 P
        · exact False.elim <| bhk_prop11_exc_Rkill 2 11 16 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 11 17 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 11 18 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 11 19 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 2 11 20 6 (1/12 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=20 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 2 11 21 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
      · -- p = 3
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 3 11 12 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=12 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 11 13 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=13 R
        · omega  -- r=14=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 11 15 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=15 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 11 16 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 11 17 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=17 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 11 18 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 3 11 19 4 (7/48 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=19 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 3 11 20 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 11 21 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
    · -- q = 12
      have hpb : p ≤ 3 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=13=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 12 14 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=14 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 15 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=15 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 16 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 12 17 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=17 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 18 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 12 19 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=19 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 20 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 21 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 22 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 12 23 2 (3/22 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=23 v4 excl
      · exact absurd hcop (by decide)  -- p=2, gcd>1
      · exact absurd hcop (by decide)  -- p=3, gcd>1
    · -- q = 13
      have hpb : p ≤ 4 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=14=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 13 15 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=15 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 16 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 17 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 18 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 13 19 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=19 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 20 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 13 21 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=21 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 22 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 23 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 13 25 2 (11/72 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=25 v4 excl
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 13 14 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=14 P
        · omega  -- r=15=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 16 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 13 17 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=17 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 13 18 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=18 P
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 19 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 20 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 21 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 22 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 13 23 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=23 P
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 2 13 24 1 (4/33 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=24 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 25 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
      · -- p = 3
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 3 13 14 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 13 15 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=15 R
        · omega  -- r=16=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 3 13 17 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 13 18 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=18 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 13 19 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=19 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 13 20 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 13 21 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 13 22 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 3 13 23 9 (1/9 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=23 v4 excl
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 13 24 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=24 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 13 25 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
      · -- p = 4
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 4 13 14 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=14 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 13 15 s 10 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=15 P
        · exact False.elim <| bhk_prop11_exc_Rkill 4 13 16 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · omega  -- r=17=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 4 13 18 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 13 19 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 13 20 s 7 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=20 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 13 21 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=21 P
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 4 13 22 10 (4/27 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=22 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 4 13 23 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 13 24 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 13 25 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
    · -- q = 14
      have hpb : p ≤ 4 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=15=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 14 16 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=16 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 17 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 18 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 20 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 21 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 22 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 24 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 25 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 14 27 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=27 P
      · exact absurd hcop (by decide)  -- p=2, gcd>1
      · -- p = 3
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 15 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=15 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 16 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · omega  -- r=17=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 18 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 19 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 14 20 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=20 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 21 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 22 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 23 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 24 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 3 14 25 10 (7/66 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=25 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 14 27 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=27 R
      · exact absurd hcop (by decide)  -- p=4, gcd>1
    · -- q = 15
      have hpb : p ≤ 4 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=16=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 15 17 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=17 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 18 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 20 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 21 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 15 22 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=22 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 23 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 24 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 25 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 26 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 27 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=27 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 15 29 3 (3/28 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=29 v4 excl
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 15 16 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=16 P
        · omega  -- r=17=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 18 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 20 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 21 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 22 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 23 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 24 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 25 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 26 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 27 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=27 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 2 15 28 1 (2/13 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=28 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 29 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
      · exact absurd hcop (by decide)  -- p=3, gcd>1
      · -- p = 4
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 16 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=16 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 17 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 18 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · omega  -- r=19=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 20 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 21 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 22 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 23 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 24 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 25 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 4 15 26 4 (1/8 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=26 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 27 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=27 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 15 29 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
    · -- q = 16
      have hpb : p ≤ 5 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=17=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 16 18 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=18 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 19 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 20 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 16 21 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=21 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 16 27 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=27 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 16 28 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=28 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 29 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=30 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 16 31 3 (11/90 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=31 v4 excl
      · exact absurd hcop (by decide)  -- p=2, gcd>1
      · -- p = 3
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 16 17 s 12 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=17 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 16 18 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · omega  -- r=19=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 16 20 s 6 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=20 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 16 21 s 6 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=21 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 16 22 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=22 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 16 23 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 16 24 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 16 25 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 16 26 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 16 27 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=27 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 16 28 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 3 16 29 6 (11/78 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=29 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 3 16 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=30 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 16 31 s 6 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=31 P
      · exact absurd hcop (by decide)  -- p=4, gcd>1
      · -- p = 5
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 17 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=17 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 18 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 19 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 16 20 s 7 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=20 P
        · omega  -- r=21=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 22 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 23 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 24 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 25 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 16 26 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=26 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 16 27 s 13 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=27 P
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 28 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 29 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=30 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 16 31 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=31 R
    · -- q = 17
      have hpb : p ≤ 5 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=18=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 17 19 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=19 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 20 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 21 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 17 22 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=22 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 23 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 24 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 17 25 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=25 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 1 17 27 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=27 P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 30 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=30 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=31 R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=32 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 1 17 33 3 (13/96 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=33 v4 excl
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 17 18 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=18 P
        · omega  -- r=19=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 20 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 17 21 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=21 P
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 22 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 23 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 17 24 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=24 P
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 25 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 26 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 27 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=27 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 28 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 29 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 30 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=30 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 2 17 31 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=31 P
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 2 17 32 10 (1/9 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=32 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 33 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=33 R
      · -- p = 3
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 18 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 19 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · omega  -- r=20=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 21 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 22 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 17 23 s 7 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=23 P
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 17 24 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=24 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 25 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 26 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 27 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=27 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 28 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 29 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=30 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 3 17 31 12 (13/84 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=31 v4 excl
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 3 17 32 s 6 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=32 P
        · exact False.elim <| bhk_prop11_exc_Rkill 3 17 33 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=33 R
      · -- p = 4
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 18 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 17 19 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=19 P
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 20 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · omega  -- r=21=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 22 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=22 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 23 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=23 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 24 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 4 17 25 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=25 P
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 27 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=27 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 28 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=29 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 4 17 30 9 (5/39 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=30 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 31 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=31 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 32 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=32 R
        · exact False.elim <| bhk_prop11_exc_Rkill 4 17 33 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=33 R
      · -- p = 5
        interval_cases r
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 18 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=18 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 19 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=19 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 20 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=20 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 21 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=21 R
        · omega  -- r=22=p+q diagonal
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 17 23 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=23 P
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 24 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=24 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 25 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=25 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 26 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=26 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 17 27 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=27 P
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=28 R
        · exact bhk_prop11_exc_v4kill w hmono hpos hsum hsmall g 5 17 29 7 (2/15 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=29 v4 excl
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=30 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=31 R
        · exact False.elim <| bhk_prop11_exc_Rkill 5 17 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- r=32 R
        · exact bhk_prop11_exc_Pkill w hmono hpos hsum hsmall g 5 17 33 s 7 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- r=33 P

/-- **Proposition 11 — indirect core (part 1).** The `B₀ = ℝ⁺` contradiction:
    for integer speeds `w₀ < ⋯ < w₄` with `w₀ + w₁ = w₂` and `3 w₀ < w₂`, the
    runners cannot cover every time within `1/6` of the origin (BHK's Parts 1–6,
    `v₁ < 1/3`). Splits on `q = w₂/gcd(w₀,w₂)`: `q ≥ 18` → `bhk_prop11_core_q18`
    (exceptional-pair dispatch), `q < 18` → `bhk_prop11_core_q_lt_18`. -/
theorem bhk_prop11_core (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    : Found w := by
  by_cases hq : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)
  · exact bhk_prop11_core_q18 w hmono hpos hsum hsmall hq
  · exact bhk_prop11_core_q_lt_18 w hmono hpos hsum hsmall (not_le.mp hq)

/-- **Gap covering with the fictional runner 0** (the windowed analog of
    `bhk_prop11_gap_covered`). On a **0123-gap** `[a, b]` — runners 1,2,3
    (`w₀, w₁, w₂`) safe (`hgap`) *and* runner 1 outside the half-way window
    `(5/12, 7/12)` (`h0safe`, so the fictional runner `2 w₀` is also safe) — the
    six-runner covering `hcov6` forces every point to be covered by runner 4 or
    runner 5. This is the *single* point at which the windowed covering enters
    the Part-2–6 pipeline: with it, the runner-5 engines
    (`bhk_prop11_gap1234_b5span` / `bhk_prop11_long_gap_absurd`) and hence the
    no-good-time facts transfer to `core2`, provided the gaps are kept window-free
    (automatic for the rectangle, where `{w₀t} ≤ 1/3 < 5/12`). -/
lemma bhk_prop11_gap_covered2 (w : Fin 5 → ℕ)
    {a b : ℝ}
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h0safe : ∀ s ∈ Set.Icc a b,
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12)) : Found6 w ∨
      (Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∪ unsafeOf w ⟨4, by omega⟩) := by
  rcases found6_or_blocked_on w (Set.Icc a b) with hF | hblk
  · exact Or.inl hF
  right
  intro s hs
  rcases hblk s hs with ⟨i, hi⟩ | hfict
  · fin_cases i
    · exact absurd hi (not_lt.mpr (hgap s hs 0))
    · exact absurd hi (not_lt.mpr (hgap s hs 1))
    · exact absurd hi (not_lt.mpr (hgap s hs 2))
    · exact Or.inl ((mem_unsafeOf_iff w _ s).mpr hi)
    · exact Or.inr ((mem_unsafeOf_iff w _ s).mpr hi)
  · exfalso
    have hr0 : (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s) := hgap s hs 0
    have h1 : (1 : ℝ) / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) := by
      have := hr0; unfold circDist at this; exact le_trans this (min_le_left _ _)
    have h2 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ≤ 5 / 6 := by
      have := hr0; unfold circDist at this; linarith [le_trans this (min_le_right _ _)]
    exact absurd hfict (not_lt.mpr (bhk_prop11_fict_window_safe h1 h2 (h0safe s hs)))

/-- **Runner-5 span engine, windowed** (the `gap_covered2` analog of
    `bhk_prop11_gap1234_b5span`). On a 0123-gap `[a, b]` — runners 1,2,3 safe
    (`hgap`), runner 1 window-free (`h0safe`), runner 4 safe (`h4safe`) — the
    six-runner covering forces runner 5 to cover, so `w₄ · (b − a) < 1/3`. -/
lemma bhk_prop11_gap1234_b5span2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h0safe : ∀ s ∈ Set.Icc a b,
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12))
    (h4safe : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s)) : Found6 w ∨
      ((w ⟨4, by omega⟩ : ℝ) * (b - a) < 1 / 3) := by
  obtain hF | hcov45 := bhk_prop11_gap_covered2 w hgap h0safe
  · exact Or.inl hF
  right
  have hsub5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩ := by
    intro s hs
    rcases hcov45 hs with h | h
    · exact absurd ((mem_unsafeOf_iff w _ s).mp h) (not_lt.mpr (h4safe s hs))
    · exact h
  obtain ⟨k, hk1, hk2⟩ := block_containment w ⟨4, by omega⟩ (hpos _) a b hab hsub5
  rw [mul_sub]; linarith

/-- **Long-gap absurdity, windowed** (the `core2` analog of
    `bhk_prop11_long_gap_absurd`). A window-free `0123`-gap `[a,b]` (runners
    `1,2,3` safe via `hgap`, runner 1 window-free via `h0safe`, runner 4 safe via
    `h4safe`) of length `≥ 1/(3w₄)` cannot exist under the six-runner covering:
    `bhk_prop11_gap1234_b5span2` forces `w₄·(b−a) < 1/3`, contradicting
    `w₄·(b−a) ≥ 1/3`. This is the windowed runner-5 closing step shared by the
    pentagon halves `no_good_time_P2_r3` / `_r4`. -/
lemma bhk_prop11_long_gap_absurd2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (a b : ℝ) (hab : a ≤ b)
    (hlen : 1 / (3 * (w ⟨4, by omega⟩ : ℝ)) ≤ b - a)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3, 1 / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h0safe : ∀ s ∈ Set.Icc a b,
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12))
    (h4safe : ∀ s ∈ Set.Icc a b, 1 / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s)) : Found6 w := by
  have hw4 : (0:ℝ) < (w ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  obtain hF | hspan := bhk_prop11_gap1234_b5span2 w hpos hab hgap h0safe h4safe
  · exact hF
  have hmul : (w ⟨4, by omega⟩ : ℝ) * (1 / (3 * (w ⟨4, by omega⟩ : ℝ)))
      ≤ (w ⟨4, by omega⟩ : ℝ) * (b - a) := mul_le_mul_of_nonneg_left hlen hw4.le
  have heq : (w ⟨4, by omega⟩ : ℝ) * (1 / (3 * (w ⟨4, by omega⟩ : ℝ))) = 1 / 3 := by field_simp
  rw [heq] at hmul
  linarith [hspan, hmul]

/-- **No-good-time (rectangle), windowed** (the `core2` analog of
    `bhk_prop11_no_good_time`). Under `6 w₀ < w₂` and the six-runner covering, no
    half-integer time `t` (`{w₂t} = 1/2`) has `{w₀t} ∈ [1/6,1/3]` *and*
    `{w₃t} ∈ [1/6,1/2]`. The rectangle's gap `[t, t + 1/(3w₃)]` is automatically
    **window-free** — `{w₀t} ≤ 1/3` and `w₀(s−t) ≤ w₀/(3w₃) < 1/18` (as
    `4 w₀ < w₃`), so `{w₀s} < 5/12` — hence the windowed runner-5 engine applies
    exactly as in part 1. This is the rectangle no-good-time that transfers
    verbatim to `core2`; the *pentagon* strengthening genuinely needs the
    fictional 0123-gap. -/
theorem bhk_prop11_no_good_time2 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ≤ 1 / 3)
    (h4lo : 1 / 6 ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h4hi : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) ≤ 1 / 2) : Found6 w := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  have hw0pos : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3pos : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega))
  have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
  have hsmall6R : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall6
  have h4w0 : 4 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  have hgap2 := bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi
  set b3 : ℝ := t + 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) with hb3
  have hab3 : t ≤ b3 := by rw [hb3]; exact le_add_of_nonneg_right (by positivity)
  have hlen_le : 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hgap_sub : ∀ s ∈ Set.Icc t b3, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    exact hgap2 s ⟨hs.1, by rw [hb3] at hs; linarith [hs.2]⟩ i
  -- The shorter gap `[t, b3]` is window-free for runner 1.
  have h0safe : ∀ s ∈ Set.Icc t b3,
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    have hd0 : 0 ≤ s - t := by linarith [hs.1]
    have hsu : s - t ≤ 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by rw [hb3] at hs; linarith [hs.2]
    have hb : (w ⟨0, by omega⟩ : ℝ) * (s - t) < 1 / 12 := by
      have h1 : (w ⟨0, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left hsu hw0pos.le
      have h2 : (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) < 1 / 12 := by
        rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [h4w0]
      linarith
    have hfs : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) + (w ⟨0, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨0, by omega⟩ : ℝ) * s
            = (w ⟨0, by omega⟩ : ℝ) * t + (w ⟨0, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by nlinarith [mul_nonneg hw0pos.le hd0]) (by linarith)]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith
  have h4safe : ∀ s ∈ Set.Icc t b3, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
    intro s hs
    have hd0 : 0 ≤ s - t := by linarith [hs.1]
    have hdu : (w ⟨3, by omega⟩ : ℝ) * (s - t) ≤ 1 / 3 := by
      have h1 : (w ⟨3, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨3, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left (by rw [hb3] at hs; linarith [hs.2]) hw3pos.le
      have h2 : (w ⟨3, by omega⟩ : ℝ) * (1 / (3 * (w ⟨3, by omega⟩ : ℝ))) = 1 / 3 := by
        field_simp
      linarith [h1, h2]
    have hbnn : 0 ≤ (w ⟨3, by omega⟩ : ℝ) * (s - t) := mul_nonneg hw3pos.le hd0
    have hfs : Int.fract ((w ⟨3, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) + (w ⟨3, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨3, by omega⟩ : ℝ) * s
            = (w ⟨3, by omega⟩ : ℝ) * t + (w ⟨3, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by linarith) (by linarith)]
    simp only [circDist]; rw [hfs]; exact le_min (by linarith) (by linarith)
  obtain hF | hspan := bhk_prop11_gap1234_b5span2 w hpos hab3 hgap_sub h0safe h4safe
  · exact hF
  rw [hb3, add_sub_cancel_left, mul_one_div, div_lt_iff₀ (by positivity)] at hspan
  nlinarith [hspan, hw34]

/-- **Pentagon `P'` no-good-time, runner-3-ends sub-region, windowed** (the
    `core2` analog of `bhk_prop11_no_good_time_P_r3`). Same `1234`-gap
    `[t + (w₄−w₂)/(3w₂w₄), t + 1/(3w₂)]` of length `1/(3w₄)`, but closed under the
    weaker six-runner covering by promoting it to a `01234`-gap: BHK's extra
    condition (43) `{w₀t} ≤ 5/12 − v₁/3` (here `v₁/3 = w₀/(3w₂)`) plus `6w₀ < w₂`
    keep runner 1 window-free across the gap (`{w₀s} ≤ 5/12`), so the fictional
    runner `2w₀` cannot cover it either. Closed by `long_gap_absurd2`. -/
theorem bhk_prop11_no_good_time_P2_r3 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i) (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h40 : 1 / 6 - (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h41 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
    (h39 : 1 / 6 - (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h42 : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)
            ≤ 5 / 6 - (w ⟨3, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)))
    (h43 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 5 / 12 - (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))) : Found6 w := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  have hw0 : (0:ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0:ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw4 : (0:ℝ) < (w ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 4 by omega))
  have hsmall6R : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall6
  have hba : (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)))
        - (t + ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
        = 1 / (3 * (w ⟨4, by omega⟩ : ℝ)) := by
    field_simp; ring
  have hab : t + ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
        / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
      ≤ t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
    have h0 : (0:ℝ) ≤ 1 / (3 * (w ⟨4, by omega⟩ : ℝ)) := by positivity
    linarith [hba]
  have hgap := bhk_prop11_pent_gap123 w hpos hmono hsum hsmall t h3 h40 h41
  have h4safe := bhk_prop11_pent_runner4_safe w hpos t h39 h42
  -- runner 1 (`w₀`) stays window-free across the gap: `{w₀ s} ≤ 5/12` by (43).
  have hapos : (0:ℝ) ≤ ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) :=
    div_nonneg (by linarith [hw24]) (by positivity)
  have h0safe : ∀ s ∈ Set.Icc (t + ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
        (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))),
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    have hd0 : 0 ≤ s - t := by linarith [hs.1, hapos]
    have hsu : s - t ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by linarith [hs.2]
    have hb : (w ⟨0, by omega⟩ : ℝ) * (s - t) ≤ (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
      have h1 : (w ⟨0, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left hsu hw0.le
      have h2 : (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ)))
          = (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) := by ring
      linarith [h1, h2]
    have hfs : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) + (w ⟨0, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨0, by omega⟩ : ℝ) * s
            = (w ⟨0, by omega⟩ : ℝ) * t + (w ⟨0, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (add_nonneg (Int.fract_nonneg _) (mul_nonneg hw0.le hd0))
          (by linarith [h43, hb])]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith [h43, hb]
  exact bhk_prop11_long_gap_absurd2 w hpos _ _ hab (le_of_eq hba.symm) hgap h0safe h4safe

set_option maxHeartbeats 800000 in
/-- **Pentagon `P'` no-good-time, runner-4-ends sub-region, windowed** (the
    `core2` analog of `bhk_prop11_no_good_time_P_r4`). Identical `1234`-gap
    `[a', b']` (start `a' = max` of the four reach-`1/6` times, end
    `b' = t + (5/6−{w₃t})/w₃`), promoted to a `01234`-gap under the six-runner
    covering. The runner-4-ends regime `hr4` gives `b'−t ≤ 1/(3w₂)` and
    `a' ≥ t − 1/(3w₂)`, so `s − t ∈ [−1/(3w₂), 1/(3w₂)]` across the gap; with (43)
    `{w₀t} ≤ 5/12 − v₁/3` (upper) and (40) (lower), runner 1 stays in
    `[1/18, 5/12]`, hence window-free, so the fictional runner `2w₀` cannot cover
    it. Closed by `long_gap_absurd2`. -/
theorem bhk_prop11_no_good_time_P2_r4 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i) (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h40 : 1 / 6 - (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h41 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
    (hxle : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) ≤ 5 / 6)
    (hr4 : 5 / 6 - (w ⟨3, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h42a : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) - 1 / 6) / (w ⟨0, by omega⟩ : ℝ))
    (h42b : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (1 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)) / (w ⟨1, by omega⟩ : ℝ))
    (h43 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 5 / 12 - (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))) : Found6 w := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  have hw0 : (0:ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw1 : (0:ℝ) < (w ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0:ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3 : (0:ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw4 : (0:ℝ) < (w ⟨4, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h12 : (w ⟨1, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (1:ℕ) < 2 by omega))
  have h23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega))
  have h34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
    exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3:ℕ) < 4 by omega))
  have hsmallR : 3 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall
  have hsmall6R : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall6
  have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsum
  set w0 : ℝ := (w ⟨0, by omega⟩ : ℝ) with hw0d
  set w1 : ℝ := (w ⟨1, by omega⟩ : ℝ) with hw1d
  set w2 : ℝ := (w ⟨2, by omega⟩ : ℝ) with hw2d
  set w3 : ℝ := (w ⟨3, by omega⟩ : ℝ) with hw3d
  set w4 : ℝ := (w ⟨4, by omega⟩ : ℝ) with hw4d
  have h24 : w2 < w4 := lt_trans h23 h34
  have hw0' : w0 ≠ 0 := ne_of_gt hw0
  have hw1' : w1 ≠ 0 := ne_of_gt hw1
  have hw2' : w2 ≠ 0 := ne_of_gt hw2
  have hw3' : w3 ≠ 0 := ne_of_gt hw3
  set y : ℝ := Int.fract (w0 * t) with hyd
  set x : ℝ := Int.fract (w3 * t) with hxd
  have hf0 : (0:ℝ) ≤ y := Int.fract_nonneg _
  have hf0' : y < 1 := Int.fract_lt_one _
  have hslack : w1 * (w4 - w2) / (3 * w2 * w4) < 1 / 3 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_right h12 (show (0:ℝ) < w4 - w2 by linarith), mul_pos hw2 hw2]
  have hy23 : y < 2 / 3 := by linarith [h41, hslack]
  have hsm0 : w0 / (3 * w2) < 1 / 9 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hsm1 : w1 / (3 * w2) < 1 / 3 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hsm2 : w2 / (3 * w2) = 1 / 3 := by field_simp
  have hbt : (5 / 6 - x) / w3 ≤ 1 / (3 * w2) := by
    rw [div_le_iff₀ hw3, show (1:ℝ) / (3 * w2) * w3 = w3 / (3 * w2) from by ring]; linarith [hr4]
  have hbtpos : (0:ℝ) ≤ (5 / 6 - x) / w3 := div_nonneg (by linarith [hxle]) hw3.le
  have key : ∀ v : ℝ, 0 ≤ v → v * ((5 / 6 - x) / w3) ≤ v / (3 * w2) := by
    intro v hv
    calc v * ((5 / 6 - x) / w3) ≤ v * (1 / (3 * w2)) := mul_le_mul_of_nonneg_left hbt hv
      _ = v / (3 * w2) := by ring
  have h1w : 1 / (3 * w4) ≤ 1 / (3 * w2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  set b' : ℝ := t + (5 / 6 - x) / w3 with hb'd
  have hb't : b' - t = (5 / 6 - x) / w3 := by rw [hb'd]; ring
  set a' : ℝ := max (t + (1 / 6 - y) / w0)
      (max (t + (y - 1 / 3) / w1) (max (t - 1 / (3 * w2)) (t + (1 / 6 - x) / w3))) with ha'd
  have hb1 : t + (1 / 6 - y) / w0 ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t + (1 / 6 - y) / w0) = (5 / 6 - x) / w3 + (y - 1 / 6) / w0 := by rw [hb'd]; ring
    linarith [h42a, e]
  have hb2 : t + (y - 1 / 3) / w1 ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t + (y - 1 / 3) / w1) = (5 / 6 - x) / w3 + (1 / 3 - y) / w1 := by rw [hb'd]; ring
    linarith [h42b, e]
  have hb3 : t - 1 / (3 * w2) ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t - 1 / (3 * w2)) = (5 / 6 - x) / w3 + 1 / (3 * w2) := by rw [hb'd]; ring
    linarith [hbtpos, h1w, e]
  have hb4 : t + (1 / 6 - x) / w3 ≤ b' - 1 / (3 * w4) := by
    have e : b' - (t + (1 / 6 - x) / w3) = (2 / 3) / w3 := by rw [hb'd]; ring
    have h2w : 1 / (3 * w4) ≤ (2 / 3) / w3 := by
      rw [le_div_iff₀ hw3, show (1:ℝ) / (3 * w4) * w3 = w3 / (3 * w4) from by ring,
        div_le_iff₀ (show (0:ℝ) < 3 * w4 by positivity)]
      linarith
    linarith [h2w, e]
  have ha'le : a' ≤ b' - 1 / (3 * w4) := by
    rw [ha'd]; exact max_le hb1 (max_le hb2 (max_le hb3 hb4))
  have hlen : 1 / (3 * w4) ≤ b' - a' := by linarith [ha'le]
  have hab' : a' ≤ b' := by
    have h0 : (0:ℝ) < 1 / (3 * w4) := by positivity
    linarith [ha'le]
  have hτ1 : t + (1 / 6 - y) / w0 ≤ a' := by rw [ha'd]; exact le_max_left _ _
  have hτ2 : t + (y - 1 / 3) / w1 ≤ a' := by
    rw [ha'd]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hτ3 : t - 1 / (3 * w2) ≤ a' := by
    rw [ha'd]; exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hτ4 : t + (1 / 6 - x) / w3 ≤ a' := by
    rw [ha'd]; exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hw1cast : w1 = w2 - w0 := by linarith [hsumR]
  have hf1base : Int.fract (w1 * t) = Int.fract (1 / 2 - y) := by
    have h0 : w1 * t = ((⌊w2 * t⌋ - ⌊w0 * t⌋ : ℤ) : ℝ) + (1 / 2 - y) := by
      have e2 := Int.floor_add_fract (w2 * t)
      have e0 := Int.floor_add_fract (w0 * t)
      rw [h3] at e2
      rw [hw1cast, sub_mul, Int.cast_sub]; linarith [e2, e0]
    rw [h0, Int.fract_intCast_add]
  -- runner 1 (w₀): reaches 1/6 at τ₁, k = 0
  have safe0 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w0 * s) :=
    bhk_prop11_pent_reach_safe w0 t a' b' 0 (t + (1 / 6 - y) / w0) hw0.le hτ1
      (by have e : w0 * ((t + (1 / 6 - y) / w0) - t) = 1 / 6 - y := by
            rw [show (t + (1 / 6 - y) / w0) - t = (1 / 6 - y) / w0 from by ring]; field_simp
          rw [e]; push_cast; ring)
      (by rw [hb't]; push_cast; have hk := key w0 hw0.le; linarith [hk, hsm0, hy23])
  -- runner 3 (w₂): at 1/2, reached 1/6 at τ₃ = t − 1/(3w₂), k = 0
  have safe2 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w2 * s) :=
    bhk_prop11_pent_reach_safe w2 t a' b' 0 (t - 1 / (3 * w2)) hw2.le hτ3
      (by rw [h3]
          have e : w2 * ((t - 1 / (3 * w2)) - t) = -(1 / 3) := by
            rw [show (t - 1 / (3 * w2)) - t = -(1 / (3 * w2)) from by ring]; field_simp
          rw [e]; push_cast; ring)
      (by rw [h3, hb't]; push_cast; have hk := key w2 hw2.le; rw [hsm2] at hk; linarith [hk])
  -- runner 4 (w₃): at x, reaches 1/6 at τ₄, reaches 5/6 at b', k = 0
  have safe3 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w3 * s) :=
    bhk_prop11_pent_reach_safe w3 t a' b' 0 (t + (1 / 6 - x) / w3) hw3.le hτ4
      (by have e : w3 * ((t + (1 / 6 - x) / w3) - t) = 1 / 6 - x := by
            rw [show (t + (1 / 6 - x) / w3) - t = (1 / 6 - x) / w3 from by ring]; field_simp
          rw [e]; push_cast; ring)
      (by rw [hb't]
          have e : w3 * ((5 / 6 - x) / w3) = 5 / 6 - x := by field_simp
          rw [e]; push_cast; linarith)
  -- runner 2 (w₁): position frac(1/2 − y); k = 0 if y ≤ 1/2, k = 1 (wrap) otherwise
  have safe1 : ∀ s ∈ Set.Icc a' b', 1 / 6 ≤ circDist (w1 * s) := by
    by_cases hle : y ≤ 1 / 2
    · have hf1 : Int.fract (w1 * t) = 1 / 2 - y := by
        rw [hf1base]; exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      exact bhk_prop11_pent_reach_safe w1 t a' b' 0 (t + (y - 1 / 3) / w1) hw1.le hτ2
        (by rw [hf1]
            have e : w1 * ((t + (y - 1 / 3) / w1) - t) = y - 1 / 3 := by
              rw [show (t + (y - 1 / 3) / w1) - t = (y - 1 / 3) / w1 from by ring]; field_simp
            rw [e]; push_cast; ring)
        (by rw [hf1, hb't]; push_cast; have hk := key w1 hw1.le; linarith [hk, hsm1, hf0])
    · have hgt : 1 / 2 < y := not_le.mp hle
      have hf1 : Int.fract (w1 * t) = 3 / 2 - y := by
        rw [hf1base, show (1:ℝ) / 2 - y = ((-1 : ℤ) : ℝ) + (3 / 2 - y) from by push_cast; ring,
          Int.fract_intCast_add]
        exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      exact bhk_prop11_pent_reach_safe w1 t a' b' 1 (t + (y - 1 / 3) / w1) hw1.le hτ2
        (by rw [hf1]
            have e : w1 * ((t + (y - 1 / 3) / w1) - t) = y - 1 / 3 := by
              rw [show (t + (y - 1 / 3) / w1) - t = (y - 1 / 3) / w1 from by ring]; field_simp
            rw [e]; push_cast; ring)
        (by rw [hf1, hb't]; push_cast; have hk := key w1 hw1.le; linarith [hk, hsm1, hgt])
  have hgap : ∀ s ∈ Set.Icc a' b', ∀ i : Fin 3, 1 / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    fin_cases i
    · exact safe0 s hs
    · exact safe1 s hs
    · exact safe2 s hs
  -- runner 1 (w₀) window-free across `[a', b']`: `{w₀ s} ∈ [1/18, 5/12]` by (40)/(43).
  have hsm0w6 : w0 / (3 * w2) ≤ 1 / 18 := by
    rw [div_le_iff₀ (by positivity)]; linarith [hsmall6R]
  have hcorr : w0 * (w4 - w2) / (3 * w2 * w4) ≤ w0 / (3 * w2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hw0 hw2, hw2, hw4, h24]
  have hylow : 1 / 6 - w0 / (3 * w2) ≤ y := by linarith [h40, hcorr]
  have h0safe : ∀ s ∈ Set.Icc a' b',
      Int.fract (w0 * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    have hsl : -(1 / (3 * w2)) ≤ s - t := by linarith [hs.1, hτ3]
    have hsu : s - t ≤ 1 / (3 * w2) := by
      have hsb : s - t ≤ b' - t := by linarith [hs.2]
      rw [hb't] at hsb; linarith [hsb, hbt]
    have hdu : w0 * (s - t) ≤ w0 / (3 * w2) := by
      have h1 : w0 * (s - t) ≤ w0 * (1 / (3 * w2)) := mul_le_mul_of_nonneg_left hsu hw0.le
      have h2 : w0 * (1 / (3 * w2)) = w0 / (3 * w2) := by ring
      linarith [h1, h2]
    have hdl : -(w0 / (3 * w2)) ≤ w0 * (s - t) := by
      have h1 : w0 * (-(1 / (3 * w2))) ≤ w0 * (s - t) := mul_le_mul_of_nonneg_left hsl hw0.le
      have h2 : w0 * (-(1 / (3 * w2))) = -(w0 / (3 * w2)) := by ring
      linarith [h1, h2]
    have hfs : Int.fract (w0 * s) = Int.fract (w0 * t) + w0 * (s - t) := by
      rw [show w0 * s = w0 * t + w0 * (s - t) from by ring,
        bhk_prop11_fract_add (by linarith [hylow, hdl, hsm0w6]) (by linarith [h43, hdu])]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith [h43, hdu]
  exact bhk_prop11_long_gap_absurd2 w hpos a' b' hab' hlen hgap h0safe safe3

/-- **Pentagon `P'` no-good-time (`C ∩ P' = ∅`), windowed** (the `core2` analog of
    `bhk_prop11_no_good_time_P`). Under `6w₀ < w₂` and the six-runner covering, no
    half-integer time `t` (`{w₂t} = 1/2`) satisfies the relaxed pentagon `P`
    (lower bounds (39)/(40), upper (41), `{w₃t} ≤ 5/6`, the (42) slants
    `h42a`/`h42b`) *together with* BHK's extra cut (43) `{w₀t} ≤ 5/12 − v₁/3`.
    The (43) cut promotes the `1234`-gap to a `01234`-gap (runner 1 window-free),
    so the fictional runner `2w₀` cannot rescue the covering. Dispatches on
    whether runner 3 or runner 4 reaches `5/6` first. -/
theorem bhk_prop11_no_good_time_P2 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i) (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h39 : 1 / 6 - (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨3, by omega⟩ : ℝ) * t))
    (h40 : 1 / 6 - (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
            ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h41 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
              / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)))
    (hxle : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t) ≤ 5 / 6)
    (h42a : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) - 1 / 6) / (w ⟨0, by omega⟩ : ℝ))
    (h42b : 1 / (3 * (w ⟨4, by omega⟩ : ℝ))
            ≤ (5 / 6 - Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)) / (w ⟨3, by omega⟩ : ℝ)
              + (1 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)) / (w ⟨1, by omega⟩ : ℝ))
    (h43 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
            ≤ 5 / 12 - (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))) : Found6 w := by
  by_cases hx : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t)
      ≤ 5 / 6 - (w ⟨3, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ))
  · exact bhk_prop11_no_good_time_P2_r3 w hmono hpos hsum hsmall6 t h3 h40 h41 h39 hx h43
  · exact bhk_prop11_no_good_time_P2_r4 w hmono hpos hsum hsmall6 t h3 h40 h41 hxle
      (le_of_lt (not_le.mp hx)) h42a h42b h43

/-- **Pentagon `P'` avoidance in reduced coordinates (`C ∩ P' = ∅`), windowed**
    (the `core2` analog of `bhk_prop11_pent_no_good`). Transports
    `bhk_prop11_no_good_time_P2` to the coset coordinates `(X,Y) =
    (fract(r/q(l+½)), fract(p/q(l+½)))`: at no half-integer index `l` does the
    C-point lie in the *smaller* pentagon `P' = P ∩ {Y ≤ 5/12 − v₁/3}` (the six
    `P` conditions plus the (43) cut, `v₁/3 = w₀/(3w₂)`). The `(1,1)`/`(1,±2)`
    windowed kills exhibit an `l` *in* `P'`, contradicting this. -/
theorem bhk_prop11_pent_no_good2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r : ℕ) (hgpos : 0 < g) (hqpos : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) : Found6 w ∨
      (∀ l : ℤ, ¬ (
      1 / 6 - (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
        ≤ Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∧
      1 / 6 - (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ))
        ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∧
      Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))
        ≤ 1 / 3 + (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
          / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) ∧
      Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ 5 / 6 ∧
      1 / (3 * (w ⟨4, by omega⟩ : ℝ))
        ≤ (5 / 6 - Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))) / (w ⟨3, by omega⟩ : ℝ)
          + (Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) - 1 / 6) / (w ⟨0, by omega⟩ : ℝ) ∧
      1 / (3 * (w ⟨4, by omega⟩ : ℝ))
        ≤ (5 / 6 - Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))) / (w ⟨3, by omega⟩ : ℝ)
          + (1 / 3 - Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))) / (w ⟨1, by omega⟩ : ℝ) ∧
      Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))
        ≤ 5 / 12 - (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)))) := by
  rw [or_iff_not_imp_right]
  intro hQ
  obtain ⟨l, hl⟩ := not_forall_not.mp hQ
  obtain ⟨h39, h40, h41, hxle, h42a, h42b, h43c⟩ := hl
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  set t : ℝ := ((l : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; exact mul_ne_zero hgR hqR
  have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (l : ℝ) + 1 / 2 := by rw [htdef]; field_simp
  have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by
    rw [htdef, c0, c2]; field_simp
  have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by
    rw [htdef, c3, c2]; field_simp
  refine bhk_prop11_no_good_time_P2 w hmono hpos hsum hsmall6 t ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  · rw [e3]; exact h39
  · rw [e0]; exact h40
  · rw [e0]; exact h41
  · rw [e3]; exact hxle
  · rw [e3, e0]; exact h42a
  · rw [e3, e0]; exact h42b
  · rw [e0]; exact h43c

/-- **Pentagon `P'` avoidance, reduced coordinates** (the `core2` analog of
    `bhk_prop11_pent_no_good_red`). Transports `bhk_prop11_pent_no_good2` to the
    reduced slant form (correction terms collapsed to `r·M`, `p·M`, `(q−p)·M` with
    `M = (s−q)/(3qs)`, slants in `1/(3s)`/`/r`/`/p` form). The seventh condition
    `h43r` is BHK's (43) cut in reduced coords, `Y ≤ 5/12 − p/(3q)`. The windowed
    `(1,±2)` kills supply a grid point `l` on the rigidity line satisfying all
    seven, contradicting this. -/
lemma bhk_prop11_pent_no_good_red2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hpqlt : p < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (l : ℤ)
    (h39 : 1/6 - (r:ℝ)*(((s:ℝ)-q)/(3*q*s)) ≤ Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)))
    (h40 : 1/6 - (p:ℝ)*(((s:ℝ)-q)/(3*q*s)) ≤ Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)))
    (h41 : Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)) ≤ 1/3 + ((q:ℝ)-p)*(((s:ℝ)-q)/(3*q*s)))
    (hxle : Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)) ≤ 5/6)
    (h42a : 1/(3*(s:ℝ)) ≤ (5/6 - Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)))/r
        + (Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)) - 1/6)/p)
    (h42b : 1/(3*(s:ℝ)) ≤ (5/6 - Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)))/r
        + (1/3 - Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)))/((q:ℝ)-p))
    (h43r : Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)) ≤ 5/12 - (p:ℝ)/(3*q)) : Found6 w := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hpR0 : (0:ℝ) < p := by exact_mod_cast hp
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  have hg0 : (g:ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q:ℝ) ≠ 0 := hqR.ne'
  have hs0 : (s:ℝ) ≠ 0 := hsR.ne'
  have hr0 : (r:ℝ) ≠ 0 := hrR.ne'
  have hp0 : (p:ℝ) ≠ 0 := hpR0.ne'
  have hpqR : (p:ℝ) < q := by exact_mod_cast hpqlt
  have hqp : (0:ℝ) < (q:ℝ) - p := by linarith
  set X : ℝ := Int.fract ((r:ℝ)/q*((l:ℝ)+1/2)) with hXdef
  set Y : ℝ := Int.fract ((p:ℝ)/q*((l:ℝ)+1/2)) with hYdef
  have hmw3 : (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (r:ℝ)*(((s:ℝ)-q)/(3*q*s)) := by
    rw [c2, c3, c4]; field_simp
  have hmw0 : (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (p:ℝ)*(((s:ℝ)-q)/(3*q*s)) := by
    rw [c0, c2, c4]; field_simp
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g:ℝ) * ((q:ℝ) - p) := by
    have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast hsum
    have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
    rw [hs1, c0, c2]; ring
  have hmw1 : (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = ((q:ℝ)-p)*(((s:ℝ)-q)/(3*q*s)) := by
    rw [c1, c2, c4]; field_simp
  have e5 : (5/6 - X)/((g:ℝ)*r) + (Y - 1/6)/((g:ℝ)*p)
      = (1/(g:ℝ)) * ((5/6 - X)/r + (Y - 1/6)/p) := by field_simp
  have e6 : (5/6 - X)/((g:ℝ)*r) + (1/3 - Y)/((g:ℝ)*((q:ℝ)-p))
      = (1/(g:ℝ)) * ((5/6 - X)/r + (1/3 - Y)/((q:ℝ)-p)) := by field_simp
  have egs : (1:ℝ)/(3*((g:ℝ)*s)) = (1/(g:ℝ)) * (1/(3*s)) := by field_simp
  have hbr : (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) = (p:ℝ)/(3*q) := by
    rw [c0, c2]; field_simp
  rcases bhk_prop11_pent_no_good2 w hmono hpos hsum hsmall6 g p q r hg hq c0 c2 c3 with hF | hpent
  · exact hF
  refine False.elim <| hpent l
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmw3]; exact h39
  · rw [hmw0]; exact h40
  · rw [hmw1]; exact h41
  · exact hxle
  · rw [c4, c3, c0, e5, egs]; exact mul_le_mul_of_nonneg_left h42a (by positivity)
  · rw [c4, c3, c1, e6, egs]; exact mul_le_mul_of_nonneg_left h42b (by positivity)
  · rw [hbr]; exact h43r

set_option maxHeartbeats 800000 in
/-- **`(2,1)/(4,2)` pentagon six-condition discharge, windowed** (`core2` analog of
    `bhk_prop11_pent_six_from_Y`). Same fold `X = 2Y − 1/2` and box/slant conditions, plus the
    `(43)` constraint `Y ≤ 5/12 − p/(3q)` passed as `h43r`; targets `pent_no_good_red2`. -/
lemma bhk_prop11_pent_six_from_Y2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hpqlt : p < q) (hr32 : 2 * r < 3 * q) (hrs : r < s)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hrig : r = 2 * p + q) (l : ℤ)
    (hYlo : 1 / 4 ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)))
    (hYhi : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) < 5 / 12)
    (h39Y : 1 / 6 - (r : ℝ) * (((s : ℝ) - q) / (3 * q * s))
        ≤ 2 * Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) - 1 / 2)
    (h41 : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))
        ≤ 1 / 3 + ((q : ℝ) - p) * (((s : ℝ) - q) / (3 * q * s)))
    (h43r : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ 5 / 12 - (p : ℝ) / (3 * q)) : Found6 w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqR : (p : ℝ) < q := by exact_mod_cast hpqlt
  have hqp : (0 : ℝ) < (q : ℝ) - p := by linarith
  have hp0 : (p : ℝ) ≠ 0 := hpR0.ne'
  have hrigR : (r : ℝ) = 2 * (p : ℝ) + q := by exact_mod_cast hrig
  have hrsR : (r : ℝ) < s := by exact_mod_cast hrs
  have hr32R : 2 * (r : ℝ) < 3 * q := by exact_mod_cast hr32
  set Y : ℝ := Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) with hYdef
  set X : ℝ := Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) with hXdef
  have hXeq : X = 2 * Y - 1 / 2 := by
    have hXarg : (r : ℝ) / q * ((l : ℝ) + 1 / 2)
        = 2 * ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) + ((l : ℤ) : ℝ) + 1 / 2 := by
      rw [hrigR]; push_cast; field_simp; ring
    rw [hXdef, hXarg]
    have hfa := Int.floor_add_fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2))
    have hsplit : 2 * ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) + ((l : ℤ) : ℝ) + 1 / 2
        = ((2 * ⌊(p : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ + l + 1 : ℤ) : ℝ) + (2 * Y - 1 / 2) := by
      rw [hYdef] at *; push_cast; linarith [hfa]
    rw [hsplit, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith [hYlo], by linarith [hYhi]⟩
  have hX13 : X < 1 / 3 := by rw [hXeq]; linarith [hYhi]
  have hsq : (q : ℝ) < s := by linarith [hrsR, hrigR, hpR0]
  have hEpos : 0 < ((s : ℝ) - q) / (3 * q * s) := div_pos (by linarith [hsq]) (by positivity)
  have ht1 : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by positivity) hrR]
    nlinarith [hrsR, hsR, mul_pos (show (0 : ℝ) < 1 / 3 - X by linarith [hX13]) hsR]
  have htq : 1 / (3 * (q : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by positivity) hrR]
    nlinarith [hr32R, hqR, mul_pos (show (0 : ℝ) < 1 / 3 - X by linarith [hX13]) hqR]
  have hMq : 1 / (3 * (s : ℝ)) + ((s : ℝ) - q) / (3 * q * s) = 1 / (3 * (q : ℝ)) := by
    field_simp; ring
  refine bhk_prop11_pent_no_good_red2 w hmono hpos hsum hsmall6 g p q r s hg hq hp hr hs
    hpqlt c0 c2 c3 c4 l ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hXdef, hXeq]; exact h39Y
  · rw [← hYdef]; nlinarith [hYlo, hEpos, mul_nonneg (le_of_lt hpR0) (le_of_lt hEpos)]
  · rw [← hYdef]; exact h41
  · rw [← hXdef, hXeq]; linarith [hYhi]
  · rw [← hXdef, ← hYdef]
    have h2 : 0 ≤ (Y - 1 / 6) / p := div_nonneg (by linarith [hYlo]) hpR0.le
    linarith [ht1, h2]
  · rw [← hXdef, ← hYdef]
    rcases le_total Y (1 / 3) with hc | hc
    · have h2 : 0 ≤ (1 / 3 - Y) / ((q : ℝ) - p) := div_nonneg (by linarith) hqp.le
      linarith [ht1, h2]
    · have hub : Y - 1 / 3 ≤ ((q : ℝ) - p) * (((s : ℝ) - q) / (3 * q * s)) := by linarith [h41]
      have hle : (Y - 1 / 3) / ((q : ℝ) - p) ≤ ((s : ℝ) - q) / (3 * q * s) := by
        rw [div_le_iff₀ hqp]; linarith [hub, mul_comm ((q : ℝ) - p) (((s : ℝ) - q) / (3 * q * s))]
      have hterm : -(((s : ℝ) - q) / (3 * q * s)) ≤ (1 / 3 - Y) / ((q : ℝ) - p) := by
        rw [show (1 : ℝ) / 3 - Y = -(Y - 1 / 3) by ring, neg_div]; linarith [hle]
      linarith [htq, hterm, hMq]
  · rw [← hYdef]; exact h43r

set_option maxHeartbeats 800000 in
/-- **BHK §5 `(2,1)` pentagon kill, windowed** (`core2` analog of
    `bhk_prop11_exc_2_1_pentkill`). Same two-regime window construction targeting the `P'`
    pentagon (extra `(43)` constraint); `q ≥ 2p+6` (from `6p < q`, `q ≥ 18`) keeps both
    windows under `5/12 − p/(3q)`. -/
lemma bhk_prop11_exc_2_1_pentkill2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (h6p : 6 * p < q) (hrig : r = 2 * p + q) : Found6 w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hpqlt : p < q := by omega
  have hs3 : q + 3 ≤ s := by omega
  have hq18R : (18 : ℝ) ≤ q := by exact_mod_cast hq18
  have h6pR : 6 * (p : ℝ) < q := by exact_mod_cast h6p
  have hs3R : (q : ℝ) + 3 ≤ s := by exact_mod_cast hs3
  have h1q18 : 1 / (q : ℝ) ≤ 1 / 18 := by
    rw [div_le_div_iff₀ hqR (by norm_num)]; linarith
  set M : ℝ := ((s : ℝ) - q) / (3 * q * s) with hM
  have hMpos : 0 < M := by
    rw [hM]; exact div_pos (by linarith [hsR]) (by positivity)
  have hrigR : (r : ℝ) = 2 * (p : ℝ) + q := by exact_mod_cast hrig
  have hwin : 1 / (q : ℝ) ≤ ((s : ℝ) - q) / (2 * s) := by
    rw [div_le_div_iff₀ hqR (by linarith [hsR])]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (s : ℝ) - (q + 3) by linarith)
      (show (0 : ℝ) ≤ (q : ℝ) - 2 by linarith)]
  have hid : ((q : ℝ) - p) * M + (r : ℝ) * M / 2 = ((s : ℝ) - q) / (2 * s) := by
    rw [hM, hrigR]; field_simp; ring
  -- (43): regime-A box top stays under 5/12 − p/(3q)
  have h43A : (1 : ℝ) / 3 - (r : ℝ) * M / 2 + 1 / q ≤ 5 / 12 - (p : ℝ) / (3 * q) := by
    have key : (0 : ℝ) ≤ (s : ℝ) * (3 * q - 12) - (4 * p * q + 2 * q ^ 2) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (s : ℝ) - (q + 3) by linarith)
        (show (0 : ℝ) ≤ 3 * (q : ℝ) - 12 by linarith), h6pR, hq18R,
        sq_nonneg ((q : ℝ) - 9),
        mul_nonneg (show (0 : ℝ) ≤ (q : ℝ) - 6 * p by linarith) (show (0 : ℝ) ≤ (q : ℝ) by positivity)]
    rw [hM, hrigR, ← sub_nonneg]
    have hfrac : 5 / 12 - (p : ℝ) / (3 * q)
          - (1 / 3 - (2 * (p : ℝ) + q) * (((s : ℝ) - q) / (3 * q * s)) / 2 + 1 / q)
        = ((s : ℝ) * (3 * q - 12) - (4 * p * q + 2 * q ^ 2)) / (12 * q * s) := by
      field_simp; ring
    rw [hfrac]; exact div_nonneg key (by positivity)
  have h43B : (1 : ℝ) / 4 + 1 / q ≤ 5 / 12 - (p : ℝ) / (3 * q) := by
    rw [← sub_nonneg]
    have hfrac : 5 / 12 - (p : ℝ) / (3 * q) - (1 / 4 + 1 / q) = ((q : ℝ) - 2 * p - 6) / (6 * q) := by
      field_simp; ring
    rw [hfrac]; apply div_nonneg _ (by positivity)
    have : (2 * (p : ℝ) + 6) ≤ q := by exact_mod_cast (show 2 * p + 6 ≤ q by omega)
    linarith
  by_cases hreg : (r : ℝ) * M ≤ 1 / 6
  · obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq p hcop
      ((p : ℝ) / (2 * q)) (1 / 3 - (r : ℝ) * M / 2) (1 / q) (le_refl _)
      (by linarith [hreg]) (by nlinarith [hMpos, hrR, h1q18])
    have harg : (p : ℝ) / (2 * q) + (l : ℝ) * (p : ℝ) / (q : ℝ)
        = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
    rw [harg] at hl
    have hY_lo : 1 / 3 - (r : ℝ) * M / 2 ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) := hl.1
    have hY_hi : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ 1 / 3 - (r : ℝ) * M / 2 + 1 / q := by
      have := hl.2; linarith
    exact bhk_prop11_pent_six_from_Y2 w hmono hpos hsum hsmall6 g p q r s hg hq hp
      (by omega) (by omega) hpqlt hr32 hrs c0 c2 c3 c4 hrig l
      (by linarith [hY_lo, hreg])
      (by linarith [hY_hi, mul_pos hrR hMpos, h1q18])
      (by rw [← hM]; linarith [hY_lo])
      (by rw [← hM]; linarith [hY_hi, hwin, hid])
      (by linarith [hY_hi, h43A])
  · have hreg' : 1 / 6 < (r : ℝ) * M := not_le.mp hreg
    obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq p hcop
      ((p : ℝ) / (2 * q)) (1 / 4) (1 / q) (le_refl _)
      (by norm_num) (by linarith [h1q18])
    have harg : (p : ℝ) / (2 * q) + (l : ℝ) * (p : ℝ) / (q : ℝ)
        = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
    rw [harg] at hl
    have hY_lo : 1 / 4 ≤ Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) := hl.1
    have hY_hi : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ≤ 1 / 4 + 1 / q := by
      have := hl.2; linarith
    exact bhk_prop11_pent_six_from_Y2 w hmono hpos hsum hsmall6 g p q r s hg hq hp
      (by omega) (by omega) hpqlt hr32 hrs c0 c2 c3 c4 hrig l
      hY_lo
      (by linarith [hY_hi, h1q18])
      (by rw [← hM]; linarith [hY_lo, hreg'])
      (by rw [← hM]; nlinarith [hY_hi, h1q18, hMpos, mul_nonneg (show (0:ℝ) ≤ (q:ℝ) - p by linarith [show (p:ℝ)<q from by exact_mod_cast hpqlt]) hMpos.le])
      (by linarith [hY_hi, h43B])

set_option maxHeartbeats 3200000 in
/-- **BHK §5 Case 5.2.9 — `(1,-2)S` windowed pentagon kill** (`core2` analog of
    `bhk_prop11_exc_1_neg2_pentkill`). Same rigidity `2r+p=3q` putting the cone
    points on `Y={3/2-2X}` and the same slant window `[Xlo,Xhi]` of width
    `r(5s-4r)/(36qs)`; but for `core2` the witness must also satisfy BHK's (43) cut
    `Y ≤ 5/12 - p/(3q)`, i.e. `X ≥ Xcut := 13/24 + p/(6q)`. For `q ≥ 18` and
    `6p < q` the cut-shifted window `[max Xlo Xcut, Xhi]` still has width `≥ 1/q`
    (`Xhi - Xcut ≥ 1/q`, numerator `= s(9q-8p-72) - 8pr ≥ r(9q-16p-72) ≥ 0`), so a
    grid point lands in `P'`, contradicting `pent_no_good2`. -/
lemma bhk_prop11_exc_1_neg2_pentkill2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hwb : 36 * (s : ℝ) ≤ (r : ℝ) * (5 * s - 4 * r))
    (hq18 : 18 ≤ q) (hsmall6N : 6 * p < q)
    (hrig : 2 * r + p = 3 * q) : Found6 w := by
  obtain hF | hpent := bhk_prop11_pent_no_good2 w hmono hpos hsum hsmall6 g p q r hg hq c0 c2 c3
  · exact hF
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpR0 : (0:ℝ) < p := by exact_mod_cast hp
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  have hpq : (p:ℝ) < q := by exact_mod_cast (show p < q by omega)
  have hsq : (q:ℝ) < s := by exact_mod_cast (show q < s by omega)
  have hg0 : (g:ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q:ℝ) ≠ 0 := hqR.ne'
  have hs0 : (s:ℝ) ≠ 0 := hsR.ne'
  have hr0 : (r:ℝ) ≠ 0 := hrR.ne'
  have hp0 : (p:ℝ) ≠ 0 := hpR0.ne'
  have hqp : (0:ℝ) < (q:ℝ) - p := by linarith [hpq]
  have hqp0 : ((q:ℝ) - p) ≠ 0 := hqp.ne'
  have hsr1R : (r:ℝ) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
  have hrrR : (p:ℝ) = 3 * q - 2 * r := by
    have h : (2:ℝ) * r + p = 3 * q := by exact_mod_cast hrig
    linarith
  have hqpR : (q:ℝ) - p = 2 * ((r:ℝ) - q) := by rw [hrrR]; ring
  have hrgtq : (q:ℝ) < r := by exact_mod_cast hrq
  have hq18R : (18:ℝ) ≤ q := by exact_mod_cast hq18
  have h6pR : 6 * (p:ℝ) < q := by exact_mod_cast hsmall6N
  have hrigR : (2:ℝ) * r + p = 3 * q := by exact_mod_cast hrig
  have hcop_rq : Nat.Coprime r q := by
    have h1 : Nat.gcd r q ∣ r := Nat.gcd_dvd_left r q
    have h2 : Nat.gcd r q ∣ q := Nat.gcd_dvd_right r q
    have h2r : Nat.gcd r q ∣ 2 * r := h1.mul_left 2
    have h2rp : Nat.gcd r q ∣ 2 * r + p := by rw [hrig]; exact h2.mul_left 3
    have hd : Nat.gcd r q ∣ p := (Nat.dvd_add_right h2r).mp h2rp
    have hg1 : Nat.gcd r q ∣ 1 := hcop ▸ Nat.dvd_gcd hd (Nat.gcd_dvd_right r q)
    exact Nat.dvd_one.mp hg1
  set M : ℝ := ((s:ℝ) - q) / (3 * (q:ℝ) * (s:ℝ)) with hM
  have hMpos : 0 < M := by
    rw [hM]; exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hqR) hsR)
  set Da : ℝ := 1/(r:ℝ) + 2/(p:ℝ) with hDa
  set Na : ℝ := 5/(6*(r:ℝ)) + 4/(3*(p:ℝ)) - 1/(3*(s:ℝ)) with hNa
  set Db : ℝ := 2/((q:ℝ)-p) - 1/(r:ℝ) with hDb
  set Nb : ℝ := 1/(3*(s:ℝ)) - 5/(6*(r:ℝ)) + 7/(6*((q:ℝ)-p)) with hNb
  have hDapos : 0 < Da := by rw [hDa]; exact add_pos (div_pos one_pos hrR) (div_pos (by norm_num) hpR0)
  have hDbpos : 0 < Db := by
    rw [hDb, sub_pos, div_lt_div_iff₀ hrR hqp]; rw [hqpR]; nlinarith [hrgtq, hrR]
  set Xhi : ℝ := Na / Da with hXhi
  set Xlo : ℝ := Nb / Db with hXlo
  have hpp2r : (0:ℝ) < (p:ℝ) + 2*r := by linarith [hpR0, hrR]
  have h2rqp : (0:ℝ) < 2*(r:ℝ) - ((q:ℝ)-p) := by
    have h := hDbpos; rw [hDb, sub_pos, div_lt_div_iff₀ hrR hqp] at h; linarith [h]
  have hXhi_eq : Xhi = (5*(p:ℝ)*s + 8*r*s - 2*r*p) / (6*s*((p:ℝ)+2*r)) := by
    rw [hXhi, hNa, hDa]; field_simp; ring
  have hXlo_eq : Xlo = (2*(r:ℝ)*((q:ℝ)-p) - 5*s*((q:ℝ)-p) + 7*r*s) / (6*s*(2*(r:ℝ)-((q:ℝ)-p))) := by
    rw [hXlo, hNb, hDb]; field_simp; ring
  have hwidth : Xhi - Xlo = (r:ℝ) * (5*s - 4*r) / (36 * q * s) := by
    rw [hXhi_eq, hXlo_eq]
    have e1 : (p:ℝ) + 2*r = 3*q := by rw [hrrR]; ring
    have e2 : 2*(r:ℝ) - ((q:ℝ)-p) = 2*q := by rw [hrrR]; ring
    rw [e1, e2, hrrR]; field_simp; ring
  have hw : 1 / (q:ℝ) ≤ Xhi - Xlo := by
    rw [hwidth, div_le_div_iff₀ hqR (by positivity)]
    nlinarith [hwb, hqR, hsR, hrR]
  have h4r3q : 3*(q:ℝ) < 4*r := by
    have : (8:ℝ)*q + 1 ≤ 6*r := by exact_mod_cast (show 8*q + 1 ≤ 6*r by omega)
    linarith
  have hp2r : (p:ℝ) < 2*r := by rw [hrrR]; linarith [h4r3q]
  have h3r7q : 3*(r:ℝ) < 7*q := by
    have : (2:ℝ)*r < 3*q := by exact_mod_cast hr32
    linarith
  have hXhi34 : Xhi < 3/4 := by
    have hid : (3:ℝ)/4 * Da - Na = 1/(3*s) - 1/(12*r) + 1/(6*p) := by
      rw [hNa, hDa]; field_simp; ring
    have hpos' : 0 < (3:ℝ)/4 * Da - Na := by
      rw [hid]
      have h1 : 1/(12*(r:ℝ)) < 1/(6*p) := by
        rw [div_lt_div_iff₀ (by linarith [hrR]) (by linarith [hpR0])]; nlinarith [hp2r]
      have h2 : (0:ℝ) < 1/(3*s) := by positivity
      linarith [h1, h2]
    rw [hXhi, div_lt_iff₀ hDapos]; linarith [hpos']
  have hXlo14 : 1/4 < Xlo := by
    have hid : Nb - (1:ℝ)/4 * Db = 1/(3*s) - 7/(12*r) + 2/(3*((q:ℝ)-p)) := by
      rw [hNb, hDb]; field_simp; ring
    have hpos' : 0 < Nb - (1:ℝ)/4 * Db := by
      rw [hid]
      have h1 : 7/(12*(r:ℝ)) < 2/(3*((q:ℝ)-p)) := by
        rw [div_lt_div_iff₀ (by linarith [hrR]) (by linarith [hqp]), hqpR]; nlinarith [h3r7q]
      have h2 : (0:ℝ) < 1/(3*s) := by positivity
      linarith [h1, h2]
    rw [hXlo, lt_div_iff₀ hDbpos]; linarith [hpos']
  -- (43) cut: Xcut = 13/24 + p/(6q); the cut-shifted window still has width ≥ 1/q
  set Xcut : ℝ := 13/24 + (p:ℝ)/(6*q) with hXcut
  have hXhi3 : Xhi = (5*(p:ℝ)*s + 8*r*s - 2*r*p) / (18*q*s) := by
    rw [hXhi_eq, show (6:ℝ)*s*((p:ℝ)+2*r) = 18*q*s from by rw [hrrR]; ring]
  have hwcut : (1:ℝ)/q ≤ Xhi - Xcut := by
    rw [hXhi3, hXcut]
    exact bhk_prop11_cut_width_aux p q r s hpR0 hrR hsR hqR hrigR hq18R h6pR (by linarith [hsr1R])
  have hXcutlo : 1/4 < Xcut := by
    rw [hXcut]; have : (0:ℝ) < (p:ℝ)/(6*q) := by positivity
    linarith
  -- place a grid point in the cut-shifted slant window [max Xlo Xcut, Xhi]
  have hwmax : 1/(q:ℝ) ≤ Xhi - max Xlo Xcut := by
    have : max Xlo Xcut ≤ Xhi - 1/q := max_le (by linarith [hw]) (by linarith [hwcut])
    linarith
  have hmax0 : 0 ≤ max Xlo Xcut := le_trans (by norm_num) (le_trans hXlo14.le (le_max_left _ _))
  have hmax1 : max Xlo Xcut + (Xhi - max Xlo Xcut) ≤ 1 := by
    have : max Xlo Xcut + (Xhi - max Xlo Xcut) = Xhi := by ring
    rw [this]; linarith [hXhi34]
  obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq r hcop_rq
    ((r : ℝ) / (2 * q)) (max Xlo Xcut) (Xhi - max Xlo Xcut) hwmax hmax0 hmax1
  have harg : (r : ℝ) / (2 * q) + (l : ℝ) * (r : ℝ) / (q : ℝ)
      = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
  rw [harg] at hl
  set X : ℝ := Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) with hXdef
  have hXmax : max Xlo Xcut ≤ X := hl.1
  have hX_lo : Xlo ≤ X := le_trans (le_max_left _ _) hXmax
  have hX_cut : Xcut ≤ X := le_trans (le_max_right _ _) hXmax
  have hX_hi : X ≤ Xhi := by have h := hl.2; linarith
  have hX14 : 1/4 < X := lt_of_lt_of_le hXlo14 hX_lo
  have hX34 : X < 3/4 := lt_of_le_of_lt hX_hi hXhi34
  set Y : ℝ := Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) with hYdef
  have hYeq : Y = 3/2 - 2*X := by
    have hYarg : (p : ℝ) / q * ((l : ℝ) + 1 / 2)
        = ((3*l + 1 : ℤ) : ℝ) + (1/2 - 2*((r : ℝ) / q * ((l : ℝ) + 1 / 2))) := by
      rw [hrrR]; push_cast; field_simp; ring
    rw [hYdef, hYarg, Int.fract_intCast_add]
    have hsplit : (1:ℝ)/2 - 2*((r : ℝ) / q * ((l : ℝ) + 1 / 2))
        = ((-2*⌊(r : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ : ℤ) : ℝ) + (1/2 - 2*X) := by
      have hfa := Int.floor_add_fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))
      rw [hXdef]; push_cast; linarith [hfa]
    rw [hsplit, Int.fract_intCast_add,
        show (1:ℝ)/2 - 2*X = (3/2 - 2*X) + ((-1 : ℤ) : ℝ) from by push_cast; ring,
        Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith [hX34], by linarith [hX14]⟩
  have hbox_hi : Xhi ≤ 2/3 + (p:ℝ)*M/2 := by
    have hkey : (2:ℝ)/3 + (p:ℝ)*M/2 - Xhi = ((p:ℝ)*(2*s+2*r-3*q)) / (18*q*s) := by
      rw [hXhi_eq, hM, show (6:ℝ)*s*((p:ℝ)+2*r) = 18*q*s from by rw [hrrR]; ring, hrrR]
      field_simp; ring
    have hnn : 0 ≤ ((p:ℝ)*(2*s+2*r-3*q)) / (18*q*s) := by
      apply div_nonneg (mul_nonneg hpR0.le (by nlinarith [hsr1R, h4r3q])) (by positivity)
    linarith [hkey, hnn]
  have hbox_lo : 7/12 - ((q:ℝ)-p)*M/2 ≤ Xlo := by
    have hkey : Xlo - (7/12 - ((q:ℝ)-p)*M/2) = (((r:ℝ)-q)*(4*r-4*q+s)) / (12*q*s) := by
      rw [hXlo_eq, hM, show (6:ℝ)*s*(2*(r:ℝ)-((q:ℝ)-p)) = 12*q*s from by rw [hrrR]; ring, hrrR]
      field_simp; ring
    have hnn : 0 ≤ (((r:ℝ)-q)*(4*r-4*q+s)) / (12*q*s) := by
      apply div_nonneg (mul_nonneg (by linarith [hrgtq]) (by nlinarith [hrgtq, hsR])) (by positivity)
    linarith [hkey, hnn]
  have hmw3 : (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (r : ℝ) * M := by
    rw [c2, c3, c4, hM]; field_simp
  have hmw0 : (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (p : ℝ) * M := by
    rw [c0, c2, c4, hM]; field_simp
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - p) := by
    have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast hsum
    have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
    rw [hs1, c0, c2]; ring
  have hmw1 : (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = ((q : ℝ) - p) * M := by
    rw [c1, c2, c4, hM]; field_simp
  have key_a : 1/(3*(s:ℝ)) ≤ (5/6 - X)/r + (Y - 1/6)/p := by
    rw [hYeq]
    have h2 : Da * Xhi = Na := by rw [hXhi]; field_simp [hDapos.ne']
    have h3 : Na - Da*X = (5/6 - X)/r + (3/2 - 2*X - 1/6)/p - 1/(3*s) := by rw [hNa, hDa]; ring
    nlinarith [mul_le_mul_of_nonneg_left hX_hi hDapos.le, h2, h3]
  have key_b : 1/(3*(s:ℝ)) ≤ (5/6 - X)/r + (1/3 - Y)/((q:ℝ) - p) := by
    rw [hYeq]
    have h2 : Db * Xlo = Nb := by rw [hXlo]; field_simp [hDbpos.ne']
    have h3 : Db*X - Nb = (5/6 - X)/r + (1/3 - (3/2 - 2*X))/((q:ℝ) - p) - 1/(3*s) := by
      rw [hNb, hDb]; field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left hX_lo hDbpos.le, h2, h3]
  have e5 : (5/6 - X)/((g:ℝ)*r) + (Y - 1/6)/((g:ℝ)*p)
      = (1/(g:ℝ)) * ((5/6 - X)/r + (Y - 1/6)/p) := by field_simp
  have e6 : (5/6 - X)/((g:ℝ)*r) + (1/3 - Y)/((g:ℝ)*((q:ℝ)-p))
      = (1/(g:ℝ)) * ((5/6 - X)/r + (1/3 - Y)/((q:ℝ)-p)) := by field_simp
  have egs : (1:ℝ)/(3*((g:ℝ)*s)) = (1/(g:ℝ)) * (1/(3*s)) := by field_simp
  have hbr2 : (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) = (p:ℝ)/(3*q) := by
    rw [c0, c2]; field_simp
  refine False.elim <| hpent l ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmw3, ← hXdef]; linarith [hX14, mul_nonneg hrR.le hMpos.le]
  · rw [hmw0, ← hYdef, hYeq]; linarith [hX_hi, hbox_hi]
  · rw [hmw1, ← hYdef, hYeq]; linarith [hX_lo, hbox_lo]
  · rw [← hXdef]; linarith [hX34]
  · rw [← hXdef, ← hYdef, c4, c3, c0, e5, egs]
    exact mul_le_mul_of_nonneg_left key_a (by positivity)
  · rw [← hXdef, ← hYdef, c4, c3, c1, e6, egs]
    exact mul_le_mul_of_nonneg_left key_b (by positivity)
  · rw [← hYdef, hYeq, hbr2]; rw [hXcut] at hX_cut
    have hpp : (p:ℝ)/(3*q) = 2*((p:ℝ)/(6*q)) := by ring
    linarith [hX_cut, hpp]

/-- **Pentagon `P'` grid-witness applicator, windowed** (the `core2` analog of
    `bhk_prop11_exc_1_neg2_witness`). Given a closed-form witness `(l, X, Y)`
    satisfying the six reduced `P` conditions *and* the (43) cut `Y ≤ 5/12 − p/(3q)`,
    discharge `pent_no_good_red2`. Used for the windowed narrow tail. -/
lemma bhk_prop11_exc_1_neg2_witness2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hr : 0 < r) (hs : 0 < s)
    (hpqlt : p < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (l : ℤ) (X Y : ℝ)
    (hX : Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) = X)
    (hY : Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) = Y)
    (h39 : 1 / 6 - (r : ℝ) * (((s : ℝ) - q) / (3 * q * s)) ≤ X)
    (h40 : 1 / 6 - (p : ℝ) * (((s : ℝ) - q) / (3 * q * s)) ≤ Y)
    (h41 : Y ≤ 1 / 3 + ((q : ℝ) - p) * (((s : ℝ) - q) / (3 * q * s)))
    (hxle : X ≤ 5 / 6)
    (h42a : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r + (Y - 1 / 6) / p)
    (h42b : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r + (1 / 3 - Y) / ((q : ℝ) - p))
    (h43w : Y ≤ 5 / 12 - (p : ℝ) / (3 * q)) : Found6 w := by
  refine bhk_prop11_pent_no_good_red2 w hmono hpos hsum hsmall6 g p q r s hg hq hp hr hs
    hpqlt c0 c2 c3 c4 l ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hX]; exact h39
  · rw [hY]; exact h40
  · rw [hY]; exact h41
  · rw [hX]; exact hxle
  · rw [hX, hY]; exact h42a
  · rw [hX, hY]; exact h42b
  · rw [hY]; exact h43w

set_option maxHeartbeats 4000000 in
/-- **BHK §5 Case 5.2.9 — `(1,-2)S` narrow-window tail, windowed** (`core2` analog of
    `bhk_prop11_exc_1_neg2_small`). In `core2` (`6p < q`) the narrow tuples reduce
    further: of the part-1 seven, only `(q,r,p) ∈ {(19,27,3),(19,28,1),(21,31,1)}`
    survive `6p < q` (the rest are killed by `omega` from `hsmall6N`). Each is closed
    by an explicit `P'`-witness (the part-1 witness, which also clears the (43) cut). -/
lemma bhk_prop11_exc_1_neg2_small2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hsmall6N : 6 * p < q) (hnar : (r : ℝ) * (5 * s - 4 * r) < 36 * s)
    (hrig : 2 * r + p = 3 * q) : Found6 w := by
  have hnar_nat : 5 * r * s < 4 * r * r + 36 * s := by
    have hsr : (r : ℝ) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
    have hR : ((5 * r * s : ℕ) : ℝ) < ((4 * r * r + 36 * s : ℕ) : ℝ) := by
      push_cast; nlinarith [hnar]
    exact_mod_cast hR
  have h4q3r : 4 * q < 3 * r := by omega
  have hr_ub : r ≤ 32 := by
    by_contra h
    have h33 : 33 ≤ r := by omega
    have hrR : (33 : ℝ) ≤ r := by exact_mod_cast h33
    have hsR : (r : ℝ) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
    nlinarith [hnar, mul_nonneg (show (0 : ℝ) ≤ (s : ℝ) - ((r : ℝ) + 1) by linarith)
        (show (0 : ℝ) ≤ 5 * (r : ℝ) - 36 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ (r : ℝ) - 33 by linarith) (show (0 : ℝ) ≤ (r : ℝ) by positivity)]
  have hq_ub : q ≤ 23 := by omega
  have hp_ub : p ≤ 7 := by omega
  interval_cases q <;> interval_cases r <;> interval_cases p <;>
    (first | omega | (exfalso; revert hcop; decide) | skip)
  · -- (19, 27, 3): s ∈ {28, 29}
    have hs_ub : s ≤ 29 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness2 w hmono hpos hsum hsmall6 g 3 19 27 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-37) (5 / 38) (9 / 38)
        (by rw [show ((27 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-52 : ℤ) : ℝ) + 5 / 38 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-6 : ℤ) : ℝ) + 9 / 38 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
  · -- (19, 28, 1): s ∈ {29, 30}
    have hs_ub : s ≤ 30 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness2 w hmono hpos hsum hsmall6 g 1 19 28 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-35) (3 / 19) (7 / 38)
        (by rw [show ((28 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-35 : ℤ) : ℝ) + 1 / 2)
                = ((-51 : ℤ) : ℝ) + 3 / 19 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ) * (((-35 : ℤ) : ℝ) + 1 / 2)
                = ((-2 : ℤ) : ℝ) + 7 / 38 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)
  · -- (21, 31, 1): s = 32
    have hs_ub : s ≤ 32 := by omega
    interval_cases s <;>
      exact bhk_prop11_exc_1_neg2_witness2 w hmono hpos hsum hsmall6 g 1 21 31 _
        hg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        c0 c2 c3 c4 (-37) (5 / 42) (11 / 42)
        (by rw [show ((31 : ℕ) : ℝ) / ((21 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-54 : ℤ) : ℝ) + 5 / 42 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by rw [show ((1 : ℕ) : ℝ) / ((21 : ℕ) : ℝ) * (((-37 : ℤ) : ℝ) + 1 / 2)
                = ((-2 : ℤ) : ℝ) + 11 / 42 by push_cast; norm_num,
              Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩])
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)

/-- **BHK §5 Case 5.2.9 — `(1,-2)S` dispatcher, windowed** (`core2` analog of
    `bhk_prop11_exc_1_neg2_kill`). Splits on the slant width: wide → `pentkill2`,
    narrow → `small2`. -/
lemma bhk_prop11_exc_1_neg2_kill2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hsmall6N : 6 * p < q) (hrig : 2 * r + p = 3 * q) : Found6 w := by
  by_cases hwb : 36 * (s : ℝ) ≤ (r : ℝ) * (5 * s - 4 * r)
  · exact bhk_prop11_exc_1_neg2_pentkill2 w hmono hpos hsum hsmall6 g p q r s hg hq
      c0 c2 c3 c4 hcop hp h3p hrq hr32 hrs hwb hq18 hsmall6N hrig
  · exact bhk_prop11_exc_1_neg2_small2 w hmono hpos hsum hsmall6 g p q r s hg hq
      c0 c2 c3 c4 hcop hp h3p hrq hr32 hrs hq18 hsmall6N (not_le.mp hwb) hrig

set_option maxHeartbeats 3200000 in
/-- **BHK §5 Case 5.2.11 — `(1,2)U` windowed pentagon kill** (`core2` analog of
    `bhk_prop11_exc_1_2_pentkill`). Rigidity `2r = 2q + p` puts the cone points on
    `Y = {2X}`; for `core2` the witness must additionally clear BHK's (43) cut
    `Y ≤ 5/12 − p/(3q)`, i.e. `X ≤ Xcut2 := 5/24 − p/(6q)`. Part 1's window (near
    `h41`, `Y ≈ 1/3`) violates (43), so we use the *lower* window
    `[max X39 X40, min Xv Xcut2]` with `X39 = 1/6 − rM`, `X40 = 1/12 − pM/2`,
    `Xv = 1/6 + (q−p)M/2`, `M = (s−q)/(3qs)`. For `q ≥ 18`, `6p < q` it has width
    `≥ 1/q` (`X40 > 0` always since `pM < 1/18`), so a grid point lands in `P'`,
    contradicting `pent_no_good2`. No special `s = q+2` case is needed. -/
lemma bhk_prop11_exc_1_2_pentkill2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hsmall6N : 6 * p < q) (hrig : 2 * r = 2 * q + p)
    (hs3 : q + 3 ≤ s) : Found6 w := by
  obtain hF | hpent := bhk_prop11_pent_no_good2 w hmono hpos hsum hsmall6 g p q r hg hq c0 c2 c3
  · exact hF
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hpR0 : (0:ℝ) < p := by exact_mod_cast hp
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  have hpq : (p:ℝ) < q := by exact_mod_cast (show p < q by omega)
  have hsq : (q:ℝ) < s := by exact_mod_cast (show q < s by omega)
  have hg0 : (g:ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q:ℝ) ≠ 0 := hqR.ne'
  have hs0 : (s:ℝ) ≠ 0 := hsR.ne'
  have hr0 : (r:ℝ) ≠ 0 := hrR.ne'
  have hp0 : (p:ℝ) ≠ 0 := hpR0.ne'
  have hqp : (0:ℝ) < (q:ℝ) - p := by linarith [hpq]
  have hqp0 : ((q:ℝ) - p) ≠ 0 := hqp.ne'
  have hsr1 : (r:ℝ) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
  have hrgtqR : (q:ℝ) < r := by exact_mod_cast hrq
  have hq18R : (18:ℝ) ≤ q := by exact_mod_cast hq18
  have h6pR : 6 * (p:ℝ) < q := by exact_mod_cast hsmall6N
  have hrigR : (2:ℝ) * r = 2 * q + p := by exact_mod_cast hrig
  have hr32R : 2 * (r:ℝ) < 3 * q := by exact_mod_cast hr32
  have hrsR : (r:ℝ) < s := by exact_mod_cast hrs
  have hrr : (p:ℝ) = 2 * r - 2 * q := by linarith [hrigR]
  have hcop_rq : Nat.Coprime r q := by
    have h1 : Nat.gcd r q ∣ r := Nat.gcd_dvd_left r q
    have h2 : Nat.gcd r q ∣ q := Nat.gcd_dvd_right r q
    have h2q : Nat.gcd r q ∣ 2 * q := h2.mul_left 2
    have h2r : Nat.gcd r q ∣ 2 * q + p := by rw [← hrig]; exact h1.mul_left 2
    have hd : Nat.gcd r q ∣ p := (Nat.dvd_add_right h2q).mp h2r
    have hg1 : Nat.gcd r q ∣ 1 := hcop ▸ Nat.dvd_gcd hd (Nat.gcd_dvd_right r q)
    exact Nat.dvd_one.mp hg1
  set M : ℝ := ((s:ℝ) - q) / (3 * (q:ℝ) * (s:ℝ)) with hM
  have hMpos : 0 < M := by
    rw [hM]; exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hqR) hsR)
  -- the three pentagon margins in reduced form
  have hmw3 : (w ⟨3, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (r : ℝ) * M := by
    rw [c2, c3, c4, hM]; field_simp
  have hmw0 : (w ⟨0, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = (p : ℝ) * M := by
    rw [c0, c2, c4, hM]; field_simp
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - p) := by
    have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
      exact_mod_cast hsum
    have hs1 : (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
    rw [hs1, c0, c2]; ring
  have hmw1 : (w ⟨1, by omega⟩ : ℝ) * ((w ⟨4, by omega⟩ : ℝ) - (w ⟨2, by omega⟩ : ℝ))
      / (3 * (w ⟨2, by omega⟩ : ℝ) * (w ⟨4, by omega⟩ : ℝ)) = ((q : ℝ) - p) * M := by
    rw [c1, c2, c4, hM]; field_simp
  have hbr2 : (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) = (p:ℝ)/(3*q) := by
    rw [c0, c2]; field_simp
  -- X40 > 0  (since pM < 1/18 from 6p < q)
  have hpM18 : (p:ℝ)*M < 1/18 := by
    have hqM : (q:ℝ)*M = ((s:ℝ)-q)/(3*s) := by rw [hM]; field_simp
    have hfrac : ((s:ℝ)-q)/(3*s) < 1/3 := by
      rw [div_lt_div_iff₀ (by linarith [hsR]) (by norm_num)]; linarith [hqR]
    have hpqM : (p:ℝ)*M < (q:ℝ)*M / 6 := by nlinarith [hMpos, h6pR]
    nlinarith [hpqM, hqM, hfrac]
  have hX40pos : (0:ℝ) < 1/12 - (p:ℝ)*M/2 := by linarith [hpM18]
  -- width facts on the lower window
  have hq118 : 1/(q:ℝ) ≤ 1/18 := by
    rw [div_le_div_iff₀ hqR (by norm_num)]; linarith [hq18R]
  have hwin39v : (1/6 - (r:ℝ)*M) + 1/q ≤ 1/6 + ((q:ℝ)-p)*M/2 := by
    have hkey : ((q:ℝ)-p)*M/2 + (r:ℝ)*M = ((s:ℝ)-q)/(2*s) := by rw [hrr, hM]; field_simp; ring
    have hwin : 1/(q:ℝ) ≤ ((q:ℝ)-p)*M/2 + (r:ℝ)*M := by
      rw [hkey, div_le_div_iff₀ hqR (by linarith [hsR])]
      have hs3R : (q:ℝ) + 3 ≤ s := by exact_mod_cast hs3
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (s:ℝ) - (q + 3) by linarith)
        (show (0:ℝ) ≤ (q:ℝ) - 2 by linarith)]
    linarith [hwin]
  have hwin40v : (1/12 - (p:ℝ)*M/2) + 1/q ≤ 1/6 + ((q:ℝ)-p)*M/2 := by
    have : 0 < (q:ℝ)*M := mul_pos hqR hMpos
    nlinarith [hq118, this]
  have hwin40c : (1/12 - (p:ℝ)*M/2) + 1/q ≤ 5/24 - (p:ℝ)/(6*q) := by
    have hp6q : (p:ℝ)/(6*q) < 1/36 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [h6pR]
    have hpMnn : 0 ≤ (p:ℝ)*M/2 := by positivity
    linarith [hq118, hp6q, hpMnn]
  have hwin39c : (1/6 - (r:ℝ)*M) + 1/q ≤ 5/24 - (p:ℝ)/(6*q) := by
    have hcw := bhk_prop11_cut_width_pos2_aux p q r s hpR0 hrR hsR hqR hrigR hq18R h6pR hsr1 hrgtqR
    rw [hM]; linarith [hcw]
  -- place a grid point in the lower window [max X39 X40, min Xv Xcut2]
  have hwmax : 1/(q:ℝ) ≤ min (1/6 + ((q:ℝ)-p)*M/2) (5/24 - (p:ℝ)/(6*q))
      - max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2) := by
    have hmaxC : max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2) ≤ (1/6 + ((q:ℝ)-p)*M/2) - 1/q :=
      max_le (by linarith [hwin39v]) (by linarith [hwin40v])
    have hmaxD : max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2) ≤ (5/24 - (p:ℝ)/(6*q)) - 1/q :=
      max_le (by linarith [hwin39c]) (by linarith [hwin40c])
    have key : max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2) + 1/q
        ≤ min (1/6 + ((q:ℝ)-p)*M/2) (5/24 - (p:ℝ)/(6*q)) :=
      le_min (by linarith [hmaxC]) (by linarith [hmaxD])
    linarith [key]
  have hmax0 : (0:ℝ) ≤ max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2) :=
    le_trans hX40pos.le (le_max_right _ _)
  have hmax1 : max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2)
      + (min (1/6 + ((q:ℝ)-p)*M/2) (5/24 - (p:ℝ)/(6*q))
          - max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2)) ≤ 1 := by
    have hmm : min (1/6 + ((q:ℝ)-p)*M/2) (5/24 - (p:ℝ)/(6*q)) ≤ 5/24 - (p:ℝ)/(6*q) :=
      min_le_right _ _
    have h5 : (5:ℝ)/24 - (p:ℝ)/(6*q) < 1 := by
      have : 0 < (p:ℝ)/(6*q) := by positivity
      linarith
    linarith [hmm, h5]
  obtain ⟨l, hl⟩ := bhk_prop11_grid_hit_coset_step q hq r hcop_rq ((r : ℝ) / (2 * q))
    (max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2))
    (min (1/6 + ((q:ℝ)-p)*M/2) (5/24 - (p:ℝ)/(6*q)) - max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2))
    hwmax hmax0 hmax1
  have harg : (r : ℝ) / (2 * q) + (l : ℝ) * (r : ℝ) / (q : ℝ)
      = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by field_simp; ring
  rw [harg] at hl
  set X : ℝ := Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) with hXdef
  have hXlo : max (1/6 - (r:ℝ)*M) (1/12 - (p:ℝ)*M/2) ≤ X := hl.1
  have hX39 : 1/6 - (r:ℝ)*M ≤ X := le_trans (le_max_left _ _) hXlo
  have hX40 : 1/12 - (p:ℝ)*M/2 ≤ X := le_trans (le_max_right _ _) hXlo
  have hXhi : X ≤ min (1/6 + ((q:ℝ)-p)*M/2) (5/24 - (p:ℝ)/(6*q)) := by
    have h := hl.2; linarith [h]
  have hXv : X ≤ 1/6 + ((q:ℝ)-p)*M/2 := le_trans hXhi (min_le_left _ _)
  have hXcut : X ≤ 5/24 - (p:ℝ)/(6*q) := le_trans hXhi (min_le_right _ _)
  have hX13 : X < 1/3 := by
    have : (0:ℝ) < (p:ℝ)/(6*q) := by positivity
    linarith [hXcut]
  have hXnn : 0 ≤ X := by rw [hXdef]; exact Int.fract_nonneg _
  -- Y = {2X}
  set Y : ℝ := Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) with hYdef
  have hYeq : Y = 2 * X := by
    have hYarg : (p : ℝ) / q * ((l : ℝ) + 1 / 2)
        = 2 * ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) - ((2 * l + 1 : ℤ) : ℝ) := by
      rw [hrr]; push_cast; field_simp
    rw [hYdef, hYarg, Int.fract_sub_intCast]
    have hsplit : 2 * ((r : ℝ) / q * ((l : ℝ) + 1 / 2))
        = ((2 * ⌊(r : ℝ) / q * ((l : ℝ) + 1 / 2)⌋ : ℤ) : ℝ) + 2 * X := by
      have hfa := Int.floor_add_fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2))
      rw [hXdef]; push_cast; linarith [hfa]
    rw [hsplit, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith [hXnn], by linarith [hX13]⟩
  -- slant inequalities
  have htq : 1 / (3 * (q : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by linarith [hqR]) hrR]
    nlinarith [hr32R, hqR, mul_pos (show (0:ℝ) < 1 / 3 - X by linarith [hX13]) hqR]
  have ht1 : 1 / (3 * (s : ℝ)) ≤ (5 / 6 - X) / r := by
    rw [div_le_div_iff₀ (by linarith [hsR]) hrR]
    nlinarith [hrsR, hsR, mul_pos (show (0:ℝ) < 1 / 3 - X by linarith [hX13]) hsR]
  have hMq : 1 / (3 * (s : ℝ)) + M = 1 / (3 * (q : ℝ)) := by rw [hM]; field_simp; ring
  have key_a : 1/(3*(s:ℝ)) ≤ (5/6 - X)/r + (Y - 1/6)/p := by
    rw [hYeq]
    have hdefa : -M ≤ (2*X - 1/6)/p := by rw [le_div_iff₀ hpR0]; nlinarith [hX40]
    linarith [htq, hdefa, hMq]
  have key_b : 1/(3*(s:ℝ)) ≤ (5/6 - X)/r + (1/3 - Y)/((q:ℝ) - p) := by
    rw [hYeq]
    rcases le_total (2*X) (1/3) with hc | hc
    · have ht2 : 0 ≤ (1/3 - 2*X)/((q:ℝ)-p) := div_nonneg (by linarith) hqp.le
      linarith [ht1, ht2]
    · have hub : 2*X - 1/3 ≤ ((q:ℝ)-p)*M := by linarith [hXv]
      have hle : (2*X - 1/3)/((q:ℝ)-p) ≤ M := by rw [div_le_iff₀ hqp]; nlinarith [hub]
      have hterm : -M ≤ (1/3 - 2*X)/((q:ℝ)-p) := by
        rw [show (1:ℝ)/3 - 2*X = -(2*X - 1/3) by ring, neg_div]; linarith [hle]
      linarith [htq, hterm, hMq]
  have e5 : (5/6 - X)/((g:ℝ)*r) + (Y - 1/6)/((g:ℝ)*p)
      = (1/(g:ℝ)) * ((5/6 - X)/r + (Y - 1/6)/p) := by field_simp
  have e6 : (5/6 - X)/((g:ℝ)*r) + (1/3 - Y)/((g:ℝ)*((q:ℝ)-p))
      = (1/(g:ℝ)) * ((5/6 - X)/r + (1/3 - Y)/((q:ℝ)-p)) := by field_simp
  have egs : (1:ℝ)/(3*((g:ℝ)*s)) = (1/(g:ℝ)) * (1/(3*s)) := by field_simp
  refine False.elim <| hpent l ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmw3, ← hXdef]; linarith [hX39]
  · rw [hmw0, ← hYdef, hYeq]; linarith [hX40]
  · rw [hmw1, ← hYdef, hYeq]; linarith [hXv]
  · rw [← hXdef]; linarith [hX13]
  · rw [← hXdef, ← hYdef, c4, c3, c0, e5, egs]
    exact mul_le_mul_of_nonneg_left key_a (by positivity)
  · rw [← hXdef, ← hYdef, c4, c3, c1, e6, egs]
    exact mul_le_mul_of_nonneg_left key_b (by positivity)
  · rw [← hYdef, hYeq, hbr2]
    have hpp : (p:ℝ)/(3*q) = 2*((p:ℝ)/(6*q)) := by ring
    linarith [hXcut, hpp]

/-- **BHK §5 Case 5.2.11 — `(1,2)U` special case `s = q+2`, windowed** (`core2`
    analog of `bhk_prop11_exc_1_2_special`). Here the horizontal pigeonhole window
    is too narrow (`< 1/q`), so BHK's direct witness applies: with speeds
    `2, q−2, q, q+1, q+2` (times `g`), pick odd `m` with `1/6 ≤ m/q ≤ 1/3` and set
    `t = m/(2qg)`. Every `circDist(wᵢ t) ≥ 1/6`, *and* the fictional runner is safe
    (`2·{w₀t} = 2(m/q) ∈ [1/3,2/3]`, so `circDist ≥ 1/3`), so neither covering
    disjunct holds — a `0123456`-gap contradicting the six-runner cover. -/
lemma bhk_prop11_exc_1_2_special2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (g q : ℕ) (hg : 0 < g) (hq9 : 9 ≤ q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * 2)
    (c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - 2))
    (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 1))
    (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 2)) : Found6 w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hg0 : (g : ℝ) ≠ 0 := hgR.ne'
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  obtain ⟨m, hmodd, hm6, hm3⟩ : ∃ m : ℕ, Odd m ∧ q ≤ 6 * m ∧ 3 * m ≤ q := by
    rcases Nat.even_or_odd (q / 6 + 1) with ⟨k, hk⟩ | ho
    · exact ⟨q / 6 + 2, ⟨k, by omega⟩, by omega, by omega⟩
    · exact ⟨q / 6 + 1, ho, by omega, by omega⟩
  obtain ⟨j, hj⟩ := hmodd
  have hmjR : (m : ℝ) = 2 * (j : ℝ) + 1 := by exact_mod_cast hj
  have hm6R : (q : ℝ) ≤ 6 * m := by exact_mod_cast hm6
  have hm3R : 3 * (m : ℝ) ≤ q := by exact_mod_cast hm3
  have hmq_lo : (1 : ℝ) / 6 ≤ (m : ℝ) / q := by rw [le_div_iff₀ hqR]; linarith
  have hmq_hi : (m : ℝ) / q ≤ 1 / 3 := by rw [div_le_iff₀ hqR]; linarith
  set t : ℝ := (m : ℝ) / (2 * q * g) with htdef
  have key : ∀ (W y : ℝ) (n : ℤ), W = (n : ℝ) + y → 1 / 6 ≤ y → y ≤ 5 / 6 →
      1 / 6 ≤ circDist W := by
    intro W y n hW hlo hhi
    have hyfr : Int.fract y = y := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hWeq : W = y + (n : ℝ) := by rw [hW]; ring
    rw [hWeq, bhk_prop11_circDist_add_int]
    unfold circDist; rw [le_min_iff, hyfr]; exact ⟨hlo, by linarith⟩
  have e0 : (w ⟨0, by omega⟩ : ℝ) * t = ((0 : ℤ) : ℝ) + (m : ℝ) / q := by
    rw [c0, htdef]; push_cast; field_simp; ring
  have e1 : (w ⟨1, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + (1 / 2 - (m : ℝ) / q) := by
    rw [c1, htdef, hmjR]; push_cast; field_simp; ring
  have e2 : (w ⟨2, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + 1 / 2 := by
    rw [c2, htdef, hmjR]; push_cast; field_simp
  have e3 : (w ⟨3, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + (1 / 2 + (m : ℝ) / q / 2) := by
    rw [c3, htdef, hmjR]; push_cast; field_simp; ring
  have e4 : (w ⟨4, by omega⟩ : ℝ) * t = ((j : ℤ) : ℝ) + (1 / 2 + (m : ℝ) / q) := by
    rw [c4, htdef, hmjR]; push_cast; field_simp; ring
  rcases found6_or_blocked w t with hF | ⟨i, hi⟩ | hfict
  · exact hF
  · refine absurd hi (not_lt.mpr ?_)
    fin_cases i
    · exact key _ _ 0 e0 hmq_lo (by linarith [hmq_hi])
    · exact key _ _ (j : ℤ) e1 (by linarith [hmq_hi]) (by linarith [hmq_lo])
    · exact key _ _ (j : ℤ) e2 (by norm_num) (by norm_num)
    · exact key _ _ (j : ℤ) e3 (by linarith [hmq_lo]) (by linarith [hmq_hi])
    · exact key _ _ (j : ℤ) e4 (by linarith [hmq_lo]) (by linarith [hmq_hi])
  · refine absurd hfict (not_lt.mpr ?_)
    have e0' : 2 * ((w ⟨0, by omega⟩ : ℝ) * t) = ((0 : ℤ) : ℝ) + 2 * ((m : ℝ) / q) := by
      rw [e0]; push_cast; ring
    exact key _ _ 0 e0' (by linarith [hmq_lo]) (by linarith [hmq_hi])

/-- **BHK §5 Case 5.2.11 — `(1,2)U` windowed dispatcher.** Splits on `s`: the
    narrow-window case `s = q+2` (forcing `r = q+1`, `p = 2`; `exc_1_2_special2`)
    versus the generic `s ≥ q+3` lower-window pigeonhole (`exc_1_2_pentkill2`). -/
lemma bhk_prop11_exc_1_2_kill2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q) (hrq : q < r) (hr32 : 2 * r < 3 * q)
    (hrs : r < s) (hq18 : 18 ≤ q) (hsmall6N : 6 * p < q) (hrig : 2 * r = 2 * q + p) : Found6 w := by
  by_cases hs2 : s = q + 2
  · have hr1 : r = q + 1 := by omega
    have hp2 : p = 2 := by omega
    have c0' : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * 2 := by rw [c0, hp2]; push_cast; ring
    have c1' : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - 2) := by
      have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
        exact_mod_cast hsum
      rw [show (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) from by linarith,
        c0', c2]; ring
    have c3' : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 1) := by rw [c3, hr1]; push_cast; ring
    have c4' : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) + 2) := by rw [c4, hs2]; push_cast; ring
    exact bhk_prop11_exc_1_2_special2 w hpos g q hg (by omega) c0' c1' c2 c3' c4'
  · have hs3 : q + 3 ≤ s := by omega
    exact bhk_prop11_exc_1_2_pentkill2 w hmono hpos hsum hsmall6 g p q r s hg hq
      c0 c2 c3 c4 hcop hp h3p hrq hr32 hrs hq18 hsmall6N hrig hs3

/-- **Lemma 12, windowed** (the `core2` analog of `bhk_prop11_lemma12`). Same
    orbit-divisibility trichotomy, from the six-runner covering on a 0123-gap. The
    covering is used twice — once via `gap_covered2`, once on the translates
    `p + i/g`. At a translate the fictional runner has the *same* fractional part
    as at `p` (since `g ∣ 2 w₀`, the orbit shift `i·(2w₀/g)` is an integer), so
    the gap's window-freeness (`h0safe`) plus `fict_window_safe` rules out the
    fictional cover there too. -/
lemma bhk_prop11_lemma12_w (w : Fin 5 → ℕ) (g : ℕ) (hg : 0 < g)
    (hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩)
    {a b : ℝ} (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h0safe : ∀ s ∈ Set.Icc a b,
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12)) : Found6 w ∨
      (Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩ ∨ Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
      ∨ (g ∣ w ⟨3, by omega⟩ ∧ g ∣ w ⟨4, by omega⟩)) := by
  have hg0w : g ∣ w ⟨0, by omega⟩ := hdvd012 0
  obtain hF | hcov45 := bhk_prop11_gap_covered2 w hgap h0safe
  · exact Or.inl hF
  rcases found6_or_blocked_on w {τ | ∃ p ∈ Set.Icc a b, ∃ i : ℕ, τ = p + (i : ℝ) * (1 / g)} with hF | hblkT
  · exact Or.inl hF
  right
  by_cases h4 : Set.Icc a b ⊆ unsafeOf w ⟨3, by omega⟩
  · exact Or.inl h4
  by_cases h5 : Set.Icc a b ⊆ unsafeOf w ⟨4, by omega⟩
  · exact Or.inr (Or.inl h5)
  refine Or.inr (Or.inr ?_)
  obtain ⟨u, huIcc, hu4, hu5⟩ := bhk_prop11_overlap w hcov45 h4 h5
  have htrans : ∀ (p : ℝ), p ∈ Set.Icc a b → ∀ i : ℕ,
      circDist ((w ⟨3, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)) < 1 / 6 ∨
      circDist ((w ⟨4, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)) < 1 / 6 := by
    intro p hp i
    have hsafe012 : ∀ j : Fin 3,
        (1 : ℝ) / 6 ≤ circDist ((w ⟨j.val, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g))) := by
      intro j
      have hjexp : (w ⟨j.val, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g))
          = (w ⟨j.val, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨j.val, by omega⟩ : ℝ) / g) := by ring
      rw [hjexp, bhk_prop11_circDist_orbit_dvd _ g hg (hdvd012 j)]
      exact hgap p hp j
    rcases hblkT _ ⟨p, hp, i, rfl⟩ with ⟨k, hk⟩ | hfict
    · fin_cases k
      · exact absurd hk (not_lt.mpr (hsafe012 0))
      · exact absurd hk (not_lt.mpr (hsafe012 1))
      · exact absurd hk (not_lt.mpr (hsafe012 2))
      · left
        rw [show (w ⟨3, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)
              = (w ⟨3, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g)) from by ring]
        exact hk
      · right
        rw [show (w ⟨4, by omega⟩ : ℝ) * p + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)
              = (w ⟨4, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g)) from by ring]
        exact hk
    · exfalso
      have hredf : circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g))))
          = circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * p)) := by
        have hform : 2 * ((w ⟨0, by omega⟩ : ℝ) * (p + (i : ℝ) * (1 / g)))
            = ((2 * w ⟨0, by omega⟩ : ℕ) : ℝ) * p
              + (i : ℝ) * (((2 * w ⟨0, by omega⟩ : ℕ) : ℝ) / g) := by push_cast; ring
        rw [hform, bhk_prop11_circDist_orbit_dvd (2 * w ⟨0, by omega⟩) g hg
          (Dvd.dvd.mul_left hg0w 2)]
        congr 1; push_cast; ring
      rw [hredf] at hfict
      have h0p : (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * p) := hgap p hp 0
      have h1 : (1 : ℝ) / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * p) := by
        have := h0p; unfold circDist at this; exact le_trans this (min_le_left _ _)
      have h2 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * p) ≤ 5 / 6 := by
        have := h0p; unfold circDist at this; linarith [le_trans this (min_le_right _ _)]
      exact absurd hfict (not_lt.mpr (bhk_prop11_fict_window_safe h1 h2 (h0safe p hp)))
  have hua : circDist ((w ⟨3, by omega⟩ : ℝ) * u) < 1 / 6 := (mem_unsafeOf_iff w _ u).mp hu4
  have hub : circDist ((w ⟨4, by omega⟩ : ℝ) * u) < 1 / 6 := (mem_unsafeOf_iff w _ u).mp hu5
  have hor : g ∣ w ⟨3, by omega⟩ ∨ g ∣ w ⟨4, by omega⟩ := by
    by_contra hcon
    rw [not_or] at hcon
    exact bhk_prop11_no_double g hg _ _ hcon.1 hcon.2 _ _ hua hub (htrans u huIcc)
  rcases hor with h3 | h4'
  · refine ⟨h3, ?_⟩
    rw [Set.not_subset] at h4
    obtain ⟨p, hpIcc, hp4⟩ := h4
    rw [mem_unsafeOf_iff, not_lt] at hp4
    apply bhk_prop11_dvd_of_orbit_covered _ g hg ((w ⟨4, by omega⟩ : ℝ) * p)
    intro i
    rcases htrans p hpIcc i with h | h
    · exfalso
      have hsafe3 : (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * p
          + (i : ℝ) * ((w ⟨3, by omega⟩ : ℝ) / g)) := by
        rw [bhk_prop11_circDist_orbit_dvd _ g hg h3]; exact hp4
      linarith
    · exact h
  · refine ⟨?_, h4'⟩
    rw [Set.not_subset] at h5
    obtain ⟨p, hpIcc, hp5⟩ := h5
    rw [mem_unsafeOf_iff, not_lt] at hp5
    apply bhk_prop11_dvd_of_orbit_covered _ g hg ((w ⟨3, by omega⟩ : ℝ) * p)
    intro i
    rcases htrans p hpIcc i with h | h
    · exact h
    · exfalso
      have hsafe4 : (1 : ℝ) / 6 ≤ circDist ((w ⟨4, by omega⟩ : ℝ) * p
          + (i : ℝ) * ((w ⟨4, by omega⟩ : ℝ) / g)) := by
        rw [bhk_prop11_circDist_orbit_dvd _ g hg h4']; exact hp5
      linarith

/-- **Lemma 17, windowed** (the `core2` analog of `bhk_prop11_lemma17`). The
    denominators of runners 4 and 5 both divide `g = gcd(w₀,w₂)`. Corollary 15's
    witness gap `[t, t+1/(3w₂)]` (with `{w₀t} ∈ [1/6,1/3]`) is window-free under
    `6 w₀ < w₂` (`{w₀s} < 1/3 + 1/18 < 5/12`), so `lemma12_w` applies; the gap is
    too long for a single `B₄`/`B₅` block, leaving only divisibility. -/
lemma bhk_prop11_lemma17_w (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found6 w ∨
      (Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨3, by omega⟩ ∧
      Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) ∣ w ⟨4, by omega⟩) := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgdvd0 : g ∣ w ⟨0, by omega⟩ := by rw [hgdef]; exact Nat.gcd_dvd_left _ _
  have hgdvd2 : g ∣ w ⟨2, by omega⟩ := by rw [hgdef]; exact Nat.gcd_dvd_right _ _
  have hgdvd1 : g ∣ w ⟨1, by omega⟩ := by
    have he : w ⟨1, by omega⟩ = w ⟨2, by omega⟩ - w ⟨0, by omega⟩ := by omega
    rw [he]; exact Nat.dvd_sub hgdvd2 hgdvd0
  have hdvd012 : ∀ i : Fin 3, g ∣ w ⟨i.val, by omega⟩ := by
    intro i; fin_cases i
    · exact hgdvd0
    · exact hgdvd1
    · exact hgdvd2
  obtain ⟨t, h3, h1lo, h1hi⟩ := bhk_prop11_witness_time w hpos hsmall hq5
  have hgap := bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi
  have hw0pos : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos ⟨2, by omega⟩
  have hsmall6R : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall6
  have h4w0 : 4 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by linarith
  -- The witness gap is window-free for runner 1.
  have h0safe : ∀ s ∈ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))),
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    have hd0 : 0 ≤ s - t := by linarith [hs.1]
    have hsu : s - t ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by linarith [hs.2]
    have hb : (w ⟨0, by omega⟩ : ℝ) * (s - t) < 1 / 12 := by
      have h1 : (w ⟨0, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left hsu hw0pos.le
      have h2 : (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) < 1 / 12 := by
        rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [h4w0]
      linarith
    have hfs : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) + (w ⟨0, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨0, by omega⟩ : ℝ) * s
            = (w ⟨0, by omega⟩ : ℝ) * t + (w ⟨0, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by nlinarith [mul_nonneg hw0pos.le hd0]) (by linarith)]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith
  have hgaplen : ∀ (j : Fin 5), w ⟨2, by omega⟩ < w j →
      (1 : ℝ) / (3 * (w j : ℝ)) < (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) - t := by
    intro j hj
    rw [add_sub_cancel_left]
    have hwj : (w ⟨2, by omega⟩ : ℝ) < (w j : ℝ) := by exact_mod_cast hj
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hn4 : ¬ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) ⊆ unsafeOf w ⟨3, by omega⟩ :=
    bhk_prop11_not_subset_unsafeOf w ⟨3, by omega⟩ (hpos _)
      (le_add_of_nonneg_right (by positivity))
      (hgaplen ⟨3, by omega⟩ (hmono (Fin.mk_lt_mk.mpr (by omega))))
  have hn5 : ¬ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) ⊆ unsafeOf w ⟨4, by omega⟩ :=
    bhk_prop11_not_subset_unsafeOf w ⟨4, by omega⟩ (hpos _)
      (le_add_of_nonneg_right (by positivity))
      (hgaplen ⟨4, by omega⟩ (hmono (Fin.mk_lt_mk.mpr (by omega))))
  rcases bhk_prop11_lemma12_w w g hg0 hdvd012 hgap h0safe with hF | hc | hc | hc
  · exact Or.inl hF
  all_goals right
  · exact absurd hc hn4
  · exact absurd hc hn5
  · exact hc

/-- **Lemma 18 (`v₄ ≤ 3/2`), windowed** (the `core2` analog of
    `bhk_prop11_v4_le_3_2`). The `bhk_prop11_gap123_long` gap
    `[t − 1/(9w₂), t + 1/(3w₂)]` is window-free under `6 w₀ < w₂` — `{w₀s} ≥ 1/6`
    (left endpoint cancels the `+a/(9n)` margin) and `{w₀s} < 1/3 + 1/18 < 5/12` —
    so `gap_covered2` applies and `bhk_lemma_4` yields `2 w₃ < 3 w₂`. -/
lemma bhk_prop11_v4_le_3_2_w (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq18 : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found6 w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < 3 * (w ⟨2, by omega⟩ : ℝ)) := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  set a := w ⟨0, by omega⟩ with ha
  set n := w ⟨2, by omega⟩ with hn
  have ha0 : 0 < a := hpos _
  have hn0 : 0 < n := by omega
  set g : ℕ := Nat.gcd a n with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ ha0
  have hga : g ∣ a := Nat.gcd_dvd_left a n
  have hgn : g ∣ n := Nat.gcd_dvd_right a n
  have ha'0 : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha0 hga) hg0
  have h3a' : 3 * (a / g) < n / g := by
    have hmul : 3 * (a / g) * g < n / g * g := by
      calc 3 * (a / g) * g = 3 * a := by rw [mul_assoc, Nat.div_mul_cancel hga]
        _ < n := hsmall
        _ = n / g * g := (Nat.div_mul_cancel hgn).symm
    exact lt_of_mul_lt_mul_right hmul (Nat.zero_le g)
  have hcop' : Nat.Coprime (a / g) (n / g) := Nat.coprime_div_gcd_div_gcd hg0
  obtain ⟨m, hm⟩ := bhk_prop11_residue_hit_narrow (a / g) (n / g) ha'0 h3a' hq18 hcop'
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg0
  have hb'R : (0 : ℝ) < ((n / g : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n / g)
  have haf : (a : ℝ) = (g : ℝ) * ((a / g : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hga]
  have hnf : (n : ℝ) = (g : ℝ) * ((n / g : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hgn]
  set t : ℝ := (2 * (m : ℝ) + 1) / (2 * (n : ℝ)) with ht
  have heq : (a : ℝ) * t
      = ((a / g : ℕ) : ℝ) * ((2 * (m : ℝ) + 1) / (2 * ((n / g : ℕ) : ℝ))) := by
    rw [ht, haf, hnf]; field_simp
  have hw1 : (w ⟨1, by omega⟩ : ℝ) = (n : ℝ) - (a : ℝ) := by
    have : (a : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (n : ℝ) := by exact_mod_cast hsum
    linarith
  have h3half : Int.fract ((n : ℝ) * t) = 1 / 2 := by
    have hh : (n : ℝ) * t = (m : ℝ) + 1 / 2 := by rw [ht]; field_simp
    rw [hh, show (m : ℝ) + 1 / 2 = ((m : ℤ) : ℝ) + 1 / 2 from by push_cast; ring,
      Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  have hep1 : ((a / g : ℕ) : ℝ) / (9 * ((n / g : ℕ) : ℝ)) = (a : ℝ) / (9 * n) := by
    rw [haf, hnf]; field_simp
  have hep2 : (((n / g : ℕ) : ℝ) - ((a / g : ℕ) : ℝ)) / (9 * ((n / g : ℕ) : ℝ))
      = ((n : ℝ) - a) / (9 * n) := by rw [haf, hnf]; field_simp
  have hbridge : Int.fract ((a : ℝ) * t)
      = Int.fract (((a / g : ℕ) : ℝ) * ((2 * (m : ℝ) + 1) / (2 * ((n / g : ℕ) : ℝ)))) := by
    rw [heq]
  have hwlo : 1 / 6 + (a : ℝ) / (9 * n) ≤ Int.fract ((a : ℝ) * t) := by
    rw [hbridge, ← hep1]; exact (Set.mem_Icc.mp hm).1
  have hwhi : Int.fract ((a : ℝ) * t) ≤ 1 / 3 - (w ⟨1, by omega⟩ : ℝ) / (9 * n) := by
    rw [hbridge, hw1, ← hep2]; exact (Set.mem_Icc.mp hm).2
  have hgap := bhk_prop11_gap123_long w hpos hsum hsmall t h3half hwlo hwhi
  -- The (long) gap is window-free for runner 1.
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have h6a : 6 * (a : ℝ) < (n : ℝ) := by exact_mod_cast hsmall6
  have h0safe : ∀ s ∈ Set.Icc (t - 1 / (9 * n)) (t + 1 / (3 * n)),
      Int.fract ((a : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    have hub : (a : ℝ) * (s - t) ≤ (a : ℝ) / (3 * n) := by
      have h : s - t ≤ 1 / (3 * (n : ℝ)) := by linarith [hs.2]
      calc (a : ℝ) * (s - t) ≤ (a : ℝ) * (1 / (3 * n)) := mul_le_mul_of_nonneg_left h ha0R.le
        _ = (a : ℝ) / (3 * n) := by ring
    have hlb : -((a : ℝ) / (9 * n)) ≤ (a : ℝ) * (s - t) := by
      have h : -(1 / (9 * (n : ℝ))) ≤ s - t := by linarith [hs.1]
      have hh := mul_le_mul_of_nonneg_left h ha0R.le
      calc -((a : ℝ) / (9 * n)) = (a : ℝ) * (-(1 / (9 * n))) := by ring
        _ ≤ (a : ℝ) * (s - t) := hh
    have ha3n : (a : ℝ) / (3 * n) < 1 / 18 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [h6a]
    have hsumlo : (1 : ℝ) / 6 ≤ Int.fract ((a : ℝ) * t) + (a : ℝ) * (s - t) := by
      linarith [hwlo, hlb]
    have hsumhi : Int.fract ((a : ℝ) * t) + (a : ℝ) * (s - t) ≤ 5 / 12 := by
      have hw1nn : (0 : ℝ) ≤ (w ⟨1, by omega⟩ : ℝ) / (9 * n) := by positivity
      linarith [hwhi, hub, hw1nn, ha3n]
    have hfs : Int.fract ((a : ℝ) * s) = Int.fract ((a : ℝ) * t) + (a : ℝ) * (s - t) := by
      rw [show (a : ℝ) * s = (a : ℝ) * t + (a : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by linarith [hsumlo]) (by linarith [hsumhi])]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith [hsumhi]
  obtain hF | hcov := bhk_prop11_gap_covered2 w hgap h0safe
  · exact Or.inl hF
  right
  have hab : t - 1 / (9 * n) ≤ t + 1 / (3 * n) := by
    have h1 : (0 : ℝ) < 1 / (9 * n) := by positivity
    have h2 : (0 : ℝ) < 1 / (3 * n) := by positivity
    linarith
  have hlen := bhk_lemma_4 w hmono hpos (t - 1 / (9 * n)) (t + 1 / (3 * n)) hab hcov
  have hw3R : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have key : 1 / (3 * (n : ℝ)) + 1 / (9 * n) < 2 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by
    linarith [hlen]
  have hcomb : 1 / (3 * (n : ℝ)) + 1 / (9 * n) = 4 / (9 * n) := by field_simp; ring
  rw [hcomb, div_lt_div_iff₀ (by positivity) (by positivity)] at key
  linarith [key]

/-- **Exceptional-pair extraction, windowed** (the `core2` analog of
    `bhk_prop11_exceptional_q18`). From the six-runner covering and `q ≥ 18`,
    produce the rational structure `g, p, q, r, s` and a minimal exceptional cone
    pair `(i, j)` with the BHK (14) order bound. The only covering-dependent
    inputs are `lemma17_w` (denominators) and the rectangle `no_good_time2`; the
    pair itself comes from the pure-arithmetic `bhk_part3_exceptional_minimal_bound`. -/
theorem bhk_prop11_exceptional_q18_w (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq18 : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found6 w ∨
      (∃ g p q r s : ℕ, 0 < g ∧
      w ⟨0, by omega⟩ = g * p ∧ w ⟨2, by omega⟩ = g * q ∧
      w ⟨3, by omega⟩ = g * r ∧ w ⟨4, by omega⟩ = g * s ∧
      Nat.gcd p q = 1 ∧ 18 ≤ q ∧
      ∃ ij : ℤ × ℤ, ij ≠ (0, 0) ∧
        (∃ k : ℤ, Int.fract ((ij.1 : ℝ) / q) = Int.fract ((k : ℝ) * r / q) ∧
                  Int.fract ((ij.2 : ℝ) / q) = Int.fract ((k : ℝ) * p / q)) ∧
        0 ≤ ij.1 ∧ (ij.1 : ℝ) < 6 ∧
        -3 - 1 / 2 * (ij.1 : ℝ) < (ij.2 : ℝ) ∧ (ij.2 : ℝ) < 3 + 1 / 2 * (ij.1 : ℝ) ∧
        (ij.1 ≠ 0 → ij.2 ≠ 0 → (ij.1.natAbs + 1) * (ij.2.natAbs + 1) - 2 ≤ q)) := by
  have hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) := by omega
  obtain hF | ⟨hgw3, hgw4⟩ := bhk_prop11_lemma17_w w hmono hpos hsum hsmall6 hq5
  · exact Or.inl hF
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgw0 : g ∣ w ⟨0, by omega⟩ := Nat.gcd_dvd_left _ _
  have hgw2 : g ∣ w ⟨2, by omega⟩ := Nat.gcd_dvd_right _ _
  set p : ℕ := w ⟨0, by omega⟩ / g with hpdef
  set q : ℕ := w ⟨2, by omega⟩ / g with hqdef
  set r : ℕ := w ⟨3, by omega⟩ / g with hrdef
  set s : ℕ := w ⟨4, by omega⟩ / g with hsdef
  have hp : w ⟨0, by omega⟩ = g * p := (Nat.mul_div_cancel' hgw0).symm
  have hq : w ⟨2, by omega⟩ = g * q := (Nat.mul_div_cancel' hgw2).symm
  have hr : w ⟨3, by omega⟩ = g * r := (Nat.mul_div_cancel' hgw3).symm
  have hs : w ⟨4, by omega⟩ = g * s := (Nat.mul_div_cancel' hgw4).symm
  have hcop : Nat.gcd p q = 1 := Nat.coprime_div_gcd_div_gcd hg_pos
  have hqpos : 0 < q := by omega
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hqne : (q : ℝ) ≠ 0 := hqR.ne'
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * (p : ℝ) := by exact_mod_cast hp
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hq
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * (r : ℝ) := by exact_mod_cast hr
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
  obtain hF | h_nogood : Found6 w ∨ (∀ k : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((k : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((k : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) := by
    rw [or_iff_not_imp_right]
    intro hQ
    obtain ⟨k, hk⟩ := not_forall_not.mp hQ
    obtain ⟨hrmem, hpmem⟩ := hk
    set t : ℝ := ((k : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
    have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (k : ℝ) + 1 / 2 := by
      rw [htdef]; field_simp
    have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((k : ℝ) + 1 / 2) := by
      rw [htdef, c0, c2]; field_simp
    have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((k : ℝ) + 1 / 2) := by
      rw [htdef, c3, c2]; field_simp
    refine bhk_prop11_no_good_time2 w hmono hpos hsum hsmall6 t ?_ ?_ ?_ ?_ ?_
    · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    · rw [e0]; exact hpmem.1
    · rw [e0]; exact hpmem.2
    · rw [e3]; exact hrmem.1
    · rw [e3]; exact hrmem.2
  · exact Or.inl hF
  right
  obtain ⟨_G, _hGlift, ij, hne, hmem, h0, h1β, hc1, hc2, _hmin, h14⟩ :=
    bhk_part3_exceptional_minimal_bound r p q (by omega) hcop h_nogood
  exact ⟨g, p, q, r, s, hg_pos, hp, hq, hr, hs, hcop, by omega, ij, hne, hmem, h0, h1β, hc1, hc2,
    h14⟩

/-! ### BHK Part 6, windowed (`core2`, fictional-runner 0123-gap)

The part-1 Part 6 family (`part6_claim19/20/21`, `part6`) proves the diagonal
case `w₃ = w₀ + w₂` (cone pair `(1,1)`) using the *five*-runner covering. In
`core2` we only have the *six*-runner covering `hcov6` (the fictional runner
`2w₀`, since `v₁ < 1/6`). The windowed analogs below thread `h0safe`
(`{w₀s} ∉ (5/12, 7/12)`) through the runner-5 engines so the fictional branch is
killed by `bhk_prop11_fict_window_safe`. Every Part 6 gap is **window-free**:
the Claim 19 gap keeps `{w₀s} ≤ 5/12` (advance `< 1/6`), and with the stronger
`6w₀ < w₂ < w₃` the Claim 20 `4`-block edges keep `{w₀ qe} ≤ 7/18 < 5/12` (the
"tighter edge-position" bound the part-1 `edge_arith` does not give). -/

/-- **Windowed Claim 19 span engine.** The `gap1234_b5span2` analog of
    `part6_claim19_span`: a `1234`-gap `[a,b]` of length `≥ 1/(6w₃)` that is also
    runner-1 window-free (`h0safe`) forces `w₄ < 2w₃` under the six-runner cover. -/
lemma bhk_prop11_part6_claim19_span2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    {a b : ℝ} (hab : a ≤ b)
    (hgap : ∀ s ∈ Set.Icc a b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s))
    (h0safe : ∀ s ∈ Set.Icc a b,
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12))
    (h4safe : ∀ s ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s))
    (hlen : 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) ≤ b - a) : Found6 w ∨
      (w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) := by
  obtain hF | hspan := bhk_prop11_gap1234_b5span2 w hpos hab hgap h0safe h4safe
  · exact Or.inl hF
  right
  have hw4 : (0 : ℝ) ≤ (w ⟨4, by omega⟩ : ℝ) := by positivity
  have hstep : (w ⟨4, by omega⟩ : ℝ) * (1 / (6 * (w ⟨3, by omega⟩ : ℝ))) < 1 / 3 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlen hw4) hspan
  have hw3 : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h6 : (0 : ℝ) < 6 * (w ⟨3, by omega⟩ : ℝ) := by positivity
  rw [mul_one_div, div_lt_iff₀ h6] at hstep
  have hreal : (w ⟨4, by omega⟩ : ℝ) < 2 * (w ⟨3, by omega⟩ : ℝ) := by linarith [hstep]
  exact_mod_cast hreal

/-- **Windowed lower-bound engine** (the `core2` analog of `part6_lower_span`).
    If `[p,q]` has width `1/(3b)` with both endpoints `1234`-safe (`hp`/`hq`) and
    runner-1 window-free (`h0p`/`h0q`), then the six-runner cover forces runner 5
    unsafe at both endpoints (the fictional branch is killed by window-freeness),
    so `2b < w₄`. Claim 20 uses `b = w₃`, Claim 21 uses `b = w₂`. -/
lemma bhk_prop11_part6_lower_span2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (b : ℝ) (hbpos : 0 < b) (hbw4 : b < (w ⟨4, by omega⟩ : ℝ))
    (p q : ℝ) (hpq : q - p = 1 / (3 * b))
    (hp : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * p))
    (hq : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * q))
    (h0p : Int.fract ((w ⟨0, by omega⟩ : ℝ) * p) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12))
    (h0q : Int.fract ((w ⟨0, by omega⟩ : ℝ) * q) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12)) : Found6 w ∨
      (2 * b < (w ⟨4, by omega⟩ : ℝ)) := by
  rcases found6_or_blocked w p with hF | hbp
  · exact Or.inl hF
  have hp5 : circDist ((w ⟨4, by omega⟩ : ℝ) * p) < 1 / 6 := by
    rcases hbp with ⟨i, hi⟩ | hfict
    · fin_cases i
      · exact absurd hi (not_lt.mpr (hp 0))
      · exact absurd hi (not_lt.mpr (hp 1))
      · exact absurd hi (not_lt.mpr (hp 2))
      · exact absurd hi (not_lt.mpr (hp 3))
      · exact hi
    · exfalso
      have hr0 : (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * p) := hp 0
      have h1 : (1 : ℝ) / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * p) := by
        have := hr0; unfold circDist at this; exact le_trans this (min_le_left _ _)
      have h2 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * p) ≤ 5 / 6 := by
        have := hr0; unfold circDist at this; linarith [le_trans this (min_le_right _ _)]
      exact absurd hfict (not_lt.mpr (bhk_prop11_fict_window_safe h1 h2 h0p))
  rcases found6_or_blocked w q with hF | hbq
  · exact Or.inl hF
  right
  have hq5 : circDist ((w ⟨4, by omega⟩ : ℝ) * q) < 1 / 6 := by
    rcases hbq with ⟨i, hi⟩ | hfict
    · fin_cases i
      · exact absurd hi (not_lt.mpr (hq 0))
      · exact absurd hi (not_lt.mpr (hq 1))
      · exact absurd hi (not_lt.mpr (hq 2))
      · exact absurd hi (not_lt.mpr (hq 3))
      · exact hi
    · exfalso
      have hr0 : (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * q) := hq 0
      have h1 : (1 : ℝ) / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * q) := by
        have := hr0; unfold circDist at this; exact le_trans this (min_le_left _ _)
      have h2 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * q) ≤ 5 / 6 := by
        have := hr0; unfold circDist at this; linarith [le_trans this (min_le_right _ _)]
      exact absurd hfict (not_lt.mpr (bhk_prop11_fict_window_safe h1 h2 h0q))
  obtain ⟨k₁, hk₁⟩ : ∃ k : ℤ, |(w ⟨4, by omega⟩ : ℝ) * p - (k : ℝ)| < 1 / 6 :=
    (mem_bhkB_iff _).mpr hp5
  obtain ⟨k₂, hk₂⟩ : ∃ k : ℤ, |(w ⟨4, by omega⟩ : ℝ) * q - (k : ℝ)| < 1 / 6 :=
    (mem_bhkB_iff _).mpr hq5
  rw [abs_lt] at hk₁ hk₂
  have hDeq : (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p
      = (w ⟨4, by omega⟩ : ℝ) / (3 * b) := by
    rw [show (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p
        = (w ⟨4, by omega⟩ : ℝ) * (q - p) from by ring, hpq]; ring
  have hDpos : (1 : ℝ) / 3 < (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p := by
    rw [hDeq, lt_div_iff₀ (by positivity)]; linarith
  have hd1 : (1 : ℤ) ≤ k₂ - k₁ := by
    have hpos' : (0 : ℝ) < ((k₂ - k₁ : ℤ) : ℝ) := by
      push_cast; linarith [hk₁.1, hk₂.2, hDpos]
    have : (0 : ℤ) < k₂ - k₁ := by exact_mod_cast hpos'
    omega
  have hD23 : (2 : ℝ) / 3 < (w ⟨4, by omega⟩ : ℝ) * q - (w ⟨4, by omega⟩ : ℝ) * p := by
    have hdR : (1 : ℝ) ≤ ((k₂ - k₁ : ℤ) : ℝ) := by exact_mod_cast hd1
    push_cast at hdR; linarith [hk₁.2, hk₂.1]
  rw [hDeq, lt_div_iff₀ (by positivity)] at hD23
  linarith

/-- **Windowed Claim 20 span engine** = `lower_span2` at `b = w₃`. -/
lemma bhk_prop11_part6_claim20_span2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (p q : ℝ) (hpq : q - p = 1 / (3 * (w ⟨3, by omega⟩ : ℝ)))
    (hp : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * p))
    (hq : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * q))
    (h0p : Int.fract ((w ⟨0, by omega⟩ : ℝ) * p) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12))
    (h0q : Int.fract ((w ⟨0, by omega⟩ : ℝ) * q) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12)) : Found6 w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
  bhk_prop11_part6_lower_span2 w hpos (w ⟨3, by omega⟩ : ℝ)
    (by exact_mod_cast hpos _) hw34 p q hpq hp hq h0p h0q

/-- **Windowed Claim 19 gap construction** (the `core2` analog of
    `part6_claim19_gap`). Same `1234`-gap `[t₀, t₀+1/(6w₃)]`; the runner-1 drift
    `< 1/6` keeps `{w₀s} ≤ 5/12`, so the gap is window-free. -/
lemma bhk_prop11_part6_claim19_gap2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (t0 : ℝ)
    (h3 : Int.fract ((w ⟨3, by omega⟩ : ℝ) * t0) = 2 / 3)
    (h0lo : 1 / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0))
    (h0hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0) ≤ 1 / 4) : Found6 w ∨
      (w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) := by
  have hw0 : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw1 : (0 : ℝ) < (w ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3 : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsum
  have hdiagR : (w ⟨3, by omega⟩ : ℝ) = (w ⟨0, by omega⟩ : ℝ) + (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hdiag
  have hw1_eq : (w ⟨1, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - 2 * (w ⟨0, by omega⟩ : ℝ) := by
    linarith
  have hw2_eq : (w ⟨2, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by
    linarith
  have hw0lt : (w ⟨0, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  have hf2 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t0)
      = 2 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0) := by
    have key : (w ⟨2, by omega⟩ : ℝ) * t0
        = ((⌊(w ⟨3, by omega⟩ : ℝ) * t0⌋ - ⌊(w ⟨0, by omega⟩ : ℝ) * t0⌋ : ℤ) : ℝ)
          + (2 / 3 - Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0)) := by
      have e3 := Int.floor_add_fract ((w ⟨3, by omega⟩ : ℝ) * t0)
      have e0 := Int.floor_add_fract ((w ⟨0, by omega⟩ : ℝ) * t0)
      rw [h3] at e3
      rw [hw2_eq, sub_mul, Int.cast_sub]
      linarith [e3, e0]
    rw [key, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hf1 : Int.fract ((w ⟨1, by omega⟩ : ℝ) * t0)
      = 2 / 3 - 2 * Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0) := by
    have key : (w ⟨1, by omega⟩ : ℝ) * t0
        = ((⌊(w ⟨3, by omega⟩ : ℝ) * t0⌋ - ⌊(w ⟨0, by omega⟩ : ℝ) * t0⌋
              - ⌊(w ⟨0, by omega⟩ : ℝ) * t0⌋ : ℤ) : ℝ)
          + (2 / 3 - 2 * Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0)) := by
      have e3 := Int.floor_add_fract ((w ⟨3, by omega⟩ : ℝ) * t0)
      have e0 := Int.floor_add_fract ((w ⟨0, by omega⟩ : ℝ) * t0)
      rw [h3] at e3
      rw [hw1_eq, sub_mul, mul_assoc, Int.cast_sub, Int.cast_sub]
      linarith [e3, e0]
    rw [key, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  set b : ℝ := t0 + 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) with hb
  have hbt : b - t0 = 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) := by rw [hb]; ring
  have hab : t0 ≤ b := by rw [hb]; have : (0:ℝ) < 1 / (6 * (w ⟨3, by omega⟩ : ℝ)) := by positivity
                          linarith
  have h6w3 : (0 : ℝ) < 6 * (w ⟨3, by omega⟩ : ℝ) := by positivity
  have hadv0 : (w ⟨0, by omega⟩ : ℝ) * (b - t0) ≤ 1 / 6 := by
    rw [hbt, mul_one_div, div_le_iff₀ h6w3]; linarith
  have hadv1 : (w ⟨1, by omega⟩ : ℝ) * (b - t0) ≤ 1 / 6 := by
    rw [hbt, mul_one_div, div_le_iff₀ h6w3]; linarith
  have hadv2 : (w ⟨2, by omega⟩ : ℝ) * (b - t0) ≤ 1 / 6 := by
    rw [hbt, mul_one_div, div_le_iff₀ h6w3]; linarith
  have hadv3 : (w ⟨3, by omega⟩ : ℝ) * (b - t0) = 1 / 6 := by
    rw [hbt, mul_one_div, div_eq_iff h6w3.ne']; ring
  have safe0 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨0, by omega⟩ : ℝ) t0 t0 b hw0.le
    · rw [sub_self, mul_zero, add_zero]; exact h0lo
    · linarith
  have safe1 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨1, by omega⟩ : ℝ) t0 t0 b hw1.le
    · rw [hf1, sub_self, mul_zero, add_zero]; linarith
    · rw [hf1]; linarith
  have safe2 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨2, by omega⟩ : ℝ) t0 t0 b hw2.le
    · rw [hf2, sub_self, mul_zero, add_zero]; linarith
    · rw [hf2]; linarith
  have safe3 : ∀ s ∈ Set.Icc t0 b, 1 / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_pent_delayed_safe (w ⟨3, by omega⟩ : ℝ) t0 t0 b hw3.le
    · rw [sub_self, mul_zero, add_zero, h3]; norm_num
    · rw [h3]; linarith
  have hgap : ∀ s ∈ Set.Icc t0 b, ∀ i : Fin 3,
      (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * s) := by
    intro s hs i
    fin_cases i
    · exact safe0 s hs
    · exact safe1 s hs
    · exact safe2 s hs
  -- the gap is window-free for runner 1:  {w₀ s} ≤ 1/4 + 1/6 = 5/12
  have h0safe : ∀ s ∈ Set.Icc t0 b,
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    have hd0 : 0 ≤ s - t0 := by linarith [hs.1]
    have hadvs : (w ⟨0, by omega⟩ : ℝ) * (s - t0) ≤ 1 / 6 := by
      have hmono' : (w ⟨0, by omega⟩ : ℝ) * (s - t0) ≤ (w ⟨0, by omega⟩ : ℝ) * (b - t0) :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2]) hw0.le
      linarith [hmono', hadv0]
    have hfs : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨0, by omega⟩ : ℝ) * t0) + (w ⟨0, by omega⟩ : ℝ) * (s - t0) := by
      rw [show (w ⟨0, by omega⟩ : ℝ) * s
            = (w ⟨0, by omega⟩ : ℝ) * t0 + (w ⟨0, by omega⟩ : ℝ) * (s - t0) from by ring,
        bhk_prop11_fract_add (add_nonneg (Int.fract_nonneg _) (mul_nonneg hw0.le hd0))
          (by linarith [h0hi, hadvs])]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith [h0hi, hadvs]
  exact bhk_prop11_part6_claim19_span2 w hpos hab hgap h0safe safe3 (le_of_eq hbt.symm)

/-- **Windowed Claim 19** (the `core2` analog of `part6_claim19`). The (55)-witness
    (cover-agnostic) plus the windowed gap construction give `w₄ < 2w₃`. -/
lemma bhk_prop11_part6_claim19_w (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (g p r : ℕ) (hg : 0 < g) (hp : 0 < p) (hr : 12 ≤ r)
    (hw0 : w ⟨0, by omega⟩ = g * p) (hw3 : w ⟨3, by omega⟩ = g * r)
    (hcop : Nat.Coprime p r) : Found6 w ∨
      (w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) := by
  obtain ⟨t0, h3, hlo, hhi⟩ :=
    bhk_prop11_part6_claim19_witness w g p r hg hp hr hw0 hw3 hcop
  exact bhk_prop11_part6_claim19_gap2 w hpos hsum hdiag t0 h3 hlo hhi

set_option maxHeartbeats 1000000 in
/-- **Windowed Claim 20 gap construction** (the `core2` analog of
    `part6_claim20_gap`). The `4`-block `[pe,qe]` is window-free: at `pe`,
    `{w₀ pe} ≤ 1/3`; at `qe`, with `6w₀ < w₂ < w₃` the drift is `< 1/18` so
    `{w₀ qe} ≤ 1/3 + 1/18 = 7/18 < 5/12`. -/
lemma bhk_prop11_part6_claim20_gap2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (t : ℝ) (N m : ℤ)
    (h0 : (w ⟨0, by omega⟩ : ℝ) * t = (N : ℝ) + 1 / 3)
    (hm : |(w ⟨3, by omega⟩ : ℝ) * t - (m : ℝ)| ≤ 1 / 6) : Found6 w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) := by
  have hw0 : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw1 : (0 : ℝ) < (w ⟨1, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2 : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3 : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3ne : (w ⟨3, by omega⟩ : ℝ) ≠ 0 := hw3.ne'
  have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hsum
  have hdiagR : (w ⟨3, by omega⟩ : ℝ) = (w ⟨0, by omega⟩ : ℝ) + (w ⟨2, by omega⟩ : ℝ) := by
    exact_mod_cast hdiag
  have hsmallR : 3 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall
  have hsmall6R : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall6
  have hw1eq : (w ⟨1, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - 2 * (w ⟨0, by omega⟩ : ℝ) := by
    linarith
  have hw2eq : (w ⟨2, by omega⟩ : ℝ) = (w ⟨3, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) := by linarith
  have h4w0 : 4 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  have h6w0w3 : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by linarith
  obtain ⟨hmlo, hmhi⟩ := abs_le.mp hm
  set pe : ℝ := ((m : ℝ) - 1 / 6) / (w ⟨3, by omega⟩ : ℝ) with hpe
  set qe : ℝ := ((m : ℝ) + 1 / 6) / (w ⟨3, by omega⟩ : ℝ) with hqe
  have hw3pe : (w ⟨3, by omega⟩ : ℝ) * pe = (m : ℝ) - 1 / 6 := by rw [hpe]; field_simp
  have hw3qe : (w ⟨3, by omega⟩ : ℝ) * qe = (m : ℝ) + 1 / 6 := by rw [hqe]; field_simp
  have hpq : qe - pe = 1 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by rw [hpe, hqe]; field_simp; ring
  have hpeqe : pe ≤ qe := by
    have h0lt : (0 : ℝ) < qe - pe := by rw [hpq]; positivity
    linarith
  obtain ⟨hw0pe_lo, hw0pe_hi, hw0qe_lo, hw0qe_hi⟩ :=
    bhk_prop11_part6_edge_arith (w ⟨0, by omega⟩ : ℝ) (w ⟨3, by omega⟩ : ℝ) hw0 hw3 h4w0
      t N m h0 hmlo hmhi pe qe hw3pe hw3qe
  have safe0 : ∀ s ∈ Set.Icc pe qe, (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * s) :=
    bhk_prop11_safe_on_Icc (w ⟨0, by omega⟩ : ℝ) N hw0pe_lo hw0qe_hi hw0.le
  have safe2 : ∀ s ∈ Set.Icc pe qe, (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_safe_on_Icc (w ⟨2, by omega⟩ : ℝ) (m - N - 1) ?_ ?_ hw2.le
    · have hcast : ((m - N - 1 : ℤ) : ℝ) = (m : ℝ) - (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨2, by omega⟩ : ℝ) * pe = ((m : ℝ) - 1 / 6) - (w ⟨0, by omega⟩ : ℝ) * pe := by
        rw [hw2eq, ← hw3pe]; ring
      rw [hcast, hval]; linarith [hw0pe_hi]
    · have hcast : ((m - N - 1 : ℤ) : ℝ) = (m : ℝ) - (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨2, by omega⟩ : ℝ) * qe = ((m : ℝ) + 1 / 6) - (w ⟨0, by omega⟩ : ℝ) * qe := by
        rw [hw2eq, ← hw3qe]; ring
      rw [hcast, hval]; linarith [hw0qe_lo]
  have safe1 : ∀ s ∈ Set.Icc pe qe, (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * s) := by
    apply bhk_prop11_safe_on_Icc (w ⟨1, by omega⟩ : ℝ) (m - 2 * N - 1) ?_ ?_ hw1.le
    · have hcast : ((m - 2 * N - 1 : ℤ) : ℝ) = (m : ℝ) - 2 * (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨1, by omega⟩ : ℝ) * pe
          = ((m : ℝ) - 1 / 6) - 2 * ((w ⟨0, by omega⟩ : ℝ) * pe) := by rw [hw1eq, ← hw3pe]; ring
      rw [hcast, hval]; linarith [hw0pe_hi]
    · have hcast : ((m - 2 * N - 1 : ℤ) : ℝ) = (m : ℝ) - 2 * (N : ℝ) - 1 := by push_cast; ring
      have hval : (w ⟨1, by omega⟩ : ℝ) * qe
          = ((m : ℝ) + 1 / 6) - 2 * ((w ⟨0, by omega⟩ : ℝ) * qe) := by rw [hw1eq, ← hw3qe]; ring
      rw [hcast, hval]; linarith [hw0qe_lo]
  have hfrpe : Int.fract ((m : ℝ) - 1 / 6) = 5 / 6 := by
    rw [show ((m : ℝ) - 1 / 6) = ((m - 1 : ℤ) : ℝ) + 5 / 6 from by push_cast; ring,
      Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have hfrqe : Int.fract ((m : ℝ) + 1 / 6) = 1 / 6 := by
    rw [show ((m : ℝ) + 1 / 6) = ((m : ℤ) : ℝ) + 1 / 6 from by push_cast; ring,
      Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have safe3pe : (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * pe) := by
    rw [hw3pe]; simp only [circDist]; rw [hfrpe]; exact le_min (by norm_num) (by norm_num)
  have safe3qe : (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * qe) := by
    rw [hw3qe]; simp only [circDist]; rw [hfrqe]; exact le_min (by norm_num) (by norm_num)
  have hp : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * pe) := by
    intro i; fin_cases i
    · exact safe0 pe ⟨le_refl _, hpeqe⟩
    · exact safe1 pe ⟨le_refl _, hpeqe⟩
    · exact safe2 pe ⟨le_refl _, hpeqe⟩
    · exact safe3pe
  have hq : ∀ i : Fin 4, (1 : ℝ) / 6 ≤ circDist ((w ⟨i.val, by omega⟩ : ℝ) * qe) := by
    intro i; fin_cases i
    · exact safe0 qe ⟨hpeqe, le_refl _⟩
    · exact safe1 qe ⟨hpeqe, le_refl _⟩
    · exact safe2 qe ⟨hpeqe, le_refl _⟩
    · exact safe3qe
  -- window-freeness at the two edges
  have h0p : Int.fract ((w ⟨0, by omega⟩ : ℝ) * pe) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    have hfr : Int.fract ((w ⟨0, by omega⟩ : ℝ) * pe) = (w ⟨0, by omega⟩ : ℝ) * pe - (N : ℝ) := by
      conv_lhs => rw [show (w ⟨0, by omega⟩ : ℝ) * pe
            = ((N : ℤ) : ℝ) + ((w ⟨0, by omega⟩ : ℝ) * pe - (N : ℝ)) from by push_cast; ring]
      rw [Int.fract_intCast_add,
        Int.fract_eq_self.mpr ⟨by linarith [hw0pe_lo], by linarith [hw0pe_hi]⟩]
    simp only [Set.mem_Ioo, not_and_or, not_lt]; left; rw [hfr]; linarith [hw0pe_hi]
  have hw3qet : (w ⟨3, by omega⟩ : ℝ) * (qe - t) = ((m : ℝ) + 1 / 6) - (w ⟨3, by omega⟩ : ℝ) * t := by
    rw [mul_sub, hw3qe]
  have hqet_nn : 0 ≤ qe - t := by
    have hge : 0 ≤ (w ⟨3, by omega⟩ : ℝ) * (qe - t) := by rw [hw3qet]; linarith [hmhi]
    exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hge) hw3
  have hw0qet : (w ⟨0, by omega⟩ : ℝ) * (qe - t) ≤ 1 / 18 := by
    have h6 : 6 * ((w ⟨0, by omega⟩ : ℝ) * (qe - t)) ≤ (w ⟨3, by omega⟩ : ℝ) * (qe - t) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (w ⟨3, by omega⟩ : ℝ) - 6 * (w ⟨0, by omega⟩ : ℝ)
        from by linarith [h6w0w3]) hqet_nn]
    have hle : (w ⟨3, by omega⟩ : ℝ) * (qe - t) ≤ 1 / 3 := by rw [hw3qet]; linarith [hmlo]
    linarith [h6, hle]
  have hw0qe_hi' : (w ⟨0, by omega⟩ : ℝ) * qe ≤ (N : ℝ) + 7 / 18 := by
    have he : (w ⟨0, by omega⟩ : ℝ) * qe
        = (w ⟨0, by omega⟩ : ℝ) * t + (w ⟨0, by omega⟩ : ℝ) * (qe - t) := by ring
    rw [he, h0]; linarith [hw0qet]
  have h0q : Int.fract ((w ⟨0, by omega⟩ : ℝ) * qe) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    have hfr : Int.fract ((w ⟨0, by omega⟩ : ℝ) * qe) = (w ⟨0, by omega⟩ : ℝ) * qe - (N : ℝ) := by
      conv_lhs => rw [show (w ⟨0, by omega⟩ : ℝ) * qe
            = ((N : ℤ) : ℝ) + ((w ⟨0, by omega⟩ : ℝ) * qe - (N : ℝ)) from by push_cast; ring]
      rw [Int.fract_intCast_add,
        Int.fract_eq_self.mpr ⟨by linarith [hw0qe_lo], by linarith [hw0qe_hi']⟩]
    simp only [Set.mem_Ioo, not_and_or, not_lt]; left; rw [hfr]; linarith [hw0qe_hi']
  exact bhk_prop11_part6_claim20_span2 w hpos hw34 pe qe hpq hp hq h0p h0q

/-- **Windowed Claim 20** (`p ≥ 3`, the `core2` analog of `part6_claim20`). -/
lemma bhk_prop11_part6_claim20_w (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g p r : ℕ) (hg : 0 < g) (hp : 3 ≤ p) (hr : 0 < r)
    (hw0 : w ⟨0, by omega⟩ = g * p) (hw3 : w ⟨3, by omega⟩ = g * r)
    (hcop : Nat.Coprime p r) : Found6 w ∨
      (2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) := by
  obtain ⟨t, N, m, h0, hm⟩ := bhk_prop11_part6_claim20_witness w g p r hg hp hr hw0 hw3 hcop
  exact bhk_prop11_part6_claim20_gap2 w hpos hsum hdiag hsmall hsmall6 hw34 t N m h0 hm

/-- **Windowed Claim 21 lower bound** (`p = 1`, the `core2` analog of
    `part6_claim21_lower`). The `w₂`-block edges have `{w₀·} ∈ [1/3, 5/12]`
    (window-free), so `lower_span2` with `b = w₂` gives `2w₂ < w₄`. -/
lemma bhk_prop11_part6_claim21_lower2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g q : ℕ) (hg : 0 < g) (hq : 0 < q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (t : ℝ) (m : ℤ) (hbt : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ))
    (h0lo : (1 : ℝ) / 3 + 1 / (6 * (q : ℝ)) ≤ (w ⟨0, by omega⟩ : ℝ) * t)
    (h0hi : (w ⟨0, by omega⟩ : ℝ) * t ≤ 5 / 12 - 1 / (6 * (q : ℝ))) : Found6 w ∨
      (2 * (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) := by
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := hw2pos.ne'
  have hw0R : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) := by exact_mod_cast hw0
  have hw2R : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hw2
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hδ : (0 : ℝ) < 1 / (6 * (q : ℝ)) := one_div_pos.mpr (by linarith)
  set pe : ℝ := ((m : ℝ) - 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hpedef
  set qe : ℝ := ((m : ℝ) + 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hqedef
  have hpe : (w ⟨2, by omega⟩ : ℝ) * pe = (m : ℝ) - 1 / 6 := by rw [hpedef]; field_simp
  have hqe : (w ⟨2, by omega⟩ : ℝ) * qe = (m : ℝ) + 1 / 6 := by rw [hqedef]; field_simp
  have hpq : qe - pe = 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by rw [hpedef, hqedef]; field_simp; ring
  obtain ⟨hsafeP, hsafeQ⟩ := bhk_prop11_part6_claim21_edges w hpos hsum hdiag g q hg hq hw0 hw2
    t m hbt h0lo h0hi pe qe hpe hqe
  have e_pe0 : (w ⟨0, by omega⟩ : ℝ) * pe = (w ⟨0, by omega⟩ : ℝ) * t - 1 / (6 * (q : ℝ)) := by
    apply mul_left_cancel₀ hw2ne
    have l : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * pe)
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * pe) := by ring
    have r : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * t - 1 / (6 * (q : ℝ)))
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * t)
          - (w ⟨2, by omega⟩ : ℝ) / (6 * (q : ℝ)) := by ring
    rw [l, r, hpe, hbt, hw0R, hw2R]; field_simp
  have e_qe0 : (w ⟨0, by omega⟩ : ℝ) * qe = (w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)) := by
    apply mul_left_cancel₀ hw2ne
    have l : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * qe)
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * qe) := by ring
    have r : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)))
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * t)
          + (w ⟨2, by omega⟩ : ℝ) / (6 * (q : ℝ)) := by ring
    rw [l, r, hqe, hbt, hw0R, hw2R]; field_simp
  have h0p : Int.fract ((w ⟨0, by omega⟩ : ℝ) * pe) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    have hhi' : (w ⟨0, by omega⟩ : ℝ) * pe ≤ 5 / 12 := by rw [e_pe0]; linarith [h0hi, hδ]
    have hlo' : (0 : ℝ) ≤ (w ⟨0, by omega⟩ : ℝ) * pe := by rw [e_pe0]; linarith [h0lo, hδ]
    rw [Int.fract_eq_self.mpr ⟨hlo', by linarith [hhi']⟩]
    simp only [Set.mem_Ioo, not_and_or, not_lt]; left; exact hhi'
  have h0q : Int.fract ((w ⟨0, by omega⟩ : ℝ) * qe) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    have hhi' : (w ⟨0, by omega⟩ : ℝ) * qe ≤ 5 / 12 := by rw [e_qe0]; linarith [h0hi, hδ]
    have hlo' : (0 : ℝ) ≤ (w ⟨0, by omega⟩ : ℝ) * qe := by rw [e_qe0]; linarith [h0lo, hδ]
    rw [Int.fract_eq_self.mpr ⟨hlo', by linarith [hhi']⟩]
    simp only [Set.mem_Ioo, not_and_or, not_lt]; left; exact hhi'
  exact bhk_prop11_part6_lower_span2 w hpos (w ⟨2, by omega⟩ : ℝ) hw2pos hw24 pe qe hpq
    hsafeP hsafeQ h0p h0q

/-- **Windowed Claim 21 lonely exclusion** (`p = 1`, the `core2` analog of
    `part6_claim21_lonely`). With `w₄ = 2w₂ + w₀`, runner 4 is safe at the right
    edge `qe` and runner 1 is window-free there, so the six-runner cover fails. -/
lemma bhk_prop11_part6_claim21_lonely2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hs : w ⟨4, by omega⟩ = 2 * w ⟨2, by omega⟩ + w ⟨0, by omega⟩)
    (g q : ℕ) (hg : 0 < g) (hq : 0 < q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (t : ℝ) (m : ℤ) (hbt : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ))
    (h0lo : (1 : ℝ) / 3 + 1 / (6 * (q : ℝ)) ≤ (w ⟨0, by omega⟩ : ℝ) * t)
    (h0hi : (w ⟨0, by omega⟩ : ℝ) * t ≤ 5 / 12 - 1 / (6 * (q : ℝ))) : Found6 w := by
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := hw2pos.ne'
  have hw0R : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) := by exact_mod_cast hw0
  have hw2R : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hw2
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hδ : (0 : ℝ) < 1 / (6 * (q : ℝ)) := one_div_pos.mpr (by linarith)
  have hsR : (w ⟨4, by omega⟩ : ℝ)
      = 2 * (w ⟨2, by omega⟩ : ℝ) + (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hs
  set pe : ℝ := ((m : ℝ) - 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hpedef
  set qe : ℝ := ((m : ℝ) + 1 / 6) / (w ⟨2, by omega⟩ : ℝ) with hqedef
  have hpe : (w ⟨2, by omega⟩ : ℝ) * pe = (m : ℝ) - 1 / 6 := by rw [hpedef]; field_simp
  have hqe : (w ⟨2, by omega⟩ : ℝ) * qe = (m : ℝ) + 1 / 6 := by rw [hqedef]; field_simp
  obtain ⟨_, hsafeQ⟩ := bhk_prop11_part6_claim21_edges w hpos hsum hdiag g q hg hq hw0 hw2
    t m hbt h0lo h0hi pe qe hpe hqe
  have e_qe0 : (w ⟨0, by omega⟩ : ℝ) * qe = (w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)) := by
    apply mul_left_cancel₀ hw2ne
    have l : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * qe)
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * qe) := by ring
    have r : (w ⟨2, by omega⟩ : ℝ) * ((w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)))
        = (w ⟨0, by omega⟩ : ℝ) * ((w ⟨2, by omega⟩ : ℝ) * t)
          + (w ⟨2, by omega⟩ : ℝ) / (6 * (q : ℝ)) := by ring
    rw [l, r, hqe, hbt, hw0R, hw2R]; field_simp
  have hw4qe : (w ⟨4, by omega⟩ : ℝ) * qe
      = ((2 * m : ℤ) : ℝ) + (1 / 3 + ((w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ)))) := by
    rw [hsR]
    have hdistr : (2 * (w ⟨2, by omega⟩ : ℝ) + (w ⟨0, by omega⟩ : ℝ)) * qe
        = 2 * ((w ⟨2, by omega⟩ : ℝ) * qe) + (w ⟨0, by omega⟩ : ℝ) * qe := by ring
    rw [hdistr, hqe, e_qe0]; push_cast; ring
  have hfr : Int.fract ((w ⟨4, by omega⟩ : ℝ) * qe)
      = 1 / 3 + ((w ⟨0, by omega⟩ : ℝ) * t + 1 / (6 * (q : ℝ))) := by
    rw [hw4qe, Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have safe4qe : (1 : ℝ) / 6 ≤ circDist ((w ⟨4, by omega⟩ : ℝ) * qe) := by
    simp only [circDist]; rw [hfr]; exact le_min (by linarith) (by linarith)
  rcases found6_or_blocked w qe with hF | ⟨i, hi⟩ | hfict
  · exact hF
  · fin_cases i
    · exact absurd hi (not_lt.mpr (hsafeQ 0))
    · exact absurd hi (not_lt.mpr (hsafeQ 1))
    · exact absurd hi (not_lt.mpr (hsafeQ 2))
    · exact absurd hi (not_lt.mpr (hsafeQ 3))
    · exact absurd hi (not_lt.mpr safe4qe)
  · have hr0 : (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * qe) := hsafeQ 0
    have h1 : (1 : ℝ) / 6 ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * qe) := by
      have := hr0; unfold circDist at this; exact le_trans this (min_le_left _ _)
    have h2 : Int.fract ((w ⟨0, by omega⟩ : ℝ) * qe) ≤ 5 / 6 := by
      have := hr0; unfold circDist at this; linarith [le_trans this (min_le_right _ _)]
    have h0qsafe : Int.fract ((w ⟨0, by omega⟩ : ℝ) * qe) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
      have hhi' : (w ⟨0, by omega⟩ : ℝ) * qe ≤ 5 / 12 := by rw [e_qe0]; linarith [h0hi, hδ]
      have hlo' : (0 : ℝ) ≤ (w ⟨0, by omega⟩ : ℝ) * qe := by rw [e_qe0]; linarith [h0lo, hδ]
      rw [Int.fract_eq_self.mpr ⟨hlo', by linarith [hhi']⟩]
      simp only [Set.mem_Ioo, not_and_or, not_lt]; left; exact hhi'
    exact absurd hfict (not_lt.mpr (bhk_prop11_fict_window_safe h1 h2 h0qsafe))

/-- **Windowed Part 6, `p = 1`** (the `core2` analog of `part6_p1`). -/
lemma bhk_prop11_part6_p1_w (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g q s : ℕ) (hg : 0 < g) (hq16 : 16 ≤ q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (hw4 : w ⟨4, by omega⟩ = g * s) : Found6 w := by
  have hq0 : 0 < q := by omega
  obtain ⟨t, m, hbt, h0lo, h0hi⟩ := bhk_prop11_part6_claim21_witness w g q hg hq16 hw0 hw2
  have hw0' : w ⟨0, by omega⟩ = g * 1 := by omega
  have hw3' : w ⟨3, by omega⟩ = g * (q + 1) := by rw [hdiag, hw0, hw2]; ring
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19_w w hpos hsum hdiag g 1 (q + 1) hg (by norm_num) (by omega)
      hw0' hw3' (Nat.coprime_one_left _)
  · exact hF
  obtain hF | (h21 : 2 * (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
    bhk_prop11_part6_claim21_lower2 w hpos hsum hdiag hw24 g q hg hq0 hw0 hw2 t m hbt h0lo h0hi
  · exact hF
  have h21n : 2 * w ⟨2, by omega⟩ < w ⟨4, by omega⟩ := by exact_mod_cast h21
  have hsqueeze : s = 2 * q + 1 := by
    have a1 : 2 * q < s := by
      have h := h21n
      rw [hw2, hw4] at h
      have h' : g * (2 * q) = 2 * (g * q) := by ring
      exact lt_of_mul_lt_mul_left (h'.trans_lt h) (Nat.zero_le g)
    have a2 : s < 2 * q + 2 := by
      have h := h19
      rw [hw4, hw3'] at h
      have h' : 2 * (g * (q + 1)) = g * (2 * q + 2) := by ring
      exact lt_of_mul_lt_mul_left (h.trans_le h'.le) (Nat.zero_le g)
    omega
  have hs : w ⟨4, by omega⟩ = 2 * w ⟨2, by omega⟩ + w ⟨0, by omega⟩ := by
    rw [hw4, hw2, hw0, hsqueeze]; ring
  exact bhk_prop11_part6_claim21_lonely2 w hpos hsum hdiag hs g q hg hq0 hw0 hw2 t m hbt h0lo h0hi

/-- **Windowed Part 6 — diagonal case `w₃ = w₀ + w₂`** (the `core2` analog of
    `part6`). Closes the `(1,1)` diagonal config under the six-runner covering. -/
lemma bhk_prop11_part6_w (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g p q r s : ℕ) (hg : 0 < g) (hp_pos : 0 < p) (hq18 : 18 ≤ q)
    (hgp : w ⟨0, by omega⟩ = g * p) (hgq : w ⟨2, by omega⟩ = g * q)
    (hgr : w ⟨3, by omega⟩ = g * r) (hgs : w ⟨4, by omega⟩ = g * s)
    (hcop : Nat.Coprime p q) : Found6 w := by
  have hrpq : r = p + q := by
    have h : g * r = g * (p + q) := by rw [← hgr, hdiag, hgp, hgq]; ring
    exact Nat.eq_of_mul_eq_mul_left hg h
  have hr12 : 12 ≤ r := by omega
  have hcopr : Nat.Coprime p r := by
    show Nat.gcd p r = 1
    rw [hrpq, Nat.add_comm p q, Nat.gcd_add_self_right]; exact hcop
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19_w w hpos hsum hdiag g p r hg hp_pos hr12 hgp hgr hcopr
  · exact hF
  have h19R : (w ⟨4, by omega⟩ : ℝ) < 2 * (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast h19
  have hw23 : w ⟨2, by omega⟩ < w ⟨3, by omega⟩ := by rw [hgq, hgr, hrpq]; nlinarith [hg, hp_pos]
  have hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) :=
    lt_trans (by exact_mod_cast hw23) hw34
  rcases lt_or_ge p 3 with hp3 | hp3
  · interval_cases p
    · have hw0g : w ⟨0, by omega⟩ = g := by omega
      exact bhk_prop11_part6_p1_w w hpos hsum hdiag hw24 g q s hg (by omega) hw0g hgq hgs
    · have hqodd : q % 2 = 1 := by
        have h2 : ¬ (2 ∣ q) := by
          intro hdvd
          have hg2 : Nat.gcd 2 q = 2 := Nat.gcd_eq_left hdvd
          have hc1 : Nat.gcd 2 q = 1 := hcop
          omega
        omega
      have hrodd : r % 2 = 1 := by omega
      obtain ⟨t, N, m, h0, hm⟩ := bhk_prop11_part6_claim20_witness_p2 w g r hg hrodd hgp hgr
      obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
        bhk_prop11_part6_claim20_gap2 w hpos hsum hdiag hsmall hsmall6 hw34 t N m h0 hm
      · exact hF
      linarith
  · obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
      bhk_prop11_part6_claim20_w w hpos hsum hdiag hsmall hsmall6 hw34 g p r hg hp3 (by omega)
        hgp hgr hcopr
    · exact hF
    linarith

/-- **Part 6 diagonal, six-runner, `p ≥ 2`, `r ≥ 12`** (`part6_w` with the `q ≥ 18`
    requirement relaxed to `r ≥ 12`, valid for the `p ≥ 2` branch only). Closes the
    `p ≥ 2` diagonals `(2,13,15)`, `(2,15,17)`, `(2,17,19)` in `core2_q_lt_18`. -/
lemma bhk_prop11_part6_ge12_w (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g p q r s : ℕ) (hg : 0 < g) (hp2 : 2 ≤ p) (hr12 : 12 ≤ r)
    (hgp : w ⟨0, by omega⟩ = g * p) (hgq : w ⟨2, by omega⟩ = g * q)
    (hgr : w ⟨3, by omega⟩ = g * r) (hgs : w ⟨4, by omega⟩ = g * s)
    (hcop : Nat.Coprime p q) : Found6 w := by
  have hrpq : r = p + q := by
    have h : g * r = g * (p + q) := by rw [← hgr, hdiag, hgp, hgq]; ring
    exact Nat.eq_of_mul_eq_mul_left hg h
  have hp_pos : 0 < p := by omega
  have hcopr : Nat.Coprime p r := by
    show Nat.gcd p r = 1
    rw [hrpq, Nat.add_comm p q, Nat.gcd_add_self_right]; exact hcop
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19_w w hpos hsum hdiag g p r hg hp_pos hr12 hgp hgr hcopr
  · exact hF
  have h19R : (w ⟨4, by omega⟩ : ℝ) < 2 * (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast h19
  have hw23 : w ⟨2, by omega⟩ < w ⟨3, by omega⟩ := by rw [hgq, hgr, hrpq]; nlinarith [hg, hp_pos]
  have hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) :=
    lt_trans (by exact_mod_cast hw23) hw34
  rcases lt_or_ge p 3 with hp3 | hp3
  · interval_cases p
    · -- p = 2
      have hqodd : q % 2 = 1 := by
        have h2 : ¬ (2 ∣ q) := by
          intro hdvd
          have hg2 : Nat.gcd 2 q = 2 := Nat.gcd_eq_left hdvd
          have hc1 : Nat.gcd 2 q = 1 := hcop
          omega
        omega
      have hrodd : r % 2 = 1 := by omega
      obtain ⟨t, N, m, h0, hm⟩ := bhk_prop11_part6_claim20_witness_p2 w g r hg hrodd hgp hgr
      obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
        bhk_prop11_part6_claim20_gap2 w hpos hsum hdiag hsmall hsmall6 hw34 t N m h0 hm
      · exact hF
      linarith
  · obtain hF | (h20 : 2 * (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
      bhk_prop11_part6_claim20_w w hpos hsum hdiag hsmall hsmall6 hw34 g p r hg hp3 (by omega)
        hgp hgr hcopr
    · exact hF
    linarith

/-- **Part 6 diagonal, six-runner, `p = 1`, explicit `(57)`-witness** (`part6_p1_w`
    with the `q ≥ 16` grid relaxed to an explicit witness `m`, valid for `q ≥ 11`).
    Combines Claim 19 (`w₄ < 2w₃`), Claim 21's lower bound and the `s = 2q+1`
    exclusion. Closes the `p = 1`, `r ≥ 12`, grid-present diagonals. -/
lemma bhk_prop11_part6_p1_wit_w (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩)
    (hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ))
    (g q s : ℕ) (hg : 0 < g) (hq11 : 11 ≤ q)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * q)
    (hw4 : w ⟨4, by omega⟩ = g * s)
    (t : ℝ) (m : ℤ) (hbt : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ))
    (h0lo : (1 : ℝ) / 3 + 1 / (6 * (q : ℝ)) ≤ (w ⟨0, by omega⟩ : ℝ) * t)
    (h0hi : (w ⟨0, by omega⟩ : ℝ) * t ≤ 5 / 12 - 1 / (6 * (q : ℝ))) : Found6 w := by
  have hq0 : 0 < q := by omega
  have hw0' : w ⟨0, by omega⟩ = g * 1 := by omega
  have hw3' : w ⟨3, by omega⟩ = g * (q + 1) := by rw [hdiag, hw0, hw2]; ring
  obtain hF | (h19 : w ⟨4, by omega⟩ < 2 * w ⟨3, by omega⟩) :=
    bhk_prop11_part6_claim19_w w hpos hsum hdiag g 1 (q + 1) hg (by norm_num) (by omega)
      hw0' hw3' (Nat.coprime_one_left _)
  · exact hF
  obtain hF | (h21 : 2 * (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ)) :=
    bhk_prop11_part6_claim21_lower2 w hpos hsum hdiag hw24 g q hg hq0 hw0 hw2 t m hbt h0lo h0hi
  · exact hF
  have h21n : 2 * w ⟨2, by omega⟩ < w ⟨4, by omega⟩ := by exact_mod_cast h21
  have hsqueeze : s = 2 * q + 1 := by
    have a1 : 2 * q < s := by
      have h := h21n
      rw [hw2, hw4] at h
      have h' : g * (2 * q) = 2 * (g * q) := by ring
      exact lt_of_mul_lt_mul_left (h'.trans_lt h) (Nat.zero_le g)
    have a2 : s < 2 * q + 2 := by
      have h := h19
      rw [hw4, hw3'] at h
      have h' : 2 * (g * (q + 1)) = g * (2 * q + 2) := by ring
      exact lt_of_mul_lt_mul_left (h.trans_le h'.le) (Nat.zero_le g)
    omega
  have hs : w ⟨4, by omega⟩ = 2 * w ⟨2, by omega⟩ + w ⟨0, by omega⟩ := by
    rw [hw4, hw2, hw0, hsqueeze]; ring
  exact bhk_prop11_part6_claim21_lonely2 w hpos hsum hdiag hs g q hg hq0 hw0 hw2 t m hbt
    h0lo h0hi

set_option maxHeartbeats 1000000 in
/-- **Windowed P-witness kill (`q < 18`/`[18,30)`, six-runner part 2).** As
    `bhk_prop11_exc_Pkill` but for the fictional-runner covering `hcov6`: it uses the
    windowed reduced pentagon `bhk_prop11_pent_no_good_red2`, which adds BHK's `(43)`
    cut `Y ≤ 5/12 − v₁/3` (hypothesis `h43rw`, an `s`-free `norm_num` goal). -/
lemma bhk_prop11_exc_Pkill2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s m : ℕ) (hg : 0 < g) (hq : 0 < q) (hp : 0 < p) (hpqlt : p < q)
    (hrq : q < r) (hrs : r < s)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (h39w : 1 / 6 - (r : ℝ) * (((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1)))
        ≤ (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ))
    (h40w : 1 / 6 - (p : ℝ) * (((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1)))
        ≤ (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ))
    (h41w : (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)
        ≤ 1 / 3 + ((q : ℝ) - p) * (((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1))))
    (hxlew : (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) ≤ 5 / 6)
    (h42aw : 1 / (3 * ((r : ℝ) + 1))
        ≤ (5 / 6 - (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)) / r
          + ((((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) - 1 / 6) / p)
    (h42bw : 1 / (3 * ((r : ℝ) + 1))
        ≤ (5 / 6 - (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)) / r
          + (1 / 3 - (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)) / ((q : ℝ) - p))
    (h43rw : (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)
        ≤ 5 / 12 - (p : ℝ) / (3 * q)) : Found6 w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hsR : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hr1R : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hrsR : (r : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast (by omega : r + 1 ≤ s)
  have hqpR : (0 : ℝ) ≤ (q : ℝ) - p := by
    have : (p : ℝ) < q := by exact_mod_cast hpqlt
    linarith
  have hcorr : ((r : ℝ) + 1 - q) / (3 * q * ((r : ℝ) + 1)) ≤ ((s : ℝ) - q) / (3 * q * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hqR.le hqR.le) (show (0 : ℝ) ≤ (s : ℝ) - ((r : ℝ) + 1) from by linarith)]
  have hrecip : 1 / (3 * (s : ℝ)) ≤ 1 / (3 * ((r : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hXrw : Int.fract ((r : ℝ) / q * (((m : ℤ) : ℝ) + 1 / 2))
      = (((2 * (r * m % q) + r) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) := by
    rw [show ((m : ℤ) : ℝ) = ((m : ℕ) : ℝ) from by push_cast; ring,
        bhk_prop11_Cpoint_eval r q m hq]
  have hYrw : Int.fract ((p : ℝ) / q * (((m : ℤ) : ℝ) + 1 / 2))
      = (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) := by
    rw [show ((m : ℤ) : ℝ) = ((m : ℕ) : ℝ) from by push_cast; ring,
        bhk_prop11_Cpoint_eval p q m hq]
  refine bhk_prop11_pent_no_good_red2 w hmono hpos hsum hsmall6 g p q r s hg hq hp hr0 hs0
    hpqlt c0 c2 c3 c4 (m : ℤ) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hXrw]; nlinarith [h39w, mul_le_mul_of_nonneg_left hcorr hrR.le]
  · rw [hYrw]
    have hp0R : (0 : ℝ) ≤ (p : ℝ) := by positivity
    nlinarith [h40w, mul_le_mul_of_nonneg_left hcorr hp0R]
  · rw [hYrw]; nlinarith [h41w, mul_le_mul_of_nonneg_left hcorr hqpR]
  · rw [hXrw]; exact hxlew
  · rw [hXrw, hYrw]; linarith [h42aw, hrecip]
  · rw [hXrw, hYrw]; linarith [h42bw, hrecip]
  · rw [hYrw]; exact h43rw

set_option maxHeartbeats 40000000 in
/-- **Windowed transversal slivers `q ∈ [18,30)` — part-2 finite R/P dispatch.** The
    six-runner (fictional-runner `hcov6`) analog of `bhk_prop11_exc_q_18_30`: R-cases
    use the rectangle `h_nogood` (`bhk_prop11_exc_Rkill`, 526), P-cases use the
    windowed pentagon `bhk_prop11_exc_Pkill2` (82, BHK `(43)` cut). 0 fails. -/
lemma bhk_prop11_exc_q_18_30_2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r s : ℕ) (hg : 0 < g) (hq18 : 18 ≤ q) (hq30 : q < 30)
    (hcop : Nat.Coprime p q) (hp : 0 < p) (h3p : 3 * p < q)
    (hrq : q < r) (hr32 : 2 * r < 3 * q) (hrs : r < s) (hndiag : r ≠ p + q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s)
    (h_nogood : ∀ l : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) : Found6 w := by
  interval_cases q
  · -- q = 18
    have hpb : p ≤ 5 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 26 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 18 20 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 21 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 22 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 23 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 24 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 25 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 18 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 26 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 19 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 20 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 21 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 24 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 25 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 18 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 19
    have hpb : p ≤ 6 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 28 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 19 21 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 23 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 25 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 19 26 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 19 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 19 28 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 19 20 s 12 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 22 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 19 23 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 19 24 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 25 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 26 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 27 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 19 28 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 20 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 21 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 19 23 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 24 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 19 25 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 26 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 19 27 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 19 28 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 20 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 19 21 s 10 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 19 22 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 24 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 25 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 26 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 19 27 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 19 28 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 19 20 s 12 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 21 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 25 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 19 26 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 19 28 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 6
      have hru : r ≤ 28 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 20 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 21 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 6 19 22 s 13 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 23 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 24 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 26 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 27 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 19 28 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 20
    have hpb : p ≤ 6 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 29 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 20 22 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 26 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 27 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 20 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 29 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 21 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 22 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 24 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 25 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 20 26 s 15 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 27 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 28 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 20 29 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
  · -- q = 21
    have hpb : p ≤ 6 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 31 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 21 23 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 24 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 27 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 28 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 21 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 2
      have hru : r ≤ 31 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 21 22 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 24 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 27 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 28 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 29 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 21 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 4
      have hru : r ≤ 31 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 22 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 23 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 24 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 26 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 27 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 28 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 29 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 21 31 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 31 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 22 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 23 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 24 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 25 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 27 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 28 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 29 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 21 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 21 31 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact absurd hcop (by decide)
  · -- q = 22
    have hpb : p ≤ 7 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 32 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 22 24 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 25 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 22 27 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 28 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 22 32 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 32 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 23 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 24 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 26 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 27 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 22 28 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 22 29 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 30 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 31 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 22 32 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 32 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 23 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 24 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 25 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 28 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 22 31 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 22 32 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 32 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 23 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 24 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 25 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 26 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 27 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 28 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 31 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 22 32 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 23
    have hpb : p ≤ 7 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 34 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 23 25 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 31 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 23 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 23 34 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 23 24 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 26 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 23 27 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 28 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 29 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 30 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 31 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 33 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 23 34 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 24 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 25 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 23 27 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 28 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 23 29 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 30 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 31 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 23 33 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 23 34 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 24 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 23 25 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 26 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 28 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 29 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 30 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 23 31 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 23 33 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 23 34 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 24 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 25 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 26 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 27 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 29 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 30 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 31 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 23 32 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 23 33 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 23 34 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 6
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 24 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 25 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 6 23 26 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 27 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 30 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 31 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 23 34 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 7
      have hru : r ≤ 34 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 24 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 25 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 26 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 27 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 28 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 29 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 7 23 31 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 33 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 23 34 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 24
    have hpb : p ≤ 7 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 35 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 24 26 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 27 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 31 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 32 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 24 35 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 35 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 25 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 26 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 27 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 28 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 30 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 31 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 32 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 33 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 24 34 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 24 35 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 35 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 25 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 26 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 27 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 32 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 24 35 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 25
    have hpb : p ≤ 8 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 37 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 25 27 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 28 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 31 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 32 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 35 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 25 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 25 37 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 25 26 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 28 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 25 29 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 30 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 33 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 34 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 36 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 25 37 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 26 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 27 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 29 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 30 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 25 31 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 32 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 33 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 34 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 25 36 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 25 37 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 26 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 25 27 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 28 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 30 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 31 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 32 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 25 33 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 34 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 35 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 25 36 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 25 37 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 6
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 26 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 27 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 6 25 28 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 30 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 32 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 35 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 25 36 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 6 25 37 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 7
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 26 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 27 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 28 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 29 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 31 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 33 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 7 25 34 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 35 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 25 37 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 8
      have hru : r ≤ 37 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 26 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 27 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 28 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 8 25 29 s 16 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 30 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 31 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 32 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 34 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 35 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 36 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 25 37 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 26
    have hpb : p ≤ 8 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 38 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 26 28 s 8 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 33 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 35 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 26 38 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 38 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 27 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 28 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 30 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 31 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 26 32 s 11 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 33 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 34 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 36 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 37 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 26 38 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 38 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 27 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 28 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 29 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 32 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 33 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 34 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 35 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 26 36 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 37 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 26 38 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 38 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 27 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 28 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 29 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 32 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 34 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 35 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 36 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 26 38 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
  · -- q = 27
    have hpb : p ≤ 8 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 40 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 27 29 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 34 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 35 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 36 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 27 40 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 27 28 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 30 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 33 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 34 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 35 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 36 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 27 40 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 4
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 28 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 29 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 30 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 32 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 33 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 34 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 35 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 36 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 37 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 38 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 39 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 27 40 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 28 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 29 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 30 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 31 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 33 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 34 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 35 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 36 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 27 37 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 27 38 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 39 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 27 40 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 7
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 28 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 29 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 30 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 35 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 36 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 27 40 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 8
      have hru : r ≤ 40 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 28 24 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 29 24 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 30 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 31 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 33 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 34 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 36 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 37 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 38 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 39 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 27 40 14 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 28
    have hpb : p ≤ 9 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 41 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 28 30 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 31 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 32 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 34 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 35 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 36 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 37 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 38 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 39 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 40 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 28 41 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 3
      have hru : r ≤ 41 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 29 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 30 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 32 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 33 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 28 34 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 35 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 36 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 38 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 39 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 40 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 28 41 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · -- p = 5
      have hru : r ≤ 41 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 29 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 30 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 31 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 32 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 34 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 35 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 36 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 37 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 28 38 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 39 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 40 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 28 41 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · exact absurd hcop (by decide)
    · -- p = 9
      have hru : r ≤ 41 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 29 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 30 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 31 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 32 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 33 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 34 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 35 19 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 36 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 38 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 39 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 40 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 28 41 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
  · -- q = 29
    have hpb : p ≤ 9 := by omega
    interval_cases p
    · -- p = 1
      have hru : r ≤ 43 := by omega
      interval_cases r
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 29 31 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 32 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 35 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 36 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 37 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 38 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 39 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 40 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 41 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 1 29 42 6 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 29 43 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 2
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 29 30 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 32 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 29 33 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 35 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 36 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 38 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 39 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 40 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 41 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 42 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 2 29 43 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 3
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 30 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 31 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 33 12 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 34 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 29 35 s 3 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 36 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 37 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 38 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 39 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 40 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 41 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 3 29 42 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 3 29 43 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 4
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 30 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 29 31 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 32 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 34 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 35 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 36 16 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 4 29 37 s 2 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 38 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 39 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 40 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 41 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 42 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 4 29 43 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 5
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 30 24 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 31 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 33 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 35 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 36 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 37 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 38 18 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 29 39 s 7 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 40 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 5 29 41 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 42 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 5 29 43 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 6
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 30 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 31 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 6 29 32 s 6 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 33 20 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 34 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 36 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 37 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 38 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 39 25 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 40 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 6 29 41 s 1 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 42 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 6 29 43 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 7
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 30 21 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 31 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 32 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 33 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 34 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 35 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 37 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 38 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 39 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 7 29 40 s 9 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 41 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 7 29 42 17 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 7 29 43 s 5 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · -- p = 8
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 30 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 31 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 32 26 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 8 29 33 s 4 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 34 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 35 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 36 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 38 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 39 11 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 40 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 41 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 42 15 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 8 29 43 22 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
    · -- p = 9
      have hru : r ≤ 43 := by omega
      interval_cases r
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 30 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 31 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 32 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 33 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 34 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 35 13 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 36 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 37 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · omega
      · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 9 29 39 s 10 hg (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 40 7 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 41 23 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 42 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      · exact False.elim <| bhk_prop11_exc_Rkill 9 29 43 26 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])

/-- **core2, `q ≥ 18` dispatch.** Mirror of `bhk_prop11_core_q18` for the
    six-runner (windowed) covering: extract a minimal exceptional pair
    (`exceptional_q18_w`), build the rectangle no-good-time (`no_good_time2`) and
    `2r < 3q` (`v4_le_3_2_w`), then dispatch. The bulk `exc_open` branch is
    *covering-agnostic* — it is reused verbatim, so the other session's
    transversal fills close it automatically. The three pentagon-dependent
    branches (Part 6 diagonal, `(1,2)`, `(1,-2)`) need the *windowed pentagon*
    (the fictional 0123-gap) and remain as the residual `core2` sorries. -/
theorem bhk_prop11_core2_q18 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq18 : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)) : Found6 w := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  obtain hF | ⟨g, p, q, r, s, hg_pos, hgp, hgq, hgr, hgs, hcop, hq18', ⟨i, j⟩, hne,
      ⟨k, hk1, hk2⟩, h0, h1β, hc1, hc2, h14⟩ :=
    bhk_prop11_exceptional_q18_w w hmono hpos hsum hsmall6 hq18
  · exact hF
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * (p : ℝ) := by exact_mod_cast hgp
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hgq
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * (r : ℝ) := by exact_mod_cast hgr
  have hp_pos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.mul_zero] at hgp
      have h0' := hpos ⟨0, by omega⟩
      omega
    · exact h
  have h3p : 3 * p < q := by
    have h : g * (3 * p) < g * q := by
      rw [show g * (3 * p) = 3 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  have hrq : q < r := by
    have hw23 : w ⟨2, by omega⟩ < w ⟨3, by omega⟩ :=
      hmono (Fin.mk_lt_mk.mpr (show (2:ℕ) < 3 by omega))
    have h : g * q < g * r := by rw [← hgq, ← hgr]; exact hw23
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  obtain hF | hreal := bhk_prop11_v4_le_3_2_w w hmono hpos hsum hsmall6 hq18
  · exact hF
  have hr32 : 2 * r < 3 * q := by
    have hgR : (0:ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
    rw [c3, c2] at hreal
    have hcancel : (g : ℝ) * (2 * (r : ℝ)) < (g : ℝ) * (3 * (q : ℝ)) := by nlinarith [hreal]
    have hR : (2 * (r : ℝ)) < 3 * (q : ℝ) := lt_of_mul_lt_mul_left hcancel hgR.le
    exact_mod_cast hR
  obtain hF | h_nogood : Found6 w ∨ (∀ l : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) := by
    rw [or_iff_not_imp_right]
    intro hQ
    obtain ⟨l, hl⟩ := not_forall_not.mp hQ
    obtain ⟨hrmem, hpmem⟩ := hl
    set t : ℝ := ((l : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
    have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
    have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (l : ℝ) + 1 / 2 := by rw [htdef]; field_simp
    have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c0, c2]; field_simp
    have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c3, c2]; field_simp
    refine bhk_prop11_no_good_time2 w hmono hpos hsum hsmall6 t ?_ ?_ ?_ ?_ ?_
    · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    · rw [e0]; exact hpmem.1
    · rw [e0]; exact hpmem.2
    · rw [e3]; exact hrmem.1
    · rw [e3]; exact hrmem.2
  · exact hF
  by_cases hdiag : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩
  · -- Part 6 (diagonal `w₃ = w₀ + w₂`, pair `(1,1)`): the windowed Part 6
    -- (Claims 19–21 with the fictional 0123-gap).
    have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
      exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
    exact bhk_prop11_part6_w w hpos hsum hsmall hsmall6 hdiag hw34 g p q r s hg_pos hp_pos
      hq18' hgp hgq hgr hgs hcop
  · by_cases h12 : i = 1 ∧ j = 2
    · -- `(1,2)` windowed pentagon kill
      obtain ⟨hi1, hj2⟩ := h12
      subst hi1; subst hj2
      have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
      have hrs : r < s := by
        have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
          hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
        have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
        exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
      have hrig : 2 * r = 2 * q + p :=
        bhk_prop11_exc_1_2 p q r hp_pos h3p hrq hr32 k hk1 hk2
      have hsmall6N : 6 * p < q := by
        have h : g * (6 * p) < g * q := by
          rw [show g * (6 * p) = 6 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall6
        exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
      exact bhk_prop11_exc_1_2_kill2 w hmono hpos hsum hsmall6 g p q r s hg_pos
        (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq18' hsmall6N hrig
    · by_cases h1n2 : i = 1 ∧ j = -2
      · -- `(1,-2)` windowed pentagon kill
        obtain ⟨hi1, hjn2⟩ := h1n2
        subst hi1; subst hjn2
        have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
        have hrs : r < s := by
          have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
            hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
          have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
          exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
        have hrig : 2 * r + p = 3 * q :=
          bhk_prop11_exc_1_neg2 p q r hp_pos h3p hrq hr32 k hk1 hk2
        have hsmall6N : 6 * p < q := by
          have h : g * (6 * p) < g * q := by
            rw [show g * (6 * p) = 6 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall6
          exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
        exact bhk_prop11_exc_1_neg2_kill2 w hmono hpos hsum hsmall6 g p q r s hg_pos
          (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq18' hsmall6N hrig
      · by_cases h21 : i = 2 ∧ j = 1
        · -- (2,1) exceptional pair: peel to the six-runner pentagon kill
          obtain ⟨hi2, hj1⟩ := h21
          subst hi2; subst hj1
          have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
          have hrs : r < s := by
            have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
              hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
            have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
            exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
          have hsmall6N : 6 * p < q := by
            have h : g * (6 * p) < g * q := by
              rw [show g * (6 * p) = 6 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall6
            exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
          have hrig : r = 2 * p + q :=
            bhk_prop11_exc_2_1 p q r hp_pos h3p hrq hr32 k hk1 hk2
          exact bhk_prop11_exc_2_1_pentkill2 w hmono hpos hsum hsmall6 g p q r s hg_pos
            (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq18' hsmall6N hrig
        · by_cases hq30 : 30 ≤ q
          · by_cases h42 : i = 4 ∧ j = 2
            · -- (4,2): only the c=2 line `r = 2p+q` survives (`6p < q` kills c=1)
              obtain ⟨hi4, hj2⟩ := h42
              subst hi4; subst hj2
              have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
              have hrs : r < s := by
                have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
                  hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
                have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
                exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
              have hsmall6N : 6 * p < q := by
                have h : g * (6 * p) < g * q := by
                  rw [show g * (6 * p) = 6 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall6
                exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
              rcases bhk_prop11_exc_4_2 p q r hp_pos h3p hrq hr32 k hk1 hk2 with hrig | hrig2
              · exact bhk_prop11_exc_2_1_pentkill2 w hmono hpos hsum hsmall6 g p q r s hg_pos
                  (by omega) c0 c2 c3 c4 hcop hp_pos h3p hrq hr32 hrs hq18' hsmall6N hrig
              · -- c=1: `2r = 4p+q` with `q < r` forces `4p > q`, contradicting `6p < q`
                omega
            · exact False.elim <| bhk_prop11_exc_open p q r hq30 hcop hp_pos h3p hrq hr32 i j k h0 h1β hc1 hc2 hne
                hk1 hk2 h_nogood h14 h12 h1n2 h21 h42 (fun h => hdiag (by rw [hgr, hgp, hgq, h]; ring))
          · -- q ∈ [18,30): windowed finite R/P dispatch
            have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
            have hrs : r < s := by
              have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
                hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
              have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
              exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
            exact bhk_prop11_exc_q_18_30_2 w hmono hpos hsum hsmall6 g p q r s hg_pos hq18'
              (by omega) hcop hp_pos h3p hrq hr32 hrs
              (fun h => hdiag (by rw [hgr, hgp, hgq, h]; ring)) c0 c2 c3 c4 h_nogood

/-- **Diagonal `s`-upper-bound engine, six-runner** (`bhk_diag_sbound` with the
    fictional runner `2w₀`). The `0123`-gap `[a,b]` (runners `0,1,2,3` safe and the
    fictional runner `2w₀` safe via `hfic`) is forced into `unsafeOf w₄` by `hcov6`. -/
lemma bhk_diag_sbound2 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (a b : ℝ) (hab : a ≤ b)
    (h0 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨0, by omega⟩ : ℝ) * τ))
    (h1 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨1, by omega⟩ : ℝ) * τ))
    (h2 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨2, by omega⟩ : ℝ) * τ))
    (h3 : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist ((w ⟨3, by omega⟩ : ℝ) * τ))
    (hfic : ∀ τ ∈ Set.Icc a b, (1 : ℝ) / 6 ≤ circDist (2 * ((w ⟨0, by omega⟩ : ℝ) * τ))) : Found6 w ∨
      (b - a ≤ 1 / (3 * (w ⟨4, by omega⟩ : ℝ))) := by
  rw [or_iff_not_imp_right]
  intro hcon
  push_neg at hcon
  -- a point of `[a, b]` outside runner 5's zone: every runner is clear there
  obtain ⟨τ, hτ, hτ4⟩ := Set.not_subset.mp
    (bhk_prop11_not_subset_unsafeOf w ⟨4, by omega⟩ (hpos _) hab hcon)
  rw [mem_unsafeOf_iff, not_lt] at hτ4
  refine ⟨τ, fun i => ?_, hfic τ hτ⟩
  fin_cases i
  · exact h0 τ hτ
  · exact h1 τ hτ
  · exact h2 τ hτ
  · exact h3 τ hτ
  · exact hτ4

/-- **Lonely-time contradiction, six-runner** (`bhk_lonely5` plus the fictional
    runner `2w₀` safe at `τ`, hypothesis `hfic`). -/
lemma bhk_lonely6 (w : Fin 5 → ℕ)
    (τ : ℝ)
    (f0 f1 f2 f3 f4 : ℝ) (K0 K1 K2 K3 K4 : ℤ)
    (e0 : (w ⟨0, by omega⟩ : ℝ) * τ = (K0 : ℝ) + f0)
    (e1 : (w ⟨1, by omega⟩ : ℝ) * τ = (K1 : ℝ) + f1)
    (e2 : (w ⟨2, by omega⟩ : ℝ) * τ = (K2 : ℝ) + f2)
    (e3 : (w ⟨3, by omega⟩ : ℝ) * τ = (K3 : ℝ) + f3)
    (e4 : (w ⟨4, by omega⟩ : ℝ) * τ = (K4 : ℝ) + f4)
    (h0 : f0 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6)) (h1 : f1 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6))
    (h2 : f2 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6)) (h3 : f3 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6))
    (h4 : f4 ∈ Set.Icc (1 / 6 : ℝ) (5 / 6))
    (ffic : ℝ) (Kfic : ℤ) (efic : 2 * ((w ⟨0, by omega⟩ : ℝ) * τ) = (Kfic : ℝ) + ffic)
    (hficmem : ffic ∈ Set.Icc (1 / 6 : ℝ) (5 / 6)) : Found6 w := by
  have key : ∀ (j : Fin 5) (K : ℤ) (f : ℝ), (w j : ℝ) * τ = (K : ℝ) + f →
      f ∈ Set.Icc (1 / 6 : ℝ) (5 / 6) → 1 / 6 ≤ circDist ((w j : ℝ) * τ) := by
    intro j K f he hf
    obtain ⟨hl, hh⟩ := hf
    have hfr : Int.fract ((w j : ℝ) * τ) = f := by
      rw [he, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    rw [circDist, hfr]; exact le_min hl (by linarith)
  rcases found6_or_blocked w τ with hF | ⟨i, hi⟩ | hfict
  · exact hF
  · fin_cases i
    · exact absurd hi (not_lt.mpr (key ⟨0, by omega⟩ K0 f0 e0 h0))
    · exact absurd hi (not_lt.mpr (key ⟨1, by omega⟩ K1 f1 e1 h1))
    · exact absurd hi (not_lt.mpr (key ⟨2, by omega⟩ K2 f2 e2 h2))
    · exact absurd hi (not_lt.mpr (key ⟨3, by omega⟩ K3 f3 e3 h3))
    · exact absurd hi (not_lt.mpr (key ⟨4, by omega⟩ K4 f4 e4 h4))
  · obtain ⟨hl, hh⟩ := hficmem
    have hfr : Int.fract (2 * ((w ⟨0, by omega⟩ : ℝ) * τ)) = ffic := by
      rw [efic, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
    exact absurd hfict (not_lt.mpr (by rw [circDist, hfr]; exact le_min hl (by linarith)))

/-- **Lemma 18 bound from a witness, six-runner** (the `core2` analog of
    `bhk_prop11_v4_bound_witness`). The `gap123_long_rho` gap `[t − ρ/w₂, t + 1/(3w₂)]`
    is window-free under `6 w₀ < w₂` (`{w₀s} ∈ [1/6, 7/18] ⊆ [1/6, 5/12)`), so
    `gap_covered2` applies and `bhk_lemma_4` yields `(1 + 3ρ)·w₃ < 2·w₂`. -/
lemma bhk_prop11_v4_bound_witness2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ6 : ρ ≤ 1 / 6)
    (t : ℝ) (h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2)
    (h1lo : 1 / 6 + ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
      ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t))
    (h1hi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
      ≤ 1 / 3 - ρ * (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)) : Found6 w ∨
      ((1 + 3 * ρ) * (w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ)) := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  have hw0R : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2R : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3R : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hsmall6R : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall6
  have hgap := bhk_prop11_gap123_long_rho w hpos hsum hsmall ρ hρ0 hρ6 t h3 h1lo h1hi
  have h0safe : ∀ s ∈ Set.Icc (t - ρ / (w ⟨2, by omega⟩ : ℝ))
        (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))),
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    obtain ⟨hsl, hsu⟩ := hs
    have hd_lo : -(ρ / (w ⟨2, by omega⟩ : ℝ)) ≤ s - t := by linarith
    have hd_hi : s - t ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by linarith
    have hub : (w ⟨0, by omega⟩ : ℝ) * (s - t)
        ≤ (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hd_hi hw0R.le; rwa [mul_one_div] at h
    have hub2 : (w ⟨0, by omega⟩ : ℝ) / (3 * (w ⟨2, by omega⟩ : ℝ)) < 1 / 18 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hlb : -(ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ))
        ≤ (w ⟨0, by omega⟩ : ℝ) * (s - t) := by
      have h := mul_le_mul_of_nonneg_left hd_lo hw0R.le
      rwa [show (w ⟨0, by omega⟩ : ℝ) * -(ρ / (w ⟨2, by omega⟩ : ℝ))
            = -(ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)) from by ring] at h
    have hsl1 : (0 : ℝ) ≤ ρ * (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ) := by positivity
    have hfs : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) + (w ⟨0, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨0, by omega⟩ : ℝ) * s
            = (w ⟨0, by omega⟩ : ℝ) * t + (w ⟨0, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by linarith [h1lo, hlb]) (by linarith [h1hi, hub, hub2, hsl1])]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith [h1hi, hub, hub2, hsl1]
  obtain hF | hcov := bhk_prop11_gap_covered2 w hgap h0safe
  · exact Or.inl hF
  right
  have hab : t - ρ / (w ⟨2, by omega⟩ : ℝ) ≤ t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
    have h1 : (0 : ℝ) < ρ / (w ⟨2, by omega⟩ : ℝ) := by positivity
    have h2 : (0 : ℝ) < 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by positivity
    linarith
  have hlen := bhk_lemma_4 w hmono hpos _ _ hab hcov
  have key : 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) + ρ / (w ⟨2, by omega⟩ : ℝ)
      < 2 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by linarith [hlen]
  have hcomb : 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) + ρ / (w ⟨2, by omega⟩ : ℝ)
      = (1 + 3 * ρ) / (3 * (w ⟨2, by omega⟩ : ℝ)) := by field_simp
  rw [hcomb, div_lt_div_iff₀ (by positivity) (by positivity)] at key
  nlinarith [key]

/-- **Lemma-18 exclusion kill, six-runner** (`exc_v4kill` with `gap_covered2`). A
    maximizing half-integer witness `m` with slack `ρ` forces `v₄ < 2/(1 + 3ρ)`; if
    `2q ≤ (1 + 3ρ)r` that is a contradiction. Excludes the large-`v₄` triples in
    `core2_q_lt_18`. -/
lemma bhk_prop11_exc_v4kill2 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (g p q r m : ℕ) (ρ : ℝ) (hg : 0 < g) (hq : 0 < q)
    (c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * p) (c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * q)
    (c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * r) (hρ0 : 0 < ρ) (hρ6 : ρ ≤ 1 / 6)
    (h1lo : 1 / 6 + ρ * (p : ℝ) / q ≤ (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ))
    (h1hi : (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ)
        ≤ 1 / 3 - ρ * ((q : ℝ) - p) / q)
    (hrb : 2 * (q : ℝ) ≤ (1 + 3 * ρ) * r) : Found6 w := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
  have hw0w2 : (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ) = (p : ℝ) / q := by
    rw [c0, c2]; rw [mul_div_mul_left _ _ hgR.ne']
  have hw1w2 : (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ) = ((q : ℝ) - p) / q := by
    have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * ((q : ℝ) - p) := by
      have hsumR : (w ⟨0, by omega⟩ : ℝ) + (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) := by
        exact_mod_cast hsum
      rw [show (w ⟨1, by omega⟩ : ℝ) = (w ⟨2, by omega⟩ : ℝ) - (w ⟨0, by omega⟩ : ℝ) from by
        linarith, c0, c2]; ring
    rw [c1, c2, mul_div_mul_left _ _ hgR.ne']
  set t : ℝ := ((m : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
  have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (m : ℝ) + 1 / 2 := by rw [htdef]; field_simp
  have h3 : Int.fract ((w ⟨2, by omega⟩ : ℝ) * t) = 1 / 2 := by
    rw [e2, show (m : ℝ) + 1 / 2 = ((m : ℤ) : ℝ) + 1 / 2 from by push_cast; ring,
        Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
  have e0t : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((m : ℝ) + 1 / 2) := by
    rw [htdef, c0, c2]; field_simp
  have hCp : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
      = (((2 * (p * m % q) + p) % (2 * q) : ℕ) : ℝ) / ((2 * q : ℕ) : ℝ) := by
    rw [e0t, bhk_prop11_Cpoint_eval p q m hq]
  have hwlo : 1 / 6 + ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
      ≤ Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) := by
    rw [hCp, show ρ * (w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
          = ρ * ((w ⟨0, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)) from by ring, hw0w2,
        show ρ * ((p : ℝ) / q) = ρ * (p : ℝ) / q from by ring]
    exact h1lo
  have hwhi : Int.fract ((w ⟨0, by omega⟩ : ℝ) * t)
      ≤ 1 / 3 - ρ * (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ) := by
    rw [hCp, show ρ * (w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)
          = ρ * ((w ⟨1, by omega⟩ : ℝ) / (w ⟨2, by omega⟩ : ℝ)) from by ring, hw1w2,
        show ρ * (((q : ℝ) - p) / q) = ρ * ((q : ℝ) - p) / q from by ring]
    exact h1hi
  obtain hF | hb := bhk_prop11_v4_bound_witness2 w hmono hpos hsum hsmall6 ρ hρ0 hρ6 t h3 hwlo hwhi
  · exact hF
  rw [c2, c3] at hb
  nlinarith [hb, hrb, hgR, mul_pos hgR hqR]

/-- **Corollary 16 (`v₄ < 2`), six-runner/unconditional** (the `core2` analog of
    `bhk_prop11_v4_lt_2v3_uncond`). Under `6 w₀ < w₂` and the six-runner cover, the
    witness-time `0123`-gap is covered only by runners 4, 5 (`gap_covered2`,
    window-free from `6 w₀ < w₂`), and `bhk_lemma_4` yields `w₃ < 2 w₂`. The `q ≥ 5`
    side condition is free from `6 w₀ < w₂` (`q > 6 p ≥ 6`). -/
theorem bhk_prop11_v4_lt_2v3_uncond_w (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    : Found6 w ∨
      ((w ⟨3, by omega⟩ : ℝ) < 2 * (w ⟨2, by omega⟩ : ℝ)) := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  have hq5 : 5 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) := by
    set g := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
    have hd0 : g ∣ w ⟨0, by omega⟩ := Nat.gcd_dvd_left _ _
    have hd2 : g ∣ w ⟨2, by omega⟩ := Nat.gcd_dvd_right _ _
    have e0 : g * (w ⟨0, by omega⟩ / g) = w ⟨0, by omega⟩ := Nat.mul_div_cancel' hd0
    have e2 : g * (w ⟨2, by omega⟩ / g) = w ⟨2, by omega⟩ := Nat.mul_div_cancel' hd2
    have hp0 : 0 < w ⟨0, by omega⟩ / g := Nat.div_pos (Nat.le_of_dvd (hpos _) hd0) hg
    have h6 : 6 * (w ⟨0, by omega⟩ / g) < w ⟨2, by omega⟩ / g := by
      have hmul : g * (6 * (w ⟨0, by omega⟩ / g)) < g * (w ⟨2, by omega⟩ / g) := by
        rw [show g * (6 * (w ⟨0, by omega⟩ / g)) = 6 * (g * (w ⟨0, by omega⟩ / g)) from by ring,
          e0, e2]; exact hsmall6
      exact lt_of_mul_lt_mul_left hmul (Nat.zero_le g)
    omega
  obtain ⟨t, h3, h1lo, h1hi⟩ := bhk_prop11_witness_time w hpos hsmall hq5
  have hgap := bhk_prop11_gap123 w hpos hsum hsmall t h3 h1lo h1hi
  have hw0pos : (0 : ℝ) < (w ⟨0, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw2pos : (0 : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have hw3pos : (0 : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by exact_mod_cast hpos _
  have h4w0 : 4 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by
    have : 6 * (w ⟨0, by omega⟩ : ℝ) < (w ⟨2, by omega⟩ : ℝ) := by exact_mod_cast hsmall6
    linarith
  have h0safe : ∀ s ∈ Set.Icc t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))),
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * s) ∉ Set.Ioo (5 / 12 : ℝ) (7 / 12) := by
    intro s hs
    have hd0 : 0 ≤ s - t := by linarith [hs.1]
    have hsu : s - t ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by linarith [hs.2]
    have hb : (w ⟨0, by omega⟩ : ℝ) * (s - t) < 1 / 12 := by
      have h1 : (w ⟨0, by omega⟩ : ℝ) * (s - t)
          ≤ (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) :=
        mul_le_mul_of_nonneg_left hsu hw0pos.le
      have h2 : (w ⟨0, by omega⟩ : ℝ) * (1 / (3 * (w ⟨2, by omega⟩ : ℝ))) < 1 / 12 := by
        rw [mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [h4w0]
      linarith
    have hfs : Int.fract ((w ⟨0, by omega⟩ : ℝ) * s)
        = Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) + (w ⟨0, by omega⟩ : ℝ) * (s - t) := by
      rw [show (w ⟨0, by omega⟩ : ℝ) * s
            = (w ⟨0, by omega⟩ : ℝ) * t + (w ⟨0, by omega⟩ : ℝ) * (s - t) from by ring,
        bhk_prop11_fract_add (by nlinarith [mul_nonneg hw0pos.le hd0]) (by linarith)]
    simp only [Set.mem_Ioo, not_and_or, not_lt]
    left; rw [hfs]; linarith
  obtain hF | hcov := bhk_prop11_gap_covered2 w hgap h0safe
  · exact Or.inl hF
  right
  have hab : t ≤ t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by
    have : (0 : ℝ) ≤ 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) := by positivity
    linarith
  have hlen := bhk_lemma_4 w hmono hpos t (t + 1 / (3 * (w ⟨2, by omega⟩ : ℝ))) hab hcov
  have hkey : 1 / (3 * (w ⟨2, by omega⟩ : ℝ)) < 2 / (3 * (w ⟨3, by omega⟩ : ℝ)) := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hkey
  linarith

set_option maxHeartbeats 1600000 in
/-- **core2 non-diagonal `(1,9,11)`** (explicit; the lone triple that fails the
    `(43)`-cut windowed pentagon `exc_Pkill2`). A fictional-safe `0123`-gap
    `[19/(66g), 17/(54g)]` bounds `s ≤ 12`; with `s > r = 11` only `s = 12` survives,
    lonely at `τ₁ = 1/(5g)` (positions `1/5,3/5,4/5,1/5,2/5`; fictional `2/5`). -/
lemma bhk_prop11_exc_special_1_9_11 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 11 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 9)
    (hw3 : w ⟨3, by omega⟩ = g * 11) (hw4 : w ⟨4, by omega⟩ = g * s) : Found6 w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 8 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 8 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 9 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 11 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (19 : ℝ) / (66 * (g : ℝ)) with ha
  set b : ℝ := (17 : ℝ) / (54 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (17 : ℝ) / (54 * g) - 19 / (66 * g) = 8 / (297 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound2 w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (19 / 66) (17 / 54)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 2 (10 / 33) (14 / 27)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 2 (13 / 22) (5 / 6)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 3 (1 / 6) (25 / 54)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (fun τ hτ => by
      have h := bhk_away_band_v (2 * (w ⟨0, by omega⟩ : ℝ)) a b (by positivity) hab 0 (19 / 33)
        (17 / 27) (by rw [c0, ha]; push_cast; field_simp <;> ring)
        (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num) τ hτ
      rwa [mul_assoc] at h)
  · exact hF
  have hsb : s ≤ 12 := by
    by_contra hcon
    have hsT : (13 : ℝ) ≤ s := by exact_mod_cast (by omega : 13 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 8 / (297 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (8 : ℝ) / (297 * g) - 1 / (3 * (g * s)) = (8 * s - 99) / (297 * g * s) := by
      field_simp <;> ring
    have hd : (0 : ℝ) < 8 / (297 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hsT]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely6 w (1 / (5 * (g : ℝ))) (1 / 5) (3 / 5) (4 / 5) (1 / 5) (2 / 5)
      0 1 1 2 2 (by rw [c0]; push_cast; field_simp <;> ring)
      (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring)
      (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (2 / 5) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **core2 diagonal `(1,7,8)`** (explicit, six-runner). -/
lemma bhk_prop11_exc_diag2_1_7 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 8 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 7)
    (hw3 : w ⟨3, by omega⟩ = g * 8) (hw4 : w ⟨4, by omega⟩ = g * s) : Found6 w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 6 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 6 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 7 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 8 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (7 : ℝ) / (36 * (g : ℝ)) with ha
  set b : ℝ := (11 : ℝ) / (48 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (11 : ℝ) / (48 * g) - 7 / (36 * g) = 5 / (144 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound2 w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (7 / 36) (11 / 48)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 1 (1 / 6) (3 / 8)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 1 (13 / 36) (29 / 48)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 1 (5 / 9) (5 / 6)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (fun τ hτ => by
      have h := bhk_away_band_v (2 * (w ⟨0, by omega⟩ : ℝ)) a b (by positivity) hab 0 (7 / 18) (11 / 24)
        (by rw [c0, ha]; push_cast; field_simp <;> ring)
        (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num) τ hτ
      rwa [mul_assoc] at h)
  · exact hF
  have hsb : s ≤ 9 := by
    by_contra hcon
    have hsT : (10 : ℝ) ≤ s := by exact_mod_cast (by omega : 10 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 5 / (144 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (5 : ℝ) / (144 * g) - 1 / (3 * (g * s)) = (15 * s - 144) / (432 * g * s) := by field_simp <;> ring
    have hd : (0 : ℝ) < 5 / (144 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hsT]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely6 w (1 / (5 * (g : ℝ))) (1 / 5) (1 / 5) (2 / 5) (3 / 5) (4 / 5) 0 1 1 1 1
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (2 / 5) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **core2 diagonal `(1,9,10)`** (explicit, six-runner). -/
lemma bhk_prop11_exc_diag2_1_9 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 10 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 9)
    (hw3 : w ⟨3, by omega⟩ = g * 10) (hw4 : w ⟨4, by omega⟩ = g * s) : Found6 w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 8 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 8 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 9 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 10 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (1 : ℝ) / (6 * (g : ℝ)) with ha
  set b : ℝ := (11 : ℝ) / (60 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (11 : ℝ) / (60 * g) - 1 / (6 * g) = 1 / (60 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound2 w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (1 / 6) (11 / 60)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 1 (1 / 3) (7 / 15)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 1 (1 / 2) (13 / 20)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 1 (2 / 3) (5 / 6)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (fun τ hτ => by
      have h := bhk_away_band_v (2 * (w ⟨0, by omega⟩ : ℝ)) a b (by positivity) hab 0 (1 / 3) (11 / 30)
        (by rw [c0, ha]; push_cast; field_simp <;> ring)
        (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num) τ hτ
      rwa [mul_assoc] at h)
  · exact hF
  have hsb : s ≤ 20 := by
    by_contra hcon
    have hsT : (21 : ℝ) ≤ s := by exact_mod_cast (by omega : 21 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 1 / (60 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (1 : ℝ) / (60 * g) - 1 / (3 * (g * s)) = (s - 20) / (60 * g * s) := by field_simp <;> ring
    have hd : (0 : ℝ) < 1 / (60 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hsT]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (5 / 6) 0 1 1 1 1
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (2 / (11 * (g : ℝ))) (2 / 11) (5 / 11) (7 / 11) (9 / 11) (2 / 11) 0 1 1 1 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (4 / 11) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (1 / 6) 0 1 1 1 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (1 / 3) 0 1 1 1 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (1 / 2) 0 1 1 1 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (2 / 3) 0 1 1 1 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (5 / 6) 0 1 1 1 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (2 / (11 * (g : ℝ))) (2 / 11) (5 / 11) (7 / 11) (9 / 11) (3 / 11) 0 1 1 1 3
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (4 / 11) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (1 / 6) 0 1 1 1 3
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 3) (1 / 2) (2 / 3) (1 / 3) 0 1 1 1 3
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **core2 diagonal `(1,10,11)`** (explicit, six-runner). -/
lemma bhk_prop11_exc_diag2_1_10 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 11 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 10)
    (hw3 : w ⟨3, by omega⟩ = g * 11) (hw4 : w ⟨4, by omega⟩ = g * s) : Found6 w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 9 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 9 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 10 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 11 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (13 : ℝ) / (54 * (g : ℝ)) with ha
  set b : ℝ := (17 : ℝ) / (66 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (17 : ℝ) / (66 * g) - 13 / (54 * g) = 5 / (297 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound2 w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (13 / 54) (17 / 66)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 2 (1 / 6) (7 / 22)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 2 (11 / 27) (19 / 33)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 2 (35 / 54) (5 / 6)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (fun τ hτ => by
      have h := bhk_away_band_v (2 * (w ⟨0, by omega⟩ : ℝ)) a b (by positivity) hab 0 (13 / 27) (17 / 33)
        (by rw [c0, ha]; push_cast; field_simp <;> ring)
        (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num) τ hτ
      rwa [mul_assoc] at h)
  · exact hF
  have hsb : s ≤ 19 := by
    by_contra hcon
    have hsT : (20 : ℝ) ≤ s := by exact_mod_cast (by omega : 20 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 5 / (297 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (5 : ℝ) / (297 * g) - 1 / (3 * (g * s)) = (15 * s - 297) / (891 * g * s) := by field_simp <;> ring
    have hd : (0 : ℝ) < 5 / (297 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hsT]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely6 w (8 / (21 * (g : ℝ))) (8 / 21) (3 / 7) (17 / 21) (4 / 21) (4 / 7) 0 3 3 4 4
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (16 / 21) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 4) 0 2 2 2 3
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 2) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 2) 0 2 2 2 3
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 2) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (3 / 4) 0 2 2 2 3
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 2) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (6 * (g : ℝ))) (1 / 6) (1 / 2) (2 / 3) (5 / 6) (2 / 3) 0 1 1 1 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 3) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 4) 0 2 2 2 4
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 2) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (1 / 2) 0 2 2 2 4
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 2) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (1 / (4 * (g : ℝ))) (1 / 4) (1 / 4) (1 / 2) (3 / 4) (3 / 4) 0 2 2 2 4
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (1 / 2) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])

set_option maxHeartbeats 1600000 in
/-- **core2 diagonal `(1,12,13)`** (explicit, six-runner). -/
lemma bhk_prop11_exc_diag2_1_12 (w : Fin 5 → ℕ) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (g s : ℕ) (hg : 0 < g) (hs : 13 < s)
    (hw0 : w ⟨0, by omega⟩ = g) (hw2 : w ⟨2, by omega⟩ = g * 12)
    (hw3 : w ⟨3, by omega⟩ = g * 13) (hw4 : w ⟨4, by omega⟩ = g * s) : Found6 w := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hgne : (g : ℝ) ≠ 0 := hgR.ne'
  have hw1 : w ⟨1, by omega⟩ = g * 11 := by omega
  have c0 : (w ⟨0, by omega⟩ : ℝ) = g := by exact_mod_cast hw0
  have c1 : (w ⟨1, by omega⟩ : ℝ) = (g : ℝ) * 11 := by exact_mod_cast hw1
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * 12 := by exact_mod_cast hw2
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * 13 := by exact_mod_cast hw3
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * s := by exact_mod_cast hw4
  set a : ℝ := (13 : ℝ) / (66 * (g : ℝ)) with ha
  set b : ℝ := (17 : ℝ) / (78 * (g : ℝ)) with hb
  have hab : a ≤ b := by
    rw [ha, hb, ← sub_nonneg]
    have hid : (17 : ℝ) / (78 * g) - 13 / (66 * g) = 3 / (143 * g) := by field_simp <;> ring
    rw [hid]; positivity
  obtain hF | hbnd := bhk_diag_sbound2 w hpos a b hab
    (bhk_away_band w ⟨0, by omega⟩ a b hab 0 (13 / 66) (17 / 78)
      (by rw [c0, ha]; push_cast; field_simp <;> ring)
      (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨1, by omega⟩ a b hab 2 (1 / 6) (31 / 78)
      (by rw [c1, ha]; push_cast; field_simp <;> ring)
      (by rw [c1, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨2, by omega⟩ a b hab 2 (4 / 11) (8 / 13)
      (by rw [c2, ha]; push_cast; field_simp <;> ring)
      (by rw [c2, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (bhk_away_band w ⟨3, by omega⟩ a b hab 2 (37 / 66) (5 / 6)
      (by rw [c3, ha]; push_cast; field_simp <;> ring)
      (by rw [c3, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num))
    (fun τ hτ => by
      have h := bhk_away_band_v (2 * (w ⟨0, by omega⟩ : ℝ)) a b (by positivity) hab 0 (13 / 33) (17 / 39)
        (by rw [c0, ha]; push_cast; field_simp <;> ring)
        (by rw [c0, hb]; push_cast; field_simp <;> ring) (by norm_num) (by norm_num) τ hτ
      rwa [mul_assoc] at h)
  · exact hF
  have hsb : s ≤ 15 := by
    by_contra hcon
    have hsT : (16 : ℝ) ≤ s := by exact_mod_cast (by omega : 16 ≤ s)
    have hsR : (0 : ℝ) < s := by linarith
    have hsne : (s : ℝ) ≠ 0 := hsR.ne'
    rw [c4] at hbnd
    have hba : b - a = 3 / (143 * (g : ℝ)) := by rw [ha, hb]; field_simp <;> ring
    rw [hba] at hbnd
    have hid : (3 : ℝ) / (143 * g) - 1 / (3 * (g * s)) = (9 * s - 143) / (429 * g * s) := by field_simp <;> ring
    have hd : (0 : ℝ) < 3 / (143 * g) - 1 / (3 * (g * s)) := by
      rw [hid]; exact div_pos (by nlinarith [hsT]) (by positivity)
    linarith
  interval_cases s
  · exact bhk_lonely6 w (1 / (5 * (g : ℝ))) (1 / 5) (1 / 5) (2 / 5) (3 / 5) (4 / 5) 0 2 2 2 2
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (2 / 5) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])
  · exact bhk_lonely6 w (3 / (14 * (g : ℝ))) (3 / 14) (5 / 14) (4 / 7) (11 / 14) (3 / 14) 0 2 2 2 3
      (by rw [c0]; push_cast; field_simp <;> ring) (by rw [c1]; push_cast; field_simp <;> ring) (by rw [c2]; push_cast; field_simp <;> ring) (by rw [c3]; push_cast; field_simp <;> ring) (by rw [c4]; push_cast; field_simp <;> ring)
      (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])
      (3 / 7) 0 (by rw [c0]; push_cast; field_simp <;> ring) (by norm_num [Set.mem_Icc])



/-- **core2, `q < 18` dispatch.** The complementary finite case for part 2; the
    six-runner analog of `bhk_prop11_core_q_lt_18`. Extraction (`lemma17_w`,
    `q ∈ [7,17]` from `6 p < q < 18`, `q < r < 2q` via `v4_lt_2v3_uncond_w`,
    `h_nogood` via `no_good_time2`) complete; residual `sorry` is the finite
    `(p, q, r)` dispatch (`p ∈ {1,2}`). The non-diagonal cases reuse the abstract
    `exc_Rkill`/`exc_v4kill` (same `h_nogood` rectangle) and `exc_Pkill2`; the
    diagonals `r = p + q` reuse `part6_w`. -/
theorem bhk_prop11_core2_q_lt_18 (w : Fin 5 → ℕ) (hmono : StrictMono w) (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    (hq : w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) < 18) : Found6 w := by
  have hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩ := by omega
  set g : ℕ := Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩) with hgdef
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left _ (hpos _)
  have hgw0 : g ∣ w ⟨0, by omega⟩ := Nat.gcd_dvd_left _ _
  have hgw2 : g ∣ w ⟨2, by omega⟩ := Nat.gcd_dvd_right _ _
  set p : ℕ := w ⟨0, by omega⟩ / g with hpdef
  set q : ℕ := w ⟨2, by omega⟩ / g with hqdef
  have hgp : w ⟨0, by omega⟩ = g * p := (Nat.mul_div_cancel' hgw0).symm
  have hgq : w ⟨2, by omega⟩ = g * q := (Nat.mul_div_cancel' hgw2).symm
  have hcop : Nat.Coprime p q := Nat.coprime_div_gcd_div_gcd hg_pos
  have hp_pos : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.mul_zero] at hgp; have h0' := hpos ⟨0, by omega⟩; omega
    · exact h
  have h6p : 6 * p < q := by
    have h : g * (6 * p) < g * q := by
      rw [show g * (6 * p) = 6 * (g * p) from by ring, ← hgp, ← hgq]; exact hsmall6
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  have h3p : 3 * p < q := by omega
  have hq7 : 7 ≤ q := by omega
  have hq17 : q < 18 := hq
  obtain hF | ⟨hgw3, hgw4⟩ :=
    bhk_prop11_lemma17_w w hmono hpos hsum hsmall6 (by rw [← hgdef, ← hqdef]; omega)
  · exact hF
  set r : ℕ := w ⟨3, by omega⟩ / g with hrdef
  set s : ℕ := w ⟨4, by omega⟩ / g with hsdef
  have hgr : w ⟨3, by omega⟩ = g * r := (Nat.mul_div_cancel' hgw3).symm
  have hgs : w ⟨4, by omega⟩ = g * s := (Nat.mul_div_cancel' hgw4).symm
  have c0 : (w ⟨0, by omega⟩ : ℝ) = (g : ℝ) * (p : ℝ) := by exact_mod_cast hgp
  have c2 : (w ⟨2, by omega⟩ : ℝ) = (g : ℝ) * (q : ℝ) := by exact_mod_cast hgq
  have c3 : (w ⟨3, by omega⟩ : ℝ) = (g : ℝ) * (r : ℝ) := by exact_mod_cast hgr
  have c4 : (w ⟨4, by omega⟩ : ℝ) = (g : ℝ) * (s : ℝ) := by exact_mod_cast hgs
  have hrq : q < r := by
    have hw23 : w ⟨2, by omega⟩ < w ⟨3, by omega⟩ :=
      hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega))
    have h : g * q < g * r := by rw [← hgq, ← hgr]; exact hw23
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  obtain hF | hreal := bhk_prop11_v4_lt_2v3_uncond_w w hmono hpos hsum hsmall6
  · exact hF
  have hr2q : r < 2 * q := by
    have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
    rw [c3, c2] at hreal
    have hcancel : (g : ℝ) * (r : ℝ) < (g : ℝ) * (2 * (q : ℝ)) := by nlinarith [hreal]
    have hR : (r : ℝ) < 2 * (q : ℝ) := lt_of_mul_lt_mul_left hcancel hgR.le
    exact_mod_cast hR
  have hrs : r < s := by
    have hw34 : w ⟨3, by omega⟩ < w ⟨4, by omega⟩ :=
      hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
    have h : g * r < g * s := by rw [← hgr, ← hgs]; exact hw34
    exact lt_of_mul_lt_mul_left h (Nat.zero_le g)
  obtain hF | h_nogood : Found6 w ∨ (∀ l : ℤ,
      ¬ (Int.fract ((r : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 2) ∧
         Int.fract ((p : ℝ) / q * ((l : ℝ) + 1 / 2)) ∈ Set.Icc (1 / 6 : ℝ) (1 / 3))) := by
    rw [or_iff_not_imp_right]
    intro hQ
    obtain ⟨l, hl⟩ := not_forall_not.mp hQ
    obtain ⟨hrmem, hpmem⟩ := hl
    set t : ℝ := ((l : ℝ) + 1 / 2) / (w ⟨2, by omega⟩ : ℝ) with htdef
    have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
    have e2 : (w ⟨2, by omega⟩ : ℝ) * t = (l : ℝ) + 1 / 2 := by rw [htdef]; field_simp
    have e0 : (w ⟨0, by omega⟩ : ℝ) * t = (p : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c0, c2]; field_simp
    have e3 : (w ⟨3, by omega⟩ : ℝ) * t = (r : ℝ) / q * ((l : ℝ) + 1 / 2) := by
      rw [htdef, c3, c2]; field_simp
    refine bhk_prop11_no_good_time2 w hmono hpos hsum hsmall6 t ?_ ?_ ?_ ?_ ?_
    · rw [e2, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    · rw [e0]; exact hpmem.1
    · rw [e0]; exact hpmem.2
    · rw [e3]; exact hrmem.1
    · rw [e3]; exact hrmem.2
  · exact hF
  clear_value g p q r s
  clear hgdef hpdef hqdef hrdef hsdef hgw0 hgw2 hgw3 hgw4
  by_cases hdiag : r = p + q
  · -- DIAGONAL
    have hdiagw : w ⟨3, by omega⟩ = w ⟨0, by omega⟩ + w ⟨2, by omega⟩ := by
      rw [hgr, hgp, hgq, hdiag]; ring
    have hw34 : (w ⟨3, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
      exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (3 : ℕ) < 4 by omega))
    have hw24 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨4, by omega⟩ : ℝ) := by
      have h23 : (w ⟨2, by omega⟩ : ℝ) < (w ⟨3, by omega⟩ : ℝ) := by
        exact_mod_cast hmono (Fin.mk_lt_mk.mpr (show (2 : ℕ) < 3 by omega))
      linarith
    have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hg_pos.ne'
    interval_cases q
    · -- q = 7
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag2_1_7 w hpos hsum g s hg_pos (by omega) (by omega) hgq hgr hgs  -- explicit
        · omega  -- r=9 non-diag
        · omega  -- r=10 non-diag
        · omega  -- r=11 non-diag
        · omega  -- r=12 non-diag
        · omega  -- r=13 non-diag
    · -- q = 8
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 8 9 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- diag P
        · omega  -- r=10 non-diag
        · omega  -- r=11 non-diag
        · omega  -- r=12 non-diag
        · omega  -- r=13 non-diag
        · omega  -- r=14 non-diag
        · omega  -- r=15 non-diag
    · -- q = 9
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag2_1_9 w hpos hsum g s hg_pos (by omega) (by omega) hgq hgr hgs  -- explicit
        · omega  -- r=11 non-diag
        · omega  -- r=12 non-diag
        · omega  -- r=13 non-diag
        · omega  -- r=14 non-diag
        · omega  -- r=15 non-diag
        · omega  -- r=16 non-diag
        · omega  -- r=17 non-diag
    · -- q = 10
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag2_1_10 w hpos hsum g s hg_pos (by omega) (by omega) hgq hgr hgs  -- explicit
        · omega  -- r=12 non-diag
        · omega  -- r=13 non-diag
        · omega  -- r=14 non-diag
        · omega  -- r=15 non-diag
        · omega  -- r=16 non-diag
        · omega  -- r=17 non-diag
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
    · -- q = 11
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · refine bhk_prop11_part6_p1_wit_w w hpos hsum hdiagw hw24 g 11 s hg_pos (by norm_num) (by omega) hgq hgs ((4 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 4 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((4 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (4 : ℝ) / 11 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((4 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (4 : ℝ) / 11 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=13 non-diag
        · omega  -- r=14 non-diag
        · omega  -- r=15 non-diag
        · omega  -- r=16 non-diag
        · omega  -- r=17 non-diag
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
    · -- q = 12
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · exact bhk_prop11_exc_diag2_1_12 w hpos hsum g s hg_pos (by omega) (by omega) hgq hgr hgs  -- explicit
        · omega  -- r=14 non-diag
        · omega  -- r=15 non-diag
        · omega  -- r=16 non-diag
        · omega  -- r=17 non-diag
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
    · -- q = 13
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · refine bhk_prop11_part6_p1_wit_w w hpos hsum hdiagw hw24 g 13 s hg_pos (by norm_num) (by omega) hgq hgs ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 5 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (5 : ℝ) / 13 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (5 : ℝ) / 13 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=15 non-diag
        · omega  -- r=16 non-diag
        · omega  -- r=17 non-diag
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
      · -- p = 2
        interval_cases r
        · omega  -- r=14 non-diag
        · exact bhk_prop11_part6_ge12_w w hpos hsum hsmall hsmall6 hdiagw hw34 g 2 13 15 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- part6_ge12_w
        · omega  -- r=16 non-diag
        · omega  -- r=17 non-diag
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
    · -- q = 14
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · refine bhk_prop11_part6_p1_wit_w w hpos hsum hdiagw hw24 g 14 s hg_pos (by norm_num) (by omega) hgq hgs ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 5 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (5 : ℝ) / 14 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((5 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (5 : ℝ) / 14 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=16 non-diag
        · omega  -- r=17 non-diag
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
        · omega  -- r=26 non-diag
        · omega  -- r=27 non-diag
      · exact absurd hcop (by decide)  -- p=2 gcd>1
    · -- q = 15
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · refine bhk_prop11_part6_p1_wit_w w hpos hsum hdiagw hw24 g 15 s hg_pos (by norm_num) (by omega) hgq hgs ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 6 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 15 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 15 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=17 non-diag
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
        · omega  -- r=26 non-diag
        · omega  -- r=27 non-diag
        · omega  -- r=28 non-diag
        · omega  -- r=29 non-diag
      · -- p = 2
        interval_cases r
        · omega  -- r=16 non-diag
        · exact bhk_prop11_part6_ge12_w w hpos hsum hsmall hsmall6 hdiagw hw34 g 2 15 17 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- part6_ge12_w
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
        · omega  -- r=26 non-diag
        · omega  -- r=27 non-diag
        · omega  -- r=28 non-diag
        · omega  -- r=29 non-diag
    · -- q = 16
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · refine bhk_prop11_part6_p1_wit_w w hpos hsum hdiagw hw24 g 16 s hg_pos (by norm_num) (by omega) hgq hgs ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 6 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 16 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 16 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=18 non-diag
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
        · omega  -- r=26 non-diag
        · omega  -- r=27 non-diag
        · omega  -- r=28 non-diag
        · omega  -- r=29 non-diag
        · omega  -- r=30 non-diag
        · omega  -- r=31 non-diag
      · exact absurd hcop (by decide)  -- p=2 gcd>1
    · -- q = 17
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · refine bhk_prop11_part6_p1_wit_w w hpos hsum hdiagw hw24 g 17 s hg_pos (by norm_num) (by omega) hgq hgs ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) 6 ?_ ?_ ?_
          · have hw2ne : (w ⟨2, by omega⟩ : ℝ) ≠ 0 := by rw [c2]; positivity
            field_simp; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 17 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
          · have hwt : (w ⟨0, by omega⟩ : ℝ) * ((6 : ℝ) / (w ⟨2, by omega⟩ : ℝ)) = (6 : ℝ) / 17 := by
              rw [c0, c2]; field_simp; ring
            rw [hwt]; norm_num
        · omega  -- r=19 non-diag
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
        · omega  -- r=26 non-diag
        · omega  -- r=27 non-diag
        · omega  -- r=28 non-diag
        · omega  -- r=29 non-diag
        · omega  -- r=30 non-diag
        · omega  -- r=31 non-diag
        · omega  -- r=32 non-diag
        · omega  -- r=33 non-diag
      · -- p = 2
        interval_cases r
        · omega  -- r=18 non-diag
        · exact bhk_prop11_part6_ge12_w w hpos hsum hsmall hsmall6 hdiagw hw34 g 2 17 19 s hg_pos (by norm_num) (by norm_num) hgp hgq hgr hgs hcop  -- part6_ge12_w
        · omega  -- r=20 non-diag
        · omega  -- r=21 non-diag
        · omega  -- r=22 non-diag
        · omega  -- r=23 non-diag
        · omega  -- r=24 non-diag
        · omega  -- r=25 non-diag
        · omega  -- r=26 non-diag
        · omega  -- r=27 non-diag
        · omega  -- r=28 non-diag
        · omega  -- r=29 non-diag
        · omega  -- r=30 non-diag
        · omega  -- r=31 non-diag
        · omega  -- r=32 non-diag
        · omega  -- r=33 non-diag
  · -- NON-DIAGONAL
    interval_cases q
    · -- q = 7
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=8=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 7 9 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 7 10 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 7 11 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 7 12 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 7 13 1 (5/36 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
    · -- q = 8
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=9=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 8 10 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 11 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 12 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 13 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 8 14 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 8 15 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
    · -- q = 9
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=10=p+q diagonal
        · exact bhk_prop11_exc_special_1_9_11 w hpos hsum g s hg_pos (by omega) (by omega) hgq hgr hgs  -- special (43-cut fallthrough)
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 12 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 13 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 14 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 15 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 9 16 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 9 17 2 (1/16 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
    · -- q = 10
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=11=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 10 12 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 13 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 14 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 10 15 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 10 16 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 17 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 10 18 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 10 19 2 (5/54 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
    · -- q = 11
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=12=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 11 13 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 14 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 15 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 11 16 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 17 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 11 18 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 11 20 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 11 21 2 (7/60 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
    · -- q = 12
      have hpb : p ≤ 1 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=13=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 12 14 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 15 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 16 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 12 17 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 18 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 12 19 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 20 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 21 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 12 22 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 12 23 2 (3/22 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
    · -- q = 13
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=14=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 13 15 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 16 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 17 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 18 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 13 19 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 20 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 13 21 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 22 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 23 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 13 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 13 25 2 (11/72 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 13 14 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · omega  -- r=15=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 16 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 13 17 s 8 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 13 18 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 19 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 20 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 21 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 22 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 13 23 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 2 13 24 1 (4/33 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
        · exact False.elim <| bhk_prop11_exc_Rkill 2 13 25 8 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
    · -- q = 14
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=15=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 14 16 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 17 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 18 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 20 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 21 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 22 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 24 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 25 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 14 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 14 27 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
      · exact absurd hcop (by decide)  -- p=2 gcd>1
    · -- q = 15
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=16=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 15 17 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 18 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 20 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 21 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 15 22 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 23 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 24 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 25 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 26 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 27 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 15 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 15 29 3 (3/28 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 15 16 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · omega  -- r=17=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 18 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 19 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 20 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 21 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 22 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 23 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 24 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 25 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 26 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 27 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 2 15 28 1 (2/13 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
        · exact False.elim <| bhk_prop11_exc_Rkill 2 15 29 9 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
    · -- q = 16
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=17=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 16 18 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 19 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 20 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 16 21 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 22 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 23 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 24 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 25 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 26 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 16 27 s 4 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 16 28 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 29 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 16 30 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 16 31 3 (11/90 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
      · exact absurd hcop (by decide)  -- p=2 gcd>1
    · -- q = 17
      have hpb : p ≤ 2 := by omega
      interval_cases p
      · -- p = 1
        interval_cases r
        · omega  -- r=18=p+q diagonal
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 17 19 s 5 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 20 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 21 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 17 22 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 23 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 24 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 17 25 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 26 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 1 17 27 s 3 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 28 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 29 5 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 30 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 31 3 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 1 17 32 4 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 1 17 33 3 (13/96 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
      · -- p = 2
        interval_cases r
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 17 18 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · omega  -- r=19=p+q diagonal
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 20 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 17 21 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 22 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 23 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 17 24 s 1 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 25 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 26 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 27 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 28 1 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 29 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 30 2 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R
        · exact bhk_prop11_exc_Pkill2 w hmono hpos hsum hsmall6 g 2 17 31 s 2 hg_pos (by norm_num) (by norm_num) (by norm_num) hrq hrs c0 c2 c3 c4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- P
        · exact bhk_prop11_exc_v4kill2 w hmono hpos hsum hsmall6 g 2 17 32 10 (1/9 : ℝ) hg_pos (by norm_num) c0 c2 c3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)  -- v4
        · exact False.elim <| bhk_prop11_exc_Rkill 2 17 33 10 (by norm_num) h_nogood (by norm_num [Set.mem_Icc]) (by norm_num [Set.mem_Icc])  -- R


/-- **Proposition 11, part 2 — the 6-runner core** (BHK Parts 2–6 with the
    fictional runner 0 prepended). The genuinely-hard content of
    `bhk_prop11_core2`: under `6 w₀ < w₂`, the **six** runners
    `w₀, 2w₀, w₁, w₂, w₃, w₄` (the five real runners together with the fictional
    runner 0 of speed `2 w₀`) cannot cover every time within `1/6`. The covering
    hypothesis `hcov6` is the disjunction "some real runner is near the origin,
    *or* the fictional runner `2 w₀` is" — exactly `B₀ = ℝ⁺` in BHK's notation.

    This mirrors `bhk_prop11_core_q18`/`core_q_lt_18`, with the fictional runner
    refining 123-gaps to 0123-gaps. The covering enters the Part-2–6 pipeline at a
    single point — the runner-5 gap engine (`bhk_prop11_gap1234_b5span` /
    `bhk_prop11_long_gap_absurd`): on a 0123-gap (where additionally runner 1
    avoids `(5/12, 7/12)`, so the fictional runner is *also* safe) the windowed
    covering forces runner 5 to cover, bounding the gap length. Decomposition:
    `core2_v4_le_3_2` (Cor 16/Lemma 18, `2 r < 3 q`), `core2_exceptional`
    (Parts 2–4, the cone pair `(i, j)` via the rectangle no-good-time, which
    transfers verbatim from the windowed covering since the rectangle's
    `{w₀t} ∈ [1/6,1/3] < 5/12` keeps the gap below the window), and the pentagon
    `core2_pent_no_good` + Part-5/6 dispatch (where the fictional runner genuinely
    supplies the 0123-gap that the runner-end argument of `no_good_time_P` cannot).
    Splits on `q = w₂/gcd(w₀,w₂)`: `q ≥ 18` → `bhk_prop11_core2_q18` (extraction +
    `exc_open` reuse + the three pentagon residuals), `q < 18` →
    `bhk_prop11_core2_q_lt_18`. -/
theorem bhk_prop11_core2_cover6 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩)
    : Found6 w := by
  by_cases hq : 18 ≤ w ⟨2, by omega⟩ / Nat.gcd (w ⟨0, by omega⟩) (w ⟨2, by omega⟩)
  · exact bhk_prop11_core2_q18 w hmono hpos hsum hsmall6 hq
  · exact bhk_prop11_core2_q_lt_18 w hmono hpos hsum hsmall6 (not_le.mp hq)

/-- **Proposition 11, part 1, at a named instant** (BHK pp. 17–40). Integer speeds
    `w₀ < ⋯ < w₄` with `w₀ + w₁ = w₂` and `3 w₀ < w₂` have a time at which every runner is
    `≥ 1/6` from the origin. The instant is the one `bhk_prop11_core` names. -/
theorem bhk_prop11_part1 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall : 3 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩) :
    ∃ t : ℝ, ∀ i, circDist ((w i : ℝ) * t) ≥ (1 : ℝ) / 6 := by
  obtain ⟨t, ht⟩ := bhk_prop11_core w hmono hpos hsum hsmall
  exact ⟨t, ht⟩

/-- **Proposition 11, part 2, at a named instant.** Under `6 w₀ < w₂` the instant can be
    chosen with `{w₀ t} ∉ (5/12, 7/12)`: it is the instant `bhk_prop11_core2_cover6` names,
    at which the fictional runner `2 w₀` is also clear. -/
theorem bhk_prop11_part2 (w : Fin 5 → ℕ) (hmono : StrictMono w)
    (hpos : ∀ i, 0 < w i)
    (hsum : w ⟨0, by omega⟩ + w ⟨1, by omega⟩ = w ⟨2, by omega⟩)
    (hsmall6 : 6 * w ⟨0, by omega⟩ < w ⟨2, by omega⟩) :
    ∃ t : ℝ, (∀ i, circDist ((w i : ℝ) * t) ≥ (1 : ℝ) / 6) ∧
      Int.fract ((w ⟨0, by omega⟩ : ℝ) * t) ∉ Set.Ioo (5/12 : ℝ) (7/12) := by
  obtain ⟨t, ht, h0⟩ := bhk_prop11_core2_cover6 w hmono hpos hsum hsmall6
  exact ⟨t, ht, fun hwin => absurd (bhk_prop11_fict_window hwin) (not_lt.mpr h0)⟩

end LRC.OrderSixN.S7.Named
