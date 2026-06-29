import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Lemmas7_9

/-!
# n = 7 (Barajas–Serra) — Lemmas 10, 11, 12 (the `|A₁|` labeling lemmas)

Source: `sources_barajas_serra_2008.txt`, lines 509–512 (Lemma 10), 569–593
(Lemma 11), 667–681 (Lemma 12).

These are the *labeling* lemmas of §6: given the residue-1 class `A₁` (3, 4, or 5
level-0 elements all `≡ r mod 7`), they produce a numbering of `A₁` exposing the
valuation/leading-residue structure of the difference set `E = (A₁−A₁)\{0}`. That
structure is exactly what the compression Lemmas 9(i)/9(ii) consume:

- **(i)** the two differences-from-the-apex have *distinct* valuations → `lemma9_i`;
- **(ii.1)** equal valuations with ratio `2` → `lemma9_ii_j2`;
- **(ii.2)** equal valuations with ratio `3` → `lemma9_ii_j3`.

The leading-residue combinatorics (BS L583–593) is a finite `ZMod 7` fact: writing
`t = r(e₀₁)/r(e₁₂)`, the six relabelings realize the ratios
`{t+1, (t+1)⁻¹, −t, −t⁻¹, t/(t+1), (t+1)/t}`, and for every admissible `t` one of
them is `2` or `3`.
-/

open Finset

namespace IntLRC7BS

/-- **7-adic valuation extraction.** Every nonzero integer has a well-defined
`7`-adic valuation: a unique `h` with `7^h ∣ δ` but `7^(h+1) ∤ δ`. Proof via
`Nat.find` on the (inhabited) set of exponents whose successor power fails to
divide `δ`; the witness `δ.natAbs` works since `δ.natAbs < 7^(δ.natAbs+1)` while a
divisor of a nonzero integer is bounded by its absolute value. -/
theorem exists_val7 (δ : ℤ) (hδ : δ ≠ 0) :
    ∃ h : ℕ, (7 : ℤ) ^ h ∣ δ ∧ ¬ (7 : ℤ) ^ (h + 1) ∣ δ := by
  have hex : ∃ j : ℕ, ¬ (7 : ℤ) ^ (j + 1) ∣ δ := by
    refine ⟨δ.natAbs, fun hdvd => ?_⟩
    have hdvdN : (7 : ℕ) ^ (δ.natAbs + 1) ∣ δ.natAbs := by
      have := (Int.natAbs_dvd_natAbs).mpr hdvd
      simpa [Int.natAbs_pow] using this
    have hle : (7 : ℕ) ^ (δ.natAbs + 1) ≤ δ.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hδ) hdvdN
    have hgt : δ.natAbs < 7 ^ (δ.natAbs + 1) :=
      lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ _))
    omega
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0]; exact one_dvd δ
  · have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [not_not] at hprev
    rwa [show (Nat.find hex - 1) + 1 = Nat.find hex from by omega] at hprev

/-- **Ultrametric for `7`-adic valuations.** If `x` is at level exactly `a` and `y`
is at level `≥ b > a`, then `x + y` is at level exactly `a` (the smaller). The
leading `7^a`-coefficient of `x` survives because `y` contributes nothing below
level `b`. -/
theorem ultra_add {x y : ℤ} {a b : ℕ}
    (hxa : (7 : ℤ) ^ a ∣ x) (hxa' : ¬ (7 : ℤ) ^ (a + 1) ∣ x) (hyb : (7 : ℤ) ^ b ∣ y)
    (hab : a < b) :
    (7 : ℤ) ^ a ∣ (x + y) ∧ ¬ (7 : ℤ) ^ (a + 1) ∣ (x + y) := by
  refine ⟨dvd_add hxa (dvd_trans (pow_dvd_pow 7 (le_of_lt hab)) hyb), fun h => hxa' ?_⟩
  have hyb1 : (7 : ℤ) ^ (a + 1) ∣ y := dvd_trans (pow_dvd_pow 7 hab) hyb
  have hx : (7 : ℤ) ^ (a + 1) ∣ (x + y) - y := dvd_sub h hyb1
  simpa using hx

set_option maxHeartbeats 1000000 in
/-- **The leading-residue ratio fact (BS L583–593).** Three nonzero `ZMod 7`
residues `a, b, c` of the pairwise differences of a 3-set, tied by the additive
relation `a = b − c` (`(d₀−d₁) = (d₀−d₂) − (d₁−d₂)`), always admit a relabeling
whose apex-difference ratio is `2` or `3`. Exhaustive over `(ZMod 7)³`. The six
disjuncts are the six orderings `(d₁,d₂,d₃)`; the condition for each is
`r(d₂−d₃) = k·r(d₁−d₃)` with `k ∈ {2,3}`. -/
theorem ratio_two_three (a b c : ZMod 7) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hrel : a = b - c) :
    (c = 2 * b ∨ c = 3 * b) ∨ (b = 2 * c ∨ b = 3 * c) ∨ (-c = 2 * a ∨ -c = 3 * a) ∨
    (a = 2 * (-c) ∨ a = 3 * (-c)) ∨ (-b = 2 * (-a) ∨ -b = 3 * (-a)) ∨
    (-a = 2 * (-b) ∨ -a = 3 * (-b)) := by
  revert ha hb hc hrel; revert a b c; decide

/-- Leading residue of a difference written as `δ = 7^h · w`: `(δ / 7^h : ZMod 7) = w`. -/
theorem res_eq {δ : ℤ} {h : ℕ} {w : ℤ} (hw : δ = 7 ^ h * w) :
    (((δ / 7 ^ h : ℤ)) : ZMod 7) = (w : ZMod 7) := by
  rw [hw, Int.mul_ediv_cancel_left _ (by positivity : (7 : ℤ) ^ h ≠ 0)]

/-- If `δ = 7^h · w` but `7^(h+1) ∤ δ`, the leading residue `w` is a unit (`≠ 0`). -/
theorem unit_res {δ : ℤ} {h : ℕ} {w : ℤ} (hw : δ = 7 ^ h * w)
    (hnd : ¬ (7 : ℤ) ^ (h + 1) ∣ δ) : (w : ZMod 7) ≠ 0 := fun hz => hnd (by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨u, hu⟩ := hz
  exact ⟨u, by rw [hw, hu, pow_succ]; ring⟩)

/-- **Lemma 11 (BS L569).** A `3`-element class `A₁` (here `b : Fin 3 → ℤ`,
injective) admits a labeling `(d₁,d₂,d₃)` — a permutation of the inputs, certified
by the set identity `hperm` — whose difference-from-apex structure is one of:

* **(i)** distinct valuations `ν(e₂₃) < ν(e₁₃)` (→ `lemma9_i`);
* **(ii)** equal valuations `h` with leading-residue ratio `2` (→ `lemma9_ii_j2`)
  or `3` (→ `lemma9_ii_j3`).

Proof: extract the three difference-valuations; by the ultrametric (`ultra_add`,
on `e₀₂ = e₀₁ + e₁₂`) either one pair has a strict-max valuation — giving (i) — or
all three coincide, and then the leading-residue ratio fact (`ratio_two_three`)
finds a relabeling with ratio `2` or `3`. -/
theorem lemma11 (b : Fin 3 → ℤ) (hinj : Function.Injective b) :
    ∃ d₁ d₂ d₃ : ℤ,
      (∀ f : ℤ → ZMod 7,
        ({f d₁, f d₂, f d₃} : Finset (ZMod 7)) = {f (b 0), f (b 1), f (b 2)}) ∧
      ((∃ h₁ h₂ : ℕ, h₂ < h₁ ∧
          (7 : ℤ) ^ h₁ ∣ (d₁ - d₃) ∧ ¬ (7 : ℤ) ^ (h₁ + 1) ∣ (d₁ - d₃) ∧
          (7 : ℤ) ^ h₂ ∣ (d₂ - d₃) ∧ ¬ (7 : ℤ) ^ (h₂ + 1) ∣ (d₂ - d₃)) ∨
        (∃ h : ℕ,
          (7 : ℤ) ^ h ∣ (d₁ - d₃) ∧ ¬ (7 : ℤ) ^ (h + 1) ∣ (d₁ - d₃) ∧
          (7 : ℤ) ^ h ∣ (d₂ - d₃) ∧ ¬ (7 : ℤ) ^ (h + 1) ∣ (d₂ - d₃) ∧
          ((((d₂ - d₃) / 7 ^ h : ℤ) : ZMod 7) = 2 * (((d₁ - d₃) / 7 ^ h : ℤ) : ZMod 7) ∨
           (((d₂ - d₃) / 7 ^ h : ℤ) : ZMod 7) = 3 * (((d₁ - d₃) / 7 ^ h : ℤ) : ZMod 7)))) := by
  -- nonzero differences
  have n01 : b 0 - b 1 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have n02 : b 0 - b 2 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have n12 : b 1 - b 2 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  obtain ⟨va, hva, hva'⟩ := exists_val7 _ n01
  obtain ⟨vb, hvb, hvb'⟩ := exists_val7 _ n02
  obtain ⟨vc, hvc, hvc'⟩ := exists_val7 _ n12
  -- the additive relation e₀₂ = e₀₁ + e₁₂
  have hadd : b 0 - b 2 = (b 0 - b 1) + (b 1 - b 2) := by ring
  rcases lt_trichotomy va vc with hac | hac | hac
  · -- va < vc : strict max is vc (pair b1,b2); output (b1, b0, b2)
    refine ⟨b 1, b 0, b 2, ?_, Or.inl ⟨vc, va, hac, hvc, hvc', ?_, ?_⟩⟩
    · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
    · rw [hadd]; exact (ultra_add hva hva' hvc hac).1
    · rw [hadd]; exact (ultra_add hva hva' hvc hac).2
  · -- va = vc : compare vb with the common value
    subst hac
    have hvb_ge : va ≤ vb := by
      by_contra hlt; rw [not_le] at hlt
      exact hvb' (hadd ▸ dvd_add (dvd_trans (pow_dvd_pow 7 hlt) hva)
        (dvd_trans (pow_dvd_pow 7 hlt) hvc))
    rcases lt_or_eq_of_le hvb_ge with hlt | heq
    · -- va < vb : strict max is vb (pair b0,b2); output (b0, b1, b2)
      refine ⟨b 0, b 1, b 2, ?_, Or.inl ⟨vb, va, hlt, hvb, hvb', hvc, hvc'⟩⟩
      intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
    · -- all three valuations equal `va` : the leading-residue ratio case (ii)
      subst heq
      -- witnesses for the three differences at the common level `va`
      obtain ⟨wa, hwa⟩ := hva
      obtain ⟨wb, hwb⟩ := hvb
      obtain ⟨wc, hwc⟩ := hvc
      have h7 : (7 : ℤ) ^ va ≠ 0 := by positivity
      -- the residues are units, tied by `ra = rb − rc`
      have rane : (wa : ZMod 7) ≠ 0 := unit_res hwa hva'
      have rbne : (wb : ZMod 7) ≠ 0 := unit_res hwb hvb'
      have rcne : (wc : ZMod 7) ≠ 0 := unit_res hwc hvc'
      have hwrel : wb = wa + wc := by
        have : (7 : ℤ) ^ va * wb = (7 : ℤ) ^ va * (wa + wc) := by
          rw [mul_add, ← hwa, ← hwc, ← hwb]; linarith [hadd]
        exact mul_left_cancel₀ h7 this
      have hrel : (wa : ZMod 7) = (wb : ZMod 7) - (wc : ZMod 7) := by
        rw [hwrel]; push_cast; ring
      -- a unit leading residue means `7^(va+1)` does not divide the difference
      have ndvd_res : ∀ (δ u : ℤ), δ = (7 : ℤ) ^ va * u → (u : ZMod 7) ≠ 0 →
          ¬ (7 : ℤ) ^ (va + 1) ∣ δ := by
        intro δ u hδ hune hdvd
        obtain ⟨z, hz⟩ := hdvd
        exact hune (by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact ⟨z, mul_left_cancel₀ h7 (by rw [← hδ, hz, pow_succ]; ring)⟩)
      -- reversed-orientation witnesses and their unit residues
      have hwa' : b 1 - b 0 = (7 : ℤ) ^ va * (-wa) := by
        rw [show b 1 - b 0 = -(b 0 - b 1) from by ring, hwa]; ring
      have hwb' : b 2 - b 0 = (7 : ℤ) ^ va * (-wb) := by
        rw [show b 2 - b 0 = -(b 0 - b 2) from by ring, hwb]; ring
      have hwc' : b 2 - b 1 = (7 : ℤ) ^ va * (-wc) := by
        rw [show b 2 - b 1 = -(b 1 - b 2) from by ring, hwc]; ring
      have ranen : ((-wa : ℤ) : ZMod 7) ≠ 0 := by simpa using rane
      have rbnen : ((-wb : ℤ) : ZMod 7) ≠ 0 := by simpa using rbne
      have rcnen : ((-wc : ℤ) : ZMod 7) ≠ 0 := by simpa using rcne
      rcases ratio_two_three (wa : ZMod 7) (wb : ZMod 7) (wc : ZMod 7) rane rbne rcne hrel with
        hD | hD | hD | hD | hD | hD
      · -- ratio at apex b2: output (b0,b1,b2)
        refine ⟨b 0, b 1, b 2, ?_,
          Or.inr ⟨va, ⟨wb, hwb⟩, ndvd_res _ _ hwb rbne, ⟨wc, hwc⟩, ndvd_res _ _ hwc rcne, ?_⟩⟩
        · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
        · rw [res_eq hwc, res_eq hwb]; exact hD
      · -- output (b1,b0,b2)
        refine ⟨b 1, b 0, b 2, ?_,
          Or.inr ⟨va, ⟨wc, hwc⟩, ndvd_res _ _ hwc rcne, ⟨wb, hwb⟩, ndvd_res _ _ hwb rbne, ?_⟩⟩
        · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
        · rw [res_eq hwb, res_eq hwc]; exact hD
      · -- output (b0,b2,b1)
        refine ⟨b 0, b 2, b 1, ?_,
          Or.inr ⟨va, ⟨wa, hwa⟩, ndvd_res _ _ hwa rane, ⟨-wc, hwc'⟩, ndvd_res _ _ hwc' rcnen, ?_⟩⟩
        · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
        · rw [res_eq hwc', res_eq hwa]; push_cast; exact hD
      · -- output (b2,b0,b1)
        refine ⟨b 2, b 0, b 1, ?_,
          Or.inr ⟨va, ⟨-wc, hwc'⟩, ndvd_res _ _ hwc' rcnen, ⟨wa, hwa⟩, ndvd_res _ _ hwa rane, ?_⟩⟩
        · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
        · rw [res_eq hwa, res_eq hwc']; push_cast; exact hD
      · -- output (b1,b2,b0)
        refine ⟨b 1, b 2, b 0, ?_,
          Or.inr ⟨va, ⟨-wa, hwa'⟩, ndvd_res _ _ hwa' ranen, ⟨-wb, hwb'⟩, ndvd_res _ _ hwb' rbnen, ?_⟩⟩
        · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
        · rw [res_eq hwb', res_eq hwa']; push_cast; exact hD
      · -- output (b2,b1,b0)
        refine ⟨b 2, b 1, b 0, ?_,
          Or.inr ⟨va, ⟨-wb, hwb'⟩, ndvd_res _ _ hwb' rbnen, ⟨-wa, hwa'⟩, ndvd_res _ _ hwa' ranen, ?_⟩⟩
        · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
        · rw [res_eq hwa', res_eq hwb']; push_cast; exact hD
  · -- vc < va : strict max is va (pair b0,b1); output (b0, b2, b1)
    refine ⟨b 0, b 2, b 1, ?_, Or.inl ⟨va, vc, hac, hva, hva', ?_, ?_⟩⟩
    · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
    · exact dvd_sub_comm.mpr hvc
    · exact fun h => hvc' (dvd_sub_comm.mp h)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Lemma 10 (ii) residue selection (BS L583–593, `|A₁| ≥ 4` case).** Four
elements with all pairwise differences at a common level `h` correspond (via the
leading parts `gᵢ = (dᵢ − d₀)/7^h`) to four *distinct* `ZMod 7` residues. Among
them there is always a relabeling `(i,j,k,l)` (apex `i`) with `r(e_{ki}) = 2·r(e_{ji})`
and `r(e_{li}) ∈ {3,4}·r(e_{ji})`. Exhaustive over injective `Fin 4 → ZMod 7`. -/
theorem lemma10_select (g : Fin 4 → ZMod 7) (hg : Function.Injective g) :
    ∃ i j k l : Fin 4, (∀ x : Fin 4, x = i ∨ x = j ∨ x = k ∨ x = l) ∧
      g k - g i = 2 * (g j - g i) ∧
      (g l - g i = 3 * (g j - g i) ∨ g l - g i = 4 * (g j - g i)) := by
  revert hg; revert g; decide

/-- Four `Fin 4` indices that cover all of `Fin 4` are pairwise distinct. -/
theorem cover_distinct (i j k l : Fin 4)
    (hc : ∀ x : Fin 4, x = i ∨ x = j ∨ x = k ∨ x = l) :
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  revert hc; revert i j k l; decide

/-- **Lemma 10 (BS L509).** A `4`-element class `A₁` (`b : Fin 4 → ℤ`, injective)
admits a labeling `(d₁,d₂,d₃,d₄)` — a permutation of the inputs (certified by
`hperm`) — with one of:

* **(i)** `ν(e₂₁) ≠ ν(e₃₁)` (distinct apex-valuations → `lemma9_i` on `{d₁,d₂,d₃}`);
* **(ii)** all of `e₂₁,e₃₁,e₄₁` at one level `h` with `r(e₃₁)=2·r(e₂₁)` and
  `r(e₄₁) ∈ {3,4}·r(e₂₁)` (→ `lemma9_ii_j2` on `{d₁,d₂,d₃}`, with `d₄` controlled).

Apex convention `d₁` (differences `dᵢ − d₁`). Proof: a connectivity cascade on the
difference-valuations gives a strict-max adjacent pair (→ i) unless all six
pairwise differences share a level, in which case the leading residues are four
distinct `ZMod 7` values and `lemma10_select` produces the (ii) labeling. -/
theorem lemma10 (b : Fin 4 → ℤ) (hinj : Function.Injective b) :
    ∃ d₁ d₂ d₃ d₄ : ℤ,
      (∀ f : ℤ → ZMod 7,
        ({f d₁, f d₂, f d₃, f d₄} : Finset (ZMod 7)) = {f (b 0), f (b 1), f (b 2), f (b 3)}) ∧
      ((∃ h₁ h₂ : ℕ, h₁ ≠ h₂ ∧
          (7 : ℤ) ^ h₁ ∣ (d₂ - d₁) ∧ ¬ (7 : ℤ) ^ (h₁ + 1) ∣ (d₂ - d₁) ∧
          (7 : ℤ) ^ h₂ ∣ (d₃ - d₁) ∧ ¬ (7 : ℤ) ^ (h₂ + 1) ∣ (d₃ - d₁)) ∨
        (∃ h : ℕ,
          (7 : ℤ) ^ h ∣ (d₂ - d₁) ∧ ¬ (7 : ℤ) ^ (h + 1) ∣ (d₂ - d₁) ∧
          (7 : ℤ) ^ h ∣ (d₃ - d₁) ∧ ¬ (7 : ℤ) ^ (h + 1) ∣ (d₃ - d₁) ∧
          (7 : ℤ) ^ h ∣ (d₄ - d₁) ∧ ¬ (7 : ℤ) ^ (h + 1) ∣ (d₄ - d₁) ∧
          (((d₃ - d₁) / 7 ^ h : ℤ) : ZMod 7) = 2 * (((d₂ - d₁) / 7 ^ h : ℤ) : ZMod 7) ∧
          ((((d₄ - d₁) / 7 ^ h : ℤ) : ZMod 7) = 3 * (((d₂ - d₁) / 7 ^ h : ℤ) : ZMod 7) ∨
           (((d₄ - d₁) / 7 ^ h : ℤ) : ZMod 7) = 4 * (((d₂ - d₁) / 7 ^ h : ℤ) : ZMod 7)))) := by
  have n10 : b 1 - b 0 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have n20 : b 2 - b 0 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have n30 : b 3 - b 0 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have n12 : b 1 - b 2 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have n13 : b 1 - b 3 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  have n23 : b 2 - b 3 ≠ 0 := sub_ne_zero.mpr (hinj.ne (by decide))
  obtain ⟨v1, hv1, hv1'⟩ := exists_val7 _ n10
  obtain ⟨v2, hv2, hv2'⟩ := exists_val7 _ n20
  obtain ⟨v3, hv3, hv3'⟩ := exists_val7 _ n30
  by_cases e12 : v1 = v2
  · by_cases e13 : v1 = v3
    · -- v1 = v2 = v3 : all differences-from-`b 0` share level `v1`
      subst e12; subst e13
      by_cases s12 : (7 : ℤ) ^ (v1 + 1) ∣ (b 1 - b 2)
      · -- ν(e₁₂) > v1 : apex switch to b 1; output (b1, b2, b0, b3)
        obtain ⟨w, hw, hw'⟩ := exists_val7 _ n12
        have hwv : w ≠ v1 := fun h => hw' (h ▸ s12)
        refine ⟨b 1, b 2, b 0, b 3, ?_, Or.inl ⟨w, v1, hwv, dvd_sub_comm.mpr hw,
          fun h => hw' (dvd_sub_comm.mp h), dvd_sub_comm.mpr hv1,
          fun h => hv1' (dvd_sub_comm.mp h)⟩⟩
        intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
      · by_cases s13 : (7 : ℤ) ^ (v1 + 1) ∣ (b 1 - b 3)
        · -- ν(e₁₃) > v1 : apex 1; output (b1, b3, b0, b2)
          obtain ⟨w, hw, hw'⟩ := exists_val7 _ n13
          have hwv : w ≠ v1 := fun h => hw' (h ▸ s13)
          refine ⟨b 1, b 3, b 0, b 2, ?_, Or.inl ⟨w, v1, hwv, dvd_sub_comm.mpr hw,
            fun h => hw' (dvd_sub_comm.mp h), dvd_sub_comm.mpr hv1,
            fun h => hv1' (dvd_sub_comm.mp h)⟩⟩
          intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
        · by_cases s23 : (7 : ℤ) ^ (v1 + 1) ∣ (b 2 - b 3)
          · -- ν(e₂₃) > v1 : apex 2; output (b2, b3, b0, b1)
            obtain ⟨w, hw, hw'⟩ := exists_val7 _ n23
            have hwv : w ≠ v1 := fun h => hw' (h ▸ s23)
            refine ⟨b 2, b 3, b 0, b 1, ?_, Or.inl ⟨w, v1, hwv, dvd_sub_comm.mpr hw,
              fun h => hw' (dvd_sub_comm.mp h), dvd_sub_comm.mpr hv2,
              fun h => hv2' (dvd_sub_comm.mp h)⟩⟩
            intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
          · -- all six differences at level v1 : the residue-selection case (ii)
            obtain ⟨gw1, hgw1⟩ := hv1
            obtain ⟨gw2, hgw2⟩ := hv2
            obtain ⟨gw3, hgw3⟩ := hv3
            set gw : Fin 4 → ℤ := ![0, gw1, gw2, gw3] with hgw_def
            have hbsub : ∀ x : Fin 4, b x - b 0 = 7 ^ v1 * gw x := by
              intro x; fin_cases x
              · simp [hgw_def]
              · simpa [hgw_def] using hgw1
              · simpa [hgw_def] using hgw2
              · simpa [hgw_def] using hgw3
            have hbdiff : ∀ x y : Fin 4, b x - b y = 7 ^ v1 * (gw x - gw y) := by
              intro x y; rw [mul_sub, ← hbsub x, ← hbsub y]; ring
            have hallnd : ∀ x y : Fin 4, x ≠ y → ¬ (7 : ℤ) ^ (v1 + 1) ∣ (b x - b y) := by
              intro x y hxy
              fin_cases x <;> fin_cases y <;>
                first
                | exact absurd rfl hxy
                | exact hv1' | exact hv2' | exact hv3' | exact s12 | exact s13 | exact s23
                | exact fun h => hv1' (dvd_sub_comm.mp h)
                | exact fun h => hv2' (dvd_sub_comm.mp h)
                | exact fun h => hv3' (dvd_sub_comm.mp h)
                | exact fun h => s12 (dvd_sub_comm.mp h)
                | exact fun h => s13 (dvd_sub_comm.mp h)
                | exact fun h => s23 (dvd_sub_comm.mp h)
            have hg_inj : Function.Injective (fun x : Fin 4 => (gw x : ZMod 7)) := by
              intro x y h
              by_contra hxy
              refine hallnd x y hxy ?_
              have hb : (gw x : ZMod 7) = (gw y : ZMod 7) := h
              have hz : ((gw x - gw y : ℤ) : ZMod 7) = 0 := by push_cast; rw [hb]; ring
              have h7 : (7 : ℤ) ∣ (gw x - gw y) := by
                exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hz
              obtain ⟨c, hc⟩ := h7
              exact ⟨c, by rw [hbdiff x y, hc, pow_succ]; ring⟩
            obtain ⟨i, j, k, l, hcover, hr2, hr34⟩ := lemma10_select _ hg_inj
            obtain ⟨hij, hik, hil, _, _, _⟩ := cover_distinct i j k l hcover
            refine ⟨b i, b j, b k, b l, ?_, Or.inr ⟨v1, ⟨gw j - gw i, hbdiff j i⟩,
              hallnd j i (Ne.symm hij), ⟨gw k - gw i, hbdiff k i⟩, hallnd k i (Ne.symm hik),
              ⟨gw l - gw i, hbdiff l i⟩, hallnd l i (Ne.symm hil), ?_, ?_⟩⟩
            · intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro (rfl | rfl | rfl | rfl)
                · fin_cases i <;> simp
                · fin_cases j <;> simp
                · fin_cases k <;> simp
                · fin_cases l <;> simp
              · rintro (rfl | rfl | rfl | rfl)
                · rcases hcover 0 with h | h | h | h <;> rw [← h] <;> simp
                · rcases hcover 1 with h | h | h | h <;> rw [← h] <;> simp
                · rcases hcover 2 with h | h | h | h <;> rw [← h] <;> simp
                · rcases hcover 3 with h | h | h | h <;> rw [← h] <;> simp
            · rw [res_eq (hbdiff k i), res_eq (hbdiff j i)]; push_cast
              push_cast at hr2; linear_combination hr2
            · rcases hr34 with h | h
              · left; rw [res_eq (hbdiff l i), res_eq (hbdiff j i)]; push_cast
                push_cast at h; linear_combination h
              · right; rw [res_eq (hbdiff l i), res_eq (hbdiff j i)]; push_cast
                push_cast at h; linear_combination h
    · -- v1 = v2, v1 ≠ v3 : (i), apex b 0, pair (1,3); output (b0, b1, b3, b2)
      refine ⟨b 0, b 1, b 3, b 2, ?_, Or.inl ⟨v1, v3, e13, hv1, hv1', hv3, hv3'⟩⟩
      intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]
  · -- v1 ≠ v2 : (i), apex b 0, pair (1,2); output (b0, b1, b2, b3)
    refine ⟨b 0, b 1, b 2, b 3, ?_, Or.inl ⟨v1, v2, e12, hv1, hv1', hv2, hv2'⟩⟩
    intro f; ext x; simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]

/-! ### Λ_m top-digit apparatus (the `ν(E) = {m}` engine)

For the case branches where every pairwise difference of `A₁` sits at the top
level `m`, a *constant* unit multiplier `u` acts affinely on the arc indices. The
foundation is that adding a multiple of `7^m` shifts the arc index by that
multiple (no carry, since `c·7^m ≡ 0 mod 7^m`). -/

/-- Adding `c·7^m` shifts the arc index by `c`: `q(x + c·7^m) = q(x) + c`. -/
theorem qz_add_mul_pow (m : ℕ) (x c : ℤ) :
    qz m (x + c * 7 ^ m) = qz m x + (c : ZMod 7) := by
  unfold qz
  rw [show x + c * 7 ^ m = x + 7 ^ m * c from by ring,
    Int.add_mul_ediv_left x c (by positivity : (7 : ℤ) ^ m ≠ 0)]
  push_cast; ring

/-- **Constant-multiplier top-digit affine action.** For level-0 elements `x, y`
whose difference is at level `≥ m` (`7^m ∣ x − y`), a constant multiplier `u`
shifts the arc index affinely: `q(u·x) = q(u·y) + u · r`, where `r = (x−y)/7^m`
is the leading coefficient of the difference. This is the engine of the
`ν(E) = {m}` branches (BS's `(i−j)⁻¹` multiplier). -/
theorem qz_top_affine (m : ℕ) (u x y : ℤ) (h : (7 : ℤ) ^ m ∣ (x - y)) :
    qz m (u * x) = qz m (u * y) + (u : ZMod 7) * (((x - y) / 7 ^ m : ℤ) : ZMod 7) := by
  obtain ⟨c, hc⟩ := h
  have hux : u * x = u * y + (u * c) * 7 ^ m := by
    have hxy : x = y + 7 ^ m * c := by linarith [hc]
    rw [hxy]; ring
  rw [hux, qz_add_mul_pow]
  congr 1
  have hcdiv : (x - y) / 7 ^ m = c := by
    rw [hc]; exact Int.mul_ediv_cancel_left c (by positivity)
  rw [hcdiv]; push_cast; ring

/-- Any two distinct residues `p ≠ q` are sent to `0` and `6` by an affine unit
map `x ↦ A + u·x` (exhaustive `decide`). -/
theorem affine_place_pair (p q : ZMod 7) (hpq : p ≠ q) :
    ∃ u A : ZMod 7, u ≠ 0 ∧ A + u * p = 0 ∧ A + u * q = 6 := by
  revert hpq; revert p q; decide

/-- **`|A₁| = 5`, `ν(E) = {m}` placement core.** Five distinct `ZMod 7` residues
(the leading coefficients of five level-`0` elements whose pairwise differences are
all at level `m`) admit an affine unit map `x ↦ A + u·x` sending all of them
outside `{0,6}` — i.e. into the central band `{1,…,5}`. (BS's `(i−j)⁻¹`
multiplier: map the two *missing* residues to `{0,6}`; the unit map then bijects
the remaining five onto `{1,…,5}`.) -/
theorem affine_place (c : Fin 5 → ZMod 7) (hc : Function.Injective c) :
    ∃ u A : ZMod 7, u ≠ 0 ∧ ∀ i, A + u * c i ≠ 0 ∧ A + u * c i ≠ 6 := by
  classical
  set S : Finset (ZMod 7) := Finset.image c Finset.univ with hS
  have hScard : S.card = 5 := by
    rw [hS, Finset.card_image_of_injective _ hc, Finset.card_univ, Fintype.card_fin]
  have hcompl : Sᶜ.card = 2 := by rw [Finset.card_compl, hScard]; decide
  obtain ⟨p, q, hpq, hSc⟩ := Finset.card_eq_two.mp hcompl
  obtain ⟨u, A, hu, hp0, hq6⟩ := affine_place_pair p q hpq
  have hpc : p ∉ S := by
    have : p ∈ Sᶜ := by rw [hSc]; exact Finset.mem_insert_self p {q}
    exact Finset.mem_compl.mp this
  have hqc : q ∉ S := by
    have : q ∈ Sᶜ := by rw [hSc]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    exact Finset.mem_compl.mp this
  refine ⟨u, A, hu, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hcip : c i = p := mul_left_cancel₀ hu (add_left_cancel (a := A) (by rw [h, hp0]))
    exact hpc (hcip ▸ Finset.mem_image_of_mem c (Finset.mem_univ i))
  · have hciq : c i = q := mul_left_cancel₀ hu (add_left_cancel (a := A) (by rw [h, hq6]))
    exact hqc (hciq ▸ Finset.mem_image_of_mem c (Finset.mem_univ i))

/-- **Case 6.1, `ν(E) = {m}` branch.** Five level-`0` elements, all `≡ 1 mod 7`,
whose pairwise differences are all at level exactly `m` (so the leading
coefficients `cᵢ = (dᵢ − d₀)/7^m` are distinct), admit a unit multiplier sending
every arc index outside `{0,6}`. The multiplier is `(1 + k·7^m)·u` with `u` the
unit from `affine_place` and `k` the `Λ₀` shift placing the base: by
`qz_top_affine` then `qz_shift0`, `q(λ·dᵢ) = q(u·d₀) + k·u + u·cᵢ`, and `k` is
chosen so `q(u·d₀) + k·u = A`, giving `q(λ·dᵢ) = A + u·cᵢ ∉ {0,6}`. -/
theorem case_61_top (m : ℕ) (hm : 0 < m) (d : Fin 5 → ℤ)
    (hres1 : ∀ i, (d i : ZMod 7) = 1)
    (htop : ∀ i, (7 : ℤ) ^ m ∣ (d i - d 0))
    (hdist : Function.Injective (fun i => (((d i - d 0) / 7 ^ m : ℤ) : ZMod 7))) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i, qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  set c : Fin 5 → ZMod 7 := fun i => (((d i - d 0) / 7 ^ m : ℤ) : ZMod 7) with hc_def
  obtain ⟨u, A, hu, havoid⟩ := affine_place c hdist
  set u_int : ℤ := (u.val : ℤ) with hu_def
  have hu_cast : ((u_int : ℤ) : ZMod 7) = u := by
    rw [hu_def]; push_cast; exact ZMod.natCast_rightInverse u
  have hu_ndvd : ¬ (7 : ℤ) ∣ u_int := by
    intro h; apply hu
    rw [← hu_cast]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd u_int 7).mpr (by exact_mod_cast h)
  set qb : ZMod 7 := qz m (u_int * d 0) with hqb
  set k : ZMod 7 := (A - qb) * u⁻¹ with hk_def
  have hku : k * u = A - qb := by rw [hk_def, mul_assoc, inv_mul_cancel₀ hu, mul_one]
  set k_int : ℤ := (k.val : ℤ) with hk_int_def
  have hk_cast : ((k_int : ℤ) : ZMod 7) = k := by
    rw [hk_int_def]; push_cast; exact ZMod.natCast_rightInverse k
  set lam : ℤ := (1 + k_int * 7 ^ m) * u_int with hlam_def
  have hlam_ndvd : ¬ (7 : ℤ) ∣ lam := by
    rw [hlam_def]
    have hp : Prime (7 : ℤ) := Nat.prime_iff_prime_int.mp (by decide)
    have h1m : ¬ (7 : ℤ) ∣ (1 + k_int * 7 ^ m) := by
      intro h
      have hd7m : (7 : ℤ) ∣ k_int * 7 ^ m :=
        Dvd.dvd.mul_left (dvd_pow_self 7 (by omega : m ≠ 0)) k_int
      have h1 : (7 : ℤ) ∣ 1 := by have := dvd_sub h hd7m; simpa using this
      exact absurd h1 (by norm_num)
    intro h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact h1m h1
    · exact hu_ndvd h2
  refine ⟨lam, hlam_ndvd, fun i => ?_⟩
  have key : qz m (lam * d i) = A + u * c i := by
    have hrw : lam * d i = (1 + k_int * 7 ^ m) * (u_int * d i) := by rw [hlam_def]; ring
    rw [hrw, qz_shift0, hk_cast]
    have hres_i : ((u_int * d i : ℤ) : ZMod 7) = u := by
      push_cast; rw [hu_cast, hres1 i]; ring
    rw [hres_i]
    have haff : qz m (u_int * d i) = qb + u * c i := by
      rw [hqb, qz_top_affine m u_int (d i) (d 0) (htop i), hu_cast, hc_def]
    rw [haff]
    have : qb + u * c i + k * u = A + u * c i := by rw [hku]; ring
    linear_combination this
  rw [key]; exact havoid i

/-- **Residue-agnostic final placement.** Five elements all `≡ r mod 7` (`r` a
unit) whose arc indices fit a length-5 window admit a `Λ₀` multiplier avoiding
`{0,6}`. Unlike `five_lambda0`, `r` is ANY unit (not restricted to `{1,2,4}`), so
this serves the `ν(E)≠{m}` branch after the `3·`-remultiply (residue 3). The
window `{a,…,a+4}` is shifted to `{1,…,5}` by `k = (1−a)·r⁻¹` (`q(λ·dᵢ) =
q(dᵢ) + k·r = (q(dᵢ)−a) + 1 ∈ {1,…,5}`). -/
theorem place_window5 (m : ℕ) (hm : 0 < m) (d : Fin 5 → ℤ)
    (r : ZMod 7) (hr : r ≠ 0) (hres : ∀ i, (d i : ZMod 7) = r)
    (hwin : ∃ a : ZMod 7, ∀ i, (qz m (d i) - a).val ≤ 4) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∀ i, qz m (lam * d i) ≠ 0 ∧ qz m (lam * d i) ≠ 6 := by
  obtain ⟨a, ha⟩ := hwin
  set k : ZMod 7 := (1 - a) * r⁻¹ with hk_def
  have hkr : k * r = 1 - a := by rw [hk_def, mul_assoc, inv_mul_cancel₀ hr, mul_one]
  set k_int : ℤ := (k.val : ℤ) with hk_int_def
  have hk_cast : ((k_int : ℤ) : ZMod 7) = k := by
    rw [hk_int_def]; push_cast; exact ZMod.natCast_rightInverse k
  set lam : ℤ := 1 + k_int * 7 ^ m with hlam_def
  have hlam_ndvd : ¬ (7 : ℤ) ∣ lam := by
    rw [hlam_def]; intro h
    have hd7m : (7 : ℤ) ∣ k_int * 7 ^ m :=
      Dvd.dvd.mul_left (dvd_pow_self 7 (by omega : m ≠ 0)) k_int
    have h1 : (7 : ℤ) ∣ 1 := by have := dvd_sub h hd7m; simpa using this
    exact absurd h1 (by norm_num)
  refine ⟨lam, hlam_ndvd, fun i => ?_⟩
  have key : qz m (lam * d i) = (qz m (d i) - a) + 1 := by
    rw [hlam_def, qz_shift0, hk_cast, hres i, hkr]; ring
  rw [key]
  have key2 : ∀ v : ZMod 7, v.val ≤ 4 → (v + 1 ≠ 0 ∧ v + 1 ≠ 6) := by decide
  exact key2 _ (ha i)

/-- **Case 6.1, `ν(E)≠{m}` dichotomy core.** Once `B={d₁,d₂,d₃}` is pinned to
`q(B) ⊂ {0,6}`, the five arc indices are `{0,6,p,q}` with `p=q(d₄), q=q(d₅)`
arbitrary. They fit a length-5 window UNLESS `{p,q}={2,4}` (which gives `{0,2,4,6}`,
ℓ=6 — the unique bad config that BS resolves by the `3·`-remultiply). Exhaustive
`decide` over `(p,q)`. The window is reported as a start `a` with all of
`0,6,p,q` within `{a,…,a+4}`. -/
theorem dichotomy_core (p q : ZMod 7)
    (hpq : ¬ ((p = 2 ∧ q = 4) ∨ (p = 4 ∧ q = 2))) :
    ∃ a : ZMod 7,
      (0 - a).val ≤ 4 ∧ (6 - a).val ≤ 4 ∧ (p - a).val ≤ 4 ∧ (q - a).val ≤ 4 := by
  revert hpq; revert p q; decide

end IntLRC7BS
