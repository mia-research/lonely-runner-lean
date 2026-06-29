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

end IntLRC7BS
