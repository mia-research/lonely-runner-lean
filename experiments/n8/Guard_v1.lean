import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The guard lemma: a reading that lands on a lower band edge blocks just below it

The AP covers `[1,7] ∪ [9,15]` because each of its eight clear points is **guarded from below**.
At a clear point `R` the guard is the reading `s` with `s·R ≡ 1 (mod 8)` — and since `(ℤ/8)ˣ` is the
Klein four-group, `s ≡ R⁻¹ ≡ R (mod 8)`. So:

```
    R =  1,  9   guard  s ≡ 1      (that is s₁ = 1 itself)
    R =  3, 11   guard  s = 3
    R =  5, 13   guard  s = 5
    R =  7, 15   guard  s ≡ 7      →  s₇ = S
```

`S` guards the **right endpoint of both regions**. Raising `S` past `7` un-guards both at once, and
the uncovered set opens as exactly two intervals

```
    [7 − 7ε/(7+ε), 7]   ∪   [15 − 15ε/(7+ε), 15],     total  22ε/(7+ε)
```

verified to ten decimal places at `ε = 10⁻², 10⁻³, 10⁻⁴` (`ap_mechanism_v1.py`). That is the
measured `(22/7)(S−7)` rate of `AP_ISOLATION_v1`, now derived rather than fitted.

`guard_blocks_below` is the step the derivation rests on: a reading sitting exactly on a lower band
edge is in the way immediately below it. -/

namespace Guard

/-- **The guard lemma.**  If reading `s > 0` has `s·R = 8k+1` — exactly the lower edge of a clear
band — then for every `δ` with `0 < δ < 1/s` the reading at `R − δ` lies strictly between `8k` and
`8k+1`, i.e. within `1` of the multiple `8k`: the runner is in the way just below `R`. -/
theorem guard_blocks_below {s R δ : ℝ} {k : ℤ} (hs : 0 < s) (hR : s * R = 8 * k + 1)
    (hδ : 0 < δ) (hδ' : δ < 1 / s) :
    8 * (k : ℝ) < s * (R - δ) ∧ s * (R - δ) < 8 * k + 1 := by
  have hsδ : s * δ < 1 := by
    rw [lt_div_iff₀ hs] at hδ'
    linarith [hδ']
  constructor
  · have : s * (R - δ) = 8 * (k : ℝ) + 1 - s * δ := by rw [mul_sub, hR]
    rw [this]; linarith
  · have : s * (R - δ) = 8 * (k : ℝ) + 1 - s * δ := by rw [mul_sub, hR]
    rw [this]
    nlinarith [mul_pos hs hδ]

/-- **The un-guarding.**  If instead the reading is `s' > s`, its value at `R` exceeds the edge:
`s'·R > 8k+1`, so it has moved *into* the clear band and no longer blocks at `R`.  With `s` the
unique guard of `R`, raising it opens a gap immediately below `R`. -/
theorem raising_unguards {s s' R : ℝ} {k : ℤ} (hR : 0 < R) (hs : s * R = 8 * k + 1) (hlt : s < s') :
    8 * (k : ℝ) + 1 < s' * R := by
  have : s * R < s' * R := by exact mul_lt_mul_of_pos_right hlt hR
  linarith [hs ▸ this]



/-! ## The guard identity, and the AP's clear points

The guard of `R` is the reading `≡ R (mod 8)` because `(ℤ/8)ˣ` is the Klein four-group, so every
unit is its own inverse: `R·R ≡ 1`. That is `klein_self_inverse`, decided.

The AP's covering rests on the other half: at an **odd** `R`, every reading `1..7` is clear, because
`8 ∤ i·R`. That is `ap_clear_at_odd`. Together they say the eight points `1,3,…,15` are clear for
the AP and each is guarded from below by the reading `≡ R`, so the AP's uncovered set is exactly
those eight points and has measure zero — v11 Theorem 11.3, now with its two halves formalised. -/

/-- **`(ℤ/8)ˣ` is Klein: every unit is its own inverse.**  Hence `R⁻¹ ≡ R`, so the guard of `R` is
the reading congruent to `R` itself. -/
theorem klein_self_inverse : ∀ r : ZMod 8, IsUnit r → r * r = 1 := by decide

/-- **The AP is clear at every odd instant.**  For a reading `1 ≤ i ≤ 7` and odd `R`, the product
`i·R` is never a multiple of `8`, so the reading is at circle distance at least `1/8`. -/
theorem ap_clear_at_odd {i R : ℤ} (h1 : 1 ≤ i) (h7 : i ≤ 7) (hR : Odd R) :
    ¬ ((8 : ℤ) ∣ i * R) := by
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ := hR
  subst hm
  interval_cases i <;> omega

/-- **The un-guarded interval, exactly.**  With the guard raised from `g` to `g + ε`, the reading at
`R − δ` stays above the band edge `8k+1` — so the guard does not block — precisely while
`δ < R·ε/(g+ε)`.  At `g = 7`, `R = 7` this is `δ < 7ε/(7+ε)`; at `R = 15`, `δ < 15ε/(7+ε)`. -/
theorem unguarded_width {g R ε δ : ℝ} {k : ℤ} (hg : 0 < g) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hR : g * R = 8 * k + 1) (hlt : δ < R * ε / (g + ε)) :
    8 * (k : ℝ) + 1 < (g + ε) * (R - δ) := by
  have hge : 0 < g + ε := by linarith
  rw [lt_div_iff₀ hge] at hlt
  nlinarith [hR]



/-! ## The integer case, in general

`ap_clear_at_odd` is the AP's instance of a fact that needs no bound on the reading: for **integer**
readings, an odd `R` is clear unless the reading is itself divisible by `8`. So an integer profile
with no reading `≡ 0 (mod 8)` has all eight odd integers of `[1,15]` clear, and `R_final = 1`.

This is the residue partition seen from the covering side: the colliding readings — those divisible
by `8` — are exactly the ones that can block every odd instant at once. -/

/-- **Integer readings, general form.**  For an odd `R`, the product `s·R` is divisible by `8` only
if `s` is.  So a reading not divisible by `8` leaves every odd instant clear. -/
theorem odd_clear_of_not_dvd {s R : ℤ} (hs : ¬ ((8 : ℤ) ∣ s)) (hR : Odd R) :
    ¬ ((8 : ℤ) ∣ s * R) := by
  intro h
  apply hs
  obtain ⟨m, hm⟩ := hR
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self m
  have hsq : R * R = 8 * k + 1 := by subst hm; nlinarith [hk]
  have hco : IsCoprime (8 : ℤ) R := ⟨-k, R, by linarith [hsq]⟩
  exact hco.dvd_of_dvd_mul_right h



/-! ## Integer readings make the blocking 8-periodic — the problem halves

For an **integer** reading `s`, `s(R+8) − sR = 8s ≡ 0 (mod 8)`, so `R` and `R+8` have the same
blocking status. Hence the two regions are translates: `[9,15] = [1,7] + 8`, and

* the uncovered set of `[9,15]` is the uncovered set of `[1,7]` shifted by `8`;
* the clear set is `8`-periodic, so it is non-empty in `[1,15]` iff it is non-empty in `[1,7]`;
* therefore **for integer readings, `R ≤ 7` whenever a clear instant exists at all.**

Observed exactly on the Branch-B minimiser `[3,4,5,7,11,24]`, whose four gaps in `[1,7]` —
`(9/7, 31/24)`, `(41/11, 15/4)`, `(17/4, 47/11)`, `(161/24, 47/7)` — reappear in `[9,15]` shifted by
`8`, with total uncovered `53/462` split evenly between the two regions. -/

/-- **Integer readings block 8-periodically.**  The reading at `R + 8` differs from the reading at
`R` by `8s`, a multiple of `8`, so the two are congruent and block together. -/
theorem block_periodic {s R : ℤ} : s * (R + 8) - s * R = 8 * s := by ring

/-- **Hence the same multiples are approached.**  `s(R+8) − 8M' = s·R − 8M` with `M' = M + s`, so a
witness that `s` is in the way at `R` transfers verbatim to `R + 8`. -/
theorem block_shift {s R M : ℤ} : s * (R + 8) - 8 * (M + s) = s * R - 8 * M := by ring

end Guard
