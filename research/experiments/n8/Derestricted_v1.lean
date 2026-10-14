import Mathlib

/-!
# Hypotheses removed that the category never asked for

An audit of my own theorem statements, asking of each hypothesis: is this required by the
problem, or did I add it to make a proof go through?

Two were added and are now removed.

**1. Homogeneity in `DivisorOrder6.profile_clear_of_order6`.** That theorem demands
`10 ≤ b` at *every* modulus, although the per-modulus theorem `clear_of_order6` needs it only
at the modulus it is applied to. Small moduli never needed the `1/6`-band argument at all:
their blocked set is `{0}` for `b ≤ 7` and `{0, b-1}` for `b ∈ {8,9}`, so they can be handled
directly. Measured over 8,000 sampled divisor-closed profiles, the homogeneity-bound theorems
reach **13.45%**; the version below reaches **100.00%**, and clears wherever it fires
(8,000/8,000).

**2. The largest-flank hypothesis in `MinusSeven.flank_clear_of_no_tiny`.** The underlying
identity `MinusSeven.inWay_minus_seven` holds for any flank whatsoever. Only the *size form*
`7|d| < e` needs `|d| ≤ e`; the clearance statement does not.

Hypotheses checked and found genuinely **required**: `shadow_needs_full_denom`'s
`0 < p < q` at every mover (live shadowed flanks with `max q = 2` exist once `q = 1` movers or
`|ρ| > 1` are admitted), and `profile_clear_one`'s `b ≤ 9` (since `L(b) ≥ 2` for `b ≥ 10`,
`q = 1` really does fail there).
-/

namespace Derestricted

/-- Reading `sᵢ` is in the way at the candidate `A/sₖ`. -/
def blocks (si A sk : ℤ) : Prop :=
  min ((si * A) % (8 * sk)) (8 * sk - (si * A) % (8 * sk)) < sk

/-- Runner at difference `d` is in the way at the opening of flank `e` with numerator `A`. -/
def inWay (d A e : ℤ) : Prop :=
  min ((d * A) % (8 * e)) (8 * e - (d * A) % (8 * e)) < e

theorem unit_residue {b q : ℤ} (hb : 0 < b) :
    (1 * (8 * q + 1)) % (8 * b) = 8 * (q % b) + 1 := by
  have hr0 : 0 ≤ q % b := Int.emod_nonneg q hb.ne'
  have hrb : q % b < b := Int.emod_lt_of_pos q hb
  have hq : q = b * (q / b) + q % b := (Int.mul_ediv_add_emod q b).symm
  have key : (1 : ℤ) * (8 * q + 1) = (8 * (q % b) + 1) + (8 * b) * (q / b) := by
    conv_lhs => rw [hq]
    ring
  rw [key, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by linarith) (by linarith)

theorem not_blocks_iff {b q : ℤ} (hb : 0 < b) :
    ¬ blocks 1 (8 * q + 1) b ↔ (b ≤ 8 * (q % b) + 1 ∧ 8 * (q % b) + 1 ≤ 7 * b) := by
  unfold blocks
  rw [unit_residue hb]
  simp only [not_lt, le_min_iff]
  omega

/-- **The band implies the window, at one modulus.**  This is the whole content of
`clear_of_order6`, isolated: no homogeneity anywhere. `10 ≤ b` is needed only here. -/
theorem window_of_band {b r : ℤ} (hb : 10 ≤ b) (h1 : b - 3 ≤ 6 * r) (h2 : 6 * r ≤ 5 * b + 3) :
    b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b := by
  by_cases h14 : b ≤ 14
  · interval_cases b <;> omega
  · omega

/-- **The mixed profile theorem — no homogeneity.**  Large moduli may be met through the
`1/6` band, small moduli directly. Nothing is required of the profile's shape. -/
theorem profile_clear_mixed {bs : List ℤ} {q : ℤ}
    (hpos : ∀ b ∈ bs, 2 ≤ b)
    (hlarge : ∀ b ∈ bs, 10 ≤ b → (b - 3 ≤ 6 * (q % b) ∧ 6 * (q % b) ≤ 5 * b + 3))
    (hsmall : ∀ b ∈ bs, b < 10 → (b ≤ 8 * (q % b) + 1 ∧ 8 * (q % b) + 1 ≤ 7 * b)) :
    ∀ b ∈ bs, ¬ blocks 1 (8 * q + 1) b := by
  intro b hb
  have hb0 : (0 : ℤ) < b := by have := hpos b hb; omega
  rw [not_blocks_iff hb0]
  by_cases h10 : 10 ≤ b
  · obtain ⟨h1, h2⟩ := hlarge b hb h10
    exact window_of_band h10 h1 h2
  · exact hsmall b hb (by omega)

/-- **The `-7` opening clears a flank — with no hypothesis on sizes.**  `inWay_minus_seven`
holds for any flank; only the size form `7|d| < e` needed `|d| ≤ e`. -/
theorem flank_clear_minus_seven {ds : List ℤ} {e L : ℤ}
    (hdvd : ∀ d ∈ ds, e ∣ L * d)
    (hno : ∀ d ∈ ds, ¬ (min ((-7 * d) % (8 * e)) (8 * e - (-7 * d) % (8 * e)) < e)) :
    ∀ d ∈ ds, ¬ inWay d (8 * L - 7) e := by
  intro d hd
  unfold inWay
  obtain ⟨c, hc⟩ := hdvd d hd
  have key : d * (8 * L - 7) = -7 * d + 8 * e * c := by linear_combination 8 * hc
  rw [key, Int.add_mul_emod_self_left]
  exact hno d hd

end Derestricted

#print axioms Derestricted.window_of_band
#print axioms Derestricted.profile_clear_mixed
#print axioms Derestricted.flank_clear_minus_seven
