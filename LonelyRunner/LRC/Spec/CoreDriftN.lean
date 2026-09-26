import LonelyRunner.LRC.Spec.Order8SkeletonN
import LonelyRunner.LRC.Cascade.Together

/-!
# The core drift bound: relay links and near-progression blocks, band by band

2026-09-26 (proof plan WP3, item 2, part 1; running log E59, E64).  A blocked stretch of a block is a relay across the
clear bands of its slowest runner `d₁`.  Over one band (one lap of `d₁`) every runner advances a whole number of its own
laps plus a deviation from the progression at scale `d₁`.  Two statements, both exact:

* **Link persistence** (`link_offset`, `link_persistence`).  A setter at speed `d` landing at `t_b = (M + b n + 1/8)/d`
  (one landing per band `b`) leaves the next runner `d′` offset from its lap line `M′ + b n′` by exactly
  `o + b η`, with `o = d′(M + 1/8)/d − M′` and `η = n d′/d − n′`: linear in `b`.  If the link holds at `b = 0`
  (`|o| < 1/8`) and at `b`, then `|b| |η| < 1/4`.  A link lasts fewer than `1/(4|η|)` bands either side.
* **Block persistence** (`block_persists`).  If every reading `d` of a block is within `ε` of a whole multiple of `d₁`
  (`|d/d₁ − n_d| ≤ ε`) and the block is clear at `τ` with margin `μ` (every reading at least `1/8 + μ`), the block is
  clear at `τ + b/d₁` for every whole `b` with `|b| ε ≤ μ`: a near-progression core has a clear instant in every band
  for `μ/ε` bands.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.CoreDrift

/-- **The offset of the next runner is linear in the band.** -/
theorem link_offset (d d' M n M' n' b : ℝ) (hd : d ≠ 0) :
    d' * ((M + b * n + 1 / 8) / d) - (M' + b * n') =
      (d' * ((M + 1 / 8) / d) - M') + b * (n * d' / d - n') := by
  field_simp; ring

/-- **A link lasts fewer than `1/(4|η|)` bands.**  If the offset is inside the zone at band `0` and at band `b`, then
`|b| |η| < 1/4`. -/
theorem link_persistence {o η b : ℝ} (h0 : |o| < 1 / 8) (hb : |o + b * η| < 1 / 8) : |b| * |η| < 1 / 4 := by
  have : |b * η| ≤ |o + b * η| + |o| := by
    have := abs_sub (o + b * η) o
    simpa using this
  rw [abs_mul] at this; linarith

/-- The drift of a link in terms of the deviations from the progression at scale `d₁`. -/
theorem link_drift_eq (d1 n n' ε ε' : ℝ) (h : n + ε ≠ 0) (hd1 : d1 ≠ 0) :
    n * ((n' + ε') * d1) / ((n + ε) * d1) - n' = (n * ε' - n' * ε) / (n + ε) := by
  field_simp; ring

/-- **Block persistence.**  A block within `ε` of the progression at scale `d₁`, clear at `τ` with margin `μ`, stays
clear at `τ + b/d₁` whenever `|b| ε ≤ μ`. -/
theorem block_persists {F : Finset ℝ} {d1 τ μ ε : ℝ} (hd1 : 0 < d1)
    (hlon : ∀ d ∈ F, (8 : ℝ)⁻¹ + μ ≤ circDist (d * τ))
    (hdev : ∀ d ∈ F, ∃ n : ℤ, |d / d1 - n| ≤ ε) {b : ℤ} (hb : |(b : ℝ)| * ε ≤ μ) :
    ∀ d ∈ F, (8 : ℝ)⁻¹ ≤ circDist (d * (τ + b / d1)) := by
  intro d hd
  obtain ⟨n, hn⟩ := hdev d hd
  have e : d * (τ + b / d1) = (d * τ + (b : ℝ) * (d / d1 - n)) + ((b * n : ℤ) : ℝ) := by
    push_cast; field_simp; ring
  rw [e, ConstructionN.circDist_add_int]
  have hlip := circDist_lipschitz.dist_le_mul (d * τ + (b : ℝ) * (d / d1 - n)) (d * τ)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, add_sub_cancel_left] at hlip
  have hsmall : |(b : ℝ) * (d / d1 - n)| ≤ μ := by
    rw [abs_mul]
    calc |(b : ℝ)| * |d / d1 - n| ≤ |(b : ℝ)| * ε := mul_le_mul_of_nonneg_left hn (abs_nonneg _)
      _ ≤ μ := hb
  have := (abs_sub_le_iff.mp hlip).2
  have := hlon d hd
  linarith

/-- **A mover cannot patch the same gap in two consecutive bands if its phase moves by more than a quarter lap.**  If
its phase `φ` is within `1/8` of a lap line `a` in one band and `φ + ρ` is within `1/8` of it in the next, then
`circDist ρ < 1/4`.  Contrapositive: a mover whose deviation from the progression at scale `d₁` is more than `1/4` of a
lap from a whole number never patches a fixed gap in two consecutive bands. -/
theorem mover_consecutive {φ ρ a : ℝ} (h0 : circDist (φ - a) < 1 / 8) (h1 : circDist (φ + ρ - a) < 1 / 8) :
    circDist ρ < 1 / 4 := by
  have e : ρ = (φ + ρ - a) - (φ - a) := by ring
  rw [e]
  have := Together.circDist_sub_le (φ + ρ - a) (φ - a)
  linarith

end LRC.CoreDrift
