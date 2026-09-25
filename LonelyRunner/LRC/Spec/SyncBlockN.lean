import LonelyRunner.LRC.Spec.FastPairEightN
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# The synchronised block: a fast block's common phase is a free shift

2026-09-25.  A block of runners `N + e`, `e ∈ E`, `0 ≤ e ≤ Emax`, moves together at rate `N` while
its internal spread `e·t` changes slowly.  Over one full turn `[t₀, t₀ + 1/N]` of the common phase,
each offset moves by at most `Emax/N`.  So if a point `y` lies at distance at least `1/8 + Emax/N`
from every offset `e·t₀`, the instant at which the common phase reads `−y` clears the whole block
(`sync_block`).  The instant is named: `t₀ + fract(−y − N·t₀)/N`.  With a core clear on the same
turn, everything is clear (`lonely_of_sync_block`).

Fast blocks of five or six nearly synchronised runners have no window rule
(`experiments/nN/robust_window_v1.out`); this rule reduces them to an `N`-free question on the core
and the offsets: is there `t₀` inside the core's clear set with the offsets `{e·t₀}` leaving a gap
wider than `1/4`?  That question holds in all 288,288 cases with speeds in `[1,16]`
(`experiments/nN/sync_block_v2.out`) and is **not** proved here.

Real speeds, any block size.  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.SyncBlock

/-- **The block's common phase is a free shift.**  If `y` is at distance at least `1/8 + Emax/N` from
every offset `e·t₀`, the named instant `t₀ + fract(−y − N·t₀)/N`, inside `[t₀, t₀ + 1/N)`, clears
every block runner `N + e`. -/
theorem sync_block {E : Finset ℝ} {N t₀ y Emax : ℝ} (hN : 0 < N) (he0 : ∀ e ∈ E, 0 ≤ e)
    (heM : ∀ e ∈ E, e ≤ Emax) (hy : ∀ e ∈ E, (8 : ℝ)⁻¹ + Emax / N ≤ circDist (y - e * t₀)) :
    let t := t₀ + Int.fract (-y - N * t₀) / N
    t₀ ≤ t ∧ t < t₀ + 1 / N ∧ ∀ e ∈ E, (8 : ℝ)⁻¹ ≤ circDist ((N + e) * t) := by
  intro t
  set s := Int.fract (-y - N * t₀) with hs
  have hs0 : 0 ≤ s := Int.fract_nonneg _
  have hs1 : s < 1 := Int.fract_lt_one _
  refine ⟨?_, ?_, fun e he => ?_⟩
  · have : 0 ≤ s / N := div_nonneg hs0 hN.le
    show t₀ ≤ t₀ + s / N; linarith
  · show t₀ + s / N < t₀ + 1 / N
    have : s / N < 1 / N := div_lt_div_of_pos_right hs1 hN
    linarith
  · -- (N + e)·t = −(y − e t₀) + e s/N − k, k = ⌊−y − N t₀⌋
    set k : ℤ := ⌊-y - N * t₀⌋ with hk
    have hfr : s = (-y - N * t₀) - k := by rw [hs, hk, Int.fract]
    have hread : (N + e) * t = (-(y - e * t₀) + e * s / N) + ((-k : ℤ) : ℝ) := by
      show (N + e) * (t₀ + s / N) = _
      rw [hfr]; push_cast; field_simp; ring
    rw [hread, ConstructionN.circDist_add_int]
    have hlip := circDist_lipschitz.dist_le_mul (-(y - e * t₀) + e * s / N) (-(y - e * t₀))
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    have hsmall : |(-(y - e * t₀) + e * s / N) - (-(y - e * t₀))| ≤ Emax / N := by
      rw [show (-(y - e * t₀) + e * s / N) - (-(y - e * t₀)) = e * s / N by ring,
        abs_of_nonneg (by have := he0 e he; positivity)]
      rw [div_le_div_iff_of_pos_right hN]
      calc e * s ≤ Emax * 1 := mul_le_mul (heM e he) hs1.le hs0 (le_trans (he0 e he) (heM e he))
        _ = Emax := mul_one _
    have hneg : circDist (-(y - e * t₀)) = circDist (y - e * t₀) := by
      rw [show -(y - e * t₀) = -1 * (y - e * t₀) by ring]
      have := circDist.symm_neg (y - e * t₀)
      simpa using this
    have h1 := hy e he
    have h2 := (abs_sub_le_iff.mp hlip).2
    rw [hneg] at h2
    linarith

/-- **A core and a synchronised block, clear together.**  If the core is clear at `1/8` throughout
the turn `[t₀, t₀ + 1/N]`, and some `y` is at distance at least `1/8 + Emax/N` from every offset
`e·t₀`, the subject is lonely at a named instant of that turn. -/
theorem lonely_of_sync_block {C E : Finset ℝ} {N t₀ y Emax : ℝ} (hN : 0 < N) (ht₀ : 0 ≤ t₀)
    (he0 : ∀ e ∈ E, 0 ≤ e) (heM : ∀ e ∈ E, e ≤ Emax)
    (hC : ∀ c ∈ C, ∀ t, t₀ ≤ t → t ≤ t₀ + 1 / N → (8 : ℝ)⁻¹ ≤ circDist (c * t))
    (hy : ∀ e ∈ E, (8 : ℝ)⁻¹ + Emax / N ≤ circDist (y - e * t₀)) :
    ∃ t : ℝ, t₀ ≤ t ∧ t ≤ t₀ + 1 / N ∧ (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist (c * t)) ∧
      ∀ e ∈ E, (8 : ℝ)⁻¹ ≤ circDist ((N + e) * t) := by
  obtain ⟨h1, h2, h3⟩ := sync_block (E := E) (y := y) hN he0 heM hy
  exact ⟨_, h1, h2.le, fun c hc => hC c hc _ h1 h2.le, h3⟩

end LRC.SyncBlock
