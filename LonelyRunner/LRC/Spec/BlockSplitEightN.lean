import LonelyRunner.LRC.Spec.FastPairEightN
import LonelyRunner.LRC.Spec.OrderSevenN
import LonelyRunner.LRC.ConstructionN.LemmaPass

/-!
# Order eight: the block split, a separation-of-scale rule with a common factor

2026-09-25.  Split the disparities into a core `C` and a block `F` whose members share a factor
`g`.  The block's readings repeat with period `1/g`, and order seven clears `F/g` at `1/7` somewhere
in every period.  The core is clear at `1/7` at some `τ` by order seven, and 1-Lipschitz `circDist`
keeps it clear at `1/8` on `[τ − δ, τ + δ]`, `δ = 1/(56·m)`, `m` a bound for the core.  If
`g ≥ 28·m` the window holds a whole period of the block, so some `(σ + j)/g` lies in it, and that
instant clears everything (`lonely_eight_of_block_split`).  It uses order seven only, and names the
instant: the block's own lonely instant `σ`, stepped by whole periods into the core's window.

Verified before formalising on 162 constructed `EightResidual` members
(`experiments/nN/block_split_v1.out`).  Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.BlockSplitEight

open LRC.FastPairEight

/-- **The block split.**  A nonempty core `C` of at most six, every element at most `m`; a nonempty
block `F` of at most six, every element a multiple of `g ≥ 28·m`.  Then all of them are clear at
`1/8` at one instant. -/
theorem lonely_eight_of_block_split {C F : Finset ℕ} (hCpos : ∀ c ∈ C, 0 < c) (hFpos : ∀ f ∈ F, 0 < f)
    (hCcard : C.card ≤ 6) (hFcard : F.card ≤ 6) (hne : C.Nonempty) {m g : ℕ}
    (hm : ∀ c ∈ C, c ≤ m) (hg : ∀ f ∈ F, g ∣ f) (hgm : 28 * m ≤ g) :
    ∃ t : ℝ, 0 < t ∧ (∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * t)) ∧
      ∀ f ∈ F, (8 : ℝ)⁻¹ ≤ circDist ((f : ℝ) * t) := by
  classical
  obtain ⟨c0, hc0⟩ := hne
  have hmpos : 0 < m := lt_of_lt_of_le (hCpos c0 hc0) (hm c0 hc0)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hgpos : 0 < g := by omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  have hgmR : (28 : ℝ) * m ≤ g := by exact_mod_cast hgm
  -- the core, by order seven
  obtain ⟨τ, hτ, hl⟩ := LRC.OrderSevenN.lonely_seven_nat C hCpos hCcard
  set δ : ℝ := 1 / (56 * m) with hδ
  have hτm : 1 / (7 * m) ≤ τ := by
    have h1 : (7 : ℝ)⁻¹ ≤ (c0 : ℝ) * τ := le_trans (hl c0 hc0) (circDist_le_self (by positivity))
    have h2 : (c0 : ℝ) ≤ m := by exact_mod_cast hm c0 hc0
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hδτ : δ < τ := by
    have : δ < 1 / (7 * m) := by
      rw [hδ]; exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  -- the block divided by g, by order seven
  set F' : Finset ℕ := F.image (fun f => f / g) with hF'
  have hF'pos : ∀ f' ∈ F', 0 < f' := by
    intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hf'
    exact Nat.div_pos (Nat.le_of_dvd (hFpos f hf) (hg f hf)) hgpos
  obtain ⟨σ, hσ, hσl⟩ := LRC.OrderSevenN.lonely_seven_nat F' hF'pos (le_trans Finset.card_image_le hFcard)
  -- step σ by whole periods into [τ − δ, τ − δ + 1/g]
  set j : ℤ := ⌈(τ - δ) * g - σ⌉ with hj
  set t : ℝ := (σ + j) / g with ht
  have hj1 : (τ - δ) * g - σ ≤ j := Int.le_ceil _
  have hj2 : (j : ℝ) < (τ - δ) * g - σ + 1 := Int.ceil_lt_add_one _
  have ht1 : τ - δ ≤ t := by rw [ht, le_div_iff₀ hgR]; linarith
  have ht2 : t ≤ τ + δ := by
    have hper : 1 / (g : ℝ) ≤ 2 * δ := by
      rw [hδ, div_le_iff₀ hgR]
      have : 2 * (1 / (56 * (m : ℝ))) * g = g / (28 * m) := by field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      linarith
    have : t < τ - δ + 1 / g := by
      rw [ht, div_lt_iff₀ hgR]
      have : (τ - δ + 1 / (g : ℝ)) * g = (τ - δ) * g + 1 := by field_simp
      linarith
    linarith
  refine ⟨t, by linarith, fun c hc => ?_, fun f hf => ?_⟩
  · -- the core stays clear on the window
    have hcR : (0 : ℝ) < c := by exact_mod_cast hCpos c hc
    have hcm : (c : ℝ) ≤ m := by exact_mod_cast hm c hc
    have hdist : |(c : ℝ) * t - (c : ℝ) * τ| ≤ 1 / 56 := by
      rw [← mul_sub, abs_mul, abs_of_pos hcR]
      have hts : |t - τ| ≤ δ := by rw [abs_le]; constructor <;> linarith
      calc (c : ℝ) * |t - τ| ≤ m * δ := mul_le_mul hcm hts (abs_nonneg _) hmR.le
        _ = 1 / 56 := by rw [hδ]; field_simp
    have hlip := circDist_lipschitz.dist_le_mul ((c : ℝ) * t) ((c : ℝ) * τ)
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    have h7 := hl c hc
    have := (abs_sub_le_iff.mp hlip).2
    norm_num at h7 ⊢
    linarith
  · -- each block runner reads its quotient's reading at σ, shifted by an integer
    obtain ⟨q, hq⟩ := hg f hf
    have hq' : q ∈ F' := Finset.mem_image.mpr ⟨f, hf, by rw [hq, Nat.mul_div_cancel_left q hgpos]⟩
    have hread : (f : ℝ) * t = (q : ℝ) * σ + ((q : ℤ) * j : ℤ) := by
      rw [ht, hq]; push_cast; field_simp
    rw [hread, ConstructionN.circDist_add_int]
    exact le_trans (by norm_num) (hσl q hq')

end LRC.BlockSplitEight
