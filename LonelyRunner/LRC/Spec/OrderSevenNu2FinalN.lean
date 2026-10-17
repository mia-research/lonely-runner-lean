import LonelyRunner.LRC.Spec.OrderSevenHalfAN
import LonelyRunner.LRC.Spec.OrderSevenHalfBN
import LonelyRunner.LRC.Spec.OrderSevenHalfC1N
import LonelyRunner.LRC.Spec.OrderSevenHalfCP0N
import LonelyRunner.LRC.Spec.OrderSevenHalfCP1N
import LonelyRunner.LRC.Spec.OrderSevenHalfCP2N
import LonelyRunner.LRC.Spec.OrderSevenNu2N

/-!
# Order seven: every set of at most six speeds with none divisible by 343 is lonely

`lonely_nu2` instantiates `lonely_nu2_of` with the four certificates.  The instant is a 7-adic grid point
`k / 7^a`, `a ≤ 4`.
-/

namespace LRC.O7L3
open LRC.O7Grid

theorem chunkC2_all : ∀ p, p < 15 → chunkC2 p = true := by
  intro p hp
  interval_cases p
  · exact chunkC2_0
  · exact chunkC2_1
  · exact chunkC2_2
  · exact chunkC2_3
  · exact chunkC2_4
  · exact chunkC2_5
  · exact chunkC2_6
  · exact chunkC2_7
  · exact chunkC2_8
  · exact chunkC2_9
  · exact chunkC2_10
  · exact chunkC2_11
  · exact chunkC2_12
  · exact chunkC2_13
  · exact chunkC2_14

theorem lonely_nu2 {S : Finset ℕ} (hS : S.card ≤ 6) (h343 : ∀ d ∈ S, ¬ 343 ∣ d) :
    ∃ t : ℝ, ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) :=
  lonely_nu2_of chunkAH_all chunkBH_all chunkC1_ok chunkC2_all hS h343

end LRC.O7L3
