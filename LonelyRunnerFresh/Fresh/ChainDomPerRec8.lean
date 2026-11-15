import Fresh.ChainDomPerRecBox1
import Fresh.ChainDomPerRecBox2
import Fresh.ChainDomPerRecBox3
import Fresh.ChainDomPerRecBox4
import Fresh.ChainDomPerRecBox5
import Fresh.ChainDomPerRecBox6
import Fresh.ChainDomPerRecBox7
import Fresh.ChainDomPerRecBox8

namespace Fresh.ChainDomPerRec8

open Fresh.ChainDomBase Fresh.CapChainsOfCarve Fresh.JoinFamComposed Fresh.OneSidedComposed Fresh.OneSidedGlue
  Fresh.UClosure Fresh.SpineSound Fresh.FilterAssembly Fresh.DumpDomData

-- the 49-point `fin_cases` checks and the big literal tables need headroom
set_option maxHeartbeats 10000000

/-- The eight strict boxes whose per-record attestations use the full closure
as their start table. The three distinct sparse-start boxes are in
`Fresh.ChainDomData`. -/
def perRec8Boxes : Finset (Fin 7 → ℤ) :=
  {(![1, 3, 4, 5, 5, 5, 7] : Fin 7 → ℤ),
   (![1, 3, 4, 5, 7, 7, 9] : Fin 7 → ℤ),
   (![1, 4, 5, 5, 5, 6, 7] : Fin 7 → ℤ),
   (![1, 4, 5, 5, 6, 7, 9] : Fin 7 → ℤ),
   (![1, 4, 5, 6, 6, 7, 8] : Fin 7 → ℤ),
   (![1, 5, 5, 5, 6, 7, 8] : Fin 7 → ℤ),
   (![1, 5, 5, 6, 6, 7, 8] : Fin 7 → ℤ),
   (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ)}

/-- Each transcribed record has an attesting chain from its full-closure
start. Realization by an arrangement is a separate premise of the consumer. -/
def chainDomPerRecord8Data : Prop :=
  ∀ b ∈ perRec8Boxes, ChainDomPerRecord8 b (dumpFamOf b)

theorem chainDomPerRecord8_data : chainDomPerRecord8Data := by
  intro b hb
  simp only [perRec8Boxes, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [dumpFamOf, chainDomPerRecord8_1_3_4_5_5_5_7]
  · simp [dumpFamOf, chainDomPerRecord8_1_3_4_5_7_7_9]
  · simp [dumpFamOf, chainDomPerRecord8_1_4_5_5_5_6_7]
  · simp [dumpFamOf, chainDomPerRecord8_1_4_5_5_6_7_9]
  · simp [dumpFamOf, chainDomPerRecord8_1_4_5_6_6_7_8]
  · simp [dumpFamOf, chainDomPerRecord8_1_5_5_5_6_7_8]
  · simp [dumpFamOf, chainDomPerRecord8_1_5_5_6_6_7_8]
  · simp [dumpFamOf, chainDomPerRecord8_1_5_5_6_7_8_8]

#print axioms chainDomPerRecord8_data

end Fresh.ChainDomPerRec8
