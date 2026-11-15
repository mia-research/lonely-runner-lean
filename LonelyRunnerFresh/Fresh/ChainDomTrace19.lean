import Fresh.ChainDomBase

namespace Fresh.ChainDomBase

open Fresh.UClosure Fresh.DumpDomData

/-- Replay one certified transition before exposing the next chain step. -/
theorem chainRun_step_some {U V : UTable} {a b : Fin 7} {Aex entry exit : ℚ}
    (h : uStep U a b Aex entry exit = some V) (rest : List Step) :
    chainRun U a Aex (⟨b, entry, exit⟩ :: rest) = chainRun V b exit rest := by
  simp only [chainRun, h, Option.bind_some]

theorem chainRun_nil (U : UTable) (a : Fin 7) (Aex : ℚ) :
    chainRun U a Aex [] = some (U,a,Aex) := rfl

/-- The certified nineteen-step trace ends at its recorded table. -/
theorem trace_1_3_4_4_5_5_7 {V : UTable} {af : Fin 7} {Af : ℚ}
    (hrun : chainRun (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) 0 1 steps_1_3_4_4_5_5_7 =
      some (V, af, Af)) : V = T_1_3_4_4_5_5_7_26 := by
  simp only [steps_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_1_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_2_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_3_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_4_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_5_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_6_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_7_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_8_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_9_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_10_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_11_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_12_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_13_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_14_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_15_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_16_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_17_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_18_1_3_4_4_5_5_7,
    chainRun_step_some stepEq_19_1_3_4_4_5_5_7,
    chainRun_nil, Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

#print axioms trace_1_3_4_4_5_5_7

end Fresh.ChainDomBase
