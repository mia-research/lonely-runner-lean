import Fresh.BandNoCarve

namespace Fresh.TransferChecks

open Fresh.BandNoCarve

/-- E827's X24 vector supplies a second-window certificate to the corrected assembly. -/
theorem x24_w1 :
    BandW1 ![1, 2767 / 1000, 749 / 200, 957 / 200, 123 / 20, 683 / 100, 11889 / 500] := by
  refine ⟨6500 / 683, by norm_num, by norm_num, ?_⟩
  intro i
  let gaps : Fin 7 → ℤ := ![1, 3, 4, 5, 7, 8, 28]
  refine ⟨gaps i, ?_⟩
  fin_cases i <;> norm_num [gaps, Set.mem_Icc, Matrix.cons_val_zero, Matrix.cons_val_succ]

#print axioms x24_w1
#print axioms Fresh.BandNoCarve.filterAssembly_of_bandData

end Fresh.TransferChecks
