import Mathlib.Tactic
import Fresh.WidthCert
import Fresh.WidthClosed_0
import Fresh.WidthClosed_1
import Fresh.WidthClosed_2
import Fresh.WidthClosed_3
import Fresh.WidthClosed_4
import Fresh.WidthClosed_5
import Fresh.WidthClosed_6
import Fresh.WidthClosed_7

/-!
# The width-closed certificates: connecting the width facts to the column-death certificates

The 7,797 per-class width facts (`wfact_k : 2/25 ≤ B_k − A_k`) consumed by
`Fresh.WidthCert.colDead50_of_width` give the per-class column-death certificates
in closed form.  The composition is one application per class — the certificates
are arithmetic consequences of the component geometry, independent of probe sampling.
-/

namespace Fresh.WidthClosedCert

/-- **The general composition.**  Any component with width ≥ 2/25 and positive edges
is column-dead over [25,50): this is `colDead50_of_width` applied to the width fact. -/
theorem width_closed_cert (A B : ℚ) (hA : 0 < A) (hB : 0 < B)
    (hw : (2:ℚ) / 25 ≤ B - A) :
    ∀ s : ℚ, 25 ≤ s → s < 50 → ∀ j : ℕ,
      ¬ ((8 * (j:ℚ) - 1) / A ≤ s ∧ s < (8 * (j:ℚ) + 1) / B) :=
  Fresh.WidthCert.colDead50_of_width ⟨A, B⟩ hA hB hw

/-- **Worked instance: class 0** — A = 5/3, B = 5/4, width = 5/4 − 5/3 = 5/12 ≥ 2/25. -/
theorem cert_0 :
    ∀ s : ℚ, 25 ≤ s → s < 50 → ∀ j : ℕ,
      ¬ ((8 * (j:ℚ) - 1) / ((5:ℚ)/4) ≤ s ∧ s < (8 * (j:ℚ) + 1) / ((5:ℚ)/3)) := by
  have hA : (0:ℚ) < (5:ℚ)/4 := by norm_num
  have hB : (0:ℚ) < (5:ℚ)/3 := by norm_num
  have hw := Fresh.WidthClosed.wfact_0
  exact width_closed_cert ((5:ℚ)/4) ((5:ℚ)/3) hA hB hw

/-- **Worked instance: class 1** — A = 5/3, B = 45/37. -/
theorem cert_1 :
    ∀ s : ℚ, 25 ≤ s → s < 50 → ∀ j : ℕ,
      ¬ ((8 * (j:ℚ) - 1) / ((45:ℚ)/37) ≤ s ∧ s < (8 * (j:ℚ) + 1) / ((5:ℚ)/3)) := by
  have hA : (0:ℚ) < (45:ℚ)/37 := by norm_num
  have hB : (0:ℚ) < (5:ℚ)/3 := by norm_num
  have hw := Fresh.WidthClosed.wfact_1
  exact width_closed_cert ((45:ℚ)/37) ((5:ℚ)/3) hA hB hw

#print axioms Fresh.WidthClosedCert.width_closed_cert
#print axioms Fresh.WidthClosedCert.cert_0
#print axioms Fresh.WidthClosedCert.cert_1

end Fresh.WidthClosedCert
