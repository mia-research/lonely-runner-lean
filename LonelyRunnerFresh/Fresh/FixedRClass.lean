import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissibleFlank

/-!
# Isolation at a fixed rational instant of the subject's own `d_min`

Written 2026-10-25.  New file.  Worklist tags: A03 (direct isolation), A08 (closed edges), G01 (distributed readings), and the first-step classes K0 and K1 of E325 in their finite-list form.
`FixedRClass a b v k` (for natural `a, b` with `1 ≤ b`): `t = a/(b d_min)`, i.e. `R = 8 d_min t = 8a/b`, clears every disparity.  The instant is fixed by the arrangement (`d_min`) and a finite list of pairs `(a, b)`; the class is an
inequality system on the readings, with a fixed proof.  `FixedRList v k` is the union over `b ≤ 12`, `a ≤ 8 b`.  Unlike `NearMultiplesClass` (free unit), the list is finite, so this is a type in the sense of the programme; its membership is a
finite check on `v`.  `ProvedTypesR` (new file) extends `ProvedTypes` by it, so the remainder after all types excludes the arrangements clear at one of the listed instants.  Grade [L].
Survey (E636, `candidate_R_cover_v1.py`): a short list of such instants covers most of the sampler output; the structured arrangements with long cascades are the remainder.
-/

open Classical

namespace Fresh.FixedRClass

open Fresh Fresh.Admissible Fresh.AdmissibleFlank

-- STANDING: DEFINITION
def FixedRClass (a b : ℕ) (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ m : ℝ, IsLeast (disparitySet v k : Set ℝ) m ∧ 0 < m ∧ ∀ d ∈ disparitySet v k, (1 / 8 : ℝ) ≤ distInt (d * ((a : ℝ) / ((b : ℝ) * m)))

-- STANDING: DEFINITION
def FixedRList (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ b ≤ 12 ∧ a ≤ 8 * b ∧ FixedRClass a b v k

theorem fixedR_isolation {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {v : Fin 8 → ℝ} {k : Fin 8} (h : FixedRClass a b v k) : Isolation v k := by
  obtain ⟨m, _, hm0, hcl⟩ := h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨(a : ℝ) / ((b : ℝ) * m), by positivity, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  exact hcl

theorem fixedRList_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : FixedRList v k) : Isolation v k := by
  obtain ⟨a, b, ha, hb, _, _, hc⟩ := h
  exact fixedR_isolation ha hb hc

#print axioms fixedR_isolation
#print axioms fixedRList_isolation

end Fresh.FixedRClass
