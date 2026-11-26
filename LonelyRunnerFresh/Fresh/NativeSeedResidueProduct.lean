import Fresh.NativePositivePointCanonical
import Fresh.NativeOwnAnchorHeightReduction

/-! Independent products of the seven native seed residues need no named
own-anchor coordinate. Existing localisation converts the transported
positive isolated point to a canonical boundary certificate. All integer
lifts are independent and signed, subject to actual physical admissibility. -/
namespace Fresh.NativeSeedResidueProduct
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (z : Fin 4) (f : Fin 8 → Fin 7) (j : Fin 8 → ℤ),
    ∀ i : Fin 8,i≠k → reading v k i=
      Fresh.NativeMixedObserverGridSeeds.base z (f i)+Fresh.NativeMixedObserverGridSeeds.step z*(j i : ℝ)

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    CanonicalReturnClass v k := by
  obtain ⟨hv,z,f,j,hr⟩ := h
  have hp := Fresh.NativeMixedObserverGridSeeds.class_point z f j hr
  have hF := (Fresh.NativeMixedObserverGridSeeds.parameter_faces z).2.2.2.2.2.2.2
  exact Fresh.NativePositivePointCanonical.positive_point hv k _ hF hp

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

theorem seed_class_into_product {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeMixedObserverGridSeeds.Class v k) : Class v k := by
  obtain ⟨hv,z,g,f,j,_hg,_hfg,_hj,hr⟩ := h
  exact ⟨hv,z,f,j,hr⟩

#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
#print axioms seed_class_into_product
end Fresh.NativeSeedResidueProduct
