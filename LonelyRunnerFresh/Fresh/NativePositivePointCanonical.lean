import Fresh.NativeMixedObserverGridSeeds

/-! Existing native localisation supplies an own boundary for any positive
isolated point. A positive interior predecessor also handles own label zero.
This is a certificate conversion, not an existence or exhaustion theorem.
Outside the V81 audit/root, pending the next physical-family integration. -/
namespace Fresh.NativePositivePointCanonical
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

theorem anchored_nonnegative {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k a : Fin 8) (E : ℝ) (L : ℤ) (ha : a≠k) (hL : 0 ≤ L)
    (ho : reading v k a*E=(L : ℝ)+1/8) (hpoint : IsolatedAt v k E) :
    CanonicalReturnClass v k := by
  have hd : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hLr : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  let Q := ((L : ℝ)+1/16)/reading v k a
  have hQ : 0<Q := div_pos (by linarith only [hLr]) hd
  have hphase : reading v k a*Q=(L : ℝ)+1/16 := by dsimp [Q]; field_simp
  have habs : |reading v k a*Q-(L : ℝ)|<1/8 := by rw [hphase]; norm_num
  have hcap : InWay (reading v k a) Q := lt_of_le_of_lt (Fresh.Cascade.distInt_le _ _) habs
  have hn : nextOpening (reading v k a) Q=E := by
    rw [nextOpening_eq habs]
    apply (div_eq_iff hd.ne').2
    nlinarith only [ho]
  have hQE : Q<E := by have hh := lt_nextOpening hd hcap; rw [hn] at hh; exact hh
  have hm : IsMove (disparitySet v k) Q E := by
    refine Or.inr ⟨reading v k a,mem_disparitySet.mpr ⟨a,ha,rfl⟩,hcap,hn.symm,?_⟩
    intro d hd' hwd
    exact nextOpening_le_of_lonely (disparitySet_pos hv k)
      ((isolatedAt_iff_lonelyAt v k E).1 hpoint) hQE.le hd' hwd
  exact Fresh.NativeFixedPrefixArrangement.canonical_of_isolating_move hv k Q E hQ hQE hm hpoint

theorem positive_point {v : Fin 8 → ℝ} (hv : IsArrangement v)
    (k : Fin 8) (F : ℝ) (hF : 0<F) (hpoint : IsolatedAt v k F) :
    CanonicalReturnClass v k := by
  obtain ⟨e,he,n,hn⟩ := Fresh.Localisation.exists_opening_of_lonely
    (disparitySet_pos hv k) (disparitySet_nonempty v k) hF
    ((isolatedAt_iff_lonelyAt v k F).1 hpoint)
  obtain ⟨a,ha,rfl⟩ := mem_disparitySet.mp he
  have hd : 0<reading v k a := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hown : reading v k a*(((n : ℝ)+1/8)/reading v k a)=((n : ℤ) : ℝ)+1/8 := by
    push_cast
    field_simp
  exact anchored_nonnegative hv k a _ (n : ℤ) ha (by exact_mod_cast Nat.zero_le n) hown
    ((isolatedAt_iff_lonelyAt v k _).2 hn)

theorem isolation_iff_canonical {v : Fin 8 → ℝ} (hv : IsArrangement v) (k : Fin 8) :
    Isolation v k ↔ CanonicalReturnClass v k := by
  constructor
  · rintro ⟨F,hF,hpoint⟩
    exact positive_point hv k F hF hpoint
  · exact canonical_isolation

#print axioms anchored_nonnegative
#print axioms positive_point
#print axioms isolation_iff_canonical
end Fresh.NativePositivePointCanonical
