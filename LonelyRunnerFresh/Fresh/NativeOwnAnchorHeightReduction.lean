import Fresh.NativeMixedObserverGridSeeds

/-! A supplied rational own boundary reduces an independent grid height
modulo its numerator. The period depends on the unbounded anchor. Reduced
reading sets may coalesce, so this is native disparity-set equivalence,
not a claim that every reduced tuple is an injective physical arrangement.
Outside the V81 audit/root; pending substantive next integration. -/
namespace Fresh.NativeOwnAnchorHeightReduction
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

theorem positions (d b q V F : ℝ) (K P Q M j : ℤ)
    (hd : 0<d) (hdV : d*V=(K : ℝ))
    (hbV : (Q : ℝ)*(b*V)=(P : ℝ)) (hbF : b*F=(M : ℝ)+1/8) :
    (q+8*(j : ℝ)*(P : ℝ)*d)*V=q*V+(8*j*P*K : ℤ) ∧
    (q+8*(j : ℝ)*(P : ℝ)*d)*(V+1/(8*d))=
      q*(V+1/(8*d))+(j*P*(8*K+1) : ℤ) ∧
    (q+8*(j : ℝ)*(P : ℝ)*d)*F=q*F+(j*Q*K*(8*M+1) : ℤ) := by
  have hW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  have hratio := Fresh.NativeTwoAnchorGridTransport.own_ratio b V F P Q M hbV hbF
  have hDF : 8*(P : ℝ)*(d*F)=(Q : ℝ)*(8*(M : ℝ)+1)*(K : ℝ) := by
    have hh := congrArg (fun x : ℝ=>d*x) hratio
    calc
      _ = d*(8*(P : ℝ)*F) := by ring
      _ = d*((Q : ℝ)*(8*(M : ℝ)+1)*V) := hh
      _ = (Q : ℝ)*(8*(M : ℝ)+1)*(d*V) := by ring
      _ = _ := by rw [hdV]
  constructor
  · calc
      _ = q*V+8*(j : ℝ)*(P : ℝ)*(d*V) := by ring
      _ = _ := by rw [hdV]; push_cast; ring
  constructor
  · calc
      _ = q*(V+1/(8*d))+8*(j : ℝ)*(P : ℝ)*(d*(V+1/(8*d))) := by ring
      _ = _ := by rw [hW]; push_cast; ring
  · calc
      _ = q*F+(j : ℝ)*(8*(P : ℝ)*(d*F)) := by ring
      _ = _ := by rw [hDF]; push_cast; ring

theorem height_reduction (d q q0 V alpha : ℝ) (K P H : ℤ)
    (hV : 0<V) (hdV : d*V=(K : ℝ))
    (hq : q*V=8*(H : ℝ)*(K : ℝ)+alpha)
    (hq0 : q0*V=8*((H%P : ℤ) : ℝ)*(K : ℝ)+alpha) :
    q=q0+8*((H/P : ℤ) : ℝ)*(P : ℝ)*d := by
  have hid : (H : ℝ)=((H%P : ℤ) : ℝ)+(P : ℝ)*((H/P : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv H P).symm
  have hh : (q0+8*((H/P : ℤ) : ℝ)*(P : ℝ)*d)*V=q*V := by
    calc
      _ = q0*V+8*((H/P : ℤ) : ℝ)*(P : ℝ)*(d*V) := by ring
      _ = _ := by rw [hq0,hdV,hq,hid]; ring
  exact (mul_right_cancel₀ hV.ne' hh).symm

theorem lonely_insert_equiv (ds : Finset ℝ) (d b q q0 V F alpha : ℝ) (K P Q M H : ℤ)
    (hd : 0<d) (hV : 0<V) (hdV : d*V=(K : ℝ))
    (hbV : (Q : ℝ)*(b*V)=(P : ℝ)) (hbF : b*F=(M : ℝ)+1/8)
    (hq : q*V=8*(H : ℝ)*(K : ℝ)+alpha)
    (hq0 : q0*V=8*((H%P : ℤ) : ℝ)*(K : ℝ)+alpha) :
    LonelyAt (insert q ds) F ↔ LonelyAt (insert q0 ds) F := by
  classical
  have he := height_reduction d q q0 V alpha K P H hV hdV hq hq0
  have hp := (positions d b q0 V F K P Q M (H/P) hd hdV hbV hbF).2.2
  have hdist : distInt (q*F)=distInt (q0*F) := by
    rw [he,hp,distInt_add_int]
  constructor
  · intro h x hx
    rcases Finset.mem_insert.mp hx with he|hx
    · subst x
      rw [←hdist]
      exact h q (Finset.mem_insert_self _ _)
    · exact h x (Finset.mem_insert_of_mem hx)
  · intro h x hx
    rcases Finset.mem_insert.mp hx with he|hx
    · subst x
      rw [hdist]
      exact h q0 (Finset.mem_insert_self _ _)
    · exact h x (Finset.mem_insert_of_mem hx)

theorem residue_range (H P : ℤ) (hP : 0<P) : 0 ≤ H%P ∧ H%P<P :=
  ⟨Int.emod_nonneg H (by omega),Int.emod_lt_of_pos H hP⟩

theorem reduced_positive (q0 V alpha : ℝ) (H P K : ℤ)
    (hP : 0<P) (hK : 0 ≤ K) (hV : 0<V) (halpha : 0<alpha)
    (hrep : q0*V=8*((H%P : ℤ) : ℝ)*(K : ℝ)+alpha) : 0<q0 := by
  have hrem : (0 : ℝ) ≤ ((H%P : ℤ) : ℝ) := by exact_mod_cast (residue_range H P hP).1
  have hKr : (0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hh := mul_nonneg hrem hKr
  by_contra hn
  have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hV.le
  nlinarith only [hrep,hh,halpha,hm]

#print axioms residue_range
#print axioms reduced_positive

#print axioms positions
#print axioms height_reduction
#print axioms lonely_insert_equiv
end Fresh.NativeOwnAnchorHeightReduction
