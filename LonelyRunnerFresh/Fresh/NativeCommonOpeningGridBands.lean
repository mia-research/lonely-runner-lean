import Fresh.NativeUpperGridHeightTransport
import Fresh.NativeSeedResidueProduct

/-! A common native AP/grid opening carries independent unbounded cosets.
Quiet entry bands are initial data; their endpoint clearance is derived
from the actual integer-to-minimum opening displacement. Outside V82 audit.
-/
namespace Fresh.NativeCommonOpeningGridBands
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeThirdReaderRetention Fresh.NativeOpeningReversal Fresh.NativeOneReaderDeformation Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention Fresh.NativeUpperGridPacket
  Fresh.NativeUpperGridHeightTransport

theorem first_displacement (d p V : ℝ) (K H : ℤ) (hd : 0<d) (hp : 0<p)
    (hK : 1 ≤ K) (hH : 1 ≤ H) (hdV : d*V=(K : ℝ))
    (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8) :
    0<labelledOpening p (V+1/(8*d))-V ∧
      d*(labelledOpening p (V+1/(8*d))-V)<5/32 := by
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  have hfast := upper_fast d p V K H hd hK hH hdV hpV
  have hc := (upper_return d p V K H hd hK hdV hpV).2.2.1
  have hstep := captured_labelled_advance p W hp hc
  have hb := mul_le_mul_of_nonneg_right hfast hstep.1.le
  have hW : 0<1/(8*d) := by positivity
  have hi : d*(1/(8*d))=1/8 := by field_simp
  change 0<Z-V ∧ d*(Z-V)<5/32
  change 0<Z-W ∧ p*(Z-W)<1/4 at hstep
  change 8*d*(Z-W) ≤ p*(Z-W) at hb
  dsimp [W] at hstep hb
  constructor <;> nlinarith only [hstep.1,hstep.2,hb,hW,hi]

theorem quiet_window (d p q V : ℝ) (K H : ℤ)
    (hd : 0<d) (hp : 0<p) (hV : 0<V) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8)
    (hqlo : 1/8 ≤ q*V) (hqhi : q*V ≤ 3/4) :
    1/8 ≤ q*labelledOpening p (V+1/(8*d)) ∧
      q*labelledOpening p (V+1/(8*d))<7/8 := by
  have ht := first_displacement d p V K H hd hp hK hH hdV hpV
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hq : 0<q := by nlinarith only [hqlo,hV]
  have hqd : 4*q ≤ 3*d := by
    by_contra hn
    have hh := mul_pos (sub_pos.mpr (lt_of_not_ge hn)) hV
    nlinarith only [hh,hqhi,hdV,hKr]
  have hlo := mul_nonneg hq.le ht.1.le
  have hhi := mul_le_mul_of_nonneg_right hqd ht.1.le
  constructor <;> nlinarith only [hlo,hhi,hqlo,hqhi,ht.2]

theorem coset_clear (d p q V : ℝ) (K H j : ℤ)
    (hd : 0<d) (hp : 0<p) (hV : 0<V) (hK : 1 ≤ K) (hH : 1 ≤ H)
    (hdV : d*V=(K : ℝ)) (hpV : p*V=8*(H : ℝ)*(K : ℝ)+7/8)
    (hq : q=p ∨ (1/8 ≤ q*V ∧ q*V ≤ 3/4)) :
    1/8 ≤ distInt ((q+8*(j : ℝ)*(period K H : ℝ)*d)*labelledOpening p (V+1/(8*d))) := by
  rw [(height_shifts d p q V K H j hd hp hK hdV hpV).2.2,distInt_add_int]
  rcases hq with he|hq
  · rw [he]
    have ho := labelled_opening_identity p (V+1/(8*d)) hp
    exact clear_of_window _ ho.ge (by linarith only [ho])
  · have hw := quiet_window d p q V K H hd hp hV hK hH hdV hpV hq.1 hq.2
    exact clear_of_window 0 (by simpa using hw.1) (by simpa using hw.2.le)

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (V : ℝ) (u a : Fin 8) (K H : ℤ),
    u≠k ∧ a≠k ∧ 1 ≤ K ∧ 1 ≤ H ∧
    reading v k u*V=(K : ℝ) ∧ reading v k a*V=8*(H : ℝ)*(K : ℝ)+7/8 ∧
    ∀ i : Fin 8,i≠k → reading v k i=reading v k u ∨ ∃ (q : ℝ) (j : ℤ),
      (q=reading v k a ∨ (1/8 ≤ q*V ∧ q*V ≤ 3/4)) ∧
      reading v k i=q+8*(j : ℝ)*(period K H : ℝ)*reading v k u

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    CanonicalReturnClass v k := by
  obtain ⟨hv,V,u,a,K,H,hu,ha,hK,hH,hdV,hpV,hread⟩ := h
  let d := reading v k u
  let p := reading v k a
  let W := V+1/(8*d)
  let Z := labelledOpening p W
  have hd : 0<d := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨u,hu,rfl⟩)
  have hp : 0<p := disparitySet_pos hv k _ (mem_disparitySet.mpr ⟨a,ha,rfl⟩)
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hV : 0<V := by nlinarith only [hdV,hKr,hd]
  have ht := first_displacement d p V K H hd hp hK hH hdV hpV
  have hdW := Fresh.NativeDoubleGridRecovery.integer_step d V K hd hdV
  change d*W=(K : ℝ)+1/8 at hdW
  have hc := (upper_return d p V K H hd hK hdV hpV).2.2.1
  have hZW := (captured_labelled_advance p W hp hc).1
  have hlo := mul_le_mul_of_nonneg_left hZW.le hd.le
  have hdZ : (K : ℝ)+1/8 ≤ d*Z ∧ d*Z<(K : ℝ)+7/8 := by
    constructor <;> nlinarith only [hdW,hlo,hdV,ht.2]
  have hpoint : IsolatedAt v k Z := by
    apply (isolatedAt_iff_lonelyAt v k Z).2
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
    change 1/8 ≤ distInt (reading v k i*Z)
    rcases hread i hi with he|⟨q,j,hq,he⟩
    · rw [he]; exact clear_of_window K hdZ.1 hdZ.2.le
    · rw [he]; exact coset_clear d p q V K H j hd hp hV hK hH hdV hpV hq
  exact Fresh.NativePositivePointCanonical.positive_point hv k Z (by linarith only [hV,ht.1]) hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms first_displacement
#print axioms quiet_window
#print axioms coset_clear
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativeCommonOpeningGridBands
