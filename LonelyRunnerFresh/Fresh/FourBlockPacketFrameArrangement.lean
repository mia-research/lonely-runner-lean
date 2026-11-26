import Fresh.FourBlockPacketFrame

/-! A common native frame: isolate at the outer opening or at a later
original left opening. The packet faces supply the reference lower edge. -/
namespace Fresh.FourBlockPacketFrameArrangement
open Fresh Fresh.OneMover Fresh.Cascade Fresh.Localisation Fresh.FourBlockNeighbour
  Fresh.FourBlockEndpointCapture Fresh.FourBlockOuterLapPhase Fresh.FourBlockOuterTailClear
  Fresh.FourBlockLeftOpening Fresh.FourBlockPacketFrame

noncomputable def selectedOpening (c g h j : ℝ) (p q r : ℕ) (m a b e rho : ℤ)
    (choice : Option (Fin 3)) (L : Fin 3 → ℤ) : ℝ :=
  match choice with
  | none => outerLapOpening g h j m a b e rho
  | some u => leftOpening c g h j p q r m a b e u (L u)

def SelectedLeftBands (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ)
    (P : ℝ) (choice : Option (Fin 3)) (L : Fin 3 → ℤ) : Prop :=
  match choice with
  | none => LeftBandsAt c g h j p q r m a b e P L
  | some u => OtherLeftBandsAt c g h j p q r m a b e P L u

def FrameBands (c g h j : ℝ) (p q r : ℕ) (m a b e rho : ℤ)
    (choice : Option (Fin 3)) (L : Fin 3 → ℤ) : Prop :=
  let P := selectedOpening c g h j p q r m a b e rho choice L
  outerLapOpening g h j m a b e rho ≤ P ∧
  (4+g+h+j)*(P-outerLapOpening g h j m a b e rho) ≤ 3/4 ∧
  (4+g+h+j)*(P-outerLapOpening g h j m a b e rho)+3*(1-(P-(m : ℝ))) ≤ 3/4 ∧
  SelectedLeftBands c g h j p q r m a b e P choice L

theorem selected_bands (c g h j : ℝ) (p q r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ)
    (choice : Option (Fin 3)) (L : Fin 3 → ℤ)
    (hb : SelectedLeftBands c g h j p q r m a b e
      (selectedOpening c g h j p q r m a b e rho choice L) choice L) :
    LeftBandsAt c g h j p q r m a b e (selectedOpening c g h j p q r m a b e rho choice L) L := by
  cases choice with
  | none => exact hb
  | some u => exact bands_at_opening c g h j p q r hq hr hg hh hj m a b e u L hb

theorem frame_clear (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hg : 0 < g) (hh : 0 < h) (hj : 0 < j) (m a b e rho : ℤ)
    (choice : Option (Fin 3)) (L : Fin 3 → ℤ)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hb : FrameBands c g h j p q r m a b e rho choice L) :
    LonelyAt (disparitySet (speeds c g h j p q r) 0)
      (selectedOpening c g h j p q r m a b e rho choice L) := by
  obtain ⟨hQP,houter,hinner,hcut⟩ := hb
  have hleft := selected_bands c g h j p q r hq hr hg hh hj m a b e rho choice L hcut
  have hprefix (u : Fin 3) : (1/8 : ℝ) ≤ distInt (leftReading c g h j p q r u*
      selectedOpening c g h j p q r m a b e rho choice L) := clear_of_window _ (hleft u).1 (hleft u).2
  intro d hd
  obtain ⟨i,hi0,rfl⟩ := mem_disparitySet.mp hd
  rw [Fresh.Localisation.distInt_abs_mul]
  by_cases hi1 : i=1
  · subst i; simpa only [leftReading,prefixIndex] using hprefix 0
  by_cases hi2 : i=2
  · subst i; simpa only [leftReading,prefixIndex] using hprefix 1
  by_cases hi3 : i=3
  · subst i; simpa only [leftReading,prefixIndex] using hprefix 2
  have hiv := i.isLt
  have hn0 := Fin.val_ne_of_ne hi0
  have hn1 := Fin.val_ne_of_ne hi1
  have hn2 := Fin.val_ne_of_ne hi2
  have hn3 := Fin.val_ne_of_ne hi3
  exact packet_clear c g h j p q r hp hq hr hs hg hh hj m a b e rho
    (selectedOpening c g h j p q r m a b e rho choice L) hhi hQP houter hinner i (by omega)

theorem all_subjects (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 4)
    (hgpos : 0 < g) (hhpos : 0 < h) (hjpos : 0 < j) (m a b e rho : ℤ)
    (choice : Option (Fin 3)) (L : Fin 3 → ℤ) (hm : 1 ≤ m) (hsmall : g+h+j ≤ 3)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (hhi : 8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e)
    (hb : FrameBands c g h j p q r m a b e rho choice L)
    (k : Fin 8) : Isolation (speeds c g h j p q r) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  by_cases hk0 : k=0
  · subst k
    have hc := frame_clear c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho choice L hhi hb
    obtain ⟨hPlo,hPhi⟩ := time_bounds g h j hgpos hhpos hjpos m a b e rho
      (selectedOpening c g h j p q r m a b e rho choice L) hhi hb.1 hb.2.1 hb.2.2.1
    exact ⟨selectedOpening c g h j p q r m a b e rho choice L,by linarith,(isolatedAt_iff _ _ _).2 hc⟩
  · by_cases hk7 : k=7
    · subst k
      exact ⟨1/8,by norm_num,FourBlockEndpoints.right_direct c g h j p q r hp hq hr (by omega)
        hgpos hhpos hjpos hsmall (by intro hbad; omega)⟩
    · have hn0 := Fin.val_ne_of_ne hk0
      have hn7 := Fin.val_ne_of_ne hk7
      have hi := k.isLt
      exact ⟨(m : ℝ)+1/8,by linarith,
        internal_at_reference c g h j p q r hp hq hr (by omega) m a b e hg hh hj hsum k (by omega) (by omega)⟩

-- STANDING: DEFINITION
def PacketFrameClassAt (V : Fin 8 → ℝ) (p q r : ℕ) (rho : ℤ)
    (choice : Option (Fin 3)) (L : Fin 3 → ℤ) : Prop :=
  (∀ i,0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h j B z : ℝ) (m a b e : ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧ p+q+r ≤ 4 ∧
    0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧ g+h+j ≤ 3 ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4 ∧
    8*(rho : ℝ)-27 ≤ 7*(g+h+j)+8*remainder g h j m a b e ∧
    FrameBands c g h j p q r m a b e rho choice L ∧ z≠0 ∧
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

-- STANDING: DEFINITION
def PacketFrameClass (V : Fin 8 → ℝ) : Prop :=
  ∃ (p q r : ℕ) (rho : ℤ) (choice : Option (Fin 3)) (L : Fin 3 → ℤ), PacketFrameClassAt V p q r rho choice L

theorem packetFrameClass_isolation {V : Fin 8 → ℝ} (hV : PacketFrameClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨p,q,r,rho,choice,L,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hhi,hb,hz,hrepr⟩ := hAt
  have hi := all_subjects c g h j p q r hp hq hr hs hgpos hhpos hjpos m a b e rho choice L
    hm hsmall hg hh hj hsum hhi hb (σ k)
  rw [hrepr]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

theorem finite_normal_form {V : Fin 8 → ℝ} (hV : PacketFrameClass V) :
    ∃ (p q r : ℕ) (rho : ℤ) (choice : Option (Fin 3)) (L : Fin 3 → ℤ),
      ((p=1 ∧ q=1 ∧ r=1) ∨ (p=2 ∧ q=1 ∧ r=1) ∨
        (p=1 ∧ q=2 ∧ r=1) ∨ (p=1 ∧ q=1 ∧ r=2)) ∧
      (rho=4 ∨ rho=5 ∨ rho=6) ∧
      0 ≤ L 0 ∧ L 0 ≤ L 1 ∧ L 1 ≤ L 2 ∧ L 2 ≤ 4 ∧ PacketFrameClassAt V p q r rho choice L := by
  obtain ⟨p,q,r,rho,choice,L,hAt⟩ := hV
  have hsave := hAt
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hhi,hb,hz,hrepr⟩ := hAt
  obtain ⟨hPlo,hPhi⟩ := time_bounds g h j hgpos hhpos hjpos m a b e rho
    (selectedOpening c g h j p q r m a b e rho choice L) hhi hb.1 hb.2.1 hb.2.2.1
  have hleft := selected_bands c g h j p q r hq hr hgpos hhpos hjpos m a b e rho choice L hb.2.2.2
  obtain ⟨hl0,hl01,hl12,hl2⟩ := Fresh.FourBlockDisplacedLeftRoles.left_roles_at_time c g h j p q r hp hq hr hs
    hgpos hhpos hjpos m a b e (selectedOpening c g h j p q r m a b e rho choice L) L hsmall
    hg hh hj hsum (by linarith) hPhi hleft
  exact ⟨p,q,r,rho,choice,L,partitions p q r hp hq hr hs,
    return_roles g h j hgpos hhpos hjpos m a b e rho (selectedOpening c g h j p q r m a b e rho choice L)
      hsmall hg hh hj hsum hhi hb.1 hb.2.2.1,hl0,hl01,hl12,hl2,hsave⟩

theorem outerTail_into_frame {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockOuterTailArrangement.OuterTailClass V) : PacketFrameClass V := by
  obtain ⟨p,q,r,rho,L,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hleft,hz,hrepr⟩ := hAt
  have hb : FrameBands c g h j p q r m a b e rho none L := by
    dsimp [FrameBands,selectedOpening,SelectedLeftBands]
    refine ⟨le_rfl,?_,?_,?_⟩
    · norm_num
    · have hQlo := (opening_bounds g h j hgpos hhpos hjpos m a b e rho hlo hhi).1
      linarith
    · simpa only [LeftBandsAt,LeftBands,leftReading,leftLap] using hleft
  exact ⟨p,q,r,rho,none,L,hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,
    hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,hg,hh,hj,hsum,hhi,hb,hz,hrepr⟩

theorem leftOpening_into_frame {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftOpeningArrangement.LeftOpeningClass V) : PacketFrameClass V := by
  obtain ⟨p,q,r,rho,u,L,hAt⟩ := hV
  obtain ⟨hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,
    hg,hh,hj,hsum,hlo,hhi,hb,hz,hrepr⟩ := hAt
  have hf : FrameBands c g h j p q r m a b e rho (some u) L := by
    simpa only [FrameBands,selectedOpening,SelectedLeftBands,Fresh.FourBlockLeftOpeningArrangement.OpeningBands] using hb
  exact ⟨p,q,r,rho,some u,L,hpos,hinj,c,g,h,j,B,z,m,a,b,e,σ,
    hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hsmall,hg,hh,hj,hsum,hhi,hf,hz,hrepr⟩

-- STANDING: DEFINITION
def PacketFrameCoveredClass (V : Fin 8 → ℝ) : Prop :=
  Fresh.FourBlockFiveReturnArrangement.FiveReturnCoveredClass V ∨ PacketFrameClass V

theorem packetFrameCovered_isolation {V : Fin 8 → ℝ} (hV : PacketFrameCoveredClass V) (k : Fin 8) : Isolation V k := by
  rcases hV with hold|hframe
  · exact Fresh.FourBlockFiveReturnArrangement.fiveReturnCovered_isolation hold k
  · exact packetFrameClass_isolation hframe k

theorem leftOpeningCovered_into_frameCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftOpeningArrangement.LeftOpeningCoveredClass V) : PacketFrameCoveredClass V := by
  rcases hV with hold|hleft
  · rcases hold with hprior|houter
    · exact Or.inl hprior
    · exact Or.inr (outerTail_into_frame houter)
  · exact Or.inr (leftOpening_into_frame hleft)

theorem leftExitCovered_into_frameCovered {V : Fin 8 → ℝ}
    (hV : Fresh.FourBlockLeftExitArrangement.LeftExitCoveredClass V) : PacketFrameCoveredClass V := by
  exact leftOpeningCovered_into_frameCovered
    (Fresh.FourBlockLeftOpeningArrangement.leftExitCovered_into_leftOpeningCovered hV)

#print axioms selected_bands
#print axioms frame_clear
#print axioms all_subjects
#print axioms packetFrameClass_isolation
#print axioms finite_normal_form
#print axioms outerTail_into_frame
#print axioms leftOpening_into_frame
#print axioms packetFrameCovered_isolation
#print axioms leftOpeningCovered_into_frameCovered
#print axioms leftExitCovered_into_frameCovered
end Fresh.FourBlockPacketFrameArrangement
