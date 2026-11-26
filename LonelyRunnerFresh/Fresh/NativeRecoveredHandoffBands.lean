import Fresh.NativeFinalHandoffBands
import Fresh.NativeGroupEndpointRecovery

/-! Independent speed bands across a variable selected opening. Readers may
start captured or clear, and may finish in different, changed integer windows.
The two extreme setter openings derive all endpoint windows and the actual
full handoff; no endpoint-clearance hypothesis or prior fixed prefix is used. -/
open Classical
namespace Fresh.NativeRecoveredHandoffBands
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport
  Fresh.NativeOpeningReversal Fresh.NativeFixedPrefixArrangement
  Fresh.NativeGroupEndpointRecovery Fresh.NativeCanonicalReturn
  Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def BandClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (g : Fin 8) (R lo hi : ℝ) (M : ℤ), g≠k ∧ 0 < R ∧ 0 < lo ∧
    lo ≤ reading v k g ∧ reading v k g ≤ hi ∧
    label (lo*R)=M ∧ label (hi*R)=M ∧ InWay hi R ∧ 0 ≤ (M : ℝ)+1/8 ∧
    ∀ i : Fin 8, i≠k → i≠g → ∃ (al ah : ℝ) (K : ℤ),
      0 < al ∧ al ≤ reading v k i ∧ reading v k i ≤ ah ∧
      (K : ℝ)+1/8 ≤ al*opening hi M ∧ ah*opening lo M ≤ (K : ℝ)+7/8

theorem band_has_isolating_move {v : Fin 8 → ℝ} {k : Fin 8} (h : BandClass v k) :
    ∃ (g : Fin 8) (R : ℝ), g≠k ∧ 0 < R ∧ InWay (reading v k g) R ∧
      R < handoffOpening v k R g ∧
      IsMove (disparitySet v k) R (handoffOpening v k R g) ∧
      IsolatedAt v k (handoffOpening v k R g) := by
  obtain ⟨hv,g,R,lo,hi,M,hg,hR,hlo,hlg,hgh,hlM,hhM,hwhi,hM,hbands⟩ := h
  have hgp : 0 < reading v k g := hlo.trans_le hlg
  have hlabel := speed_interval_label lo (reading v k g) hi R hlg hgh hR.le (hlM.trans hhM.symm)
  rw [hlM] at hlabel
  have hw := speed_interval_capture lo (reading v k g) hi R hlg hgh hR.le (hlM.trans hhM.symm) hwhi
  let T := handoffOpening v k R g
  have hT : T=opening (reading v k g) M := by dsimp [T,handoffOpening]; rw [hlabel]
  have hstep := Fresh.NativeThirdReaderRetention.captured_labelled_advance (reading v k g) R hgp hw
  have hRT : R < T := by
    change R < labelledOpening (reading v k g) R
    linarith only [hstep.1]
  have hbound : opening hi M ≤ T ∧ T ≤ opening lo M := by
    rw [hT]
    exact interval_opening_bounds lo (reading v k g) hi M hlo hlg hgh hM
  have hhi : 0 < hi := hgp.trans_le hgh
  have hleft : 0 ≤ opening hi M := by dsimp [opening]; positivity
  have hclear : LonelyAt (disparitySet v k) T := by
    intro s hs
    obtain ⟨i,hik,rfl⟩ := mem_disparitySet.mp hs
    change (1/8 : ℝ) ≤ distInt (reading v k i*T)
    by_cases hig : i=g
    · subst i
      have he := handoff_identity hv k g R hg
      change reading v k g*T=(label (reading v k g*R) : ℝ)+1/8 at he
      exact clear_of_window _ he.ge (by linarith only [he])
    · obtain ⟨al,ah,K,hal,hl,hh,hstart,hend⟩ := hbands i hik hig
      exact not_lt.mp (interval_band_at_point al (reading v k i) ah
        (opening hi M) T (opening lo M) K hal hl hh hleft hbound.1 hbound.2 hstart hend).1
  have hgm : reading v k g∈disparitySet v k := mem_disparitySet.mpr ⟨g,hg,rfl⟩
  have hm : IsMove ({reading v k g} : Finset ℝ) R T := by
    simpa only [T,handoffOpening,labelledOpening] using singleton_captured_move (reading v k g) R hw
  have hfull := endpoint_clear_preserves_move
    (added := (disparitySet v k).erase (reading v k g))
    (fun d hd=>by rw [Finset.mem_singleton.mp hd]; exact hgp)
    (fun d hd=>disparitySet_pos hv k d (Finset.mem_erase.mp hd).2)
    R T hm (fun d hd=>not_lt.mpr (hclear d (Finset.mem_erase.mp hd).2))
  have hunion : ({reading v k g} : Finset ℝ)∪(disparitySet v k).erase (reading v k g)=disparitySet v k := by
    simp only [Finset.singleton_union,Finset.insert_erase hgm]
  rw [hunion] at hfull
  exact ⟨g,R,hg,hR,hw,hRT,hfull,(isolatedAt_iff_lonelyAt v k T).2 hclear⟩

theorem band_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : BandClass v k) : CanonicalReturnClass v k := by
  obtain ⟨g,R,hg,hR,hw,hRT,hm,hclear⟩ := band_has_isolating_move h
  exact canonical_of_isolating_move h.1 k R _ hR hRT hm hclear

theorem band_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : BandClass v k) : Isolation v k :=
  canonical_isolation (band_into_canonical h)

theorem retainedBands_into_recoveredBands {v : Fin 8 → ℝ} {k : Fin 8}
    (h : Fresh.NativeFinalHandoffBands.BandClass v k) : BandClass v k := by
  obtain ⟨hv,g,R,lo,hi,M,hg,hR,hlo,hlg,hgh,hlM,hhM,hwhi,hM,hbands⟩ := h
  have hhi : 0 < hi := (hlo.trans_le hlg).trans_le hgh
  have hc := (capture_at_label hi R hwhi).2
  rw [hhM] at hc
  have hearly : R < opening hi M := by
    dsimp [opening]
    apply (lt_div_iff₀ hhi).2
    simpa only [mul_comm] using hc
  refine ⟨hv,g,R,lo,hi,M,hg,hR,hlo,hlg,hgh,hlM,hhM,hwhi,hM,?_⟩
  intro i hik hig
  obtain ⟨al,ah,K,hal,hl,hh,hstart,hend⟩ := hbands i hik hig
  exact ⟨al,ah,K,hal,hl,hh,hstart.trans (mul_le_mul_of_nonneg_left hearly.le hal.le),hend⟩

#print axioms retainedBands_into_recoveredBands

#print axioms band_has_isolating_move
#print axioms band_into_canonical
#print axioms band_isolation
end Fresh.NativeRecoveredHandoffBands
