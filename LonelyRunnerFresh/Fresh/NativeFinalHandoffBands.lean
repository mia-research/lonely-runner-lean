import Fresh.NativeRebasedPacketChart

/-! Independent speed bands around a sole captured final setter. All other
readers retain their input clear labels until even the slowest allowed
setter opening. This derives PartnerClass without endpoint-clear premises. -/
open Classical
namespace Fresh.NativeFinalHandoffBands
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeReturnClosingOrder Fresh.NativeOneReaderDeformation
  Fresh.NativeCoalescedCaptureRelay Fresh.NativeFixedPrefixTransport Fresh.NativeCapturedPartnerJoin
  Fresh.FastestCaptureRetention

-- STANDING: DEFINITION
noncomputable def BandClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (g : Fin 8) (R lo hi : ℝ) (M : ℤ), g≠k ∧ 0<R ∧ 0<lo ∧
    lo ≤ reading v k g ∧ reading v k g ≤ hi ∧
    label (lo*R)=M ∧ label (hi*R)=M ∧ InWay hi R ∧ 0 ≤ (M : ℝ)+1/8 ∧
    ∀ i : Fin 8,i≠k → i≠g → ∃ (al ah : ℝ) (K : ℤ), 0<al ∧ al ≤ reading v k i ∧ reading v k i ≤ ah ∧
      (K : ℝ)+1/8 ≤ al*R ∧ ah*opening lo M ≤ (K : ℝ)+7/8

theorem band_into_partner {v : Fin 8 → ℝ} {k : Fin 8} (h : BandClass v k) : PartnerClass v k := by
  obtain ⟨hv,g,R,lo,hi,M,hg,hR,hlo,hlg,hgh,hlM,hhM,hwhi,hM,hbands⟩ := h
  have hgp : 0<reading v k g := hlo.trans_le hlg
  have hlabel := speed_interval_label lo (reading v k g) hi R hlg hgh hR.le (hlM.trans hhM.symm)
  rw [hlM] at hlabel
  have hw := speed_interval_capture lo (reading v k g) hi R hlg hgh hR.le (hlM.trans hhM.symm) hwhi
  have hS : labelledOpening (reading v k g) R=opening (reading v k g) M := by simp only [labelledOpening,hlabel]
  have hstep := Fresh.NativeThirdReaderRetention.captured_labelled_advance (reading v k g) R hgp hw
  have hRS : R<labelledOpening (reading v k g) R := by linarith only [hstep.1]
  have hbound : labelledOpening (reading v k g) R ≤ opening lo M := by
    rw [hS]
    exact (interval_opening_bounds lo (reading v k g) hi M hlo hlg hgh hM).2
  have hpoints : ∀ i : Fin 8,i≠k → i≠g →
      ¬InWay (reading v k i) R ∧ labelledOpening (reading v k g) R ≤ closing (reading v k i) R := by
    intro i hi hig
    obtain ⟨al,ah,K,hal,hl,hhi,hstart,hend⟩ := hbands i hi hig
    have hsClear := interval_band_at_point al (reading v k i) ah R R (opening lo M) K hal hl hhi hR.le le_rfl (hRS.le.trans hbound) hstart hend
    have hsLabel := hsClear.2
    have hsEnd := interval_band_at_point al (reading v k i) ah R (labelledOpening (reading v k g) R) (opening lo M) K hal hl hhi hR.le hRS.le hbound hstart hend
    have hip : 0<reading v k i := hal.trans_le hl
    have hupper := mul_le_mul_of_nonneg_right hhi (le_trans hR.le (hRS.le.trans hbound))
    have hupper' : reading v k i*opening lo M ≤ (K : ℝ)+7/8 := hupper.trans hend
    refine ⟨hsClear.1,?_⟩
    apply (le_div_iff₀ hip).2
    dsimp [closing]
    rw [hsLabel]
    have hh := mul_le_mul_of_nonneg_left hbound hip.le
    nlinarith only [hh,hupper']
  have hmove : IsMove (disparitySet v k) R (labelledOpening (reading v k g) R) := by
    refine Or.inr ⟨reading v k g,mem_disparitySet.mpr ⟨g,hg,rfl⟩,hw,(captured_opening _ R hw).symm,?_⟩
    intro s hs hws
    obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hs
    have hig : i=g := by by_contra hn; exact (hpoints i hi hn).1 hws
    subst i
    change nextOpening (reading v k g) R ≤ labelledOpening (reading v k g) R
    exact (captured_opening (reading v k g) R hw).le
  refine ⟨hv,R,g,hR,hg,hw,?_,?_⟩
  · simpa only [handoffOpening,labelledOpening] using hmove
  · intro i hi
    refine ⟨?_,?_⟩
    · intro hwi
      have hig : i=g := by by_contra hn; exact (hpoints i hi hn).1 hwi
      exact Or.inr (by rw [hig])
    · intro hci
      have hig : i≠g := by intro he; subst i; exact hci hw
      simpa only [handoffOpening,labelledOpening] using (hpoints i hi hig).2

theorem band_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : BandClass v k) : Isolation v k :=
  partner_isolation (band_into_partner h)

theorem initial_capture_of_band (m s ml mh sl sh : ℝ) (L : ℤ)
    (hm : 0 < m) (hml : ml ≤ m) (hmh : m ≤ mh) (hsl : sl ≤ s) (hsh : s ≤ sh)
    (hL : 1 ≤ L) (hleft : (8*(L : ℝ)-1)*mh < sl) (hright : sh < (8*(L : ℝ)+1)*ml) :
    InWay s (1/(8*m)) := by
  have hLR : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hp : 0 ≤ 8*(L : ℝ)-1 := by linarith only [hLR]
  have hp' : 0 ≤ 8*(L : ℝ)+1 := by linarith only [hLR]
  have hlo := (mul_le_mul_of_nonneg_left hmh hp).trans_lt (hleft.trans_le hsl)
  have hhi := (hsh.trans_lt hright).trans_le (mul_le_mul_of_nonneg_left hml hp')
  have hden : 0 < 8*m := by positivity
  have hlow : (L : ℝ)-1/8 < s/(8*m) := (lt_div_iff₀ hden).2 (by nlinarith only [hlo])
  have hhigh : s/(8*m) < (L : ℝ)+1/8 := (div_lt_iff₀ hden).2 (by nlinarith only [hhi])
  apply lt_of_le_of_lt (Fresh.Cascade.distInt_le _ L)
  rw [abs_lt]
  constructor <;> rw [mul_one_div] <;> linarith only [hlow,hhigh]

#print axioms initial_capture_of_band

#print axioms band_into_partner
#print axioms band_isolation
end Fresh.NativeFinalHandoffBands
