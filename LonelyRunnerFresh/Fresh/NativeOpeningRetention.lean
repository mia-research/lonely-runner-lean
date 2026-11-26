import Fresh.FourBlockPacketChartJoins

/-! Original positive readings at a captured opening. Retention follows
from the actual capture deficit and physical speed order. -/
namespace Fresh.NativeOpeningRetention
open Fresh Fresh.Localisation

theorem opening_displacement (d Q P : ℝ) (N : ℤ)
    (hopen : d*P=(N : ℝ)+1/8) :
    d*(P-Q)=(N : ℝ)+1/8-d*Q := by nlinarith only [hopen]

theorem capture_advance (d Q P : ℝ) (N : ℤ) (hd : 0 < d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hlo : (N : ℝ)-1/8 < d*Q) (hhi : d*Q < (N : ℝ)+1/8) :
    0 < P-Q ∧ d*(P-Q) < 1/4 := by
  have he := opening_displacement d Q P N hopen
  constructor <;> nlinarith

theorem slower_window (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hs : 0 ≤ s) (hsd : s ≤ d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hcaplo : (N : ℝ)-1/8 < d*Q) (hcaphi : d*Q < (N : ℝ)+1/8)
    (hlo : (K : ℝ)+1/8 ≤ s*Q) (hhi : s*Q ≤ (K : ℝ)+5/8) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P < (K : ℝ)+7/8 := by
  obtain ⟨ht,hadvance⟩ := capture_advance d Q P N hd hopen hcaplo hcaphi
  have hnonneg := mul_nonneg hs ht.le
  have hle := mul_le_mul_of_nonneg_right hsd ht.le
  constructor <;> nlinarith only [hnonneg,hle,hadvance,hlo,hhi]

theorem weighted_window (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hs : 0 ≤ s) (hQP : Q ≤ P) (hopen : d*P=(N : ℝ)+1/8)
    (hlo : (K : ℝ)+1/8 ≤ s*Q)
    (hclose : s*((N : ℝ)+1/8-d*Q) ≤ d*((K : ℝ)+7/8-s*Q)) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P ≤ (K : ℝ)+7/8 := by
  have hlow := mul_nonneg hs (sub_nonneg.mpr hQP)
  have he := opening_displacement d Q P N hopen
  have hsopen := congrArg (fun t : ℝ => s*t) hopen
  have hx : d*(s*P-((K : ℝ)+7/8)) ≤ 0 := by nlinarith only [hclose,hsopen]
  constructor <;> nlinarith only [hlow,hlo,hx,hd]

theorem weighted_upper (d s Q P : ℝ) (N K : ℤ) (upper : ℝ) (hd : 0 < d)
    (hs : 0 ≤ s) (hQP : Q ≤ P) (hopen : d*P=(N : ℝ)+1/8)
    (hlo : (K : ℝ)+1/8 ≤ s*Q)
    (hclose : s*((N : ℝ)+1/8-d*Q) ≤ d*((K : ℝ)+upper-s*Q)) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P ≤ (K : ℝ)+upper := by
  have hlow := mul_nonneg hs (sub_nonneg.mpr hQP)
  have hsopen := congrArg (fun t : ℝ => s*t) hopen
  have hx : d*(s*P-((K : ℝ)+upper)) ≤ 0 := by nlinarith only [hclose,hsopen]
  constructor <;> nlinarith only [hlow,hlo,hx,hd]

#print axioms weighted_upper
#print axioms opening_displacement
#print axioms capture_advance
#print axioms slower_window
#print axioms weighted_window
end Fresh.NativeOpeningRetention
