import Fresh.NativeOpeningRecovery

/-! Separately recover the two original packet faces. A lower face is retained
or explicitly passed; the upper face uses the actual capture deficit and does
not require that same reading to be clear at entry. -/
namespace Fresh.NativeOpeningFaces
open Fresh Fresh.NativeOpeningRecovery

theorem lower_from_entry (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hs : 0 ≤ s) (hQP : Q ≤ P) (hopen : d*P=(N : ℝ)+1/8)
    (hlo : LowerRecovery d s Q N K) : (K : ℝ)+1/8 ≤ s*P := by
  rcases hlo with hretained|hpassed
  · have hi := mul_nonneg hs (sub_nonneg.mpr hQP)
    nlinarith only [hi,hretained]
  · exact opening_order_lower d s P N K hd hopen hpassed.2

theorem upper_from_deficit (d s Q P : ℝ) (N K : ℤ) (upper : ℝ) (hd : 0 < d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hclose : s*((N : ℝ)+1/8-d*Q) ≤ d*((K : ℝ)+upper-s*Q)) :
    s*P ≤ (K : ℝ)+upper := by
  have hscaled := congrArg (fun x : ℝ => s*x) hopen
  nlinarith only [hclose,hscaled,hd]

#print axioms lower_from_entry
#print axioms upper_from_deficit
end Fresh.NativeOpeningFaces
