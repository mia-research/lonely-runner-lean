import Fresh.NativeOpeningRetention

/-! Recovery into an original integer window after a new opening. Lower
faces are either retained from entry or passed in the explicit order of
original boundaries; upper faces use the actual opening deficit. -/
namespace Fresh.NativeOpeningRecovery
open Fresh

theorem opening_order_band (d s P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hlo : d*((K : ℝ)+1/8) ≤ s*((N : ℝ)+1/8))
    (hhi : s*((N : ℝ)+1/8) ≤ d*((K : ℝ)+7/8)) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P ≤ (K : ℝ)+7/8 := by
  have hscaled := congrArg (fun x : ℝ => s*x) hopen
  constructor <;> nlinarith only [hscaled,hlo,hhi,hd]

theorem opening_order_lower (d s P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hlo : d*((K : ℝ)+1/8) ≤ s*((N : ℝ)+1/8)) : (K : ℝ)+1/8 ≤ s*P := by
  have hscaled := congrArg (fun x : ℝ => s*x) hopen
  nlinarith only [hscaled,hlo,hd]

theorem opening_order_upper (d s P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hopen : d*P=(N : ℝ)+1/8)
    (hhi : s*((N : ℝ)+1/8) ≤ d*((K : ℝ)+7/8)) : s*P ≤ (K : ℝ)+7/8 := by
  have hscaled := congrArg (fun x : ℝ => s*x) hopen
  nlinarith only [hscaled,hhi,hd]

#print axioms opening_order_lower
#print axioms opening_order_upper
def LowerRecovery (d s Q : ℝ) (N K : ℤ) : Prop :=
  (K : ℝ)+1/8 ≤ s*Q ∨
    (s*Q < (K : ℝ)+1/8 ∧ d*((K : ℝ)+1/8) ≤ s*((N : ℝ)+1/8))

theorem recovered_window (d s Q P : ℝ) (N K : ℤ) (hd : 0 < d)
    (hs : 0 ≤ s) (hQP : Q ≤ P) (hopen : d*P=(N : ℝ)+1/8)
    (hlo : LowerRecovery d s Q N K)
    (hhi : s*((N : ℝ)+1/8-d*Q) ≤ d*((K : ℝ)+7/8-s*Q)) :
    (K : ℝ)+1/8 ≤ s*P ∧ s*P ≤ (K : ℝ)+7/8 := by
  rcases hlo with hretained|hpassed
  · exact Fresh.NativeOpeningRetention.weighted_window d s Q P N K hd hs hQP hopen hretained hhi
  · have hscaled := congrArg (fun x : ℝ => s*x) hopen
    have hupper : s*((N : ℝ)+1/8) ≤ d*((K : ℝ)+7/8) := by nlinarith only [hhi]
    exact opening_order_band d s P N K hd hopen hpassed.2 hupper

#print axioms opening_order_band
#print axioms recovered_window
end Fresh.NativeOpeningRecovery
