import Fresh.FourBlockTwoOutside

/-! Closed entering and leaving faces, simultaneous setters, and isolated
singletons. These are exact original phase equalities, without slack. -/
namespace Fresh.NativeBoundaryJoins
open Fresh Fresh.Cascade

theorem opening_tie (d e P U : ℝ) (N K : ℤ) (hd : 0 < d) (he : 0 < e)
    (hP : d*P=(N : ℝ)+1/8) (hU : e*U=(K : ℝ)+1/8) :
    P=U ↔ e*((N : ℝ)+1/8)=d*((K : ℝ)+1/8) := by
  rw [←hP,←hU]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have hp : 0 < d*e := mul_pos hd he
    nlinarith only [h,hp]

theorem entering_side (d P t : ℝ) (N : ℤ) (hd : 0 < d)
    (hP : d*P=(N : ℝ)+1/8) (ht : t < P) (hl : (N : ℝ)-1/8 < d*t) : InWay d t := by
  have hh : d*t < (N : ℝ)+1/8 := by nlinarith only [hd,ht,hP]
  apply lt_of_le_of_lt (Fresh.Cascade.distInt_le _ N)
  rw [abs_lt]
  constructor <;> linarith

theorem leaving_side (e P t : ℝ) (K : ℤ) (he : 0 < e)
    (hP : e*P=(K : ℝ)+7/8) (ht : P < t) (hh : e*t < (K : ℝ)+9/8) : InWay e t := by
  have hl : (K : ℝ)+7/8 < e*t := by nlinarith only [he,ht,hP]
  apply lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (K+1))
  rw [abs_lt]
  push_cast
  constructor <;> linarith

theorem singleton_between_faces {ds : Finset ℝ} (d e P : ℝ) (N K : ℤ)
    (hd : d∈ds) (he : e∈ds) (hdpos : 0 < d) (hepos : 0 < e)
    (hopen : d*P=(N : ℝ)+1/8) (hclose : e*P=(K : ℝ)+7/8)
    (hclear : LonelyAt ds P) :
    ∀ t : ℝ, (N : ℝ)-1/8 < d*t → e*t < (K : ℝ)+9/8 →
      (LonelyAt ds t ↔ t=P) := by
  intro t hlo hhi
  constructor
  · intro htclear
    rcases lt_trichotomy t P with hlt|heq|hgt
    · exact False.elim (not_lt.mpr (htclear d hd) (entering_side d P t N hdpos hopen hlt hlo))
    · exact heq
    · exact False.elim (not_lt.mpr (htclear e he) (leaving_side e P t K hepos hclose hgt hhi))
  · intro heq; simpa [heq] using hclear

#print axioms opening_tie
#print axioms entering_side
#print axioms leaving_side
#print axioms singleton_between_faces
end Fresh.NativeBoundaryJoins
