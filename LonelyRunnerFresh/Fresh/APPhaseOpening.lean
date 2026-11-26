import Fresh.OpeningClump

/-!
Rules1–4,8–18. Exact AP packet phase placement from the actual-cascade
anchor map. [PROVISIONAL: counting tool] the named opening advances phase
by at most1/96. Regional parameter inequalities retain the unchanged AP
core bands. No density, future isolation, or cascade stopping bound.
-/
namespace Fresh.APPhaseOpening
open Fresh Fresh.Localisation Fresh.OpeningClump

theorem phase_opening (r : ℕ) (hr1 : 1≤r) (hr5 : r≤5) (h : ℕ)
    {x b lo hi : ℝ} (hb : 1≤b) (hx : 96*b≤x)
    (hwidth : lo+1/96≤hi)
    (hregionalLower : 8*(r : ℝ)*(lo+1/96)≤7*b)
    (hregionalUpper : b≤8*(hi-1/96)) :
    ∃T : ℝ, ∃N : ℤ, 0<T ∧
      (∀j : ℕ, 1≤j → j≤r → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      lo≤b*T ∧ b*T≤hi ∧ (x+(h : ℝ)*b)*T=(N : ℝ)+1/8 := by
  have hbpos : 0<b := by linarith
  have hrpos : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hr5R : (r : ℝ)≤5 := by exact_mod_cast hr5
  have hhr : 0≤(h : ℝ)*b := mul_nonneg (Nat.cast_nonneg _) hbpos.le
  have hX : 0<x+(h : ℝ)*b := by linarith
  let α : ℝ := max (b/8) lo
  have hαlo : lo≤α := le_max_right _ _
  have hαb : b/8≤α := le_max_left _ _
  have hαhi : α+1/96≤hi := by
    dsimp [α]
    rcases le_total (b/8) lo with hh | hh
    · rw [max_eq_right hh]; exact hwidth
    · rw [max_eq_left hh]; linarith
  have hαcore : 8*(r : ℝ)*(α+1/96)≤7*b := by
    dsimp [α]
    rcases le_total (b/8) lo with hh | hh
    · rw [max_eq_right hh]; exact hregionalLower
    · rw [max_eq_left hh]
      have hp : 0≤(b-1)*(7-(r : ℝ)) := mul_nonneg (by linarith) (by linarith)
      nlinarith
  obtain ⟨h1,h2,h3⟩ := openingAfter_spec (lo:=α/b) hX
  have htlo : (1/8 : ℝ)≤openingAfter (x+(h : ℝ)*b) (α/b) := by
    have hh : (1/8 : ℝ)≤α/b := by rw [le_div_iff₀ hbpos]; linarith
    exact hh.trans h1
  have hp1 : α≤b*openingAfter (x+(h : ℝ)*b) (α/b) := by
    have := (div_le_iff₀ hbpos).mp h1
    nlinarith
  have hfrac : b/(x+(h : ℝ)*b)≤1/96 := by
    rw [div_le_iff₀ hX]
    nlinarith
  have hp2 : b*openingAfter (x+(h : ℝ)*b) (α/b)≤α+1/96 := by
    have hh := mul_le_mul_of_nonneg_left h2.le hbpos.le
    have he : b*(α/b+1/(x+(h : ℝ)*b))=α+b/(x+(h : ℝ)*b) := by field_simp
    rw [he] at hh
    linarith
  have htcore : openingAfter (x+(h : ℝ)*b) (α/b)≤7/(8*(r : ℝ)) := by
    rw [le_div_iff₀ (by positivity : 0<8*(r : ℝ))]
    have hh := mul_le_mul_of_nonneg_left hp2 (by positivity : 0≤8*(r : ℝ))
    have hh2 : b*(openingAfter (x+(h : ℝ)*b) (α/b)*(8*(r : ℝ)))≤b*7 := by nlinarith
    exact le_of_mul_le_mul_left hh2 hbpos
  refine ⟨openingAfter (x+(h : ℝ)*b) (α/b),_,by linarith,?_,hαlo.trans hp1,hp2.trans hαhi,h3⟩
  intro j hj1 hjr
  have hj1R : (1 : ℝ)≤j := by exact_mod_cast hj1
  have hjrR : (j : ℝ)≤r := by exact_mod_cast hjr
  have htpos : 0<openingAfter (x+(h : ℝ)*b) (α/b) := by linarith
  apply clear_of_window 0 <;> push_cast
  · have hh := mul_le_mul_of_nonneg_right hj1R htpos.le
    nlinarith
  · have hh := mul_le_mul_of_nonneg_right hjrR htpos.le
    have hh2 := (le_div_iff₀ (by positivity : 0<8*(r : ℝ))).mp htcore
    nlinarith

/-- Endpoint inequalities on an entire packet phase interval transfer
all readings, including both signs of the offset from the chosen anchor. -/
theorem packet_phase_endpoints (L h : ℕ) (K : ℕ→ℤ)
    {x b T lo hi : ℝ} (N : ℤ)
    (hlo : lo≤b*T) (hhi : b*T≤hi)
    (hopen : (x+(h : ℝ)*b)*T=(N : ℝ)+1/8)
    (hbands : ∀j : ℕ, j≤L →
      (K j : ℝ)≤((j : ℝ)-(h : ℝ))*lo ∧
      ((j : ℝ)-(h : ℝ))*lo≤(K j : ℝ)+3/4 ∧
      (K j : ℝ)≤((j : ℝ)-(h : ℝ))*hi ∧
      ((j : ℝ)-(h : ℝ))*hi≤(K j : ℝ)+3/4) :
    ∀j : ℕ, j≤L → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  intro j hj
  obtain ⟨hl1,hl2,hh1,hh2⟩ := hbands j hj
  have hmid : (K j : ℝ)≤((j : ℝ)-(h : ℝ))*(b*T) ∧
      ((j : ℝ)-(h : ℝ))*(b*T)≤(K j : ℝ)+3/4 := by
    by_cases hm : 0≤(j : ℝ)-(h : ℝ)
    · have h1 := mul_le_mul_of_nonneg_left hlo hm
      have h2 := mul_le_mul_of_nonneg_left hhi hm
      constructor <;> nlinarith
    · have hm' : (j : ℝ)-(h : ℝ)≤0 := le_of_not_ge hm
      have h1 := mul_le_mul_of_nonpos_left hlo hm'
      have h2 := mul_le_mul_of_nonpos_left hhi hm'
      constructor <;> nlinarith
  have he : (x+(j : ℝ)*b)*T=(N : ℝ)+1/8+((j : ℝ)-(h : ℝ))*(b*T) := by
    calc (x+(j : ℝ)*b)*T=(x+(h : ℝ)*b)*T+((j : ℝ)-(h : ℝ))*(b*T) := by ring
         _=(N : ℝ)+1/8+((j : ℝ)-(h : ℝ))*(b*T) := by rw [hopen]
  apply clear_of_window (N+K j)
  · push_cast; rw [he]; linarith [hmid.1]
  · push_cast; rw [he]; linarith [hmid.2]

/-- Common AP cycle for an arbitrarily large packet step. The polynomial
threshold is enough to place the derived cycle inside the frozen core.
The packet's independent whole laps are N+jq. -/
theorem ap_packet_large (r : ℕ) (hr1 : 1≤r) (hr5 : r≤5)
    {x b : ℝ} (hb : 1≤b) (hx : 96*b≤x)
    (hlarge : 97*(r : ℝ)≤12*b*(7-(r : ℝ))) :
    ∃T : ℝ, 0<T ∧
      (∀j : ℕ, 1≤j → j≤r → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀j : ℕ, j≤6-r → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  have hbpos : 0<b := by linarith
  have hrpos : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  let L : ℕ := 6-r
  have hLpos : (0 : ℝ)<L := by exact_mod_cast (show 0<L by dsimp [L]; omega)
  have hL5 : (L : ℝ)≤5 := by exact_mod_cast (show L≤5 by dsimp [L]; omega)
  let w : ℝ := 3/(4*(L : ℝ))
  have hw : (1/96 : ℝ)≤w := by
    dsimp [w]; rw [le_div_iff₀ (by positivity : 0<4*(L : ℝ))]; nlinarith
  let q : ℤ := ⌈b/8⌉
  have hq1 : b/8≤(q : ℝ) := Int.le_ceil _
  have hq2 : (q : ℝ)<b/8+1 := Int.ceil_lt_add_one _
  have hrL : 8*(r : ℝ)*((q : ℝ)+1/96)≤7*b := by
    have hh := mul_lt_mul_of_pos_left hq2 hrpos
    nlinarith
  have hrU : b≤8*((q : ℝ)+w-1/96) := by linarith
  obtain ⟨T,N,ht,hcore,hlo,hhi,hopen⟩ :=
    phase_opening r hr1 hr5 0 hb hx (lo:=(q : ℝ)) (hi:=(q : ℝ)+w) (by linarith) hrL hrU
  have hopen' : x*T=(N : ℝ)+1/8 := by simpa using hopen
  have hwprod : (L : ℝ)*w=3/4 := by dsimp [w]; field_simp
  refine ⟨T,ht,hcore,fun j hj=>?_⟩
  have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
  have hjL : (j : ℝ)≤L := by exact_mod_cast hj
  have hdiff0 : 0≤b*T-(q : ℝ) := by linarith
  have hdiffw : b*T-(q : ℝ)≤w := by linarith
  have hlow := mul_nonneg hj0 hdiff0
  have hupper1 := mul_le_mul_of_nonneg_left hdiffw (le_of_lt hLpos)
  have hupper2 := mul_le_mul_of_nonneg_right hjL hdiff0
  have he : (x+(j : ℝ)*b)*T=(N : ℝ)+1/8+((j : ℤ)*q : ℤ)+(j : ℝ)*(b*T-(q : ℝ)) := by
    push_cast
    calc (x+(j : ℝ)*b)*T=x*T+(j : ℝ)*(q : ℝ)+(j : ℝ)*(b*T-(q : ℝ)) := by ring
         _=(N : ℝ)+1/8+(j : ℝ)*(q : ℝ)+(j : ℝ)*(b*T-(q : ℝ)) := by rw [hopen']
  apply clear_of_window (N+(j : ℤ)*q)
  · push_cast; rw [he]; push_cast; nlinarith
  · push_cast; rw [he]; push_cast; nlinarith

#print axioms packet_phase_endpoints
#print axioms ap_packet_large

#print axioms phase_opening
end Fresh.APPhaseOpening
