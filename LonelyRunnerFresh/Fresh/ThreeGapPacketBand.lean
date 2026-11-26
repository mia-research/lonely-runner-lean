import Fresh.TwoGapPacketBand

/-! Three independently displaced AP generators, with arbitrary selections
from eight AP packets. Original exact mapping/jitter precedes this proof:
train_flank_three_gap_packet_map_v1 and three_gap_packet_jitter_v1.
No bound on original g+h+j, and no arbitrary-reading representation claim.
[PROVISIONAL: covering] finite bit cases in clear_packet. -/
set_option maxHeartbeats 2000000
namespace Fresh.ThreeGapPacketBand
open Fresh Fresh.OneMover

theorem clear_packet (g h j : ℝ) (m a b c : ℤ) (D e f l : ℕ)
    (hD : D ≤ 3) (he : e ≤ 1) (hf : f ≤ 1) (hl : l ≤ 1) (hne : 1 ≤ D+e+f+l)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(c : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(c : ℝ))+4) :
    (1/8 : ℝ) ≤ distInt
      (((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h+(l : ℝ)*j)*((m : ℝ)+1/8)) := by
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hD3 : (D : ℝ) ≤ 3 := by exact_mod_cast hD
  have hnr : (1 : ℝ) ≤ (D : ℝ)+(e : ℝ)+(f : ℝ)+(l : ℝ) := by exact_mod_cast hne
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have hw : (1/8 : ℝ) ≤ j*((m : ℝ)+1/8)-(c : ℝ) := by nlinarith
  have huv : (g+h+j)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)+(c : ℝ)) ≤ 1/2 := by nlinarith
  interval_cases e <;> interval_cases f <;> interval_cases l
  · have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+0*a+0*b+0*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+0*a+0*b+1*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+0*a+1*b+0*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+0*a+1*b+1*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+1*a+0*b+0*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+1*a+0*b+1*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+1*a+1*b+0*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+1*a+1*b+1*c)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith

-- STANDING: DEFINITION
def ThreeGapPacketClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (u g h j : ℝ) (m a b c : ℤ),
    0 < u ∧ 0 < g ∧ 0 < h ∧ 0 < j ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    8*(c : ℝ)+1 ≤ (8*(m : ℝ)+1)*j ∧
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(c : ℝ))+4 ∧
    ∀ i, i ≠ k → ∃ D e f l : ℕ,
      D ≤ 3 ∧ e ≤ 1 ∧ f ≤ 1 ∧ l ≤ 1 ∧ 1 ≤ D+e+f+l ∧
      |V i-V k|=u*((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h+(l : ℝ)*j)

theorem threeGapPacket_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : ThreeGapPacketClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,u,g,h,j,m,a,b,c,hu,hgpos,hhpos,hjpos,hm,hg,hh,hj,hsum,hshape⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨((m : ℝ)+1/8)/u,by positivity,fun i hik => ?_⟩
  obtain ⟨D,e,f,l,hD,he,hf,hl,hne,hdis⟩ := hshape i hik
  rw [← Fresh.Localisation.distInt_abs_mul,hdis]
  have ht : (u*((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h+(l : ℝ)*j))*(((m : ℝ)+1/8)/u)=
      ((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h+(l : ℝ)*j)*((m : ℝ)+1/8) := by field_simp
  rw [ht]
  exact clear_packet g h j m a b c D e f l hD he hf hl hne hg hh hj hsum

#print axioms clear_packet
#print axioms threeGapPacket_isolation
end Fresh.ThreeGapPacketBand
