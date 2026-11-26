import Fresh.ThreeBlockWideLaps

/-! A structural reading rule shared by the three-block families and more
irregular selections from four AP packets. Original exact physical cascade
mapping: train_flank_two_gap_packet_map_v1.py/json. The two positive gap
generators share their native AP index; their whole laps are independent.
There is no bound on the original sum g+h. No assertion that arbitrary
readings admit this representation is used.
[PROVISIONAL: covering] finite bit-coefficient cases in clear_packet.
-/
namespace Fresh.TwoGapPacketBand
open Fresh Fresh.OneMover

theorem clear_packet (g h : ℝ) (m a b : ℤ) (D e f : ℕ)
    (hD : D ≤ 4) (he : e ≤ 1) (hf : f ≤ 1) (hne : 1 ≤ D+e+f)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    (1/8 : ℝ) ≤ distInt
      (((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h)*((m : ℝ)+1/8)) := by
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hD4 : (D : ℝ) ≤ 4 := by exact_mod_cast hD
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) ≤ 3/8 := by nlinarith
  interval_cases e <;> interval_cases f
  · have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    apply Fresh.Localisation.clear_of_window ((D : ℤ)*m)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+b)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+a)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith
  · apply Fresh.Localisation.clear_of_window ((D : ℤ)*m+a+b)
    all_goals push_cast
    all_goals norm_num
    all_goals nlinarith

-- STANDING: DEFINITION
def TwoGapPacketClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (u g h : ℝ) (m a b : ℤ),
    0 < u ∧ 0 < g ∧ 0 < h ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3 ∧
    ∀ i, i ≠ k → ∃ D e f : ℕ,
      D ≤ 4 ∧ e ≤ 1 ∧ f ≤ 1 ∧ 1 ≤ D+e+f ∧
      |V i-V k|=u*((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h)

theorem twoGapPacket_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : TwoGapPacketClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,u,g,h,m,a,b,hu,hgpos,hhpos,hm,hg,hh,hsum,hshape⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨((m : ℝ)+1/8)/u,by positivity,fun i hik => ?_⟩
  obtain ⟨D,e,f,hD,he,hf,hne,hdis⟩ := hshape i hik
  rw [← Fresh.Localisation.distInt_abs_mul,hdis]
  have ht : (u*((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h))*(((m : ℝ)+1/8)/u)=
      ((D : ℝ)+(e : ℝ)*g+(f : ℝ)*h)*((m : ℝ)+1/8) := by
    field_simp
  rw [ht]
  exact clear_packet g h m a b D e f hD he hf hne hg hh hsum

#print axioms clear_packet
#print axioms twoGapPacket_isolation
end Fresh.TwoGapPacketBand
