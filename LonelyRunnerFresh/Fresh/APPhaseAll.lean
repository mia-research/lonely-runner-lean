import Fresh.APPhaseCharts

/-! Every positive step ratio b≥1 for an AP core and an AP packet.
[PROVISIONAL: covering] the finite bounded-step joins are supplied by exact
anchor charts. [PROVISIONAL: counting tool] the unbounded end derives its
common AP cycle; no lap cap or density is used.
-/
namespace Fresh.APPhaseCharts
open Fresh Fresh.APPhaseOpening

theorem ap_packet_all (r : ℕ) (hr1 : 1≤r) (hr5 : r≤5) (x b : ℝ)
    (hb : 1≤b) (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1≤j → j≤r → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤6-r → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  interval_cases r
  · by_cases hB : b≤23/15
    · exact packet_bounded_r1 b x hb hB hx
    · exact ap_packet_large 1 (by omega) (by omega) hb hx (by norm_num; linarith)
  · by_cases hB : b≤19/5
    · exact packet_bounded_r2 b x hb hB hx
    · exact ap_packet_large 2 (by omega) (by omega) hb hx (by norm_num; linarith)
  · by_cases hB : b≤15/2
    · exact packet_bounded_r3 b x hb hB hx
    · exact ap_packet_large 3 (by omega) (by omega) hb hx (by norm_num; linarith)
  · by_cases hB : b≤44/3
    · exact packet_bounded_r4 b x hb hB hx
    · exact ap_packet_large 4 (by omega) (by omega) hb hx (by norm_num; linarith)
  · by_cases hB : b≤35
    · exact packet_bounded_r5 b x hb hB hx
    · exact ap_packet_large 5 (by omega) (by omega) hb hx (by norm_num; linarith)

#print axioms ap_packet_all
end Fresh.APPhaseCharts
