import Fresh.APPhaseOpening

/-! Exact AP packet charts, selected from actual cascade controls.
[PROVISIONAL: counting tool] reference-opening placement is inherited.
[PROVISIONAL: covering] the finite parameter joins support the bounded-step laws. -/

namespace Fresh.APPhaseCharts
open Fresh Fresh.Localisation Fresh.APPhaseOpening

theorem packet_chart_0 (b x : ℝ) (hb : 1≤b) (hB : b≤(23 / 15 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤1 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤5 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 1 (by omega) (by omega) 0
    (lo:=(1 / 3 : ℝ)) (hi:=(7 / 20 : ℝ)) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(1 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_0

theorem packet_chart_1 (b x : ℝ) (hb : 1≤b) (hB : b≤(19 / 5 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤2 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤4 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 2 (by omega) (by omega) 3
    (lo:=(5 / 12 : ℝ)) (hi:=(1 / 2 : ℝ)) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(-2 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(-1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(-1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_1

theorem packet_chart_2 (b x : ℝ) (hb : 1≤b) (hB : b≤(47 / 12 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤3 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤3 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 3 (by omega) (by omega) 2
    (lo:=(1 / 4 : ℝ)) (hi:=(1 / 2 : ℝ)) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(-1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(-1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_2

theorem packet_chart_3 (b x : ℝ) (hb : (73 / 28 : ℝ)≤b) (hB : b≤(15 / 2 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤3 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤3 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 3 (by omega) (by omega) 3
    (lo:=(3 / 4 : ℝ)) (hi:=1) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(-3 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(-2 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(-1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_3

theorem packet_chart_4 (b x : ℝ) (hb : 1≤b) (hB : b≤(35 / 12 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤4 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤2 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 4 (by omega) (by omega) 0
    (lo:=0) (hi:=(3 / 8 : ℝ)) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_4

theorem packet_chart_5 (b x : ℝ) (hb : (61 / 21 : ℝ)≤b) (hB : b≤(95 / 12 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤4 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤2 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 4 (by omega) (by omega) 2
    (lo:=(5 / 8 : ℝ)) (hi:=1) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(-2 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(-1 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_5

theorem packet_chart_6 (b x : ℝ) (hb : (157 / 21 : ℝ)≤b) (hB : b≤(44 / 3 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤4 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤2 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 4 (by omega) (by omega) 2
    (lo:=(13 / 8 : ℝ)) (hi:=2) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(-4 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(-2 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_6

theorem packet_chart_7 (b x : ℝ) (hb : 1≤b) (hB : b≤(71 / 12 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤5 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤1 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 5 (by omega) (by omega) 0
    (lo:=0) (hi:=(3 / 4 : ℝ)) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_7

theorem packet_chart_8 (b x : ℝ) (hb : (485 / 84 : ℝ)≤b) (hB : b≤(167 / 12 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤5 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤1 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 5 (by omega) (by omega) 0
    (lo:=1) (hi:=(7 / 4 : ℝ)) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(1 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_8

theorem packet_chart_9 (b x : ℝ) (hb : (155 / 12 : ℝ)≤b) (hB : b≤(287 / 12 : ℝ))
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤5 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤1 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 5 (by omega) (by omega) 1
    (lo:=(9 / 4 : ℝ)) (hi:=3) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(-3 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_9

theorem packet_chart_10 (b x : ℝ) (hb : (275 / 12 : ℝ)≤b) (hB : b≤35)
    (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤5 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤1 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  obtain ⟨T,N,hT,hcore,hlo,hhi,hopen⟩ := phase_opening 5 (by omega) (by omega) 0
    (lo:=4) (hi:=(19 / 4 : ℝ)) (by linarith) hx (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  refine ⟨T,hT,hcore,?_⟩
  intro j hj
  interval_cases j
  · apply clear_of_window (N+(0 : ℤ)) <;> push_cast <;> nlinarith
  · apply clear_of_window (N+(4 : ℤ)) <;> push_cast <;> nlinarith

#print axioms packet_chart_10

theorem packet_bounded_r1 (b x : ℝ) (hb : 1≤b) (hB : b≤(23 / 15 : ℝ)) (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤1 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤5 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  exact packet_chart_0 b x (by linarith) hB hx

#print axioms packet_bounded_r1

theorem packet_bounded_r2 (b x : ℝ) (hb : 1≤b) (hB : b≤(19 / 5 : ℝ)) (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤2 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤4 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  exact packet_chart_1 b x (by linarith) hB hx

#print axioms packet_bounded_r2

theorem packet_bounded_r3 (b x : ℝ) (hb : 1≤b) (hB : b≤(15 / 2 : ℝ)) (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤3 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤3 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  by_cases h2 : b≤(47 / 12 : ℝ)
  · exact packet_chart_2 b x (by linarith) h2 hx
  exact packet_chart_3 b x (by linarith) hB hx

#print axioms packet_bounded_r3

theorem packet_bounded_r4 (b x : ℝ) (hb : 1≤b) (hB : b≤(44 / 3 : ℝ)) (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤4 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤2 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  by_cases h4 : b≤(35 / 12 : ℝ)
  · exact packet_chart_4 b x (by linarith) h4 hx
  by_cases h5 : b≤(95 / 12 : ℝ)
  · exact packet_chart_5 b x (by linarith) h5 hx
  exact packet_chart_6 b x (by linarith) hB hx

#print axioms packet_bounded_r4

theorem packet_bounded_r5 (b x : ℝ) (hb : 1≤b) (hB : b≤35) (hx : 96*b≤x) :
    ∃ T : ℝ, 0<T ∧ (∀ j : ℕ, 1≤j → j≤5 → (1/8 : ℝ)≤distInt ((j : ℝ)*T)) ∧
      ∀ j : ℕ, j≤1 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  by_cases h7 : b≤(71 / 12 : ℝ)
  · exact packet_chart_7 b x (by linarith) h7 hx
  by_cases h8 : b≤(167 / 12 : ℝ)
  · exact packet_chart_8 b x (by linarith) h8 hx
  by_cases h9 : b≤(287 / 12 : ℝ)
  · exact packet_chart_9 b x (by linarith) h9 hx
  exact packet_chart_10 b x (by linarith) hB hx

#print axioms packet_bounded_r5

end Fresh.APPhaseCharts
