import Fresh.UnitAPPacketFourLift

/-! Four original AP phases have fourteen closed retained-window charts.
Each chart needs only the two extremal phase faces. Integer unit and base
laps remain explicit in consumers; this is no isolation-time selector. -/
namespace Fresh.UnitAPPacketFourCharts
open Fresh Fresh.Localisation
set_option maxHeartbeats 8000000

def carry (role : Fin 14) (i : Fin 4) : ℤ :=
  match role.val, i.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 0
  | 1, 3 => 1
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 0
  | 2, 3 => 1
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 2 => 1
  | 3, 3 => 1
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 2 => 1
  | 4, 3 => 1
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 1
  | 5, 3 => 2
  | 6, 0 => 0
  | 6, 1 => 0
  | 6, 2 => 1
  | 6, 3 => 2
  | 7, 0 => 0
  | 7, 1 => 1
  | 7, 2 => 1
  | 7, 3 => 1
  | 8, 0 => 0
  | 8, 1 => 1
  | 8, 2 => 1
  | 8, 3 => 1
  | 9, 0 => 0
  | 9, 1 => 1
  | 9, 2 => 1
  | 9, 3 => 2
  | 10, 0 => 0
  | 10, 1 => 1
  | 10, 2 => 1
  | 10, 3 => 2
  | 11, 0 => 0
  | 11, 1 => 1
  | 11, 2 => 2
  | 11, 3 => 2
  | 12, 0 => 0
  | 12, 1 => 1
  | 12, 2 => 2
  | 12, 3 => 2
  | 13, 0 => 0
  | 13, 1 => 1
  | 13, 2 => 2
  | 13, 3 => 3
  | _, _ => 0

def Chart (role : Fin 14) (x theta : ℝ) : Prop :=
  match role.val with
  | 0 => 0 ≤ theta ∧ theta ≤ (1/4 : ℝ) ∧
      (1/8 : ℝ) ≤ x+0*theta-0 ∧ x+3*theta-0 ≤ (7/8 : ℝ)
  | 1 => (1/4 : ℝ) ≤ theta ∧ theta ≤ (1/3 : ℝ) ∧
      (1/8 : ℝ) ≤ x+3*theta-1 ∧ x+2*theta-0 ≤ (7/8 : ℝ)
  | 2 => (1/3 : ℝ) ≤ theta ∧ theta ≤ (3/8 : ℝ) ∧
      (1/8 : ℝ) ≤ x+0*theta-0 ∧ x+2*theta-0 ≤ (7/8 : ℝ)
  | 3 => (1/4 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) ∧
      (1/8 : ℝ) ≤ x+2*theta-1 ∧ x+1*theta-0 ≤ (7/8 : ℝ)
  | 4 => (1/2 : ℝ) ≤ theta ∧ theta ≤ (7/12 : ℝ) ∧
      (1/8 : ℝ) ≤ x+0*theta-0 ∧ x+3*theta-1 ≤ (7/8 : ℝ)
  | 5 => (5/8 : ℝ) ≤ theta ∧ theta ≤ (2/3 : ℝ) ∧
      (1/8 : ℝ) ≤ x+3*theta-2 ∧ x+1*theta-0 ≤ (7/8 : ℝ)
  | 6 => (2/3 : ℝ) ≤ theta ∧ theta ≤ (3/4 : ℝ) ∧
      (1/8 : ℝ) ≤ x+0*theta-0 ∧ x+1*theta-0 ≤ (7/8 : ℝ)
  | 7 => (1/4 : ℝ) ≤ theta ∧ theta ≤ (1/3 : ℝ) ∧
      (1/8 : ℝ) ≤ x+1*theta-1 ∧ x+0*theta-0 ≤ (7/8 : ℝ)
  | 8 => (1/3 : ℝ) ≤ theta ∧ theta ≤ (3/8 : ℝ) ∧
      (1/8 : ℝ) ≤ x+1*theta-1 ∧ x+3*theta-1 ≤ (7/8 : ℝ)
  | 9 => (5/12 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) ∧
      (1/8 : ℝ) ≤ x+3*theta-2 ∧ x+0*theta-0 ≤ (7/8 : ℝ)
  | 10 => (1/2 : ℝ) ≤ theta ∧ theta ≤ (3/4 : ℝ) ∧
      (1/8 : ℝ) ≤ x+1*theta-1 ∧ x+2*theta-1 ≤ (7/8 : ℝ)
  | 11 => (5/8 : ℝ) ≤ theta ∧ theta ≤ (2/3 : ℝ) ∧
      (1/8 : ℝ) ≤ x+2*theta-2 ∧ x+0*theta-0 ≤ (7/8 : ℝ)
  | 12 => (2/3 : ℝ) ≤ theta ∧ theta ≤ (3/4 : ℝ) ∧
      (1/8 : ℝ) ≤ x+2*theta-2 ∧ x+3*theta-2 ≤ (7/8 : ℝ)
  | _ => (3/4 : ℝ) ≤ theta ∧ theta ≤ 1 ∧
      (1/8 : ℝ) ≤ x+3*theta-3 ∧ x+0*theta-0 ≤ (7/8 : ℝ)

theorem chart_windows (role : Fin 14) (x theta : ℝ) (hc : Chart role x theta) :
    ∀ i : Fin 4, (carry role i : ℝ)+1/8 ≤ x+(i : ℝ)*theta ∧
      x+(i : ℝ)*theta ≤ (carry role i : ℝ)+7/8 := by
  fin_cases role <;> dsimp [Chart] at hc
  all_goals obtain ⟨h0,h1,hl,hh⟩ := hc
  all_goals intro i; fin_cases i <;> norm_num [carry] <;> constructor <;> linarith

theorem chart_clear (role : Fin 14) (x theta : ℝ) (hc : Chart role x theta) :
    ∀ i : Fin 4, (1/8 : ℝ) ≤ distInt (x+(i : ℝ)*theta) := by
  intro i
  exact clear_of_window (carry role i) (chart_windows role x theta hc i).1 (chart_windows role x theta hc i).2

theorem clear_chart (x theta : ℝ) (hx0 : (1/8 : ℝ) ≤ x) (hx1 : x ≤ (7/8 : ℝ))
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hc : ∀ i : Fin 4, (1/8 : ℝ) ≤ distInt (x+(i : ℝ)*theta)) :
    ∃ role : Fin 14, Chart role x theta := by
  let n1 : ℤ := ⌊x+1*theta⌋
  have hc1 : (1/8 : ℝ) ≤ distInt (x+1*theta) := by
    have hh := hc (1 : Fin 4)
    norm_num at hh ⊢
    exact hh
  have hf1 := (clear_iff_fract _).mp hc1
  change (1/8 : ℝ) ≤ x+1*theta-(n1 : ℝ) ∧ x+1*theta-(n1 : ℝ) ≤ 7/8 at hf1
  have hn1loR : (-1 : ℝ) < n1 := by linarith [hf1.2]
  have hn1hiR : (n1 : ℝ) < 2 := by linarith [hf1.1]
  have hn1loZ : (-1 : ℤ) < n1 := by exact_mod_cast hn1loR
  have hn1hiZ : n1 < (2 : ℤ) := by exact_mod_cast hn1hiR
  have hn1lo : (0 : ℤ) ≤ n1 := by omega
  have hn1hi : n1 ≤ (1 : ℤ) := by omega
  let n2 : ℤ := ⌊x+2*theta⌋
  have hc2 : (1/8 : ℝ) ≤ distInt (x+2*theta) := by
    have hh := hc (2 : Fin 4)
    norm_num at hh ⊢
    exact hh
  have hf2 := (clear_iff_fract _).mp hc2
  change (1/8 : ℝ) ≤ x+2*theta-(n2 : ℝ) ∧ x+2*theta-(n2 : ℝ) ≤ 7/8 at hf2
  have hn2loR : (-1 : ℝ) < n2 := by linarith [hf2.2]
  have hn2hiR : (n2 : ℝ) < 3 := by linarith [hf2.1]
  have hn2loZ : (-1 : ℤ) < n2 := by exact_mod_cast hn2loR
  have hn2hiZ : n2 < (3 : ℤ) := by exact_mod_cast hn2hiR
  have hn2lo : (0 : ℤ) ≤ n2 := by omega
  have hn2hi : n2 ≤ (2 : ℤ) := by omega
  let n3 : ℤ := ⌊x+3*theta⌋
  have hc3 : (1/8 : ℝ) ≤ distInt (x+3*theta) := by
    have hh := hc (3 : Fin 4)
    norm_num at hh ⊢
    exact hh
  have hf3 := (clear_iff_fract _).mp hc3
  change (1/8 : ℝ) ≤ x+3*theta-(n3 : ℝ) ∧ x+3*theta-(n3 : ℝ) ≤ 7/8 at hf3
  have hn3loR : (-1 : ℝ) < n3 := by linarith [hf3.2]
  have hn3hiR : (n3 : ℝ) < 4 := by linarith [hf3.1]
  have hn3loZ : (-1 : ℤ) < n3 := by exact_mod_cast hn3loR
  have hn3hiZ : n3 < (4 : ℤ) := by exact_mod_cast hn3hiR
  have hn3lo : (0 : ℤ) ≤ n3 := by omega
  have hn3hi : n3 ≤ (3 : ℤ) := by omega
  interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;> norm_num at hf1 hf2 hf3
  all_goals try (exfalso; linarith)
  all_goals by_cases hthird : theta ≤ (1/3 : ℝ)
  all_goals by_cases hhalf : theta ≤ (1/2 : ℝ)
  all_goals by_cases htwothirds : theta ≤ (2/3 : ℝ)
  all_goals first
    | exact ⟨0,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨1,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨2,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨3,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨4,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨5,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨6,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨7,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨8,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨9,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨10,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨11,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨12,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨13,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exfalso; linarith

#print axioms chart_windows
#print axioms chart_clear
#print axioms clear_chart
end Fresh.UnitAPPacketFourCharts
