import Fresh.UnitAPPacketFourCharts

/-! Six closed native boundary charts for three consecutive AP readings.
Each retains the original integer windows and two extremal phase faces. -/
namespace Fresh.UnitAPPacketThreeCharts
open Fresh Fresh.Localisation
set_option maxHeartbeats 2000000

def carry (role : Fin 6) (i : Fin 3) : ℤ :=
  match role.val, i.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 1, 0 => 0
  | 1, 1 => 0
  | 1, 2 => 1
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => 1
  | 3, 0 => 0
  | 3, 1 => 1
  | 3, 2 => 1
  | 4, 0 => 0
  | 4, 1 => 1
  | 4, 2 => 1
  | 5, 0 => 0
  | 5, 1 => 1
  | 5, 2 => 2
  | _, _ => 0

def Chart (role : Fin 6) (x theta : ℝ) : Prop :=
  match role.val with
  | 0 => 0 ≤ theta ∧ theta ≤ (3/8 : ℝ) ∧
      (1/8 : ℝ) ≤ x+0*theta-0 ∧ x+2*theta-0 ≤ (7/8 : ℝ)
  | 1 => (1/4 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) ∧
      (1/8 : ℝ) ≤ x+2*theta-1 ∧ x+1*theta-0 ≤ (7/8 : ℝ)
  | 2 => (1/2 : ℝ) ≤ theta ∧ theta ≤ (3/4 : ℝ) ∧
      (1/8 : ℝ) ≤ x+0*theta-0 ∧ x+1*theta-0 ≤ (7/8 : ℝ)
  | 3 => (1/4 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) ∧
      (1/8 : ℝ) ≤ x+1*theta-1 ∧ x+0*theta-0 ≤ (7/8 : ℝ)
  | 4 => (1/2 : ℝ) ≤ theta ∧ theta ≤ (3/4 : ℝ) ∧
      (1/8 : ℝ) ≤ x+1*theta-1 ∧ x+2*theta-1 ≤ (7/8 : ℝ)
  | _ => (5/8 : ℝ) ≤ theta ∧ theta ≤ 1 ∧
      (1/8 : ℝ) ≤ x+2*theta-2 ∧ x+0*theta-0 ≤ (7/8 : ℝ)

theorem chart_windows (role : Fin 6) (x theta : ℝ) (hc : Chart role x theta) :
    ∀ i : Fin 3, (carry role i : ℝ)+1/8 ≤ x+(i : ℝ)*theta ∧
      x+(i : ℝ)*theta ≤ (carry role i : ℝ)+7/8 := by
  fin_cases role <;> dsimp [Chart] at hc
  all_goals obtain ⟨h0,h1,hl,hh⟩ := hc
  all_goals intro i; fin_cases i <;> norm_num [carry] <;> constructor <;> linarith

theorem chart_clear (role : Fin 6) (x theta : ℝ) (hc : Chart role x theta) :
    ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (x+(i : ℝ)*theta) := by
  intro i
  exact clear_of_window (carry role i) (chart_windows role x theta hc i).1 (chart_windows role x theta hc i).2

theorem clear_chart (x theta : ℝ) (hx0 : (1/8 : ℝ) ≤ x) (hx1 : x ≤ (7/8 : ℝ))
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1)
    (hc : ∀ i : Fin 3, (1/8 : ℝ) ≤ distInt (x+(i : ℝ)*theta)) :
    ∃ role : Fin 6, Chart role x theta := by
  let n1 : ℤ := ⌊x+1*theta⌋
  have hc1 : (1/8 : ℝ) ≤ distInt (x+1*theta) := by
    have hh := hc (1 : Fin 3)
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
    have hh := hc (2 : Fin 3)
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
  interval_cases n1 <;> interval_cases n2 <;> norm_num at hf1 hf2
  all_goals by_cases hhalf : theta ≤ (1/2 : ℝ)
  all_goals first
    | exact ⟨0,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨1,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨2,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨3,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨4,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exact ⟨5,by dsimp [Chart]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩⟩
    | exfalso; linarith

#print axioms chart_windows
#print axioms chart_clear
#print axioms clear_chart
end Fresh.UnitAPPacketThreeCharts
