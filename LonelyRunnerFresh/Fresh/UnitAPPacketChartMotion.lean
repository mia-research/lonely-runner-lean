import Fresh.UnitAPPacketFourCharts

/-! D_min transport of original packet windows. A positive time advance
retains every lower face; only the appropriate upper face can close. -/
namespace Fresh.UnitAPPacketChartMotion
set_option maxHeartbeats 2000000
open Fresh Fresh.UnitAPPacketFourCharts

noncomputable def lo (role : Fin 14) : ℝ :=
  match role.val with
  | 0 => 0
  | 1 => (1/4 : ℝ)
  | 2 => (1/3 : ℝ)
  | 3 => (1/4 : ℝ)
  | 4 => (1/2 : ℝ)
  | 5 => (5/8 : ℝ)
  | 6 => (2/3 : ℝ)
  | 7 => (1/4 : ℝ)
  | 8 => (1/3 : ℝ)
  | 9 => (5/12 : ℝ)
  | 10 => (1/2 : ℝ)
  | 11 => (5/8 : ℝ)
  | 12 => (2/3 : ℝ)
  | _ => (3/4 : ℝ)

noncomputable def hi (role : Fin 14) : ℝ :=
  match role.val with
  | 0 => (1/4 : ℝ)
  | 1 => (1/3 : ℝ)
  | 2 => (3/8 : ℝ)
  | 3 => (1/2 : ℝ)
  | 4 => (7/12 : ℝ)
  | 5 => (2/3 : ℝ)
  | 6 => (3/4 : ℝ)
  | 7 => (1/3 : ℝ)
  | 8 => (3/8 : ℝ)
  | 9 => (1/2 : ℝ)
  | 10 => (3/4 : ℝ)
  | 11 => (2/3 : ℝ)
  | 12 => (3/4 : ℝ)
  | _ => 1

def minimum (role : Fin 14) : Fin 4 :=
  match role.val with
  | 0 => 0
  | 1 => 3
  | 2 => 0
  | 3 => 2
  | 4 => 0
  | 5 => 3
  | 6 => 0
  | 7 => 1
  | 8 => 1
  | 9 => 3
  | 10 => 1
  | 11 => 2
  | 12 => 2
  | _ => 3

def maximum (role : Fin 14) : Fin 4 :=
  match role.val with
  | 0 => 3
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | 4 => 3
  | 5 => 1
  | 6 => 1
  | 7 => 0
  | 8 => 3
  | 9 => 0
  | 10 => 2
  | 11 => 0
  | 12 => 3
  | _ => 0

def Sector (role : Fin 14) (theta : ℝ) : Prop := lo role ≤ theta ∧ theta ≤ hi role

def Compatible (before after : Fin 14) : Prop := ∀ i : Fin 4, carry before i=carry after i

theorem chart_sector (role : Fin 14) (x theta : ℝ) (hc : Chart role x theta) : Sector role theta := by
  fin_cases role <;> exact ⟨hc.1,hc.2.1⟩

theorem from_extrema (role : Fin 14) (x theta : ℝ) (hs : Sector role theta)
    (hl : (1/8 : ℝ) ≤ x+(minimum role : ℝ)*theta-(carry role (minimum role) : ℝ))
    (hh : x+(maximum role : ℝ)*theta-(carry role (maximum role) : ℝ) ≤ (7/8 : ℝ)) : Chart role x theta := by
  fin_cases role <;> norm_num [Sector,lo,hi,minimum,maximum,carry,Chart] at * <;> tauto

theorem transport (before after : Fin 14) (x theta base delta : ℝ)
    (hc : Chart before x theta) (hlabels : Compatible before after)
    (hbase : 0 ≤ base) (hd : 0 ≤ delta) (hs : Sector after (theta+delta))
    (hclosing : x+(maximum after : ℝ)*theta-(carry after (maximum after) : ℝ)+
      (base+(maximum after : ℝ))*delta ≤ (7/8 : ℝ)) :
    Chart after (x+base*delta) (theta+delta) := by
  apply from_extrema after _ _ hs
  · have hlow := (chart_windows before x theta hc (minimum after)).1
    rw [hlabels] at hlow
    have hi : (0 : ℝ) ≤ (minimum after : ℝ) := Nat.cast_nonneg _
    have hinc := mul_nonneg (add_nonneg hbase hi) hd
    nlinarith only [hlow,hinc]
  · nlinarith only [hclosing]

def ShiftCompatible (before after : Fin 14) (shift : ℤ) : Prop :=
  ∀ i : Fin 4, carry before i=carry after i+(i.val : ℤ)*shift

theorem transport_rebased (before after : Fin 14) (shift : ℤ) (x theta base delta : ℝ)
    (hc : Chart before x theta) (hlabels : ShiftCompatible before after shift)
    (hbase : 0 ≤ base) (hd : 0 ≤ delta) (hs : Sector after (theta+delta-(shift : ℝ)))
    (hclosing : x+(maximum after : ℝ)*theta-(carry before (maximum after) : ℝ)+
      (base+(maximum after : ℝ))*delta ≤ (7/8 : ℝ)) :
    Chart after (x+base*delta) (theta+delta-(shift : ℝ)) := by
  apply from_extrema after _ _ hs
  · have hlow := (chart_windows before x theta hc (minimum after)).1
    have hlabel := congrArg (fun z : ℤ => (z : ℝ)) (hlabels (minimum after))
    push_cast at hlabel
    have hi : (0 : ℝ) ≤ (minimum after : ℝ) := Nat.cast_nonneg _
    have hinc := mul_nonneg (add_nonneg hbase hi) hd
    nlinarith only [hlow,hlabel,hinc]
  · have hlabel := congrArg (fun z : ℤ => (z : ℝ)) (hlabels (maximum after))
    push_cast at hlabel
    nlinarith only [hclosing,hlabel]

theorem whole_unit_join : ShiftCompatible 13 0 1 := by
  intro i
  fin_cases i <;> norm_num [carry]

#print axioms transport_rebased
#print axioms whole_unit_join
theorem forward_roles (before after : Fin 14) (theta theta' : ℝ)
    (hlabels : Compatible before after) (hb : Sector before theta) (ha : Sector after theta')
    (ht : theta < theta') :
    before=after ∨ (before=1 ∧ after=2) ∨ (before=3 ∧ after=4) ∨
      (before=5 ∧ after=6) ∨ (before=7 ∧ after=8) ∨
      (before=9 ∧ after=10) ∨ (before=11 ∧ after=12) := by
  have h1 := hlabels 1
  have h2 := hlabels 2
  have h3 := hlabels 3
  dsimp [Sector] at hb ha
  clear hlabels
  fin_cases before <;> fin_cases after <;> simp_all [carry,lo,hi] <;> linarith

#print axioms forward_roles
#print axioms chart_sector
#print axioms from_extrema
#print axioms transport
end Fresh.UnitAPPacketChartMotion
