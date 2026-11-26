import Fresh.UnitAPPacketThreeCharts

/-! Native three-packet faces and their D_min transport. Compatible original
integer labels permit six self roles and two forward joins. -/
namespace Fresh.UnitAPPacketThreeMotion
open Fresh Fresh.UnitAPPacketThreeCharts
set_option maxHeartbeats 2000000

noncomputable def lo (role : Fin 6) : ℝ :=
  match role.val with
  | 0 => 0
  | 1 => 1/4
  | 2 => 1/2
  | 3 => 1/4
  | 4 => 1/2
  | _ => 5/8

noncomputable def hi (role : Fin 6) : ℝ :=
  match role.val with
  | 0 => 3/8
  | 1 => 1/2
  | 2 => 3/4
  | 3 => 1/2
  | 4 => 3/4
  | _ => 1

def minimum (role : Fin 6) : Fin 3 :=
  match role.val with
  | 0 => 0
  | 1 => 2
  | 2 => 0
  | 3 => 1
  | 4 => 1
  | _ => 2

def maximum (role : Fin 6) : Fin 3 :=
  match role.val with
  | 0 => 2
  | 1 => 1
  | 2 => 1
  | 3 => 0
  | 4 => 2
  | _ => 0

def Sector (role : Fin 6) (theta : ℝ) : Prop := lo role ≤ theta ∧ theta ≤ hi role

def Compatible (before after : Fin 6) : Prop := ∀ i : Fin 3, carry before i=carry after i

def ShiftCompatible (before after : Fin 6) (shift : ℤ) : Prop :=
  ∀ i : Fin 3, carry before i=carry after i+(i.val : ℤ)*shift

theorem chart_sector (role : Fin 6) (x theta : ℝ) (hc : Chart role x theta) : Sector role theta := by
  fin_cases role <;> exact ⟨hc.1,hc.2.1⟩

theorem from_extrema (role : Fin 6) (x theta : ℝ) (hs : Sector role theta)
    (hl : (1/8 : ℝ) ≤ x+(minimum role : ℝ)*theta-(carry role (minimum role) : ℝ))
    (hh : x+(maximum role : ℝ)*theta-(carry role (maximum role) : ℝ) ≤ (7/8 : ℝ)) : Chart role x theta := by
  fin_cases role <;> norm_num [Sector,lo,hi,minimum,maximum,carry,Chart] at * <;> tauto

theorem transport (before after : Fin 6) (x theta base delta : ℝ)
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

theorem transport_rebased (before after : Fin 6) (shift : ℤ) (x theta base delta : ℝ)
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

theorem whole_unit_join : ShiftCompatible 5 0 1 := by
  intro i
  fin_cases i <;> norm_num [carry]

theorem forward_roles (before after : Fin 6) (theta theta' : ℝ)
    (hlabels : Compatible before after) (hb : Sector before theta) (ha : Sector after theta')
    (ht : theta < theta') : before=after ∨ (before=1 ∧ after=2) ∨ (before=3 ∧ after=4) := by
  have h1 := hlabels 1
  have h2 := hlabels 2
  dsimp [Sector] at hb ha
  clear hlabels
  fin_cases before <;> fin_cases after <;> simp_all [carry,lo,hi] <;> linarith

#print axioms chart_sector
#print axioms from_extrema
#print axioms transport
#print axioms transport_rebased
#print axioms whole_unit_join
#print axioms forward_roles
end Fresh.UnitAPPacketThreeMotion
