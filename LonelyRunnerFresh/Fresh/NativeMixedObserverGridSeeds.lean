import Fresh.NativeTwoAnchorPhysicalTransport

/-! Four exact native changed-label recovery seeds and their independent
AP/grid lifts. Every physical reading independently chooses a seed residue
and an integer lift; a positive-label own anchor supplies the canonical
join. This is a proved family, not an exhaustive list of arrangements. -/
namespace Fresh.NativeMixedObserverGridSeeds
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnHandoff
  Fresh.NativeCanonicalReturn Fresh.FastestCaptureRetention

noncomputable def base (z : Fin 4) (i : Fin 7) : ℝ :=
  match z.val,i.val with
  | 0,0 => 71/8
  | 0,1 => 263/8
  | 0,2 => 327/8
  | 0,3 => 1095/8
  | 0,4 => 1/1
  | 0,5 => 1/8
  | 0,6 => 79/9
  | 1,0 => 903/8
  | 1,1 => 3591/8
  | 1,2 => 4615/8
  | 1,3 => 15239/8
  | 1,4 => 2/1
  | 1,5 => 1/8
  | 1,6 => 583/9
  | 2,0 => 135/8
  | 2,1 => 263/8
  | 2,2 => 903/8
  | 2,3 => 128000000000007/8
  | 2,4 => 2/1
  | 2,5 => 1/8
  | 2,6 => 151/9
  | 3,0 => 3143/8
  | 3,1 => 12551/8
  | 3,2 => 16135/8
  | 3,3 => 53319/8
  | 3,4 => 7/1
  | 3,5 => 1/8
  | 3,6 => 2023/9
  | _,_ => 0

noncomputable def ending (z : Fin 4) : ℝ := ![(305/263 : ℝ),(3833/3591 : ℝ),(977/903 : ℝ),(16449/16135 : ℝ)] z
noncomputable def entry (z : Fin 4) : ℝ := ![(729/632 : ℝ),(4977/4664 : ℝ),(1305/1208 : ℝ),(16497/16184 : ℝ)] z
def K (z : Fin 4) : ℤ := ![1,2,2,7] z
def P (z : Fin 4) : ℤ := ![79,583,151,2023] z
def R (z : Fin 4) : ℤ := ![263,3591,903,16135] z
def L (z : Fin 4) : ℤ := ![10,69,18,229] z
def M (z : Fin 4) : ℤ := ![38,479,122,2056] z
def anchor (z : Fin 4) : Fin 7 := ![1,1,2,2] z
def terminalLabel (z : Fin 4) (i : Fin 7) : ℤ := ![![10,38,47,158,1,0,10],![120,479,615,2033,2,0,69],![18,35,122,17311184939092,2,0,18],![400,1599,2056,6794,7,0,229]] z i

noncomputable def step (z : Fin 4) : ℝ := 8*(P z : ℝ)*(R z : ℝ)*(K z : ℝ)
def terminalStep (z : Fin 4) : ℤ := P z*8*K z*(8*M z+1)

theorem parameter_faces (z : Fin 4) :
    0<(K z : ℝ) ∧ (9 : ℝ)*(base z 6*1)=(P z : ℝ) ∧
    (8 : ℝ)*(base z (anchor z)*1)=(R z : ℝ) ∧
    base z 6*entry z=(L z : ℝ)+1/8 ∧
    base z (anchor z)*ending z=(M z : ℝ)+1/8 ∧
    0<M z ∧ 0<terminalStep z ∧ 0<ending z := by
  fin_cases z <;> norm_num [K,P,R,L,M,base,anchor,entry,ending,terminalStep]

theorem seed_windows (z : Fin 4) (i : Fin 7) :
    (terminalLabel z i : ℝ)+1/8 ≤ base z i*ending z ∧
      base z i*ending z ≤ (terminalLabel z i : ℝ)+7/8 := by
  fin_cases z <;> fin_cases i <;> norm_num [base,ending,terminalLabel]

theorem lifted_position (z : Fin 4) (q : ℝ) (j : ℤ) :
    (q+step z*(j : ℝ))*ending z=q*ending z+(j*terminalStep z : ℤ) := by
  have hh := parameter_faces z
  have hx := Fresh.NativeTwoAnchorGridTransport.two_anchor_shifts
    (K z : ℝ) (base z 6) (base z (anchor z)) q 1 (entry z) (ending z)
    (K z) (P z) 9 (R z) 8 (L z) (M z) j hh.1 (by ring) hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2.1
  convert hx.2.2.2 using 1 <;> dsimp [step,terminalStep] <;> push_cast <;> ring

theorem lifted_clear (z : Fin 4) (i : Fin 7) (j : ℤ) :
    1/8 ≤ distInt ((base z i+step z*(j : ℝ))*ending z) := by
  rw [lifted_position,distInt_add_int]
  exact clear_of_window (terminalLabel z i) (seed_windows z i).1 (seed_windows z i).2

-- STANDING: DEFINITION
noncomputable def Class (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (z : Fin 4) (g : Fin 8) (f : Fin 8 → Fin 7) (j : Fin 8 → ℤ),
    g≠k ∧ f g=anchor z ∧ 0 ≤ j g ∧
    ∀ i : Fin 8,i≠k → reading v k i=base z (f i)+step z*(j i : ℝ)

theorem class_point {v : Fin 8 → ℝ} {k : Fin 8} (z : Fin 4)
    (f : Fin 8 → Fin 7) (j : Fin 8 → ℤ)
    (hr : ∀ i : Fin 8,i≠k → reading v k i=base z (f i)+step z*(j i : ℝ)) :
    IsolatedAt v k (ending z) := by
  apply (isolatedAt_iff_lonelyAt v k _).2
  intro x hx
  obtain ⟨i,hi,rfl⟩ := mem_disparitySet.mp hx
  change 1/8 ≤ distInt (reading v k i*ending z)
  rw [hr i hi]
  exact lifted_clear z (f i) (j i)

theorem class_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) :
    CanonicalReturnClass v k := by
  obtain ⟨hv,z,g,f,j,hg,hfg,hj,hr⟩ := h
  have hpoint := class_point z f j hr
  have hh := parameter_faces z
  have hown : reading v k g*ending z=((M z+j g*terminalStep z : ℤ) : ℝ)+1/8 := by
    rw [hr g hg,hfg,lifted_position,hh.2.2.2.2.1]
    push_cast
    ring
  have hlabel : 0<M z+j g*terminalStep z := by
    have hmul := mul_nonneg hj (le_of_lt hh.2.2.2.2.2.2.1)
    omega
  exact Fresh.NativeArbitraryThirdReversal.anchored_point_into_canonical hv k g _ _ hg hlabel hown hpoint

theorem class_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : Class v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (class_into_canonical h)

-- STANDING: DEFINITION
noncomputable def ScaledClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ c : ℝ,0<c ∧ Class (fun i=>c*v i) k

theorem scaled_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ScaledClass v k) : Isolation v k := by
  obtain ⟨_hv,c,hc,hbase⟩ := h
  exact Fresh.ProvedTypesScale.Isolation_smul_of hc (class_isolation hbase)

#print axioms parameter_faces
#print axioms seed_windows
#print axioms lifted_position
#print axioms lifted_clear
#print axioms class_point
#print axioms class_into_canonical
#print axioms class_isolation
#print axioms scaled_isolation
end Fresh.NativeMixedObserverGridSeeds
