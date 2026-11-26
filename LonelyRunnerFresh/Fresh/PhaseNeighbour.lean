import Fresh.Localisation

/-! Rules: 1–4, 8–18. Native neighbour geometry for an explicitly given
lifted AP phase. Original full-cascade controls precede this lemma:
phase_neighbour_map_v1.py/json. No arbitrary arrangement representation
or existence of such a lift is asserted. Internal subjects retain an
opposite endpoint neighbour, giving the closed7/8 edge from totalspan1.
-/
namespace Fresh.PhaseNeighbour
open Fresh

/-- Adjacent retained phase gaps separate every ordered pair. -/
theorem phase_separation (X : Fin 8→ℝ)
    (hgap : ∀i : Fin 7,(1/8 : ℝ)≤X i.succ-X i.castSucc)
    (i j : Fin 8) (hij : i<j) : (1/8 : ℝ)≤X j-X i := by
  let Y : Fin 8→ℝ := fun i=>X i-((i : ℕ) : ℝ)/8
  have hmono : Monotone Y := by
    apply Fin.monotone_iff_le_succ.mpr
    intro a
    have hh := hgap a
    change X a.castSucc-((a : ℕ) : ℝ)/8≤X a.succ-(((a : ℕ)+1 : ℕ) : ℝ)/8
    push_cast
    linarith
  have hh := hmono hij.le
  have hn : (i : ℕ)+1≤(j : ℕ) := Nat.succ_le_of_lt hij
  have hnR : ((i : ℕ) : ℝ)+1≤((j : ℕ) : ℝ) := by exact_mod_cast hn
  dsimp [Y] at hh
  linarith

/-- A supplied lifted phase isolates every internal subject at that exact
instant. Integer lap labels remain explicit for every physical reading. -/
theorem phase_neighbour (V X : Fin 8→ℝ) (N : Fin 8→ℤ) (T : ℝ)
    (hphase : ∀i,V i*T=X i+(N i : ℝ))
    (hgap : ∀i : Fin 7,(1/8 : ℝ)≤X i.succ-X i.castSucc)
    (hspan : X (7 : Fin 8)-X 0≤1)
    (k : Fin 8) (hk1 : 1≤(k : ℕ)) (hk6 : (k : ℕ)≤6) :
    IsolatedAt V k T := by
  have hmono : Monotone X := by
    apply Fin.monotone_iff_le_succ.mpr
    intro a
    have := hgap a
    linarith
  have hleft := phase_separation X hgap (0 : Fin 8) k (by change 0<(k : ℕ);omega)
  have hright := phase_separation X hgap k (7 : Fin 8) (by change (k : ℕ)<7;omega)
  intro i hik
  have hmin : X 0≤X i := hmono (by
    change (0 : ℕ) ≤ (i : ℕ)
    exact Nat.zero_le _)
  have hmax : X i≤X (7 : Fin 8) := hmono (by
    change (i : ℕ) ≤ 7
    have hi := i.isLt
    omega)
  have he : (V i-V k)*T=X i-X k+((N i-N k : ℤ) : ℝ) := by
    rw [sub_mul,hphase i,hphase k]
    push_cast
    ring
  rcases lt_or_gt_of_ne hik with hlt | hgt
  · have hs := phase_separation X hgap i k hlt
    apply Fresh.Localisation.clear_of_window (N i-N k-1)
    all_goals rw [he]
    all_goals push_cast
    all_goals linarith
  · have hs := phase_separation X hgap k i hgt
    apply Fresh.Localisation.clear_of_window (N i-N k)
    all_goals rw [he]
    all_goals push_cast
    all_goals linarith

/-- Positive-time consumer of the same explicit lifted geometry. -/
theorem internal_isolation (V X : Fin 8→ℝ) (N : Fin 8→ℤ) (T : ℝ)
    (hT : 0<T) (hphase : ∀i,V i*T=X i+(N i : ℝ))
    (hgap : ∀i : Fin 7,(1/8 : ℝ)≤X i.succ-X i.castSucc)
    (hspan : X (7 : Fin 8)-X 0≤1)
    (k : Fin 8) (hk1 : 1≤(k : ℕ)) (hk6 : (k : ℕ)≤6) :
    Isolation V k :=
  ⟨T,hT,phase_neighbour V X N T hphase hgap hspan k hk1 hk6⟩

#print axioms phase_separation
#print axioms phase_neighbour
#print axioms internal_isolation
end Fresh.PhaseNeighbour
