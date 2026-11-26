import Fresh.NativeStrictRatioGuards

namespace Fresh.NativeRationalGuardPaths

open NativeStrictRatioGuards

structure Guard where
  source : Fin 7
  dest : Fin 7
  factor : ℚ
  strict : Bool
  deriving DecidableEq

/-- Rational guard interpreted on the real starting readings. -/
-- STANDING: DEFINITION
def Guard.valid (g : Guard) (r : Fin 7 → ℝ) : Prop :=
  Holds g.strict (r g.dest) ((g.factor : ℝ) * r g.source)

def walk (allowed : List Guard) (source : Fin 7) : List Guard → Option Guard
  | [] => some ⟨source, source, 1, false⟩
  | e :: rest => do
    if e.source = source ∧ e ∈ allowed ∧ 0 < e.factor then
      let tail ← walk allowed e.dest rest
      pure ⟨source, tail.dest, tail.factor * e.factor, e.strict || tail.strict⟩
    else none

theorem walk_sound (allowed : List Guard) (r : Fin 7 → ℝ)
    (h : ∀ g ∈ allowed, g.valid r) (source : Fin 7) (path : List Guard)
    {out : Guard} (hw : walk allowed source path = some out) :
    out.source = source ∧ 0 < out.factor ∧ out.valid r := by
  induction path generalizing source out with
  | nil =>
    simp [walk] at hw
    subst out
    simp [Guard.valid, Holds]
  | cons e rest ih =>
    by_cases he : e.source = source ∧ e ∈ allowed ∧ 0 < e.factor
    · cases ht : walk allowed e.dest rest with
      | none => simp [walk, he, ht] at hw
      | some tail =>
        have hc := ih e.dest ht
        simp [walk, he, ht] at hw
        subst out
        refine ⟨rfl, mul_pos hc.2.1 he.2.2, ?_⟩
        have hfirst := h e he.2.1
        have hsecond := hc.2.2
        unfold Guard.valid at hfirst hsecond ⊢
        rw [he.1] at hfirst
        rw [hc.1] at hsecond
        push_cast
        exact compose (by exact_mod_cast hc.2.1) _ _ hfirst hsecond
    · simp [walk, he] at hw

def verify (allowed : List Guard) (target : Guard) (path : List Guard) : Bool :=
  match walk allowed target.source path with
  | none => false
  | some result =>
    decide (result.dest = target.dest ∧
      (result.factor < target.factor ∨ result.factor = target.factor ∧
        (target.strict = true → result.strict = true)))

theorem verify_sound {allowed : List Guard} {target : Guard} {path : List Guard}
    (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i) (h : ∀ g ∈ allowed, g.valid r)
    (hv : verify allowed target path = true) : target.valid r := by
  cases hw : walk allowed target.source path with
  | none => simp [verify, hw] at hv
  | some out =>
    have hs := walk_sound allowed r h _ _ hw
    simp only [verify, hw, decide_eq_true_eq] at hv
    have hface : (out.factor : ℝ) < (target.factor : ℝ) ∨
        (out.factor : ℝ) = (target.factor : ℝ) ∧
          (target.strict = true → out.strict = true) := by
      rcases hv.2 with hlt | ⟨he, hp⟩
      · exact Or.inl (by exact_mod_cast hlt)
      · exact Or.inr ⟨by exact_mod_cast he, hp⟩
    have hc := hs.2.2
    unfold Guard.valid at hc ⊢
    rw [hs.1, hv.1] at hc
    exact weaken (hp _) _ _ hc hface

/-- One kernel-checked list supplies all retained guard implications. -/
theorem verify_all_sound {allowed : List Guard} {rows : List (Guard × List Guard)}
    (r : Fin 7 → ℝ) (hp : ∀ i, 0 < r i) (h : ∀ g ∈ allowed, g.valid r)
    (hv : rows.all (fun row => verify allowed row.1 row.2) = true) :
    ∀ row ∈ rows, row.1.valid r := by
  intro row hr
  exact verify_sound r hp h (List.all_eq_true.mp hv row hr)

#print axioms walk_sound
#print axioms verify_sound
#print axioms verify_all_sound

end Fresh.NativeRationalGuardPaths
