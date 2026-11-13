import Mathlib

namespace Fresh.FilterAssembly
/-- The per-coordinate raw-box face's lower end: `max(2n-1, 2)/2` — the nearest-integer box
`ρ ∈ [n - 1/2, n + 1/2]` cut at `1` (readings are at least the least reading `1`). -/
-- STANDING: DEFINITION
noncomputable def FaceLo (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2

/-- The per-coordinate raw-box face's upper end: `(2n+1)/2`. -/
-- STANDING: DEFINITION
noncomputable def FaceHi (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((2 * n i + 1 : ℤ) : ℝ) / 2
end Fresh.FilterAssembly

namespace Fresh.UClosure

open Fresh.FilterAssembly

/-! ## 1. Bounds, tables, realizability (the ratio-system semantics) -/

/-- One stored bound `(c, s)`: the ratio is `≤ c` (strictly `< c` iff `s`).  `none` = unbounded
(loosest).  Verbatim data of `m4comp_lib_v1.py`'s `U[i][j] = (value, strict)` entries with
`INF = None`. -/
abbrev UBound := Option (ℚ × Bool)

/-- The semantic of one stored bound `(c, s)` on a real ratio `x`. -/
-- STANDING: DEFINITION
def BHolds : Bool → ℝ → ℚ → Prop
  | true, x, c => x < (c : ℝ)
  | false, x, c => x ≤ (c : ℝ)

/-- The semantic of one table entry ( ∀-form, so no match reduction is ever needed). -/
-- STANDING: DEFINITION
def BHoldsOf (b : UBound) (x : ℝ) : Prop :=
  ∀ c : ℚ, ∀ s : Bool, b = some (c, s) → BHolds s x c

/-- The entry-semantic helpers. -/
theorem bhof_none {x : ℝ} : BHoldsOf none x := fun _ _ hb => absurd hb (by simp)

theorem bhof_some {x : ℝ} {c : ℚ} {s : Bool} (h : BHolds s x c) : BHoldsOf (some (c, s)) x :=
  fun _ _ hb => by
    rw [Option.some.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact h

theorem bhof_some_of {x : ℝ} {b : UBound} {c : ℚ} {s : Bool} (hb : b = some (c, s))
    (h : BHolds s x c) : BHoldsOf b x := by
  rw [hb]
  exact bhof_some h

theorem bhof_none_of {x : ℝ} {b : UBound} (hb : b = none) : BHoldsOf b x := by
  rw [hb]
  exact bhof_none

theorem bhof_eq_some {x : ℝ} {b : UBound} {c : ℚ} {s : Bool} (h : BHoldsOf b x)
    (hb : b = some (c, s)) : BHolds s x c := h c s hb

#print axioms bhof_none
#print axioms bhof_some
#print axioms bhof_some_of
#print axioms bhof_none_of
#print axioms bhof_eq_some

/-- A ratio table: `U i j` bounds `ρ i / ρ j` (`U[i][j] = sup ρᵢ/ρⱼ` in the artifact). -/
def UTable := Fin 7 → Fin 7 → UBound

/-- Realizability: the readings `ρ` (all positive in our uses) satisfy every bound. -/
-- STANDING: DEFINITION
def UFine (ρ : Fin 7 → ℝ) (U : UTable) : Prop := ∀ i j, BHoldsOf (U i j) (ρ i / ρ j)

/-- A satisfied bound has a positive value (the readings are positive). -/
theorem bpos_of_holds {x : ℝ} (hx : 0 < x) {c : ℚ} {s : Bool} (h : BHolds s x c) : 0 < c := by
  cases s <;> simp only [BHolds] at h
  · exact Rat.cast_pos.mp (lt_of_lt_of_le hx h)
  · exact Rat.cast_pos.mp (lt_trans hx h)

#print axioms bpos_of_holds

/-! ## 2. Link 2 — the ratio-chain arithmetic (difference constraints after x = log ρ) -/

/-- Two chained ratio bounds compose: `(u/v ≤|< A) → (v/w ≤|< C) → u/w ≤ A·C` with the
strictness OR-ed — the two-edge case of the log-sum/difference-constraint composition. -/
theorem bh_le_mul2 {u v w : ℝ} {A C : ℚ} (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : u / v ≤ (A : ℝ)) (h2 : v / w ≤ (C : ℝ)) : u / w ≤ ((A * C : ℚ) : ℝ) := by
  rw [Rat.cast_mul]
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have e1 : u ≤ (A : ℝ) * v := (div_le_iff₀ hv).mp h1
  have e2 : v ≤ (C : ℝ) * w := (div_le_iff₀ hw).mp h2
  have h : u ≤ (A : ℝ) * (C : ℝ) * w := by
    calc u ≤ (A : ℝ) * v := e1
      _ ≤ (A : ℝ) * ((C : ℝ) * w) := mul_le_mul_of_nonneg_left e2 hA'.le
      _ = (A : ℝ) * (C : ℝ) * w := by ring
  exact (div_le_iff₀ hw).mpr h

#print axioms bh_le_mul2

/-- Strict on the first factor. -/
theorem bh_lt_mul2_left {u v w : ℝ} {A C : ℚ} (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : u / v < (A : ℝ)) (h2 : v / w ≤ (C : ℝ)) : u / w < ((A * C : ℚ) : ℝ) := by
  rw [Rat.cast_mul]
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have e1 : u < (A : ℝ) * v := (div_lt_iff₀ hv).mp h1
  have e2 : v ≤ (C : ℝ) * w := (div_le_iff₀ hw).mp h2
  have h : u < (A : ℝ) * (C : ℝ) * w := by
    calc u < (A : ℝ) * v := e1
      _ ≤ (A : ℝ) * ((C : ℝ) * w) := mul_le_mul_of_nonneg_left e2 hA'.le
      _ = (A : ℝ) * (C : ℝ) * w := by ring
  exact (div_lt_iff₀ hw).mpr h

#print axioms bh_lt_mul2_left

/-- Strict on the second factor. -/
theorem bh_lt_mul2_right {u v w : ℝ} {A C : ℚ} (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : u / v ≤ (A : ℝ)) (h2 : v / w < (C : ℝ)) : u / w < ((A * C : ℚ) : ℝ) := by
  rw [Rat.cast_mul]
  have hA' : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have e1 : u ≤ (A : ℝ) * v := (div_le_iff₀ hv).mp h1
  have e2 : v < (C : ℝ) * w := (div_lt_iff₀ hw).mp h2
  have h : u < (A : ℝ) * (C : ℝ) * w := by
    calc u ≤ (A : ℝ) * v := e1
      _ < (A : ℝ) * ((C : ℝ) * w) := mul_lt_mul_of_pos_left e2 hA'
      _ = (A : ℝ) * (C : ℝ) * w := by ring
  exact (div_lt_iff₀ hw).mpr h

#print axioms bh_lt_mul2_right

/-- The two-link composition with strictness flags OR-ed (the `||`-propagation of `add`). -/
theorem bhold_mul2 (f1 f2 : Bool) {u v w : ℝ} {A C : ℚ}
    (hv : 0 < v) (hw : 0 < w) (hA : 0 < A) (hC : 0 < C)
    (h1 : BHolds f1 (u / v) A) (h2 : BHolds f2 (v / w) C) :
    BHolds (f1 || f2) (u / w) (A * C) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  cases f1 <;> cases f2 <;>
    simp only [BHolds, Bool.true_or, Bool.false_or] at h1 h2 ⊢
  · exact bh_le_mul2 hv hw hA hC h1 h2
  · exact bh_lt_mul2_right hv hw hA hC h1 h2
  · exact bh_lt_mul2_left hv hw hA hC h1 h2
  · exact bh_lt_mul2_left hv hw hA hC h1 (le_of_lt h2)

#print axioms bhold_mul2

/-- Three chained bounds compose with strictness OR-ed — the full propagation law for one
`add` step (`p → i → j → q` through the added constraint). -/
theorem bhold3 (f1 f2 f3 : Bool) {x1 x2 x3 x4 : ℝ} {A C B : ℚ}
    (h1 : 0 < x1) (h2 : 0 < x2) (h3 : 0 < x3) (h4 : 0 < x4)
    (hA : 0 < A) (hC : 0 < C) (hB : 0 < B)
    (H1 : BHolds f1 (x1 / x2) A) (H2 : BHolds f2 (x2 / x3) C) (H3 : BHolds f3 (x3 / x4) B) :
    BHolds (f1 || f2 || f3) (x1 / x4) (A * C * B) := by
  have hm := bhold_mul2 f1 f2 h2 h3 hA hC H1 H2
  exact bhold_mul2 (f1 || f2) f3 h3 h4 (mul_pos hA hC) hB hm H3

#print axioms bhold3

/-- The two-cycle test, verbatim from `add`'s back-check: the new bound `ρᵢ/ρⱼ ≤(<) c`
against the reverse bound `ρⱼ/ρᵢ ≤(<) d` is rejected iff `d·c < 1`, or `= 1` with either
side strict — the reviewed feasibility criterion at the pair the algorithm tests. -/
def uBackCond (d c : ℚ) (s t : Bool) : Bool := d * c < 1 || (d * c = 1 && (s || t))

/-- **Link 2 (the reviewed criterion, sound direction).**  A two-cycle of satisfied bounds
can never satisfy the rejection test: `(ρⱼ/ρᵢ ≤(<) d) ∧ (ρᵢ/ρⱼ ≤(<) c)` forces `1 ≤(<) d·c`,
so `d·c < 1` is impossible and `d·c = 1` leaves both sides non-strict. -/
theorem twoCycle_contra {ρi ρj : ℝ} (hi : 0 < ρi) (hj : 0 < ρj) {d c : ℚ} (hd : 0 < d)
    (hc : 0 < c) {t s : Bool} (h1 : BHolds t (ρj / ρi) d) (h2 : BHolds s (ρi / ρj) c) :
    ¬ ((d * c : ℚ) < 1 ∨ ((d * c : ℚ) = 1 ∧ (s = true ∨ t = true))) := by
  have key : BHolds (t || s) (ρj / ρj) (d * c) := bhold_mul2 t s hi hj hd hc h1 h2
  rw [div_self (ne_of_gt hj)] at key
  cases t <;> cases s <;> simp only [BHolds, Bool.true_or, Bool.false_or] at key
  · have hle : (1 : ℚ) ≤ d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · simp at hb
  · have hlt : (1 : ℚ) < d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · linarith
  · have hlt : (1 : ℚ) < d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · linarith
  · have hlt : (1 : ℚ) < d * c := by exact_mod_cast key
    rintro (h | ⟨heq, hb⟩)
    · linarith
    · linarith

#print axioms twoCycle_contra

/-! ## 3. The `add` step: verbatim decidable propagation + its soundness -/

/-- The keep-current test of `add`: the stored bound `(cc, ss)` at `(i, j)` already implies
the new `(c, s)` iff `cc < c`, or `cc = c` with `ss` strict or the new bound non-strict. -/
def uKeepCur (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : Bool :=
  match U i j with
  | none => false
  | some (cc, ss) => cc < c || (cc = c && (ss || !s))

/-- The back-check of `add`: reject iff the reverse entry makes the two-cycle infeasible
(`uBackCond`); no reverse entry = no rejection. -/
def uBack (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : Bool :=
  match U j i with
  | none => false
  | some (d, t) => uBackCond d c s t

/-- The per-entry replace-if-tighter rule of `add`'s propagation loop (verbatim: replace the
stored entry iff the new bound is smaller, or equal with the new one strict and the stored
one not). -/
def uTighter (new : ℚ × Bool) (old : UBound) : UBound :=
  match old with
  | none => some new
  | some (w0, w1) =>
    if new.1 < w0 || (new.1 = w0 && new.2 && !w1) then some new else some (w0, w1)

/-- The propagation of `add`, verbatim: every two-edge path `p → i → j → q` gains the bound
`(a·c·b, a₁ ∨ s ∨ b₁)`, kept only when tighter than the stored entry. -/
def uProp (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : UTable := fun p q =>
  match U p i, U j q with
  | some (a0, a1), some (b0, b1) => uTighter (a0 * c * b0, a1 || s || b1) (U p q)
  | _, _ => U p q

/-- One `add` step, verbatim `m4comp_lib_v1.add`: keep-cur test, then two-cycle rejection,
then propagation. -/
def uAdd (U : UTable) (i j : Fin 7) (c : ℚ) (s : Bool) : Option UTable :=
  if uKeepCur U i j c s then some U
  else if uBack U i j c s then none
  else some (uProp U i j c s)

/-- **Link 2 (soundness of a step).**  If `ρ` realizes the table, is positive, and satisfies
the added bound, a surviving `add` step returns a table again realized by `ρ` — every
propagated bound `a·c·b` is a consequence of the three chained bounds (strictness OR-ed). -/
theorem uAdd_fine_some {ρ : Fin 7 → ℝ} {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U) (hsat : BHolds s (ρ i / ρ j) c)
    {V : UTable} (hV : uAdd U i j c s = some V) : UFine ρ V := by
  unfold uAdd at hV
  split at hV
  · simp only [Option.some.injEq] at hV
    subst hV
    exact hfine
  · split at hV
    · exact absurd hV (by simp)
    · simp only [Option.some.injEq] at hV
      subst hV
      have hci : 0 < c := bpos_of_holds (div_pos (hpos i) (hpos j)) hsat
      intro p q
      show BHoldsOf (uProp U i j c s p q) (ρ p / ρ q)
      cases hA : U p i with
      | none => simp only [uProp, hA]; exact hfine p q
      | some aa =>
        obtain ⟨a0, a1⟩ := aa
        have hfa : BHolds a1 (ρ p / ρ i) a0 := hfine p i a0 a1 hA
        have hap : 0 < a0 := bpos_of_holds (div_pos (hpos p) (hpos i)) hfa
        cases hB : U j q with
        | none => simp only [uProp, hA, hB]; exact hfine p q
        | some bb =>
          obtain ⟨b0, b1⟩ := bb
          have hbq : BHolds b1 (ρ j / ρ q) b0 := hfine j q b0 b1 hB
          have hbp : 0 < b0 := bpos_of_holds (div_pos (hpos j) (hpos q)) hbq
          have hkey : BHolds (a1 || s || b1) (ρ p / ρ q) (a0 * c * b0) :=
            bhold3 a1 s b1 (hpos p) (hpos i) (hpos j) (hpos q) hap hci hbp hfa hsat hbq
          simp only [uProp, hA, hB]
          cases hW : U p q with
          | none =>
            simp only [uTighter]
            exact bhof_some hkey
          | some ww =>
            obtain ⟨w0, w1⟩ := ww
            have hfold : BHolds w1 (ρ p / ρ q) w0 := hfine p q w0 w1 hW
            simp only [uTighter]
            by_cases hif : a0 * c * b0 < w0 || (a0 * c * b0 = w0 && (a1 || s || b1) && !w1)
            · rw [if_pos hif]
              exact bhof_some hkey
            · rw [if_neg hif]
              exact bhof_some hfold

#print axioms uAdd_fine_some

/-- **Link 2 (no false rejection).**  A realized table + a bound satisfied by `ρ` is never
rejected: the two-cycle test would contradict `twoCycle_contra`. -/
theorem uAdd_none_of_fine_sat {ρ : Fin 7 → ℝ} {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U) (hsat : BHolds s (ρ i / ρ j) c) :
    uAdd U i j c s ≠ none := by
  intro hnone
  unfold uAdd at hnone
  split at hnone
  · exact absurd hnone (by simp)
  · split at hnone
    · rename_i hb
      exfalso
      unfold uBack at hb
      cases hd2 : U j i with
      | none => rw [hd2] at hb; simp at hb
      | some dd =>
        obtain ⟨d, t⟩ := dd
        rw [hd2] at hb
        simp only [uBackCond, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hb
        have hback : BHolds t (ρ j / ρ i) d := hfine j i d t hd2
        have hd' : 0 < d := bpos_of_holds (div_pos (hpos j) (hpos i)) hback
        have hc' : 0 < c := bpos_of_holds (div_pos (hpos i) (hpos j)) hsat
        exact twoCycle_contra (hpos i) (hpos j) hd' hc' hback hsat hb
    · exact absurd hnone (by simp)

#print axioms uAdd_none_of_fine_sat

/-! ## 4. The `gt` step and one chain step -/

/-- One `gt` step, verbatim `m4comp_lib_v1.gt` (the sign case analysis; in the envelope all
numerators are positive, where `gt` reduces to the strict `add(U, a, b, A/B, True)`). -/
def uGt (U : UTable) (A : ℚ) (a : Fin 7) (B : ℚ) (b : Fin 7) : Option UTable :=
  if 0 < A && B ≤ 0 then some U
  else if A ≤ 0 && 0 < B then none
  else if A = 0 then if B < 0 then some U else none
  else if B = 0 then if 0 < A then some U else none
  else if 0 < A then uAdd U a b (A / B) true
  else uAdd U b a ((-B) / (-A)) true

/-- On positive numerators `gt` is the strict `add` (the envelope case). -/
theorem uGt_pos (U : UTable) (a b : Fin 7) {A B : ℚ} (hA : 0 < A) (hB : 0 < B) :
    uGt U A a B b = uAdd U a b (A / B) true := by
  unfold uGt
  have n1 : ¬ (0 < A && B ≤ 0) := by simp [not_le_of_gt hB]
  have n2 : ¬ (A ≤ 0 && 0 < B) := by simp [not_le_of_gt hA]
  have n3 : ¬ (A = 0) := ne_of_gt hA
  have n4 : ¬ (B = 0) := ne_of_gt hB
  rw [if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_pos hA]

#print axioms uGt_pos

/-- One chain step, verbatim the two `gt` calls of the DFS: cap the last reading by the new
zone's entry edge, and the new reading by the last zone's exit edge. -/
def uStep (U : UTable) (a b : Fin 7) (Aex A B : ℚ) : Option UTable :=
  (uGt U Aex a A b).bind fun V => uGt V B b Aex a

/-- A surviving step on positive numerators is two strict `add` steps. -/
theorem uStep_some_add {U V : UTable} {a b : Fin 7} {Aex A B : ℚ}
    (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)
    (h : uStep U a b Aex A B = some V) :
    ∃ V1, uAdd U a b (Aex / A) true = some V1 ∧ uAdd V1 b a (B / Aex) true = some V := by
  unfold uStep at h
  rw [uGt_pos U a b hAex hA] at h
  obtain ⟨V1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  rw [uGt_pos V1 b a hB hAex] at h2
  exact ⟨V1, h1, h2⟩

#print axioms uStep_some_add

/-! ## 5. Link 4 — the componentwise-loosest merge is realized by every component -/

/-- The loosest-merge of two bounds, verbatim `looser` of `m4comp_uclosure_v1.py`: `none`
wins (loosest), else the larger value, ties AND the strict flags (non-strict is looser). -/
def uLooserB : UBound → UBound → UBound
  | none, _ => none
  | _, none => none
  | some (a0, a1), some (b0, b1) =>
    if b0 < a0 then some (a0, a1)
    else if a0 < b0 then some (b0, b1)
    else some (a0, a1 && b1)

/-- The componentwise-loosest table merge. -/
def uLooser (U V : UTable) : UTable := fun i j => uLooserB (U i j) (V i j)

/-- **Link 4 (the disjunction point).**  A bound satisfied by `x` stays satisfied by the
loosest merge with ANY other bound — so a merged table is realized by each component's own
readings ("the merged feasible set contains the union of the merged states' feasible sets",
the [P] of `m4comp_uclosure_v1.py`). -/
theorem holdsOf_looserB_left {x : ℝ} {b b' : UBound} (h : BHoldsOf b x) :
    BHoldsOf (uLooserB b b') x := by
  cases b with
  | none => exact bhof_none_of (by simp only [uLooserB])
  | some pa =>
    obtain ⟨a0, a1⟩ := pa
    cases b' with
    | none => exact bhof_none_of (by simp only [uLooserB])
    | some pb =>
      obtain ⟨b0, b1⟩ := pb
      simp only [uLooserB]
      split
      · exact h
      · split
        · rename_i h2
          have hab : ((a0 : ℚ) : ℝ) < ((b0 : ℚ) : ℝ) := by exact_mod_cast h2
          have h' := bhof_eq_some h rfl
          refine bhof_some_of rfl ?_
          cases a1 <;> simp only [BHolds] at h' <;> cases b1
          · exact le_trans h' hab.le
          · exact lt_of_le_of_lt h' hab
          · exact le_of_lt (lt_trans h' hab)
          · exact lt_trans h' hab
        · refine bhof_some_of rfl ?_
          have h' := bhof_eq_some h rfl
          cases hab : a1 && b1
          · simp only [BHolds]
            cases a1 <;> simp only [BHolds] at h'
            · exact h'
            · exact le_of_lt h'
          · have ha1 : a1 = true := (Bool.and_eq_true_iff.mp hab).1
            subst ha1
            simp only [BHolds]
            exact h'

#print axioms holdsOf_looserB_left

/-- The merged table is realized by each component's readings. -/
theorem ufine_looser {ρ : Fin 7 → ℝ} {U V : UTable} (h : UFine ρ U) : UFine ρ (uLooser U V) :=
  fun i j => holdsOf_looserB_left (h i j)

#print axioms ufine_looser

/-! ## 6. The direct-exit completion check -/

/-- The direct exit check, verbatim `add(U, a, 0, Aex/7, True)` of `merged_kill`: the chain
can leave the window past its right end (`R = Aex/ρ_a > 7`) exactly when the bound
`ρ_a/ρ₀ < Aex/7` is consistent with the table. -/
def uExitOK (U : UTable) (a : Fin 7) (Aex : ℚ) : Bool := (uAdd U a 0 (Aex / 7) true).isSome

/-- A real chain's exit past 7 forces the check to fire on any table it realizes. -/
theorem uExitOK_of_fine {ρ : Fin 7 → ℝ} {U : UTable} {a : Fin 7} {Aex : ℚ}
    (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U) (hsat : BHolds true (ρ a / ρ 0) (Aex / 7)) :
    uExitOK U a Aex = true := by
  unfold uExitOK
  cases h : uAdd U a 0 (Aex / 7) true with
  | none => exact absurd h (uAdd_none_of_fine_sat hpos hfine hsat)
  | some _ => rfl

#print axioms uExitOK_of_fine

/-! ## 7. The 90-type envelope, chain steps, and the real chain's trace -/

/-- The exit-numerator envelope: `8j+1` for `j = 1..15`, i.e. `9, 17, …, 121` — the 12
census numerators `9..97` plus the comb tail up to the window bound (window 7, face hi
`35/2` forces `8j−1 < 7·35/2`, so `j ≤ 15`); the 90-type leaf envelope = `Fin 6` (ranks
2..7) × these 15 numerators. -/
def exitNum (k : Fin 15) : ℚ := ((8 * (k.val + 1) + 1 : ℕ) : ℚ)

/-- One strict monotone chain step: next reading row `b`, zone edges `A = 8j−1` (entry) and
`B = A+2 = 8j+1` (exit, the new exit numerator). -/
structure Step where
  b : Fin 7
  A : ℚ
  B : ℚ

/-- The chain's table trace: fold `uStep` over the steps, tracking the last row and exit
numerator (the DFS state `(U, a, Aex)`). -/
def chainRun (U : UTable) (a : Fin 7) (Aex : ℚ) : List Step → Option (UTable × Fin 7 × ℚ)
  | [] => some (U, a, Aex)
  | st :: rest =>
    (uStep U a st.b Aex st.A st.B).bind fun V => chainRun V st.b st.B rest

/-- A real W₀ chain (table-semantics form): each step's two `gt` bounds are satisfied by the
chain's readings `ρ`, the step survives on the chain's own table, zone numerators positive,
and the chain ends with an exit past 7 (the base case). -/
-- STANDING: DEFINITION
def ChainRealized (ρ : Fin 7 → ℝ) (U : UTable) (a : Fin 7) (Aex : ℚ) : List Step → Prop
  | [] => BHolds true (ρ a / ρ 0) (Aex / 7)
  | st :: rest =>
    ∃ V, uStep U a st.b Aex st.A st.B = some V ∧
      0 < st.A ∧ 0 < st.B ∧
        BHolds true (ρ a / ρ st.b) (Aex / st.A) ∧
        BHolds true (ρ st.b / ρ a) (st.B / Aex) ∧
        ChainRealized ρ V st.b st.B rest

/-- **Link 3's engine (projection, arithmetic side).**  A real chain's whole trace stays
realized by the chain's readings, and it ends with the exit-past-7 bound — every step's
table is a consequence of the chain's own constraints, so no step of a real chain is ever
rejected. -/
theorem chain_fine_of_realized {ρ : Fin 7 → ℝ} {U : UTable} {a : Fin 7} {Aex : ℚ}
    {steps : List Step} (hpos : ∀ k, 0 < ρ k) (hfine : UFine ρ U)
    (h : ChainRealized ρ U a Aex steps) :
    ∃ Uf af Af, chainRun U a Aex steps = some (Uf, af, Af) ∧ UFine ρ Uf ∧
      BHolds true (ρ af / ρ 0) (Af / 7) := by
  induction steps generalizing U a Aex with
  | nil => exact ⟨U, a, Aex, rfl, hfine, h⟩
  | cons st rest ih =>
    simp only [ChainRealized] at h
    obtain ⟨V, hV, hA, hB, sat1, sat2, hrest⟩ := h
    have hc1 : 0 < (Aex / st.A : ℚ) := bpos_of_holds (div_pos (hpos a) (hpos st.b)) sat1
    have hAex' : 0 < Aex := by
      have h1 : Aex = (Aex / st.A) * st.A := by field_simp
      rw [h1]
      exact mul_pos hc1 hA
    obtain ⟨V1, hadd1, hadd2⟩ := uStep_some_add hAex' hA hB hV
    have hfine1 : UFine ρ V1 := uAdd_fine_some hpos hfine sat1 hadd1
    have hfine2 : UFine ρ V := uAdd_fine_some hpos hfine1 sat2 hadd2
    obtain ⟨Uf, af, Af, hrun, hfineF, hexit⟩ := ih hfine2 hrest
    refine ⟨Uf, af, Af, ?_, hfineF, hexit⟩
    simp only [chainRun, hV, Option.bind_some]
    exact hrun

#print axioms chain_fine_of_realized
end Fresh.UClosure

namespace Fresh.SpineSound
open Fresh.FilterAssembly
/-- The box faces are positive (each `FaceLo ≥ 1`), so every arrangement in a box has
positive readings — the engine's positivity side conditions. -/
theorem faceLo_pos (n : Fin 7 → ℤ) (i : Fin 7) : 0 < FaceLo n i := by
  unfold FaceLo
  have h3 : (0 : ℤ) < max (2 * n i - 1) 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) (le_max_right _ _)
  exact div_pos (by exact_mod_cast h3) (by norm_num : (0 : ℝ) < 2)

#print axioms faceLo_pos

/-- Every arrangement in a box has positive readings. -/
theorem face_pos {n : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) (i : Fin 7) : 0 < g i :=
  lt_of_lt_of_le (faceLo_pos n i) (hface i).1

#print axioms face_pos
end Fresh.SpineSound

namespace Fresh.JoinFamComposed
inductive ChainReal (g : Fin 7 → ℝ) : Fin 7 → List (Fin 7 × ℝ) → Fin 7 → Prop
  | nil (u : Fin 7) (hupos : 0 < g u) : ChainReal g u [] u
  | cons (u v : Fin 7) (c : ℝ) (l : List (Fin 7 × ℝ)) (w : Fin 7)
      (hcap : g u / g v ≤ c) (hupos : 0 < g u) (hvpos : 0 < g v)
      (hrest : ChainReal g v l w) : ChainReal g u ((v, c) :: l) w

/-- One composed record: the `(x, y, A, B)` word demand bundled with ITS composed cap
chain — the caps walk `y → z₁ → … → x` through the node/cap list `(z₁, c₁), …, (zₙ, cₙ)`
(the E813 box-end bound + seam-ratio products).  The joinedge dump's "list of
`(x, y, A, B)` demands + list of composed cap chains" is carried as this record list: the
demand-chain pairing is what the per-arrangement kill consumes. -/
structure ComposedEdge where
  x : Fin 7
  y : Fin 7
  A : ℤ
  B : ℤ
  caps : List (Fin 7 × ℝ)
/-- The walk end of a cap chain started at `y` (the datum-level endpoint check). -/
noncomputable def chainEnd (y : Fin 7) (caps : List (Fin 7 × ℝ)) : Fin 7 :=
  caps.foldl (fun _ p => p.1) y

/-- Datum-level validity of one composed record: positive demand numerator/denominator,
positive caps, the chain runs from `y` to `x`, and the composed datum
`A·c₁⋯cₙ ≤ B` (`d·∏c ≤ 1`).  Note: NO `8m±1` numerator condition — that is exactly what
the composed extension drops (E813 item 7: composed caps are not raw `8m±1` edges). -/
-- STANDING: DEFINITION
def ComposedEdgeValid (e : ComposedEdge) : Prop :=
  0 < e.A ∧ 0 < e.B ∧ (∀ p ∈ e.caps, 0 < p.2) ∧ chainEnd e.y e.caps = e.x ∧
    (e.A : ℝ) * (e.caps.map Prod.snd).prod ≤ (e.B : ℝ)

/-- The composed family carrier: the list of composed records (each demand with its
chain). -/
structure ComposedFam where
  edges : List ComposedEdge

/-- The family validity datum (mirrors `JoinFam`'s datum role): every record in the
family satisfies the composed datum conditions. -/
-- STANDING: DEFINITION
def ComposedFamData (f : ComposedFam) : Prop := ∀ e ∈ f.edges, ComposedEdgeValid e
end Fresh.JoinFamComposed

namespace Fresh.OneSidedGlue
open Fresh.JoinFamComposed
-- STANDING: DEFINITION
def capChainsRealized (g : Fin 7 → ℝ) (f : ComposedFam) : Prop :=
  ∀ e ∈ f.edges, ChainReal g e.y e.caps e.x
end Fresh.OneSidedGlue

namespace Fresh.CapChainsOfCarve
open Fresh.FilterAssembly Fresh.SpineSound Fresh.JoinFamComposed Fresh.OneSidedGlue Fresh.UClosure
inductive CapsDom (V : UTable) : Fin 7 → List (Fin 7 × ℝ) → Fin 7 → Prop
  | nil (x : Fin 7) : CapsDom V x [] x
  | cons (y z : Fin 7) (c : ℝ) (l : List (Fin 7 × ℝ)) (w : Fin 7)
      (hentry : ∃ c₀ : ℚ, ∃ s : Bool, V y z = some (c₀, s) ∧ ((c₀ : ℚ) : ℝ) ≤ c)
      (hrest : CapsDom V z l w) : CapsDom V y ((z, c) :: l) w

/-- The singleton domination builder: one table entry dominating the one cap. -/
theorem capsDom_single {V : UTable} {y z : Fin 7} {c : ℝ}
    (hentry : ∃ c₀ : ℚ, ∃ s : Bool, V y z = some (c₀, s) ∧ ((c₀ : ℚ) : ℝ) ≤ c) :
    CapsDom V y [(z, c)] z :=
  CapsDom.cons y z c [] z hentry (CapsDom.nil z)

#print axioms capsDom_single

/-- **The domination-augmented trace-realization induction**: if `g` realizes the table
`V` (`UFine`) and every cap of the walk is dominated by `V`'s entries, the walk is a
realized cap chain on `g` (`ChainReal`).  Each step is `ChainReal.cons` on a realized
table entry (`bhof_eq_some`) shrunk by the value domination; the strict flag is handled
by cases (strict `ρ < c₀ ≤ c`, non-strict `ρ ≤ c₀ ≤ c`). -/
theorem chainReal_of_capsDom {g : Fin 7 → ℝ} (hpos : ∀ k, 0 < g k)
    {V : UTable} (hfine : UFine g V) {y x : Fin 7} {caps : List (Fin 7 × ℝ)}
    (h : CapsDom V y caps x) : ChainReal g y caps x := by
  induction h with
  | nil x => exact ChainReal.nil x (hpos x)
  | cons y z c l w hentry hrest ih =>
    obtain ⟨c₀, s, hV, hcle⟩ := hentry
    have hholds : BHolds s (g y / g z) c₀ := bhof_eq_some (hfine y z) hV
    have hcap : g y / g z ≤ ((c₀ : ℚ) : ℝ) := by
      cases s with
      | false => simpa only [BHolds] using hholds
      | true => exact le_of_lt (by simpa only [BHolds] using hholds)
    exact ChainReal.cons y z c l w (le_trans hcap hcle) (hpos y) (hpos z) ih

#print axioms chainReal_of_capsDom
/-- The faithful two-sided form (the dump's per-record semantics: each banked cap is
box-side or J-side): box-side caps dominated by the opening table, J-side caps dominated
by the closed trace table — EITHER suffices per record. -/
theorem capChainsRealized_of_domData (f : ComposedFam)
    {n : Fin 7 → ℤ} {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (U : UTable) (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g U) (hchain : ChainRealized g U a Aex steps)
    (hdom : ∀ e ∈ f.edges,
      CapsDom U e.y e.caps e.x ∨
        (∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
          chainRun U a Aex steps = some (V, af, Af) → CapsDom V e.y e.caps e.x)) :
    capChainsRealized g f := by
  have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
  obtain ⟨Uf, af, Af, hrun, hfine, -⟩ := chain_fine_of_realized hpos hfine0 hchain
  intro e he
  rcases hdom e he with hU | hV
  · exact chainReal_of_capsDom hpos hfine0 hU
  · exact chainReal_of_capsDom hpos hfine (hV Uf af Af hrun)

#print axioms capChainsRealized_of_domData
-- STANDING: OWED
def DumpDom (n : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
    ∀ (U : UTable) (a : Fin 7) (Aex : ℚ) (steps : List Step),
      UFine g U → ChainRealized g U a Aex steps →
      ∀ e ∈ f.edges,
        CapsDom U e.y e.caps e.x ∨
          (∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
            chainRun U a Aex steps = some (V, af, Af) → CapsDom V e.y e.caps e.x)
end Fresh.CapChainsOfCarve

open Fresh.UClosure Fresh.JoinFamComposed Fresh.OneSidedGlue Fresh.CapChainsOfCarve Fresh.FilterAssembly Fresh.SpineSound

/-! ## 1. The certified-bound engine (the data-side vocabulary) -/

/-- The certified-bound datum: at every pair where the bound function `bnd` prescribes a
nonzero bound, the table `U` stores an entry whose value is at most that bound.  This is
the data-side certificate the dump's strict witnesses carry per hop (dom_box / dom_J
values, census-verified `<=` the hop value), lifted to a whole table. -/
-- STANDING: DEFINITION
def CertBelow (bnd : Fin 7 → Fin 7 → ℚ) (U : UTable) : Prop :=
  ∀ i j, bnd i j ≠ 0 → ∃ c₀ : ℚ, ∃ s : Bool, U i j = some (c₀, s) ∧
    ((c₀ : ℚ) : ℝ) ≤ ((bnd i j : ℚ) : ℝ)

/-- The `uTighter` rule always stores SOME entry. -/
theorem uTighter_some {old : UBound} {v : ℚ} {t : Bool} :
    ∃ w : ℚ, ∃ tw : Bool, uTighter (v, t) old = some (w, tw) := by
  cases old with
  | none => exact ⟨v, t, rfl⟩
  | some p =>
    obtain ⟨c₀, s₀⟩ := p
    simp only [uTighter]
    split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- The `uTighter` rule never increases the stored value. -/
theorem uTighter_le {old : UBound} {v : ℚ} {t : Bool} {c₀ : ℚ} {s₀ : Bool}
    (hold : old = some (c₀, s₀)) :
    ∀ w : ℚ, ∀ tw : Bool, uTighter (v, t) old = some (w, tw) →
      ((w : ℚ) : ℝ) ≤ ((c₀ : ℚ) : ℝ) := by
  intro w tw h
  cases hold
  simp only [uTighter] at h ⊢
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, _⟩ := h
    subst e1
    rcases Bool.or_eq_true_iff.mp hc with hv | hand
    · exact le_of_lt (by exact_mod_cast (Bool.of_decide_eq_true hv))
    · have heq : v = c₀ := Bool.of_decide_eq_true (Bool.and_eq_true_iff.mp hand).1
      rw [heq]
      exact le_refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, _⟩ := h
    subst e1
    exact le_refl _

#print axioms uTighter_some
#print axioms uTighter_le

/-- **Certified bounds are preserved by every surviving `add`**: `uAdd` never increases a
stored entry (the `uTighter` replace rule keeps the smaller value) and never deletes one,
so a table dominating `bnd` has its surviving `add` result still dominating `bnd`.  No
constraint on the added bound `c` — the preservation is unconditional. -/
theorem certBelow_uAdd {bnd : Fin 7 → Fin 7 → ℚ} {U : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    {V : UTable} (hc : CertBelow bnd U) (h : uAdd U i j c s = some V) : CertBelow bnd V := by
  intro p q hpq
  unfold uAdd at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact hc p q hpq
  · split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq] at h
      subst h
      cases hpi : U p i with
      | none => simp only [uProp, hpi]; exact hc p q hpq
      | some aa =>
        cases hpj : U j q with
        | none => simp only [uProp, hpi, hpj]; exact hc p q hpq
        | some bb =>
          obtain ⟨c₀, s₀, hV, hcle⟩ := hc p q hpq
          obtain ⟨w, tw, hw⟩ := uTighter_some (v := aa.1 * c * bb.1) (t := aa.2 || s || bb.2)
              (old := U p q)
          refine ⟨w, tw, ?_, ?_⟩
          · simp only [uProp, hpi, hpj]
            rw [hV] at hw ⊢
            exact hw
          · exact le_trans (uTighter_le hV w tw hw) hcle

#print axioms certBelow_uAdd

/-- **Certified bounds survive a chain step** (on positive zone numerators, where each
`uGt` is the strict `uAdd` — `uGt_pos`): the step's two `add`s each preserve the
certificate, so the stepped table is again certified. -/
theorem certBelow_uStep {bnd : Fin 7 → Fin 7 → ℚ} {U V : UTable} {a b : Fin 7} {Aex A B₀ : ℚ}
    (hAex : 0 < Aex) (hA : 0 < A) (hB₀ : 0 < B₀)
    (hc : CertBelow bnd U) (h : uStep U a b Aex A B₀ = some V) : CertBelow bnd V := by
  unfold uStep at h
  rw [uGt_pos (U := U) (a := a) (b := b) (A := Aex) (B := A) hAex hA] at h
  cases hb1 : uAdd U a b (Aex / A) true with
  | none => rw [hb1] at h; simp at h
  | some W =>
    rw [hb1] at h
    simp only [Option.bind_some] at h
    rw [uGt_pos (U := W) (a := b) (b := a) (A := B₀) (B := Aex) hB₀ hAex] at h
    exact certBelow_uAdd (certBelow_uAdd hc hb1) h

#print axioms certBelow_uStep

/-- **Certified bounds survive the whole chain run**: the closed trace table of any real
chain (each step's numerators positive, per `ChainRealized`) opened at a certified table
is again certified — the engine behind the trace disjunct of
`Fresh.CapChainsOfCarve.capChainsRealized_of_domData`. -/
theorem certBelow_chainRun {bnd : Fin 7 → Fin 7 → ℚ} {g : Fin 7 → ℝ} {U : UTable}
    {a : Fin 7} {Aex : ℚ} {steps : List Step}
    (hpos : ∀ k, 0 < g k) (hc : CertBelow bnd U) :
    ChainRealized g U a Aex steps → ∀ W : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
      chainRun U a Aex steps = some (W, af, Af) → CertBelow bnd W := by
  induction steps generalizing U a Aex with
  | nil =>
    intro hchain W af Af h
    simp only [ChainRealized] at hchain
    simp only [chainRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hc
  | cons st rest ih =>
    intro hchain W af Af h
    simp only [ChainRealized] at hchain
    obtain ⟨V₀, hstep, hA, hB, sat1, _, hrest⟩ := hchain
    have hci : 0 < (Aex / st.A : ℚ) := bpos_of_holds (div_pos (hpos a) (hpos st.b)) sat1
    have hAex' : 0 < Aex := by
      have h1 : Aex = (Aex / st.A) * st.A := by field_simp
      rw [h1]
      exact mul_pos hci hA
    simp only [chainRun] at h
    rw [hstep] at h
    simp only [Option.bind_some] at h
    exact ih (certBelow_uStep hAex' hA hB hc hstep) hrest W af Af h

#print axioms certBelow_chainRun

/-- The walk-shaped certified domination: each hop's cap is at least the certified bound
of its pair (with the pair certified, i.e. nonzero).  The `CapsDom` mirror of the dump's
per-hop census. -/
-- STANDING: DEFINITION
def CapsB (bnd : Fin 7 → Fin 7 → ℚ) : List (Fin 7 × ℝ) → Fin 7 → Fin 7 → Prop
  | [], y, x => y = x
  | (z, c) :: l, y, x => bnd y z ≠ 0 ∧ ((bnd y z : ℚ) : ℝ) ≤ c ∧ CapsB bnd l z x

/-- Certified walks are dominated walks: a certified trace table realizes every certified
walk as a `CapsDom` chain (each step's stored entry value is squeezed between the
certified bound and the cap). -/
theorem capsDom_of_capsB {bnd : Fin 7 → Fin 7 → ℚ} {V : UTable} (hc : CertBelow bnd V) :
    ∀ (caps : List (Fin 7 × ℝ)) (y x : Fin 7), CapsB bnd caps y x → CapsDom V y caps x := by
  intro caps
  induction caps with
  | nil => intro y x h; cases h; exact CapsDom.nil _
  | cons p l ih =>
    intro y x h
    obtain ⟨hnz, hcap, hrest⟩ := h
    obtain ⟨z, c⟩ := p
    obtain ⟨c₀, s₀, hV, hcle⟩ := hc y z hnz
    exact CapsDom.cons y z c l x ⟨c₀, s₀, hV, le_trans hcle hcap⟩ (ih z x hrest)

#print axioms capsDom_of_capsB


/-- The box closure `U0` of box (1, 5, 5, 6, 7, 8, 8): verbatim `joinedge2_perbox_v1.jsonl` `U0_entries`
(the `mkp`-style face table: diagonal 1, face_hi `(2n+1)/2` on `(y,0)`, face_lo
`2/(2n-1)` and the strict `1` on `(0,y)` (whichever is tighter), ordination `1` on
`(y,y+1)`, plus the propagated compositions).  49 entries, exact rationals. -/
def u0_1_5_5_6_7_8_8 : UTable := fun i j =>
  match i.val, j.val with
  | 0, 0 => some ((1/1 : ℚ), false)
  | 0, 1 => some ((2/9 : ℚ), false)
  | 0, 2 => some ((2/9 : ℚ), true)
  | 0, 3 => some ((2/11 : ℚ), false)
  | 0, 4 => some ((2/13 : ℚ), false)
  | 0, 5 => some ((2/15 : ℚ), false)
  | 0, 6 => some ((2/15 : ℚ), true)
  | 1, 0 => some ((11/2 : ℚ), true)
  | 1, 1 => some ((1/1 : ℚ), false)
  | 1, 2 => some ((1/1 : ℚ), true)
  | 1, 3 => some ((1/1 : ℚ), true)
  | 1, 4 => some ((11/13 : ℚ), true)
  | 1, 5 => some ((11/15 : ℚ), true)
  | 1, 6 => some ((11/15 : ℚ), true)
  | 2, 0 => some ((11/2 : ℚ), false)
  | 2, 1 => some ((11/9 : ℚ), false)
  | 2, 2 => some ((1/1 : ℚ), false)
  | 2, 3 => some ((1/1 : ℚ), true)
  | 2, 4 => some ((11/13 : ℚ), false)
  | 2, 5 => some ((11/15 : ℚ), false)
  | 2, 6 => some ((11/15 : ℚ), true)
  | 3, 0 => some ((13/2 : ℚ), false)
  | 3, 1 => some ((13/9 : ℚ), false)
  | 3, 2 => some ((13/9 : ℚ), true)
  | 3, 3 => some ((1/1 : ℚ), false)
  | 3, 4 => some ((1/1 : ℚ), true)
  | 3, 5 => some ((13/15 : ℚ), false)
  | 3, 6 => some ((13/15 : ℚ), true)
  | 4, 0 => some ((15/2 : ℚ), false)
  | 4, 1 => some ((5/3 : ℚ), false)
  | 4, 2 => some ((5/3 : ℚ), true)
  | 4, 3 => some ((15/11 : ℚ), false)
  | 4, 4 => some ((1/1 : ℚ), false)
  | 4, 5 => some ((1/1 : ℚ), true)
  | 4, 6 => some ((1/1 : ℚ), true)
  | 5, 0 => some ((17/2 : ℚ), true)
  | 5, 1 => some ((17/9 : ℚ), true)
  | 5, 2 => some ((17/9 : ℚ), true)
  | 5, 3 => some ((17/11 : ℚ), true)
  | 5, 4 => some ((17/13 : ℚ), true)
  | 5, 5 => some ((1/1 : ℚ), false)
  | 5, 6 => some ((1/1 : ℚ), true)
  | 6, 0 => some ((17/2 : ℚ), false)
  | 6, 1 => some ((17/9 : ℚ), false)
  | 6, 2 => some ((17/9 : ℚ), true)
  | 6, 3 => some ((17/11 : ℚ), false)
  | 6, 4 => some ((17/13 : ℚ), false)
  | 6, 5 => some ((17/15 : ℚ), false)
  | 6, 6 => some ((1/1 : ℚ), false)
  | _, _ => none

/-- The certified opening of box (1, 5, 5, 6, 7, 8, 8): the box closure tightened at the family's hop
pairs to the dump's certified dominating values (the `dom_J` join-entry value where
present, else the `dom_box` closure value; the census verifies `<=` every hop value
at its pair).  Mirrors the dump's one-sided DFS opening `UJ = U0 (+) J` restricted
to the pairs the strict witnesses use. -/
def uj_1_5_5_6_7_8_8 : UTable := fun i j =>
  match i.val, j.val with
  | 0, 1 => some ((98/465 : ℚ), true)  -- J
  | 0, 2 => some ((311542/1639125 : ℚ), true)  -- J
  | 0, 3 => some ((578/3375 : ℚ), true)  -- J
  | 0, 4 => some ((34/225 : ℚ), true)  -- J
  | 0, 6 => some ((6358/52875 : ℚ), true)  -- J
  | 1, 0 => some ((11849/2457 : ℚ), true)  -- J
  | 1, 2 => some ((155771/170469 : ℚ), true)  -- J
  | 2, 0 => some ((130339/24675 : ℚ), true)  -- J
  | 2, 1 => some ((1617/1457 : ℚ), true)  -- J
  | 2, 3 => some ((3179/3525 : ℚ), true)  -- J
  | 2, 4 => some ((187/235 : ℚ), true)  -- J
  | 2, 5 => some ((33/47 : ℚ), true)  -- J
  | 2, 6 => some ((34969/55225 : ℚ), true)  -- J
  | 3, 0 => some ((41/7 : ℚ), true)  -- J
  | 3, 2 => some ((1617/1457 : ℚ), true)  -- J
  | 4, 0 => some ((697/105 : ℚ), true)  -- J
  | 4, 2 => some ((9163/7285 : ℚ), true)  -- J
  | 5, 0 => some ((11849/1575 : ℚ), true)  -- J
  | 5, 2 => some ((155771/109275 : ℚ), true)  -- J
  | 6, 0 => some ((912373/109275 : ℚ), true)  -- J
  | 6, 2 => some ((49/31 : ℚ), true)  -- J
  | _, _ => u0_1_5_5_6_7_8_8 i j

/-- The certified-bound function: the certified opening's own entry value at each
pair (0 = unconstrained). -/
def bnd_1_5_5_6_7_8_8 : Fin 7 → Fin 7 → ℚ := fun i j =>
  match uj_1_5_5_6_7_8_8 i j with
  | some (c, _) => c
  | none => 0

/-- The certified opening dominates its own certified-bound function. -/
theorem certBelow_1_5_5_6_7_8_8 : CertBelow (bnd_1_5_5_6_7_8_8) (uj_1_5_5_6_7_8_8) := by
  intro i j hne
  cases hj : uj_1_5_5_6_7_8_8 i j with
  | none =>
    exfalso
    simp only [bnd_1_5_5_6_7_8_8, hj] at hne
    exact absurd rfl hne
  | some p =>
    obtain ⟨c, s⟩ := p
    refine ⟨c, s, rfl, ?_⟩
    simp only [bnd_1_5_5_6_7_8_8, hj]
    exact le_refl _

#print axioms certBelow_1_5_5_6_7_8_8

/-- The strict-class composed family of box (1, 5, 5, 6, 7, 8, 8): every death row's strict-complete
primary witness from `joinedge2_perbox_v1.jsonl` (census: EVERY row of this box is
strict-complete), as a `ComposedEdge` `(y1-1, x1-1, P, Q, walk)` carrying the
witness's cap walk (hop product = the row's cap exactly; `P*cap <= Q` datum holds;
14 rows, 14 hops; w0n=156 chains enumerated). -/

def fam_1_5_5_6_7_8_8 : ComposedFam :=
  ⟨[
    ⟨2, 0, 49, 15, [(2, ((311542/1639125 : ℚ) : ℝ))]⟩,
    ⟨2, 1, 49, 47, [(2, ((155771/170469 : ℚ) : ℝ))]⟩,
    ⟨2, 1, 49, 55, [(2, ((155771/170469 : ℚ) : ℝ))]⟩,
    ⟨2, 1, 49, 63, [(2, ((155771/170469 : ℚ) : ℝ))]⟩,
    ⟨2, 1, 49, 71, [(2, ((155771/170469 : ℚ) : ℝ))]⟩,
    ⟨2, 1, 49, 79, [(2, ((155771/170469 : ℚ) : ℝ))]⟩,
    ⟨2, 3, 49, 55, [(2, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨2, 3, 49, 63, [(2, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨2, 3, 49, 71, [(2, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨2, 3, 49, 79, [(2, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨2, 3, 49, 87, [(2, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨2, 3, 49, 95, [(2, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨2, 4, 49, 63, [(2, ((9163/7285 : ℚ) : ℝ))]⟩,
    ⟨2, 4, 49, 71, [(2, ((9163/7285 : ℚ) : ℝ))]⟩
  ]⟩

/-- Per-record certified domination: every hop of every record's walk is bounded below
by the certified value (`CapsB`), i.e. the dump's dom_box/dom_J census, kernel-checked. -/
theorem capsB_1_5_5_6_7_8_8 : ∀ e ∈ (fam_1_5_5_6_7_8_8).edges, CapsB (bnd_1_5_5_6_7_8_8) e.caps e.y e.x := by
  intro e he
  simp only [fam_1_5_5_6_7_8_8, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact ⟨by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], by norm_num [bnd_1_5_5_6_7_8_8, uj_1_5_5_6_7_8_8, u0_1_5_5_6_7_8_8], rfl⟩
  · exact absurd h0 (by simp)

#print axioms capsB_1_5_5_6_7_8_8

/-- The certified-opening dump-v2 datum of box (1, 5, 5, 6, 7, 8, 8): for every in-box `g`, every real
W₀ chain opened at the certified opening `uj_1_5_5_6_7_8_8` has its closed trace dominate every
record's caps, hence the family's cap chains are realized on `g`
(`Fresh.CapChainsOfCarve.capChainsRealized_of_domData`'s trace disjunct).  This is
the certified-opening restriction of `Fresh.CapChainsOfCarve.DumpDom` (which
quantifies over arbitrary openings and is FALSE; see `not_dumpDom_1_5_5_6_7_8_8`). -/

theorem dumpDomData_1_5_5_6_7_8_8 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 5, 5, 6, 7, 8, 8] : Fin 7 → ℤ) i)
    (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g (uj_1_5_5_6_7_8_8)) (hchain : ChainRealized g (uj_1_5_5_6_7_8_8) a Aex steps) :
    capChainsRealized g (fam_1_5_5_6_7_8_8) :=
  capChainsRealized_of_domData (fam_1_5_5_6_7_8_8) hface (uj_1_5_5_6_7_8_8) a Aex steps hfine0 hchain (by
    intro e he
    have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
    refine Or.inr (fun V afn Af hrun => ?_)
    exact capsDom_of_capsB (certBelow_chainRun hpos (certBelow_1_5_5_6_7_8_8) hchain V afn Af hrun)
      (capsB_1_5_5_6_7_8_8 e he)

#print axioms dumpDomData_1_5_5_6_7_8_8

/-- The box closure `U0` of box (1, 3, 4, 4, 5, 5, 7): verbatim `joinedge2_perbox_v1.jsonl` `U0_entries`
(the `mkp`-style face table: diagonal 1, face_hi `(2n+1)/2` on `(y,0)`, face_lo
`2/(2n-1)` and the strict `1` on `(0,y)` (whichever is tighter), ordination `1` on
`(y,y+1)`, plus the propagated compositions).  49 entries, exact rationals. -/
def u0_1_3_4_4_5_5_7 : UTable := fun i j =>
  match i.val, j.val with
  | 0, 0 => some ((1/1 : ℚ), false)
  | 0, 1 => some ((2/5 : ℚ), false)
  | 0, 2 => some ((2/7 : ℚ), false)
  | 0, 3 => some ((2/7 : ℚ), true)
  | 0, 4 => some ((2/9 : ℚ), false)
  | 0, 5 => some ((2/9 : ℚ), true)
  | 0, 6 => some ((2/13 : ℚ), false)
  | 1, 0 => some ((7/2 : ℚ), false)
  | 1, 1 => some ((1/1 : ℚ), false)
  | 1, 2 => some ((1/1 : ℚ), true)
  | 1, 3 => some ((1/1 : ℚ), true)
  | 1, 4 => some ((7/9 : ℚ), false)
  | 1, 5 => some ((7/9 : ℚ), true)
  | 1, 6 => some ((7/13 : ℚ), false)
  | 2, 0 => some ((9/2 : ℚ), true)
  | 2, 1 => some ((9/5 : ℚ), true)
  | 2, 2 => some ((1/1 : ℚ), false)
  | 2, 3 => some ((1/1 : ℚ), true)
  | 2, 4 => some ((1/1 : ℚ), true)
  | 2, 5 => some ((1/1 : ℚ), true)
  | 2, 6 => some ((9/13 : ℚ), true)
  | 3, 0 => some ((9/2 : ℚ), false)
  | 3, 1 => some ((9/5 : ℚ), false)
  | 3, 2 => some ((9/7 : ℚ), false)
  | 3, 3 => some ((1/1 : ℚ), false)
  | 3, 4 => some ((1/1 : ℚ), true)
  | 3, 5 => some ((1/1 : ℚ), true)
  | 3, 6 => some ((9/13 : ℚ), false)
  | 4, 0 => some ((11/2 : ℚ), true)
  | 4, 1 => some ((11/5 : ℚ), true)
  | 4, 2 => some ((11/7 : ℚ), true)
  | 4, 3 => some ((11/7 : ℚ), true)
  | 4, 4 => some ((1/1 : ℚ), false)
  | 4, 5 => some ((1/1 : ℚ), true)
  | 4, 6 => some ((11/13 : ℚ), true)
  | 5, 0 => some ((11/2 : ℚ), false)
  | 5, 1 => some ((11/5 : ℚ), false)
  | 5, 2 => some ((11/7 : ℚ), false)
  | 5, 3 => some ((11/7 : ℚ), true)
  | 5, 4 => some ((11/9 : ℚ), false)
  | 5, 5 => some ((1/1 : ℚ), false)
  | 5, 6 => some ((11/13 : ℚ), false)
  | 6, 0 => some ((15/2 : ℚ), false)
  | 6, 1 => some ((3/1 : ℚ), false)
  | 6, 2 => some ((15/7 : ℚ), false)
  | 6, 3 => some ((15/7 : ℚ), true)
  | 6, 4 => some ((5/3 : ℚ), false)
  | 6, 5 => some ((5/3 : ℚ), true)
  | 6, 6 => some ((1/1 : ℚ), false)
  | _, _ => none

/-- The certified opening of box (1, 3, 4, 4, 5, 5, 7): the box closure tightened at the family's hop
pairs to the dump's certified dominating values (the `dom_J` join-entry value where
present, else the `dom_box` closure value; the census verifies `<=` every hop value
at its pair).  Mirrors the dump's one-sided DFS opening `UJ = U0 (+) J` restricted
to the pairs the strict witnesses use. -/
def uj_1_3_4_4_5_5_7 : UTable := fun i j =>
  match i.val, j.val with
  | 0, 1 => some ((55/161 : ℚ), true)  -- J
  | 0, 2 => some ((119/465 : ℚ), true)  -- J
  | 0, 3 => some ((7/31 : ℚ), true)  -- J
  | 0, 4 => some ((595/2883 : ℚ), true)  -- J
  | 0, 5 => some ((9/49 : ℚ), true)  -- J
  | 0, 6 => some ((1/7 : ℚ), true)  -- J
  | 1, 0 => some ((33/10 : ℚ), true)  -- J
  | 1, 3 => some ((17/23 : ℚ), true)  -- J
  | 2, 0 => some ((81675/20398 : ℚ), true)  -- J
  | 2, 3 => some ((40425/45167 : ℚ), true)  -- J
  | 2, 4 => some ((25/31 : ℚ), true)  -- J
  | 2, 5 => some ((7425/10199 : ℚ), true)  -- J
  | 2, 6 => some ((825/1457 : ℚ), true)  -- J
  | 3, 1 => some ((425/279 : ℚ), true)  -- J
  | 3, 2 => some ((17/15 : ℚ), true)  -- J
  | 4, 0 => some ((3267/658 : ℚ), true)  -- J
  | 4, 3 => some ((1617/1457 : ℚ), true)  -- J
  | 4, 6 => some ((33/47 : ℚ), true)  -- J
  | 6, 0 => some ((99/14 : ℚ), true)  -- J
  | 6, 1 => some ((55/23 : ℚ), true)  -- J
  | 6, 2 => some ((833/465 : ℚ), true)  -- J
  | 6, 3 => some ((49/31 : ℚ), true)  -- J
  | 6, 5 => some ((9/7 : ℚ), true)  -- J
  | _, _ => u0_1_3_4_4_5_5_7 i j

/-- The certified-bound function: the certified opening's own entry value at each
pair (0 = unconstrained). -/
def bnd_1_3_4_4_5_5_7 : Fin 7 → Fin 7 → ℚ := fun i j =>
  match uj_1_3_4_4_5_5_7 i j with
  | some (c, _) => c
  | none => 0

/-- The certified opening dominates its own certified-bound function. -/
theorem certBelow_1_3_4_4_5_5_7 : CertBelow (bnd_1_3_4_4_5_5_7) (uj_1_3_4_4_5_5_7) := by
  intro i j hne
  cases hj : uj_1_3_4_4_5_5_7 i j with
  | none =>
    exfalso
    simp only [bnd_1_3_4_4_5_5_7, hj] at hne
    exact absurd rfl hne
  | some p =>
    obtain ⟨c, s⟩ := p
    refine ⟨c, s, rfl, ?_⟩
    simp only [bnd_1_3_4_4_5_5_7, hj]
    exact le_refl _

#print axioms certBelow_1_3_4_4_5_5_7

/-- The strict-class composed family of box (1, 3, 4, 4, 5, 5, 7): every death row's strict-complete
primary witness from `joinedge2_perbox_v1.jsonl` (census: EVERY row of this box is
strict-complete), as a `ComposedEdge` `(y1-1, x1-1, P, Q, walk)` carrying the
witness's cap walk (hop product = the row's cap exactly; `P*cap <= Q` datum holds;
14 rows, 14 hops; w0n=1176 chains enumerated).  The FIRST edge is the rule-22 falsity witness of `not_dumpDom_1_3_4_4_5_5_7`
(row `end`, x1=4, y1=1, demand 41/15, cap 7/31 at pair (0,3), J-class). -/

def fam_1_3_4_4_5_5_7 : ComposedFam :=
  ⟨[
    ⟨3, 0, 41, 15, [(3, ((7/31 : ℚ) : ℝ))]⟩,
    ⟨6, 0, 65, 15, [(6, ((1/7 : ℚ) : ℝ))]⟩,
    ⟨3, 1, 41, 31, [(3, ((17/23 : ℚ) : ℝ))]⟩,
    ⟨3, 1, 41, 39, [(3, ((17/23 : ℚ) : ℝ))]⟩,
    ⟨3, 1, 41, 47, [(3, ((17/23 : ℚ) : ℝ))]⟩,
    ⟨3, 2, 41, 39, [(3, ((40425/45167 : ℚ) : ℝ))]⟩,
    ⟨3, 2, 41, 47, [(3, ((40425/45167 : ℚ) : ℝ))]⟩,
    ⟨3, 2, 41, 55, [(3, ((40425/45167 : ℚ) : ℝ))]⟩,
    ⟨3, 2, 41, 63, [(3, ((40425/45167 : ℚ) : ℝ))]⟩,
    ⟨3, 4, 41, 47, [(3, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨3, 4, 41, 55, [(3, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨3, 4, 41, 63, [(3, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨3, 4, 41, 71, [(3, ((1617/1457 : ℚ) : ℝ))]⟩,
    ⟨3, 4, 41, 79, [(3, ((1617/1457 : ℚ) : ℝ))]⟩
  ]⟩

/-- Per-record certified domination: every hop of every record's walk is bounded below
by the certified value (`CapsB`), i.e. the dump's dom_box/dom_J census, kernel-checked. -/
theorem capsB_1_3_4_4_5_5_7 : ∀ e ∈ (fam_1_3_4_4_5_5_7).edges, CapsB (bnd_1_3_4_4_5_5_7) e.caps e.y e.x := by
  intro e he
  simp only [fam_1_3_4_4_5_5_7, List.mem_cons] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact ⟨by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], by norm_num [bnd_1_3_4_4_5_5_7, uj_1_3_4_4_5_5_7, u0_1_3_4_4_5_5_7], rfl⟩
  · exact absurd h0 (by simp)

#print axioms capsB_1_3_4_4_5_5_7

/-- The certified-opening dump-v2 datum of box (1, 3, 4, 4, 5, 5, 7): for every in-box `g`, every real
W₀ chain opened at the certified opening `uj_1_3_4_4_5_5_7` has its closed trace dominate every
record's caps, hence the family's cap chains are realized on `g`
(`Fresh.CapChainsOfCarve.capChainsRealized_of_domData`'s trace disjunct).  This is
the certified-opening restriction of `Fresh.CapChainsOfCarve.DumpDom` (which
quantifies over arbitrary openings and is FALSE; see `not_dumpDom_1_3_4_4_5_5_7`). -/

theorem dumpDomData_1_3_4_4_5_5_7 {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i ≤ g i ∧
      g i ≤ FaceHi (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) i)
    (a : Fin 7) (Aex : ℚ) (steps : List Step)
    (hfine0 : UFine g (uj_1_3_4_4_5_5_7)) (hchain : ChainRealized g (uj_1_3_4_4_5_5_7) a Aex steps) :
    capChainsRealized g (fam_1_3_4_4_5_5_7) :=
  capChainsRealized_of_domData (fam_1_3_4_4_5_5_7) hface (uj_1_3_4_4_5_5_7) a Aex steps hfine0 hchain (by
    intro e he
    have hpos : ∀ k, 0 < g k := fun k => face_pos hface k
    refine Or.inr (fun V afn Af hrun => ?_)
    exact capsDom_of_capsB (certBelow_chainRun hpos (certBelow_1_3_4_4_5_5_7) hchain V afn Af hrun)
      (capsB_1_3_4_4_5_5_7 e he)

#print axioms dumpDomData_1_3_4_4_5_5_7

/-! ## 3. Rule 22 — literal `DumpDom` is false (the honest residual) -/

/-- The counterexample box (1, 3, 4, 4, 5, 5, 7) as an explicit function (so `simp` reduces
its values). -/
def box134455_7 : Fin 7 → ℤ := fun i =>
  match i.val with
  | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 4 | 4 => 5 | 5 => 5 | 6 => 7 | _ => 0

/-- The counterexample readings: an interior point of the box (kernel-checked in
`not_dumpDom_1_3_4_4_5_5_7`). -/
def gbad_134455_7 : Fin 7 → ℝ := fun i =>
  ((match i.val with
    | 0 => (32 : ℚ) / 25
    | 1 => (13 : ℚ) / 4
    | 2 => (17 : ℚ) / 4
    | 3 => (171 : ℚ) / 40
    | 4 => (9 : ℚ) / 2
    | 5 => (21 : ℚ) / 4
    | 6 => (29 : ℚ) / 4
    | _ => 0 : ℚ) : ℝ)

/-- The all-`none` opening table: realized by ANY readings (all entries vacuous). -/
def uNone : UTable := fun _ _ => none

theorem uNone_fine (g : Fin 7 → ℝ) : UFine g uNone := fun _ _ _ _ hb => absurd hb (by simp [uNone])

#print axioms uNone_fine

/-- The counterexample's one chain step survives on `uNone`: no stored entries means the
keep/back tests fail and the propagation has no paths to compose, so both `uAdd`s return
`some uNone`. -/
theorem uProp_uNone (i j : Fin 7) (c : ℚ) (s : Bool) : uProp uNone i j c s = uNone := by
  funext p q
  simp [uProp, uNone]

theorem uAdd_uNone_none (i j : Fin 7) (c : ℚ) (s : Bool) :
    uAdd uNone i j c s = some uNone := by
  simp [uAdd, uKeepCur, uBack, uNone, uProp_uNone]

theorem uStep_none_none : uStep uNone 3 4 23 23 25 = some uNone := by
  unfold uStep
  rw [uGt_pos (U := uNone) (a := 3) (b := 4) (A := 23) (B := 23) (by norm_num) (by norm_num)]
  simp only [uAdd_uNone_none, Option.bind_some]
  rw [uGt_pos (U := uNone) (a := 4) (b := 3) (A := 25) (B := 23) (by norm_num) (by norm_num)]
  exact uAdd_uNone_none 4 3 (25 / 23) true

#print axioms uStep_none_none

/-- The counterexample chain is REAL: each step's two strict seam bounds and the exit
bound hold at `gbad_134455_7` (kernel-checked), the step survives on `uNone`. -/
theorem chain_bad_134455_7 : ChainRealized gbad_134455_7 uNone 3 23 [⟨4, 23, 25⟩] := by
  refine ⟨uNone, uStep_none_none, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · simp only [BHolds, gbad_134455_7]; push_cast; norm_num
  · simp only [BHolds, gbad_134455_7]; push_cast; norm_num
  · simp only [ChainRealized, BHolds, gbad_134455_7]; push_cast; norm_num

#print axioms chain_bad_134455_7

/-- The counterexample chain's closed trace: `uNone` itself (no entries created). -/
theorem hrun_bad : chainRun uNone 3 23 [⟨4, 23, 25⟩] = some (uNone, (4 : Fin 7), (25 : ℚ)) := by
  simp only [chainRun, uStep_none_none, Option.bind_some]

#print axioms hrun_bad

/-- A `CapsDom` claim against the all-`none` table is absurd at any nonempty walk: the
first hop needs a stored entry. -/
theorem capsDom_uNone_false {y z : Fin 7} {c : ℝ} {l : List (Fin 7 × ℝ)} {x : Fin 7}
    (h : CapsDom uNone y ((z, c) :: l) x) : False := by
  cases h with
  | cons _ _ _ _ _ hentry _ =>
    obtain ⟨_, _, hn, _⟩ := hentry
    simp [uNone] at hn

#print axioms capsDom_uNone_false

/-- The counterexample edge: the family's first record (J-side cap `7/31` at pair `(0,3)`,
demand `41/15`). -/
theorem mem_cb_edge :
    ⟨0, 3, 41, 15, [(3, ((7/31 : ℚ) : ℝ))]⟩ ∈ (fam_1_3_4_4_5_5_7).edges := by
  simp only [fam_1_3_4_4_5_5_7, List.mem_cons]
  exact Or.inl rfl

#print axioms mem_cb_edge

/-- **Rule 22 (the falsity witness).**  Literal `Fresh.CapChainsOfCarve.DumpDom` for the
strict family of box (1, 3, 4, 4, 5, 5, 7) is FALSE: the all-`none` opening `uNone` is
realized by the interior readings `gbad_134455_7`, the one-step chain `chain_bad_134455_7`
is real with closed trace `uNone` (`hrun_bad`), and BOTH of `DumpDom`'s disjuncts fail on
the family's first record — its cap's certifying entries live in the box closure / join
tables, not in an arbitrary opening or a short chain's trace.  The dump's certification
(domination by the box closure or the enumerated join, per hop) is therefore strictly
weaker than the quantifier shape `DumpDom` carries, and the bankable form is the
certified-opening restriction `dumpDomData_*` of this file. -/
theorem not_dumpDom_1_3_4_4_5_5_7 :
    ¬ DumpDom box134455_7 fam_1_3_4_4_5_5_7 := by
  intro h
  have hg : ∀ i, FaceLo box134455_7 i ≤ gbad_134455_7 i ∧
      gbad_134455_7 i ≤ FaceHi box134455_7 i := by
    intro i
    fin_cases i
    all_goals (simp only [FaceLo, FaceHi, box134455_7, gbad_134455_7]; push_cast; norm_num)
  have hsp := h gbad_134455_7 hg uNone 3 23 [⟨4, 23, 25⟩] (uNone_fine _) chain_bad_134455_7
  rcases hsp ⟨0, 3, 41, 15, [(3, ((7/31 : ℚ) : ℝ))]⟩ mem_cb_edge with h1 | h2
  · exact capsDom_uNone_false h1
  · exact capsDom_uNone_false (h2 uNone 4 25 hrun_bad)

#print axioms not_dumpDom_1_3_4_4_5_5_7
