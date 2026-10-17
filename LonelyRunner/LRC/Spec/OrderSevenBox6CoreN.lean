import LonelyRunner.LRC.Spec.OrderSevenKappaTreeCoreN

/-!
# Order seven: the six-runner box-tree checker and its soundness

Ratios `x_i = v_i / v6 ∈ [a_i, b_i]` (`i = 0..4`), time `τ` in units `1/v6`.  A **leaf** `L p q n0 … n5` names the instant
`τ = p/q` and laps with `a_i τ ≥ n_i + 1/7`, `b_i τ ≤ n_i + 6/7` (term-wise linear bounds) and, for runner 6 (ratio 1),
`n5 + 1/7 ≤ τ ≤ n5 + 6/7`.  **E**: no increasing point.  **S d p q l r**: split coordinate `d` at the value
`p/q` stored in the tree (the generator uses the point `k/42` nearest the midpoint, else the midpoint).  Split trees as in `OrderSevenKappaTreeCoreN`.

`lonely_of_win6`: whole numbers `0 < v1 < … < v6` with ratios in the root box are lonely at `1/7`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Box6

open LRC.MirrorCentre LRC.O7Split

structure Bx where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  a4 : ℚ
  b0 : ℚ
  b1 : ℚ
  b2 : ℚ
  b3 : ℚ
  b4 : ℚ
  deriving DecidableEq

inductive T
  | L (p q n0 n1 n2 n3 n4 n5 : ℕ)
  | E
  | S (d p q : ℕ) (l r : T)

def runOK (a b τ : ℚ) (n : ℕ) : Bool :=
  decide (0 < a) && decide ((n : ℚ) + 1 / 7 ≤ a * τ) && decide (b * τ ≤ (n : ℚ) + 6 / 7)

def leafOK (B : Bx) (p q n0 n1 n2 n3 n4 n5 : ℕ) : Bool :=
  decide (0 < q) &&
    runOK B.a0 B.b0 ((p : ℚ) / q) n0 && runOK B.a1 B.b1 ((p : ℚ) / q) n1 &&
    runOK B.a2 B.b2 ((p : ℚ) / q) n2 && runOK B.a3 B.b3 ((p : ℚ) / q) n3 &&
    runOK B.a4 B.b4 ((p : ℚ) / q) n4 && runOK 1 1 ((p : ℚ) / q) n5

def emptyB (B : Bx) : Bool :=
  decide (B.b1 ≤ B.a0) || decide (B.b2 ≤ B.a1) || decide (B.b3 ≤ B.a2) || decide (B.b4 ≤ B.a3) ||
    decide (1 ≤ B.a4)

/-- Split coordinate `d` at the value `x` (any value: soundness only uses that the two halves cover the box). -/
def splitB (B : Bx) (d : ℕ) (x : ℚ) : Bx × Bx :=
  if d = 0 then ({ B with b0 := x }, { B with a0 := x })
  else if d = 1 then ({ B with b1 := x }, { B with a1 := x })
  else if d = 2 then ({ B with b2 := x }, { B with a2 := x })
  else if d = 3 then ({ B with b3 := x }, { B with a3 := x })
  else ({ B with b4 := x }, { B with a4 := x })

def check : T → Bx → Bool
  | .L p q n0 n1 n2 n3 n4 n5, B => leafOK B p q n0 n1 n2 n3 n4 n5
  | .E, B => emptyB B
  | .S d p q l r, B => check l (splitB B d ((p : ℚ) / q)).1 && check r (splitB B d ((p : ℚ) / q)).2

def root (x y : ℚ) : Bx := ⟨x, x, x, x, y, 1, 1, 1, 1, 1⟩

def Mem (B : Bx) (x : Fin 5 → ℝ) : Prop :=
  ((B.a0 : ℝ) ≤ x 0 ∧ x 0 ≤ B.b0) ∧ ((B.a1 : ℝ) ≤ x 1 ∧ x 1 ≤ B.b1) ∧
    ((B.a2 : ℝ) ≤ x 2 ∧ x 2 ≤ B.b2) ∧ ((B.a3 : ℝ) ≤ x 3 ∧ x 3 ≤ B.b3) ∧
    ((B.a4 : ℝ) ≤ x 4 ∧ x 4 ≤ B.b4) ∧
    x 0 < x 1 ∧ x 1 < x 2 ∧ x 2 < x 3 ∧ x 3 < x 4 ∧ x 4 < 1

def Inst (x : Fin 5 → ℝ) : Prop :=
  ∃ τ : ℝ, (1 : ℝ) / 7 ≤ circDist τ ∧ ∀ i, (1 : ℝ) / 7 ≤ circDist (x i * τ)

theorem runOK_band {a b τ : ℚ} {n : ℕ} (h : runOK a b τ n = true) {x : ℝ} (hxa : (a : ℝ) ≤ x)
    (hxb : x ≤ b) : (1 : ℝ) / 7 ≤ circDist (x * τ) := by
  simp only [runOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha, h1⟩, h2⟩ := h
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h1' : (n : ℝ) + 1 / 7 ≤ (a : ℝ) * τ := by
    have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast at this; linarith
  have h2' : (b : ℝ) * τ ≤ (n : ℝ) + 6 / 7 := by
    have := (Rat.cast_le (K := ℝ)).mpr h2; push_cast at this; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hτ : (0 : ℝ) < τ := by
    by_contra hc; rw [not_lt] at hc; nlinarith
  apply circDist_ge_of_window (m := (n : ℤ)) _ _ (by norm_num)
  · push_cast; nlinarith
  · push_cast; nlinarith

theorem leafOK_inst {B : Bx} {p q n0 n1 n2 n3 n4 n5 : ℕ} (h : leafOK B p q n0 n1 n2 n3 n4 n5 = true)
    {x : Fin 5 → ℝ} (hx : Mem B x) : Inst x := by
  simp only [leafOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  obtain ⟨hx0, hx1, hx2, hx3, hx4, -⟩ := hx
  refine ⟨(((p : ℚ) / q : ℚ) : ℝ), ?_, ?_⟩
  · simpa using runOK_band h5 (x := 1) (by norm_num) (by norm_num)
  · intro i
    fin_cases i
    · exact runOK_band h0 hx0.1 hx0.2
    · exact runOK_band h1 hx1.1 hx1.2
    · exact runOK_band h2 hx2.1 hx2.2
    · exact runOK_band h3 hx3.1 hx3.2
    · exact runOK_band h4 hx4.1 hx4.2

theorem emptyB_false {B : Bx} (h : emptyB B = true) {x : Fin 5 → ℝ} (hx : Mem B x) : False := by
  simp only [emptyB, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hx0, hx1, hx2, hx3, hx4, h01, h12, h23, h34, h41⟩ := hx
  rcases h with (((h | h) | h) | h) | h
  · have : (B.b1 : ℝ) ≤ B.a0 := by exact_mod_cast h
    linarith [hx0.1, hx1.2]
  · have : (B.b2 : ℝ) ≤ B.a1 := by exact_mod_cast h
    linarith [hx1.1, hx2.2]
  · have : (B.b3 : ℝ) ≤ B.a2 := by exact_mod_cast h
    linarith [hx2.1, hx3.2]
  · have : (B.b4 : ℝ) ≤ B.a3 := by exact_mod_cast h
    linarith [hx3.1, hx4.2]
  · have : (1 : ℝ) ≤ B.a4 := by exact_mod_cast h
    linarith [hx4.1]

theorem mem_split {B : Bx} (d : ℕ) (c : ℚ) {x : Fin 5 → ℝ} (hx : Mem B x) :
    Mem (splitB B d c).1 x ∨ Mem (splitB B d c).2 x := by
  obtain ⟨hx0, hx1, hx2, hx3, hx4, ho⟩ := hx
  unfold splitB
  split_ifs
  · rcases le_total (x 0) (c : ℝ) with h | h
    · exact Or.inl ⟨⟨hx0.1, h⟩, hx1, hx2, hx3, hx4, ho⟩
    · exact Or.inr ⟨⟨h, hx0.2⟩, hx1, hx2, hx3, hx4, ho⟩
  · rcases le_total (x 1) (c : ℝ) with h | h
    · exact Or.inl ⟨hx0, ⟨hx1.1, h⟩, hx2, hx3, hx4, ho⟩
    · exact Or.inr ⟨hx0, ⟨h, hx1.2⟩, hx2, hx3, hx4, ho⟩
  · rcases le_total (x 2) (c : ℝ) with h | h
    · exact Or.inl ⟨hx0, hx1, ⟨hx2.1, h⟩, hx3, hx4, ho⟩
    · exact Or.inr ⟨hx0, hx1, ⟨h, hx2.2⟩, hx3, hx4, ho⟩
  · rcases le_total (x 3) (c : ℝ) with h | h
    · exact Or.inl ⟨hx0, hx1, hx2, ⟨hx3.1, h⟩, hx4, ho⟩
    · exact Or.inr ⟨hx0, hx1, hx2, ⟨h, hx3.2⟩, hx4, ho⟩
  · rcases le_total (x 4) (c : ℝ) with h | h
    · exact Or.inl ⟨hx0, hx1, hx2, hx3, ⟨hx4.1, h⟩, ho⟩
    · exact Or.inr ⟨hx0, hx1, hx2, hx3, ⟨h, hx4.2⟩, ho⟩

theorem check_sound : ∀ (t : T) (B : Bx), check t B = true → ∀ x, Mem B x → Inst x
  | .L p q n0 n1 n2 n3 n4 n5, B, h, x, hx => leafOK_inst h hx
  | .E, B, h, x, hx => (emptyB_false h hx).elim
  | .S d p q l r, B, h, x, hx => by
    simp only [check, Bool.and_eq_true] at h
    rcases mem_split d ((p : ℚ) / q) hx with h1 | h2
    · exact check_sound l _ h.1 x h1
    · exact check_sound r _ h.2 x h2

inductive TS
  | Sub (i : ℕ)
  | S (d p q : ℕ) (l r : TS)

def boxesOf : TS → Bx → List (ℕ × Bx)
  | .Sub i, B => [(i, B)]
  | .S d p q l r, B => boxesOf l (splitB B d ((p : ℚ) / q)).1 ++ boxesOf r (splitB B d ((p : ℚ) / q)).2

theorem boxesOf_cover : ∀ (ts : TS) (B : Bx) (x : Fin 5 → ℝ), Mem B x → ∃ p ∈ boxesOf ts B, Mem p.2 x
  | .Sub i, B, x, hx => ⟨(i, B), by simp [boxesOf], hx⟩
  | .S d p q l r, B, x, hx => by
    rcases mem_split d ((p : ℚ) / q) hx with h1 | h2
    · obtain ⟨u, hu, hm⟩ := boxesOf_cover l _ x h1
      exact ⟨u, by simp only [boxesOf, List.mem_append]; exact Or.inl hu, hm⟩
    · obtain ⟨u, hu, hm⟩ := boxesOf_cover r _ x h2
      exact ⟨u, by simp only [boxesOf, List.mem_append]; exact Or.inr hu, hm⟩

def skelOK (ts : TS) (B : Bx) (all : List (T × Bx)) : Bool :=
  (boxesOf ts B).all (fun p => decide (p.1 < all.length) && decide ((all.getD p.1 (T.E, B)).2 = p.2))

theorem split_sound {ts : TS} {B : Bx} {all : List (T × Bx)} (hs : skelOK ts B all = true)
    (hall : all.all (fun p => check p.1 p.2) = true) : ∀ x, Mem B x → Inst x := by
  intro x hx
  obtain ⟨p, hp, hm⟩ := boxesOf_cover ts B x hx
  have h1 := List.all_eq_true.mp hs p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨hlt, heq⟩ := h1
  have hmem : all.getD p.1 (T.E, B) ∈ all := by
    rw [List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem hlt
  have hc := List.all_eq_true.mp hall _ hmem
  rw [heq] at hc
  exact check_sound _ _ hc x hm

/-- **Order seven from a checked six-runner tree.**  Whole numbers `0 < v1 < … < v6` with `X v6 ≤ v1` and
`Y v6 ≤ v5` are lonely at `1/7`. -/
theorem lonely_of_inst {X Y : ℚ} (hW : ∀ x, Mem (root X Y) x → Inst x) {v1 v2 v3 v4 v5 v6 : ℕ} (h0 : 0 < v1)
    (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5) (h56 : v5 < v6)
    (hX : (X : ℝ) * v6 ≤ v1) (hY : (Y : ℝ) * v6 ≤ v5) :
    ∃ t : ℝ, ∀ d ∈ ({v1, v2, v3, v4, v5, v6} : Finset ℕ), (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  have h6 : (0 : ℝ) < v6 := by exact_mod_cast (show 0 < v6 by omega)
  set x : Fin 5 → ℝ := ![(v1 : ℝ) / v6, (v2 : ℝ) / v6, (v3 : ℝ) / v6, (v4 : ℝ) / v6, (v5 : ℝ) / v6] with hxdef
  have hc : ∀ {a b : ℕ}, a < b → (a : ℝ) / v6 < (b : ℝ) / v6 := fun hab =>
    div_lt_div_of_pos_right (by exact_mod_cast hab) h6
  have hle1 : ∀ {a : ℕ}, a < v6 → (a : ℝ) / v6 < 1 := fun ha => by
    rw [div_lt_one h6]; exact_mod_cast ha
  have hX1 : (X : ℝ) ≤ (v1 : ℝ) / v6 := by rw [le_div_iff₀ h6]; exact hX
  have hY1 : (Y : ℝ) ≤ (v5 : ℝ) / v6 := by rw [le_div_iff₀ h6]; exact hY
  have e0 : x 0 = (v1 : ℝ) / v6 := rfl
  have e1 : x 1 = (v2 : ℝ) / v6 := rfl
  have e2 : x 2 = (v3 : ℝ) / v6 := rfl
  have e3 : x 3 = (v4 : ℝ) / v6 := rfl
  have e4 : x 4 = (v5 : ℝ) / v6 := rfl
  have h12' := hc h12; have h23' := hc h23; have h34' := hc h34; have h45' := hc h45
  have hmem : Mem (root X Y) x := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [root, e0, e1, e2, e3, e4, Rat.cast_one]
    · exact hX1
    · exact (hle1 (by omega)).le
    · linarith
    · exact (hle1 (by omega)).le
    · linarith
    · exact (hle1 (by omega)).le
    · linarith
    · exact (hle1 (by omega)).le
    · exact hY1
    · exact (hle1 h56).le
    · exact h12'
    · exact h23'
    · exact h34'
    · exact h45'
    · exact hle1 h56
  obtain ⟨τ, h6b, hib⟩ := hW x hmem
  refine ⟨τ / v6, fun d hd => ?_⟩
  have key : ∀ (i : Fin 5) (a : ℕ), x i = (a : ℝ) / v6 → (1 : ℝ) / 7 ≤ circDist ((a : ℝ) * (τ / v6)) := by
    intro i a hxi
    have := hib i
    rwa [hxi, show (a : ℝ) / v6 * τ = a * (τ / v6) by ring] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key 0 _ rfl
  · exact key 1 _ rfl
  · exact key 2 _ rfl
  · exact key 3 _ rfl
  · exact key 4 _ rfl
  · rwa [show (d : ℝ) * (τ / d) = τ by field_simp]

end LRC.O7Box6
