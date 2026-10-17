import LonelyRunner.LRC.Spec.OrderSevenSplitN

/-!
# Order seven: the `kappa ≥ 3/28` box-tree checker and its soundness

Ratios `x_i = v_i / v5 ∈ [a_i, b_i]` (`i = 0..3`), time `τ` in units `1/v5`.  A **leaf** `L p q n0 n1 n2 n3 n4`
names the window `[ℓ, ℓ + 3/28]`, `ℓ = p/q`, and laps with `a_i ℓ ≥ n_i + 1/7`, `b_i (ℓ + 3/28) ≤ n_i + 6/7`, and for
runner 5 (ratio 1) `n4 + 1/7 ≤ ℓ`, `ℓ + 3/28 ≤ n4 + 6/7`; these are term-wise linear bounds, `x_i τ` being increasing
in both factors.  **E** marks a box with no increasing point (`a_i ≥ b_{i+1}` or `a_3 ≥ 1`).  **S d l r** splits
coordinate `d` at `splitPt` (the point `k/7` inside the interval nearest its midpoint, else the midpoint).

`check_sound`: a checked tree gives, for every increasing `x` in the box, a window of length `3/28` on which every
`x_i τ` and `τ` read inside `[1/7, 6/7]`.  `kappa_of_check`: for whole numbers `v1 < … < v5` with ratios in the box,
`InBandOn {v1, …, v5}` on an interval of length `3/(28 v5)`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7KTree

open LRC.MirrorCentre LRC.O7Split

structure Bx where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  b0 : ℚ
  b1 : ℚ
  b2 : ℚ
  b3 : ℚ
  deriving DecidableEq

inductive T
  | L (p q n0 n1 n2 n3 n4 : ℕ)
  | E
  | S (d : ℕ) (l r : T)

def Bx.a (B : Bx) : Fin 4 → ℚ := ![B.a0, B.a1, B.a2, B.a3]
def Bx.b (B : Bx) : Fin 4 → ℚ := ![B.b0, B.b1, B.b2, B.b3]

def K : ℚ := 3 / 28

def runOK (a b ℓ : ℚ) (n : ℕ) : Bool :=
  decide (0 < a) && decide ((n : ℚ) + 1 / 7 ≤ a * ℓ) && decide (b * (ℓ + K) ≤ (n : ℚ) + 6 / 7)

def leafOK (B : Bx) (p q n0 n1 n2 n3 n4 : ℕ) : Bool :=
  decide (0 < q) &&
    runOK B.a0 B.b0 ((p : ℚ) / q) n0 && runOK B.a1 B.b1 ((p : ℚ) / q) n1 &&
    runOK B.a2 B.b2 ((p : ℚ) / q) n2 && runOK B.a3 B.b3 ((p : ℚ) / q) n3 &&
    runOK 1 1 ((p : ℚ) / q) n4

def emptyB (B : Bx) : Bool :=
  decide (B.b1 ≤ B.a0) || decide (B.b2 ≤ B.a1) || decide (B.b3 ≤ B.a2) || decide (1 ≤ B.a3)

/-- The point `k/7` strictly inside `(a, b)` nearest the midpoint (first such `k` on ties), else the midpoint. -/
def splitPt (a b : ℚ) : ℚ :=
  let m := (a + b) / 2
  let cands := (List.range 6).map (fun k => ((k : ℚ) + 1) / 7) |>.filter (fun z => decide (a < z) && decide (z < b))
  cands.foldl (fun best z => if |z - m| < |best - m| then z else best) (cands.headD m)

def splitB (B : Bx) (d : ℕ) : Bx × Bx :=
  if d = 0 then let x := splitPt B.a0 B.b0; ({ B with b0 := x }, { B with a0 := x })
  else if d = 1 then let x := splitPt B.a1 B.b1; ({ B with b1 := x }, { B with a1 := x })
  else if d = 2 then let x := splitPt B.a2 B.b2; ({ B with b2 := x }, { B with a2 := x })
  else let x := splitPt B.a3 B.b3; ({ B with b3 := x }, { B with a3 := x })

def check : T → Bx → Bool
  | .L p q n0 n1 n2 n3 n4, B => leafOK B p q n0 n1 n2 n3 n4
  | .E, B => emptyB B
  | .S d l r, B => check l (splitB B d).1 && check r (splitB B d).2

def root (x : ℚ) : Bx := ⟨x, x, x, x, 1, 1, 1, 1⟩

/-- `x` lies in the box `B` and is increasing with `x 3 < 1`. -/
def Mem (B : Bx) (x : Fin 4 → ℝ) : Prop :=
  ((B.a0 : ℝ) ≤ x 0 ∧ x 0 ≤ B.b0) ∧ ((B.a1 : ℝ) ≤ x 1 ∧ x 1 ≤ B.b1) ∧
    ((B.a2 : ℝ) ≤ x 2 ∧ x 2 ≤ B.b2) ∧ ((B.a3 : ℝ) ≤ x 3 ∧ x 3 ≤ B.b3) ∧
    x 0 < x 1 ∧ x 1 < x 2 ∧ x 2 < x 3 ∧ x 3 < 1

/-- The window property at ratio vector `x`. -/
def Win (x : Fin 4 → ℝ) : Prop :=
  ∃ ℓ : ℝ, ∀ τ, ℓ ≤ τ → τ ≤ ℓ + 3 / 28 →
    (1 : ℝ) / 7 ≤ circDist τ ∧ ∀ i, (1 : ℝ) / 7 ≤ circDist (x i * τ)

theorem runOK_band {a b ℓ : ℚ} {n : ℕ} (h : runOK a b ℓ n = true) {x τ : ℝ} (hxa : (a : ℝ) ≤ x)
    (hxb : x ≤ b) (hτ1 : (ℓ : ℝ) ≤ τ) (hτ2 : τ ≤ ℓ + 3 / 28) : (1 : ℝ) / 7 ≤ circDist (x * τ) := by
  simp only [runOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha, h1⟩, h2⟩ := h
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h1' : (n : ℝ) + 1 / 7 ≤ (a : ℝ) * ℓ := by
    have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast at this; linarith
  have h2' : (b : ℝ) * ((ℓ : ℝ) + 3 / 28) ≤ (n : ℝ) + 6 / 7 := by
    simp only [K] at h2
    have := (Rat.cast_le (K := ℝ)).mpr h2; push_cast at this; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hℓ : (0 : ℝ) < ℓ := by
    by_contra hc; rw [not_lt] at hc; nlinarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha' hxa
  have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hℓ hτ1
  apply circDist_ge_of_window (m := (n : ℤ)) _ _ (by norm_num)
  · push_cast; nlinarith
  · push_cast; nlinarith

theorem leafOK_win {B : Bx} {p q n0 n1 n2 n3 n4 : ℕ} (h : leafOK B p q n0 n1 n2 n3 n4 = true)
    {x : Fin 4 → ℝ} (hx : Mem B x) : Win x := by
  simp only [leafOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  obtain ⟨hx0, hx1, hx2, hx3, -⟩ := hx
  refine ⟨(((p : ℚ) / q : ℚ) : ℝ), fun τ hτ1 hτ2 => ⟨?_, ?_⟩⟩
  · have := runOK_band h4 (x := 1) (by norm_num) (by norm_num) hτ1 hτ2
    simpa using this
  · intro i
    fin_cases i
    · exact runOK_band h0 hx0.1 hx0.2 hτ1 hτ2
    · exact runOK_band h1 hx1.1 hx1.2 hτ1 hτ2
    · exact runOK_band h2 hx2.1 hx2.2 hτ1 hτ2
    · exact runOK_band h3 hx3.1 hx3.2 hτ1 hτ2

theorem emptyB_false {B : Bx} (h : emptyB B = true) {x : Fin 4 → ℝ} (hx : Mem B x) : False := by
  simp only [emptyB, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hx0, hx1, hx2, hx3, h01, h12, h23, h31⟩ := hx
  rcases h with ((h | h) | h) | h
  · have : (B.b1 : ℝ) ≤ B.a0 := by exact_mod_cast h
    linarith [hx0.1, hx1.2]
  · have : (B.b2 : ℝ) ≤ B.a1 := by exact_mod_cast h
    linarith [hx1.1, hx2.2]
  · have : (B.b3 : ℝ) ≤ B.a2 := by exact_mod_cast h
    linarith [hx2.1, hx3.2]
  · have : (1 : ℝ) ≤ B.a3 := by exact_mod_cast h
    linarith [hx3.1]

theorem mem_split {B : Bx} (d : ℕ) {x : Fin 4 → ℝ} (hx : Mem B x) :
    Mem (splitB B d).1 x ∨ Mem (splitB B d).2 x := by
  obtain ⟨hx0, hx1, hx2, hx3, ho⟩ := hx
  unfold splitB
  split_ifs
  · rcases le_total (x 0) (splitPt B.a0 B.b0 : ℝ) with h | h
    · exact Or.inl ⟨⟨hx0.1, h⟩, hx1, hx2, hx3, ho⟩
    · exact Or.inr ⟨⟨h, hx0.2⟩, hx1, hx2, hx3, ho⟩
  · rcases le_total (x 1) (splitPt B.a1 B.b1 : ℝ) with h | h
    · exact Or.inl ⟨hx0, ⟨hx1.1, h⟩, hx2, hx3, ho⟩
    · exact Or.inr ⟨hx0, ⟨h, hx1.2⟩, hx2, hx3, ho⟩
  · rcases le_total (x 2) (splitPt B.a2 B.b2 : ℝ) with h | h
    · exact Or.inl ⟨hx0, hx1, ⟨hx2.1, h⟩, hx3, ho⟩
    · exact Or.inr ⟨hx0, hx1, ⟨h, hx2.2⟩, hx3, ho⟩
  · rcases le_total (x 3) (splitPt B.a3 B.b3 : ℝ) with h | h
    · exact Or.inl ⟨hx0, hx1, hx2, ⟨hx3.1, h⟩, ho⟩
    · exact Or.inr ⟨hx0, hx1, hx2, ⟨h, hx3.2⟩, ho⟩

/-- **Soundness of the checker.** -/
theorem check_sound : ∀ (t : T) (B : Bx), check t B = true → ∀ x, Mem B x → Win x
  | .L p q n0 n1 n2 n3 n4, B, h, x, hx => leafOK_win h hx
  | .E, B, h, x, hx => (emptyB_false h hx).elim
  | .S d l r, B, h, x, hx => by
    simp only [check, Bool.and_eq_true] at h
    rcases mem_split d hx with h1 | h2
    · exact check_sound l _ h.1 x h1
    · exact check_sound r _ h.2 x h2


/-! ### Trees split across modules

A skeleton `TS` holds the top levels; its leaves `Sub i` point into a list of `(subtree, box)` pairs, each checked in
its own module.  `boxesOf` lists the boxes the skeleton assigns to its leaves; they cover the root. -/

inductive TS
  | Sub (i : ℕ)
  | S (d : ℕ) (l r : TS)

def boxesOf : TS → Bx → List (ℕ × Bx)
  | .Sub i, B => [(i, B)]
  | .S d l r, B => boxesOf l (splitB B d).1 ++ boxesOf r (splitB B d).2

theorem boxesOf_cover : ∀ (ts : TS) (B : Bx) (x : Fin 4 → ℝ), Mem B x → ∃ p ∈ boxesOf ts B, Mem p.2 x
  | .Sub i, B, x, hx => ⟨(i, B), by simp [boxesOf], hx⟩
  | .S d l r, B, x, hx => by
    rcases mem_split d hx with h1 | h2
    · obtain ⟨p, hp, hm⟩ := boxesOf_cover l _ x h1
      exact ⟨p, by simp only [boxesOf, List.mem_append]; exact Or.inl hp, hm⟩
    · obtain ⟨p, hp, hm⟩ := boxesOf_cover r _ x h2
      exact ⟨p, by simp only [boxesOf, List.mem_append]; exact Or.inr hp, hm⟩

/-- The skeleton's boxes match the listed boxes, by index. -/
def skelOK (ts : TS) (B : Bx) (all : List (T × Bx)) : Bool :=
  (boxesOf ts B).all (fun p => decide (p.1 < all.length) && decide ((all.getD p.1 (T.E, B)).2 = p.2))

/-- **Soundness of a split tree.** -/
theorem split_sound {ts : TS} {B : Bx} {all : List (T × Bx)} (hs : skelOK ts B all = true)
    (hall : all.all (fun p => check p.1 p.2) = true) : ∀ x, Mem B x → Win x := by
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

/-- **`kappa ≥ 3/28` from a checked tree.**  Whole numbers `0 < v1 < … < v5` with `X v5 ≤ v1`: the five speeds are in
band on an interval of length `3/(28 v5)`. -/
theorem kappa_of_win {X : ℚ} (hW : ∀ x, Mem (root X) x → Win x) {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1)
    (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5) (hX : (X : ℝ) * v5 ≤ v1) :
    ∃ s₀ : ℝ, InBandOn {v1, v2, v3, v4, v5} (Set.Icc s₀ (s₀ + 3 / (28 * v5))) := by
  have h5 : (0 : ℝ) < v5 := by exact_mod_cast (show 0 < v5 by omega)
  set x : Fin 4 → ℝ := ![(v1 : ℝ) / v5, (v2 : ℝ) / v5, (v3 : ℝ) / v5, (v4 : ℝ) / v5] with hxdef
  have hc : ∀ {a b : ℕ}, a < b → (a : ℝ) / v5 < (b : ℝ) / v5 := fun hab =>
    div_lt_div_of_pos_right (by exact_mod_cast hab) h5
  have hle1 : ∀ {a : ℕ}, a < v5 → (a : ℝ) / v5 < 1 := fun ha => by
    rw [div_lt_one h5]; exact_mod_cast ha
  have hX1 : (X : ℝ) ≤ (v1 : ℝ) / v5 := by rw [le_div_iff₀ h5]; exact hX
  have e0 : x 0 = (v1 : ℝ) / v5 := rfl
  have e1 : x 1 = (v2 : ℝ) / v5 := rfl
  have e2 : x 2 = (v3 : ℝ) / v5 := rfl
  have e3 : x 3 = (v4 : ℝ) / v5 := rfl
  have h12' := hc h12; have h23' := hc h23; have h34' := hc h34
  have hmem : Mem (root X) x := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
      simp only [root, e0, e1, e2, e3, Rat.cast_one]
    · exact hX1
    · exact (hle1 (by omega)).le
    · linarith
    · exact (hle1 (by omega)).le
    · linarith
    · exact (hle1 (by omega)).le
    · linarith
    · exact (hle1 h45).le
    · exact h12'
    · exact h23'
    · exact h34'
    · exact hle1 h45
  obtain ⟨ℓ, hℓ⟩ := hW x hmem
  refine ⟨ℓ / v5, fun s hs d hd => ?_⟩
  have hτ1 : ℓ ≤ v5 * s := by have := hs.1; rw [div_le_iff₀ h5] at this; linarith
  have hτ2 : v5 * s ≤ ℓ + 3 / 28 := by
    have := hs.2
    have e : ℓ / v5 + 3 / (28 * v5) = (ℓ + 3 / 28) / v5 := by field_simp
    rw [e, le_div_iff₀ h5] at this; linarith
  obtain ⟨h5b, hib⟩ := hℓ (v5 * s) hτ1 hτ2
  have key : ∀ (i : Fin 4) (a : ℕ), x i = (a : ℝ) / v5 → (1 : ℝ) / 7 ≤ circDist ((a : ℝ) * s) := by
    intro i a hxi
    have := hib i
    rwa [hxi, show (a : ℝ) / v5 * (v5 * s) = a * s by field_simp] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  · exact key 0 _ rfl
  · exact key 1 _ rfl
  · exact key 2 _ rfl
  · exact key 3 _ rfl
  · simpa [mul_comm] using h5b

theorem kappa_of_check {t : T} {X : ℚ} (h : check t (root X) = true) {v1 v2 v3 v4 v5 : ℕ} (h0 : 0 < v1)
    (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5) (hX : (X : ℝ) * v5 ≤ v1) :
    ∃ s₀ : ℝ, InBandOn {v1, v2, v3, v4, v5} (Set.Icc s₀ (s₀ + 3 / (28 * v5))) :=
  kappa_of_win (check_sound t _ h) h0 h12 h23 h34 h45 hX

end LRC.O7KTree
