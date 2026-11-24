import Mathlib
import Fresh.CarveExclusionCerts
import Fresh.FilterAssembly

/-!
# A self-splitting fixed-clear-point checker for the M4 boxes (2026-11-22)

New file; nothing existing is edited.

A box is a list of faces `[a_i/2^e, b_i/2^e]` (natural numbers `a_i, b_i`, common scale `2^e`).
`leafOK` asks for one clear instant `R ∈ [1,7]` (the time `R/8 ∈ [1/8, 7/8]`) that holds for
every reading over the whole face: `R·[a_i, b_i]/2^e ⊆ [8j_i+1, 8j_i+7]`.  The candidates for
`R` are `1` and the exit edges `(8j+1)·2^e / a_i`; this is complete, because the least point of
any nonempty piece of the feasible set is one of them.  `check` tries the leaf and otherwise
bisects the widest face at its midpoint, up to `fuel` levels.

`check_sound`: a `true` verdict gives, for every reading vector in the box, a common clear
instant `R ∈ [1,7]`.  The sub-boxes cover the box [PROVISIONAL: covering -- supports
"a clear instant for every reading vector in the box"].  The clear instant of each leaf is the
place: the first point of the leaf's feasible set, an exit edge `(8j+1)/ρ_i` of one reading
(or `R = 1`).
-/

namespace Fresh.M4SplitCheck

open Fresh Fresh.Certs

/-! ## The checker (computable, natural-number arithmetic only) -/

/-- Face `[a,b]` scaled by `p`, over the denominator `D = q·2^e`, lies in one closed gap
`[8j+1, 8j+7]` with `j = ⌊(pa − D)/(8D)⌋`. -/
def gapOK (p a b D : ℕ) : Bool :=
  decide (D ≤ p * a) && decide (p * b ≤ (8 * ((p * a - D) / (8 * D)) + 7) * D)

/-- The instant `R = p/q` is clear for every face of the box and lies in `[1,7]`. -/
def leafAt (p q e : ℕ) (box : List (ℕ × ℕ)) : Bool :=
  decide (0 < q) && decide (q ≤ p) && decide (p ≤ 7 * q) &&
    box.all (fun ab => gapOK p ab.1 ab.2 (q * 2 ^ e))

/-- Some candidate instant (`1` or an exit edge `(8j+1)·2^e/a`) is clear for the whole box. -/
def leafOK (e : ℕ) (box : List (ℕ × ℕ)) : Bool :=
  leafAt 1 1 e box ||
    box.any (fun ab => (List.range 16).any (fun j => leafAt ((8 * j + 1) * 2 ^ e) ab.1 e box))

/-- Index of the first widest face. -/
def widestAux : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ
  | [], _, bi, _ => bi
  | ab :: t, i, bi, bw =>
      if bw < ab.2 - ab.1 then widestAux t (i + 1) i (ab.2 - ab.1) else widestAux t (i + 1) bi bw

def widest (box : List (ℕ × ℕ)) : ℕ := widestAux box 0 0 0

/-- Rescale every face to `2^(e+1)`. -/
def dbl : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | ab :: t => (2 * ab.1, 2 * ab.2) :: dbl t

/-- Lower half at index `k`, everything rescaled to `2^(e+1)`. -/
def splitL : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | 0, ab :: t => (2 * ab.1, ab.1 + ab.2) :: dbl t
  | k + 1, ab :: t => (2 * ab.1, 2 * ab.2) :: splitL k t

/-- Upper half at index `k`, everything rescaled to `2^(e+1)`. -/
def splitR : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | 0, ab :: t => (ab.1 + ab.2, 2 * ab.2) :: dbl t
  | k + 1, ab :: t => (2 * ab.1, 2 * ab.2) :: splitR k t

/-- Leaf, or bisect the widest face and check both halves. -/
def check : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | 0, e, box => leafOK e box
  | f + 1, e, box =>
      leafOK e box ||
        (check f (e + 1) (splitL (widest box) box) && check f (e + 1) (splitR (widest box) box))

/-! ## Semantics -/

/-- The reading vector `g` lies in the box (scale `2^e`); the box has at least 7 faces. -/
-- STANDING: DEFINITION
def InBox (e : ℕ) (box : List (ℕ × ℕ)) (g : Fin 7 → ℝ) : Prop :=
  7 ≤ box.length ∧ ∀ i : Fin 7,
    ((box.getD i (0, 0)).1 : ℝ) / 2 ^ e ≤ g i ∧ g i ≤ ((box.getD i (0, 0)).2 : ℝ) / 2 ^ e

/-- `R` is a clear instant in `[1,7]` for every reading. -/
-- STANDING: DEFINITION
def GoodR (g : Fin 7 → ℝ) (R : ℝ) : Prop :=
  1 ≤ R ∧ R ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (R / 8))

/-! ## Soundness -/

theorem gap_sound {p q e a b : ℕ} {x : ℝ} (hq : 0 < q)
    (h : gapOK p a b (q * 2 ^ e) = true)
    (hx1 : (a : ℝ) / 2 ^ e ≤ x) (hx2 : x ≤ (b : ℝ) / 2 ^ e) :
    ∃ j : ℤ, x * ((p : ℝ) / q) ∈ Set.Icc (((8 * j : ℤ) : ℝ) + 1) (((8 * j : ℤ) : ℝ) + 7) := by
  simp only [gapOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  set D := q * 2 ^ e with hD
  set J := (p * a - D) / (8 * D) with hJ
  have hle : J * (8 * D) ≤ p * a - D := Nat.div_mul_le_self (p * a - D) (8 * D)
  have h3 : (8 * J + 1) * D ≤ p * a := by
    calc (8 * J + 1) * D = J * (8 * D) + D := by ring
      _ ≤ (p * a - D) + D := Nat.add_le_add_right hle D
      _ = p * a := Nat.sub_add_cancel h1
  have hr3 : ((8 : ℝ) * J + 1) * ((q : ℝ) * 2 ^ e) ≤ (p : ℝ) * a := by
    have := (Nat.cast_le (α := ℝ)).mpr h3
    push_cast [hD] at this
    linarith
  have hr2 : (p : ℝ) * b ≤ ((8 : ℝ) * J + 7) * ((q : ℝ) * 2 ^ e) := by
    have := (Nat.cast_le (α := ℝ)).mpr h2
    push_cast [hD] at this
    linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have h2e : (0 : ℝ) < 2 ^ e := by positivity
  have hpq : (0 : ℝ) ≤ (p : ℝ) / q := by positivity
  refine ⟨J, ?_, ?_⟩
  · have key : ((8 : ℝ) * J + 1) ≤ (a : ℝ) / 2 ^ e * ((p : ℝ) / q) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      nlinarith [hr3]
    have hmono : (a : ℝ) / 2 ^ e * ((p : ℝ) / q) ≤ x * ((p : ℝ) / q) :=
      mul_le_mul_of_nonneg_right hx1 hpq
    push_cast
    linarith
  · have key : (b : ℝ) / 2 ^ e * ((p : ℝ) / q) ≤ ((8 : ℝ) * J + 7) := by
      rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
      nlinarith [hr2]
    have hmono : x * ((p : ℝ) / q) ≤ (b : ℝ) / 2 ^ e * ((p : ℝ) / q) :=
      mul_le_mul_of_nonneg_right hx2 hpq
    push_cast
    linarith

#print axioms gap_sound

theorem leafAt_sound {p q e : ℕ} {box : List (ℕ × ℕ)} {g : Fin 7 → ℝ}
    (h : leafAt p q e box = true) (hg : InBox e box g) : GoodR g ((p : ℝ) / q) := by
  simp only [leafAt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hq, hqp⟩, hp7⟩, hall⟩ := h
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hqpos]; simpa using (Nat.cast_le (α := ℝ)).mpr hqp
  · rw [div_le_iff₀ hqpos]
    have := (Nat.cast_le (α := ℝ)).mpr hp7
    push_cast at this; linarith
  · intro i
    obtain ⟨hlen, hin⟩ := hg
    have hi : (i : ℕ) < box.length := lt_of_lt_of_le i.isLt hlen
    have hmem : box.getD i (0, 0) ∈ box := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    have hgap := hall _ hmem
    obtain ⟨j, hj⟩ := gap_sound hq hgap (hin i).1 (hin i).2
    exact (clearAt_R_iff (g i) ((p : ℝ) / q)).mpr ⟨j, hj⟩

#print axioms leafAt_sound

theorem leafOK_sound {e : ℕ} {box : List (ℕ × ℕ)} {g : Fin 7 → ℝ}
    (h : leafOK e box = true) (hg : InBox e box g) : ∃ R, GoodR g R := by
  simp only [leafOK, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨ab, -, j, -, hj⟩
  · exact ⟨_, leafAt_sound h hg⟩
  · exact ⟨_, leafAt_sound hj hg⟩

#print axioms leafOK_sound

theorem dbl_length (t : List (ℕ × ℕ)) : (dbl t).length = t.length := by
  induction t with
  | nil => rfl
  | cons ab t ih => simp [dbl, ih]

theorem splitL_length (k : ℕ) (t : List (ℕ × ℕ)) : (splitL k t).length = t.length := by
  induction t generalizing k with
  | nil => cases k <;> rfl
  | cons ab t ih => cases k <;> simp [splitL, ih, dbl_length]

theorem splitR_length (k : ℕ) (t : List (ℕ × ℕ)) : (splitR k t).length = t.length := by
  induction t generalizing k with
  | nil => cases k <;> rfl
  | cons ab t ih => cases k <;> simp [splitR, ih, dbl_length]

theorem dbl_getD (t : List (ℕ × ℕ)) (i : ℕ) :
    (dbl t).getD i (0, 0) = (2 * (t.getD i (0, 0)).1, 2 * (t.getD i (0, 0)).2) := by
  induction t generalizing i with
  | nil => simp [dbl]
  | cons ab t ih =>
    cases i with
    | zero => simp only [dbl, List.getD_cons_zero]
    | succ i => simp only [dbl, List.getD_cons_succ]; exact ih i

theorem splitL_getD (k : ℕ) (t : List (ℕ × ℕ)) (i : ℕ) :
    (splitL k t).getD i (0, 0) =
      if i = k then (2 * (t.getD i (0, 0)).1, (t.getD i (0, 0)).1 + (t.getD i (0, 0)).2)
      else (2 * (t.getD i (0, 0)).1, 2 * (t.getD i (0, 0)).2) := by
  induction t generalizing k i with
  | nil => cases k <;> simp [splitL]
  | cons ab t ih =>
    cases k with
    | zero =>
      cases i with
      | zero => simp only [splitL, List.getD_cons_zero, if_true]
      | succ i =>
        simp only [splitL, List.getD_cons_succ, dbl_getD]
        rw [if_neg (Nat.succ_ne_zero i)]
    | succ k =>
      cases i with
      | zero => simp only [splitL, List.getD_cons_zero]; rw [if_neg (Nat.zero_ne_add_one k)]
      | succ i =>
        simp only [splitL, List.getD_cons_succ]
        rw [ih k i]
        by_cases h : i = k
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]

theorem splitR_getD (k : ℕ) (t : List (ℕ × ℕ)) (i : ℕ) :
    (splitR k t).getD i (0, 0) =
      if i = k then ((t.getD i (0, 0)).1 + (t.getD i (0, 0)).2, 2 * (t.getD i (0, 0)).2)
      else (2 * (t.getD i (0, 0)).1, 2 * (t.getD i (0, 0)).2) := by
  induction t generalizing k i with
  | nil => cases k <;> simp [splitR]
  | cons ab t ih =>
    cases k with
    | zero =>
      cases i with
      | zero => simp only [splitR, List.getD_cons_zero, if_true]
      | succ i =>
        simp only [splitR, List.getD_cons_succ, dbl_getD]
        rw [if_neg (Nat.succ_ne_zero i)]
    | succ k =>
      cases i with
      | zero => simp only [splitR, List.getD_cons_zero]; rw [if_neg (Nat.zero_ne_add_one k)]
      | succ i =>
        simp only [splitR, List.getD_cons_succ]
        rw [ih k i]
        by_cases h : i = k
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]

theorem twice_div (a e : ℕ) : ((2 * a : ℕ) : ℝ) / 2 ^ (e + 1) = (a : ℝ) / 2 ^ e := by
  push_cast; rw [pow_succ]; field_simp

/-- Bisection covers the box: a reading vector lies in the lower or the upper half
[PROVISIONAL: covering -- supports `check_sound`]. -/
theorem inBox_split {e : ℕ} {box : List (ℕ × ℕ)} {g : Fin 7 → ℝ} (k : ℕ) (hg : InBox e box g) :
    InBox (e + 1) (splitL k box) g ∨ InBox (e + 1) (splitR k box) g := by
  obtain ⟨hlen, hin⟩ := hg
  by_cases hk : k < 7
  · set kk : Fin 7 := ⟨k, hk⟩
    set a := (box.getD k (0, 0)).1
    set b := (box.getD k (0, 0)).2
    by_cases hx : g kk ≤ ((a + b : ℕ) : ℝ) / 2 ^ (e + 1)
    · left
      refine ⟨by rw [splitL_length]; exact hlen, fun i => ?_⟩
      rw [splitL_getD]
      by_cases hik : (i : ℕ) = k
      · have hii : i = kk := Fin.ext hik
        subst hii
        simp only [if_pos hik]
        refine ⟨?_, ?_⟩
        · rw [twice_div]; exact (hin kk).1
        · simpa [a, b] using hx
      · simp only [if_neg hik, twice_div]; exact hin i
    · right
      push Not at hx
      refine ⟨by rw [splitR_length]; exact hlen, fun i => ?_⟩
      rw [splitR_getD]
      by_cases hik : (i : ℕ) = k
      · have hii : i = kk := Fin.ext hik
        subst hii
        simp only [if_pos hik]
        refine ⟨?_, ?_⟩
        · simpa [a, b] using hx.le
        · rw [twice_div]; exact (hin kk).2
      · simp only [if_neg hik, twice_div]; exact hin i
  · left
    refine ⟨by rw [splitL_length]; exact hlen, fun i => ?_⟩
    rw [splitL_getD]
    have hik : (i : ℕ) ≠ k := by omega
    simp only [if_neg hik, twice_div]; exact hin i

#print axioms inBox_split

/-- **Soundness of the self-splitting checker.** -/
theorem check_sound (f e : ℕ) (box : List (ℕ × ℕ)) (h : check f e box = true)
    (g : Fin 7 → ℝ) (hg : InBox e box g) : ∃ R, GoodR g R := by
  induction f generalizing e box with
  | zero => exact leafOK_sound h hg
  | succ f ih =>
    simp only [check, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hL, hR⟩
    · exact leafOK_sound h hg
    · rcases inBox_split (widest box) hg with hg' | hg'
      · exact ih (e + 1) _ hL hg'
      · exact ih (e + 1) _ hR hg'

#print axioms check_sound

/-- A common clear instant in `[1,7]` is `NoCarve`. -/
theorem noCarve_of_goodR {g : Fin 7 → ℝ} {R : ℝ} (h : GoodR g R) : Fresh.Certs.NoCarve g := by
  obtain ⟨h1, h7, hc⟩ := h
  refine (Fresh.FilterAssembly.notCarve_witness g).mpr ⟨R / 8, by linarith, by linarith, ?_⟩
  intro d hd
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hd
  exact hc i

#print axioms noCarve_of_goodR

end Fresh.M4SplitCheck
