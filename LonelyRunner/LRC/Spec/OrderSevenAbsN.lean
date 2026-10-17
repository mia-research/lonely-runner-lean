import LonelyRunner.LRC.Spec.OrderSevenGridN

/-!
# Order seven at every level: the depth-two fold with multipliers `c ≤ 6`

Instants `k = c (1 + 7^(a-2) s)`.  A runner `x` (a residue mod `7^a`) enters only through its top two
digits `T = x / 7^(a-2)`, its remainder vector `g = (c (x mod 7^(a-2)) / 7^(a-2))_{c ≤ 6}` and its residue
`x mod 49` (`gridOK_fold`).  The remainder vector is one of twelve (`rvec_mem`).  So "five units share an
instant" at every level `a ≥ 3` follows from one finite statement about these states (`AbsU5`), and the
mixed shapes from two more (`AbsP1`, `AbsP2`).

The three finite statements are named `Prop`s here, **not proved in Lean**: each was checked by an exact
exhaustive search (`experiments/n7_native/cascade/seven_abstract_*`, log E24/E25).  Every theorem below that
uses one takes it as a hypothesis.  No `sorry`, no `native_decide`.
-/

namespace LRC.O7Abs
open LRC.O7Grid

/-- The twelve remainder vectors `(⌊c y⌋)_{c = 1..6}`, `y ∈ [0, 1)`. -/
def fvecs : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [0, 0, 0, 1, 1, 1], [0, 0, 1, 1, 1, 2],
   [0, 0, 1, 1, 2, 2], [0, 1, 1, 2, 2, 3], [0, 1, 1, 2, 3, 3], [0, 1, 2, 2, 3, 4], [0, 1, 2, 3, 3, 4],
   [0, 1, 2, 3, 4, 4], [0, 1, 2, 3, 4, 5]]

/-- Abstract band test: a runner with top digits `T`, remainder vector `g`, residue `ρ`, at instant `(c, s)`. -/
def ok (T : ℕ) (g : List ℕ) (ρ c s : ℕ) : Prop :=
  7 ≤ (c * T + g.getD (c - 1) 0 + s * c * ρ) % 49 ∧ (c * T + g.getD (c - 1) 0 + s * c * ρ) % 49 ≤ 41

/-- A unit state. -/
def UnitSt (T : ℕ) (g : List ℕ) (ρ : ℕ) : Prop := T < 49 ∧ g ∈ fvecs ∧ ρ < 49 ∧ ρ % 7 ≠ 0

/-- **Finite statement U5.**  Runner `1` (state `(0, 0, 1)`) and any four unit states share an instant. -/
def AbsU5 : Prop :=
  ∀ T2 g2 ρ2 T3 g3 ρ3 T4 g4 ρ4 T5 g5 ρ5, UnitSt T2 g2 ρ2 → UnitSt T3 g3 ρ3 → UnitSt T4 g4 ρ4 →
    UnitSt T5 g5 ρ5 → ∃ c s, 1 ≤ c ∧ c ≤ 6 ∧ ok 0 [0, 0, 0, 0, 0, 0] 1 c s ∧ ok T2 g2 ρ2 c s ∧
      ok T3 g3 ρ3 c s ∧ ok T4 g4 ρ4 c s ∧ ok T5 g5 ρ5 c s

/-- **Finite statement P1.**  Runner `1`, three unit states and one state of residue `7·unit` share an instant. -/
def AbsP1 : Prop :=
  ∀ T2 g2 ρ2 T3 g3 ρ3 T4 g4 ρ4 Tz gz ρz, UnitSt T2 g2 ρ2 → UnitSt T3 g3 ρ3 → UnitSt T4 g4 ρ4 →
    Tz < 49 → gz ∈ fvecs → ρz < 49 → ρz % 7 = 0 → ρz ≠ 0 →
    ∃ c s, 1 ≤ c ∧ c ≤ 6 ∧ ok 0 [0, 0, 0, 0, 0, 0] 1 c s ∧ ok T2 g2 ρ2 c s ∧ ok T3 g3 ρ3 c s ∧
      ok T4 g4 ρ4 c s ∧ ok Tz gz ρz c s

/-- **Finite statement P2.**  A runner with top digits `0` and any three unit states share an instant with
`c ≤ 5`. -/
def AbsP2 : Prop :=
  ∀ g1 ρ1 T2 g2 ρ2 T3 g3 ρ3 T4 g4 ρ4, UnitSt 0 g1 ρ1 → UnitSt T2 g2 ρ2 → UnitSt T3 g3 ρ3 →
    UnitSt T4 g4 ρ4 → ∃ c s, 1 ≤ c ∧ c ≤ 5 ∧ ok 0 g1 ρ1 c s ∧ ok T2 g2 ρ2 c s ∧ ok T3 g3 ρ3 c s ∧
      ok T4 g4 ρ4 c s

/-! ## The instant formula -/

theorem fold_core {N x c s : ℕ} (hN : 0 < N) (hx : x < 49 * N) (hr : c * (x % N) % N ≠ 0) :
    (7 * N ≤ x * (c * (1 + N * s)) % (49 * N) ∧ x * (c * (1 + N * s)) % (49 * N) ≤ 42 * N) ↔
      (7 ≤ (c * (x / N) + c * (x % N) / N + s * c * (x % 49)) % 49 ∧
        (c * (x / N) + c * (x % N) / N + s * c * (x % 49)) % 49 ≤ 41) := by
  set T := x / N
  set r := x % N
  set f := c * r / N
  set r' := c * r % N
  have hx' : x = N * T + r := (Nat.div_add_mod x N).symm
  have hcr : c * r = N * f + r' := (Nat.div_add_mod _ N).symm
  set Q0 := c * T + f + s * c * x
  have e : x * (c * (1 + N * s)) = N * Q0 + r' := by
    have h1 : c * x = N * (c * T) + (N * f + r') := by
      rw [← hcr]; conv_lhs => rw [hx']
      ring
    calc x * (c * (1 + N * s)) = c * x + N * (s * c * x) := by ring
      _ = N * Q0 + r' := by rw [h1]; ring
  have hr'lt : r' < N := Nat.mod_lt _ hN
  have hq := Nat.mod_lt Q0 (by norm_num : 49 > 0)
  have hlt : N * (Q0 % 49) + r' < 49 * N := by nlinarith
  have hsplit : N * Q0 + r' = (N * (Q0 % 49) + r') + 49 * N * (Q0 / 49) := by
    have := Nat.mod_add_div Q0 49
    calc N * Q0 + r' = N * (Q0 % 49 + 49 * (Q0 / 49)) + r' := by rw [this]
      _ = _ := by ring
  have hmod : x * (c * (1 + N * s)) % (49 * N) = N * (Q0 % 49) + r' := by
    rw [e, hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hQ : Q0 % 49 = (c * T + f + s * c * (x % 49)) % 49 := by
    simp only [Q0, Nat.add_mod (c * T + f), Nat.mul_mod (s * c) x, Nat.mul_mod (s * c) (x % 49), Nat.mod_mod]
  rw [hmod, ← hQ]
  have hr'pos : 0 < r' := Nat.pos_of_ne_zero hr
  set q := Q0 % 49
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · by_contra hc; push Not at hc
      have : N * q ≤ N * 6 := Nat.mul_le_mul_left N (by omega)
      omega
    · by_contra hc; push Not at hc
      have : N * 42 ≤ N * q := Nat.mul_le_mul_left N (by omega)
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : N * 7 ≤ N * q := Nat.mul_le_mul_left N h1
      omega
    · have : N * q ≤ N * 41 := Nat.mul_le_mul_left N h2
      omega

/-- The remainder vector of `x` at depth `N`. -/
def rvec (x N : ℕ) : List ℕ := (List.range 6).map fun i => (i + 1) * (x % N) / N

theorem rvec_getD {x N c : ℕ} (h1 : 1 ≤ c) (h6 : c ≤ 6) : (rvec x N).getD (c - 1) 0 = c * (x % N) / N := by
  unfold rvec
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [show c - 1 + 1 = c by omega]

theorem pow_split {a : ℕ} (ha : 2 ≤ a) : (7 : ℕ) ^ a = 49 * 7 ^ (a - 2) ∧ (7 : ℕ) ^ (a - 1) = 7 * 7 ^ (a - 2) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  simp only [Nat.add_sub_cancel, show b + 2 - 1 = b + 1 by omega]
  constructor <;> ring

/-- **The instant formula.**  At level `a ≥ 2`, a residue `x < 7^a` is in band at `c (1 + 7^(a-2) s)` iff its
abstract state passes `ok` (given that `c (x mod 7^(a-2))` is not a multiple of `7^(a-2)`). -/
theorem gridOK_fold {a x c s : ℕ} (ha : 2 ≤ a) (hx : x < 7 ^ a) (h1 : 1 ≤ c) (h6 : c ≤ 6)
    (hr : c * (x % 7 ^ (a - 2)) % 7 ^ (a - 2) ≠ 0) :
    GridOK a (c * (1 + 7 ^ (a - 2) * s)) x ↔ ok (x / 7 ^ (a - 2)) (rvec x (7 ^ (a - 2))) (x % 49) c s := by
  obtain ⟨e1, e2⟩ := pow_split ha
  unfold GridOK ok
  rw [rvec_getD h1 h6, e1, e2, show 6 * (7 * 7 ^ (a - 2)) = 42 * 7 ^ (a - 2) by ring]
  rw [e1] at hx
  exact fold_core (by positivity) hx hr

/-! ## The twelve remainder vectors -/

/-- Constraint satisfied by every floor vector: `g_u + g_v ≤ g_{u+v} ≤ g_u + g_v + 1`. -/
def fvCond (g2 g3 g4 g5 g6 : ℕ) : Bool :=
  decide (g3 ≤ g2 + 1 ∧ g2 ≤ g3 ∧ g4 ≤ g3 + 1 ∧ g3 ≤ g4 ∧ 2 * g2 ≤ g4 ∧ g4 ≤ 2 * g2 + 1 ∧ g5 ≤ g4 + 1 ∧ g4 ≤ g5 ∧
    g2 + g3 ≤ g5 ∧ g5 ≤ g2 + g3 + 1 ∧ g6 ≤ g5 + 1 ∧ g5 ≤ g6 ∧ g2 + g4 ≤ g6 ∧ g6 ≤ g2 + g4 + 1 ∧ 2 * g3 ≤ g6 ∧
    g6 ≤ 2 * g3 + 1)

def fvCheck : Bool :=
  (List.range 2).all fun g2 => (List.range 3).all fun g3 => (List.range 4).all fun g4 =>
    (List.range 5).all fun g5 => (List.range 6).all fun g6 =>
      !(fvCond g2 g3 g4 g5 g6) || decide ([0, g2, g3, g4, g5, g6] ∈ fvecs)

theorem fvCheck_ok : fvCheck = true := by decide

theorem fvec_table {g2 g3 g4 g5 g6 : ℕ} (h2 : g2 < 2) (h3 : g3 < 3) (h4 : g4 < 4) (h5 : g5 < 5) (h6 : g6 < 6)
    (hc : fvCond g2 g3 g4 g5 g6 = true) : [0, g2, g3, g4, g5, g6] ∈ fvecs := by
  have h := fvCheck_ok
  simp only [fvCheck, List.all_eq_true, List.mem_range] at h
  have := h g2 h2 g3 h3 g4 h4 g5 h5 g6 h6
  simpa [hc] using this

theorem div_add_le {u v N : ℕ} (hN : 0 < N) : (u + v) / N ≤ u / N + v / N + 1 := by
  rw [Nat.add_div hN]; split_ifs <;> omega

theorem rvec_mem {x N : ℕ} (hN : 0 < N) : rvec x N ∈ fvecs := by
  set r := x % N
  have hr : r < N := Nat.mod_lt _ hN
  have g1 : 1 * r / N = 0 := by rw [one_mul]; exact Nat.div_eq_of_lt hr
  have lt : ∀ c, 0 < c → c * r / N < c := fun c hc =>
    (Nat.div_lt_iff_lt_mul hN).mpr (by nlinarith)
  have sup : ∀ u v, u * r / N + v * r / N ≤ (u + v) * r / N := fun u v => by
    rw [add_mul]; exact Nat.add_div_le_add_div _ _ _
  have sub : ∀ u v, (u + v) * r / N ≤ u * r / N + v * r / N + 1 := fun u v => by
    rw [add_mul]; exact div_add_le hN
  have hv : rvec x N = [0, 2 * r / N, 3 * r / N, 4 * r / N, 5 * r / N, 6 * r / N] := by
    simp [rvec, List.range_succ, r]
  rw [hv]
  have s11 := sub 1 1; have p11 := sup 1 1
  have s12 := sub 1 2; have p12 := sup 1 2
  have s13 := sub 1 3; have p13 := sup 1 3
  have s22 := sub 2 2; have p22 := sup 2 2
  have s14 := sub 1 4; have p14 := sup 1 4
  have s23 := sub 2 3; have p23 := sup 2 3
  have s15 := sub 1 5; have p15 := sup 1 5
  have s24 := sub 2 4; have p24 := sup 2 4
  have s33 := sub 3 3; have p33 := sup 3 3
  norm_num [g1] at s11 p11 s12 p12 s13 p13 s22 p22 s14 p14 s23 p23 s15 p15 s24 p24 s33 p33
  have l2 := lt 2 (by norm_num); have l3 := lt 3 (by norm_num); have l4 := lt 4 (by norm_num)
  have l5 := lt 5 (by norm_num); have l6 := lt 6 (by norm_num)
  refine fvec_table l2 l3 l4 l5 l6 ?_
  have g1' : r / N = 0 := Nat.div_eq_of_lt hr
  simp only [fvCond, decide_eq_true_eq]
  omega

/-! ## Consequences -/

theorem inv_pow7 {u n : ℕ} (hu : ¬ 7 ∣ u) (hn : 1 ≤ n) : ∃ b, ¬ 7 ∣ b ∧ b * u % 7 ^ n = 1 := by
  have hc : Nat.Coprime u 7 := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hu)
  obtain ⟨b, -, hb⟩ := Nat.exists_mul_mod_eq_one_of_coprime (Nat.Coprime.pow_right n hc)
    (Nat.one_lt_pow (by omega) (by norm_num))
  refine ⟨b, fun h7 => ?_, by rw [mul_comm]; exact hb⟩
  have : 7 ∣ u * b % 7 ^ n := (Nat.dvd_mod_iff (dvd_pow_self 7 (by omega))).mpr (dvd_mul_of_dvd_right h7 _)
  rw [hb] at this; norm_num at this

theorem not7_mod {x N : ℕ} (hN : 7 ∣ N) : 7 ∣ x % N ↔ 7 ∣ x := Nat.dvd_mod_iff hN

theorem noncop {x N c : ℕ} (hN : 7 ∣ N) (hx : ¬ 7 ∣ x) (h1 : 1 ≤ c) (h6 : c ≤ 6) : c * (x % N) % N ≠ 0 := by
  intro h0
  have h7 : 7 ∣ c * (x % N) := dvd_trans hN (Nat.dvd_of_mod_eq_zero h0)
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h7 with h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · exact hx ((not7_mod hN).mp h)

theorem unit_inst {b c N s : ℕ} (hb : ¬ 7 ∣ b) (h1 : 1 ≤ c) (h6 : c ≤ 6) (hN : 7 ∣ N) :
    ¬ 7 ∣ b * (c * (1 + N * s)) := by
  intro h
  have p7 : Nat.Prime 7 := by norm_num
  rcases p7.dvd_mul.mp h with h | h
  · exact hb h
  rcases p7.dvd_mul.mp h with h | h
  · have := Nat.le_of_dvd (by omega) h; omega
  · obtain ⟨M, rfl⟩ := hN
    rw [show 1 + 7 * M * s = 7 * (M * s) + 1 by ring] at h
    have := (Nat.dvd_add_right (dvd_mul_right 7 (M * s))).mp h
    norm_num at this

theorem unit_state {x a : ℕ} (ha : 3 ≤ a) (hx : x < 7 ^ a) (hx7 : ¬ 7 ∣ x) :
    UnitSt (x / 7 ^ (a - 2)) (rvec x (7 ^ (a - 2))) (x % 49) := by
  obtain ⟨e1, -⟩ := pow_split (show 2 ≤ a by omega)
  refine ⟨(Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [e1] at hx; linarith), rvec_mem (by positivity),
    Nat.mod_lt _ (by norm_num), ?_⟩
  rw [Nat.mod_mod_of_dvd x (by norm_num : 7 ∣ 49)]
  exact fun h => hx7 (Nat.dvd_of_mod_eq_zero h)

theorem one_state {N : ℕ} (hN : 7 ≤ N) : 1 / N = 0 ∧ rvec 1 N = [0, 0, 0, 0, 0, 0] ∧ 1 % 49 = 1 := by
  have h1 : 1 % N = 1 := Nat.mod_eq_of_lt (by omega)
  refine ⟨Nat.div_eq_of_lt (by omega), ?_, rfl⟩
  unfold rvec; rw [h1]
  have z : ∀ m, m ≤ 6 → m / N = 0 := fun m hm => Nat.div_eq_of_lt (by omega)
  simp [List.range_succ, z]

/-- The other elements of a finset, as four slots (padded with `u1`). -/
theorem four_slots {U : Finset ℕ} {u1 : ℕ} (hu1 : u1 ∈ U) (hc : U.card ≤ 5) :
    ∃ w : ℕ → ℕ, (∀ i, w i ∈ U) ∧ ∀ u ∈ U, u = u1 ∨ u = w 0 ∨ u = w 1 ∨ u = w 2 ∨ u = w 3 := by
  set l := (U.erase u1).toList
  have hl : l.length ≤ 4 := by
    rw [Finset.length_toList, Finset.card_erase_of_mem hu1]; omega
  refine ⟨fun i => l.getD i u1, fun i => ?_, fun u hu => ?_⟩
  · show l.getD i u1 ∈ U
    by_cases hi : i < l.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact Finset.mem_of_mem_erase (Finset.mem_toList.mp (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (by omega)]; exact hu1
  · by_cases h : u = u1
    · exact Or.inl h
    · have hm : u ∈ l := Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h, hu⟩)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
      right
      have e : l.getD i u1 = l[i] := List.getD_eq_getElem _ _ hi
      have hi4 : i < 4 := by omega
      interval_cases i <;> simp_all

theorem three_slots {U : Finset ℕ} {u1 : ℕ} (hu1 : u1 ∈ U) (hc : U.card ≤ 4) :
    ∃ w : ℕ → ℕ, (∀ i, w i ∈ U) ∧ ∀ u ∈ U, u = u1 ∨ u = w 0 ∨ u = w 1 ∨ u = w 2 := by
  obtain ⟨w, hw, hcov⟩ := four_slots hu1 (by omega)
  set l := (U.erase u1).toList
  have hl : l.length ≤ 3 := by
    rw [Finset.length_toList, Finset.card_erase_of_mem hu1]; omega
  refine ⟨fun i => l.getD i u1, fun i => ?_, fun u hu => ?_⟩
  · show l.getD i u1 ∈ U
    by_cases hi : i < l.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact Finset.mem_of_mem_erase (Finset.mem_toList.mp (List.getElem_mem hi))
    · rw [List.getD_eq_default _ _ (by omega)]; exact hu1
  · by_cases h : u = u1
    · exact Or.inl h
    · have hm : u ∈ l := Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨h, hu⟩)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hm
      right
      have e : l.getD i u1 = l[i] := List.getD_eq_getElem _ _ hi
      have hi4 : i < 3 := by omega
      interval_cases i <;> simp_all

/-- A residue whose scaled abstract state passes is in band at the scaled instant. -/
theorem band_of_ok {a b u c s : ℕ} (ha : 3 ≤ a) (h1 : 1 ≤ c) (h6 : c ≤ 6)
    (hr : c * (b * u % 7 ^ a % 7 ^ (a - 2)) % 7 ^ (a - 2) ≠ 0)
    (hok : ok (b * u % 7 ^ a / 7 ^ (a - 2)) (rvec (b * u % 7 ^ a) (7 ^ (a - 2))) (b * u % 7 ^ a % 49) c s) :
    GridOK a (b * (c * (1 + 7 ^ (a - 2) * s))) u := by
  rw [gridOK_scale, gridOK_mod]
  exact (gridOK_fold (by omega) (Nat.mod_lt _ (by positivity)) h1 h6 hr).mpr hok

theorem unit_res {a b u : ℕ} (ha : 1 ≤ a) (hb : ¬ 7 ∣ b) (hu : ¬ 7 ∣ u) : ¬ 7 ∣ b * u % 7 ^ a := by
  rw [not7_mod (dvd_pow_self 7 (by omega))]
  exact fun h => ((Nat.Prime.dvd_mul (by norm_num)).mp h).elim hb hu

/-- **Five units at every level `a ≥ 3`** (from `AbsU5`). -/
theorem units_all (h : AbsU5) {a : ℕ} (ha : 3 ≤ a) {U : Finset ℕ} (hc : U.card ≤ 5) (hu : ∀ u ∈ U, ¬ 7 ∣ u) :
    ∃ k, ¬ 7 ∣ k ∧ ∀ u ∈ U, GridOK a k u := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨u1, hu1⟩
  · exact ⟨1, by norm_num, by simp⟩
  obtain ⟨b, hb7, hb⟩ := inv_pow7 (hu u1 hu1) (show 1 ≤ a by omega)
  have hN7 : 7 ∣ 7 ^ (a - 2) := dvd_pow_self 7 (by omega)
  have hN : 7 ≤ 7 ^ (a - 2) := by
    calc 7 = 7 ^ 1 := by norm_num
      _ ≤ 7 ^ (a - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hst : ∀ u ∈ U, UnitSt (b * u % 7 ^ a / 7 ^ (a - 2)) (rvec (b * u % 7 ^ a) (7 ^ (a - 2))) (b * u % 7 ^ a % 49) :=
    fun u hu' => unit_state ha (Nat.mod_lt _ (by positivity)) (unit_res (by omega) hb7 (hu u hu'))
  obtain ⟨w, hw, hcov⟩ := four_slots hu1 hc
  obtain ⟨c, s, h1, h6, k1, k2, k3, k4, k5⟩ :=
    h _ _ _ _ _ _ _ _ _ _ _ _ (hst _ (hw 0)) (hst _ (hw 1)) (hst _ (hw 2)) (hst _ (hw 3))
  have hr : ∀ u ∈ U, c * (b * u % 7 ^ a % 7 ^ (a - 2)) % 7 ^ (a - 2) ≠ 0 :=
    fun u hu' => noncop hN7 (unit_res (by omega) hb7 (hu u hu')) h1 h6
  refine ⟨b * (c * (1 + 7 ^ (a - 2) * s)), unit_inst hb7 h1 h6 hN7, fun u hu' => ?_⟩
  rcases hcov u hu' with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨e1, e2, e3⟩ := one_state hN
    refine band_of_ok ha h1 h6 (hr _ hu') ?_
    rw [hb, e1, e2, e3]; exact k1
  · exact band_of_ok ha h1 h6 (hr _ hu') k2
  · exact band_of_ok ha h1 h6 (hr _ hu') k3
  · exact band_of_ok ha h1 h6 (hr _ hu') k4
  · exact band_of_ok ha h1 h6 (hr _ hu') k5

theorem gridOK_succ_seven' {a : ℕ} (ha : 1 ≤ a) (k d : ℕ) : GridOK (a + 1) k (7 * d) ↔ GridOK a k d := by
  unfold GridOK
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have e : 7 * d * k % 7 ^ (b + 1 + 1) = 7 * (d * k % 7 ^ (b + 1)) := by
    rw [show 7 * d * k = 7 * (d * k) by ring, pow_succ' 7 (b + 1), Nat.mul_mod_mul_left]
  rw [e]
  generalize d * k % 7 ^ (b + 1) = x
  rw [pow_succ' 7 b]
  constructor <;> intro h <;> omega

/-- A runner of valuation `w` at level `L + w` is its cofactor at level `L`. -/
theorem gridOK_pow7 {L : ℕ} (hL : 1 ≤ L) (k m : ℕ) : ∀ w, GridOK (L + w) k (7 ^ w * m) ↔ GridOK L k m
  | 0 => by simp
  | w + 1 => by
    rw [show L + (w + 1) = (L + w) + 1 by ring, pow_succ, show 7 ^ w * 7 * m = 7 * (7 ^ w * m) by ring,
      gridOK_succ_seven' (by omega), gridOK_pow7 hL k m w]

/-- **Four units and one runner of valuation 1, every level `a ≥ 4`** (from `AbsP1`). -/
theorem units_val1_all (h : AbsP1) {a : ℕ} (ha : 4 ≤ a) {U : Finset ℕ} (hc : U.card ≤ 4) (hU : U.Nonempty)
    (hu : ∀ u ∈ U, ¬ 7 ∣ u) {m : ℕ} (hm : ¬ 7 ∣ m) :
    ∃ k, ¬ 7 ∣ k ∧ (∀ u ∈ U, GridOK a k u) ∧ GridOK a k (7 * m) := by
  obtain ⟨u1, hu1⟩ := hU
  obtain ⟨b, hb7, hb⟩ := inv_pow7 (hu u1 hu1) (show 1 ≤ a by omega)
  have hN7 : 7 ∣ 7 ^ (a - 2) := dvd_pow_self 7 (by omega)
  have hN : 7 ≤ 7 ^ (a - 2) := by
    calc 7 = 7 ^ 1 := by norm_num
      _ ≤ 7 ^ (a - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hst : ∀ u ∈ U, UnitSt (b * u % 7 ^ a / 7 ^ (a - 2)) (rvec (b * u % 7 ^ a) (7 ^ (a - 2))) (b * u % 7 ^ a % 49) :=
    fun u hu' => unit_state (by omega) (Nat.mod_lt _ (by positivity)) (unit_res (by omega) hb7 (hu u hu'))
  -- the valuation-1 runner
  set xz := b * (7 * m) % 7 ^ a with hxz
  have h49a : (49 : ℕ) ∣ 7 ^ a := by
    rw [show (49 : ℕ) = 7 ^ 2 by norm_num]; exact pow_dvd_pow 7 (by omega)
  have hz49 : xz % 49 = b * (7 * m) % 49 := Nat.mod_mod_of_dvd _ h49a
  have hbm : ¬ 7 ∣ b * m := fun h => ((Nat.Prime.dvd_mul (by norm_num)).mp h).elim hb7 hm
  have hz0 : xz % 49 ≠ 0 := by
    rw [hz49, show b * (7 * m) = 7 * (b * m) by ring, show (49 : ℕ) = 7 * 7 by norm_num, Nat.mul_mod_mul_left]
    intro h0
    have : b * m % 7 = 0 := by omega
    exact hbm (Nat.dvd_of_mod_eq_zero this)
  have hz7 : xz % 49 % 7 = 0 := by
    rw [hz49, Nat.mod_mod_of_dvd _ (by norm_num : 7 ∣ 49)]
    exact Nat.mod_eq_zero_of_dvd ⟨b * m, by ring⟩
  have hzr : ∀ c, 1 ≤ c → c ≤ 6 → c * (xz % 7 ^ (a - 2)) % 7 ^ (a - 2) ≠ 0 := by
    intro c h1 h6
    have hM7 : 7 ∣ 7 ^ (a - 3) := dvd_pow_self 7 (by omega)
    have eN : (7 : ℕ) ^ (a - 2) = 7 * 7 ^ (a - 3) := by
      rw [show a - 2 = (a - 3) + 1 by omega, pow_succ]; ring
    have hNa : 7 ^ (a - 2) ∣ 7 ^ a := pow_dvd_pow 7 (by omega)
    rw [hxz, Nat.mod_mod_of_dvd _ hNa, show b * (7 * m) = 7 * (b * m) by ring, eN, Nat.mul_mod_mul_left,
      show c * (7 * (b * m % 7 ^ (a - 3))) = 7 * (c * (b * m % 7 ^ (a - 3))) by ring, Nat.mul_mod_mul_left]
    exact fun h0 => noncop hM7 hbm h1 h6 (by omega)
  have hTz : xz / 7 ^ (a - 2) < 49 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    obtain ⟨e1, -⟩ := pow_split (show 2 ≤ a by omega)
    have := Nat.mod_lt (b * (7 * m)) (show 0 < 7 ^ a by positivity)
    rw [hxz]; rw [e1] at this ⊢; linarith
  obtain ⟨w, hw, hcov⟩ := three_slots hu1 hc
  obtain ⟨c, s, h1, h6, k1, k2, k3, k4, kz⟩ :=
    h _ _ _ _ _ _ _ _ _ (xz / 7 ^ (a - 2)) (rvec xz (7 ^ (a - 2))) (xz % 49) (hst _ (hw 0)) (hst _ (hw 1))
      (hst _ (hw 2)) hTz (rvec_mem (by positivity)) (Nat.mod_lt _ (by norm_num)) hz7 hz0
  have hr : ∀ u ∈ U, c * (b * u % 7 ^ a % 7 ^ (a - 2)) % 7 ^ (a - 2) ≠ 0 :=
    fun u hu' => noncop hN7 (unit_res (by omega) hb7 (hu u hu')) h1 h6
  refine ⟨b * (c * (1 + 7 ^ (a - 2) * s)), unit_inst hb7 h1 h6 hN7, fun u hu' => ?_,
    band_of_ok (by omega) h1 h6 (hzr c h1 h6) kz⟩
  rcases hcov u hu' with rfl | rfl | rfl | rfl
  · obtain ⟨e1, e2, e3⟩ := one_state hN
    refine band_of_ok (by omega) h1 h6 (hr _ hu') ?_
    rw [hb, e1, e2, e3]; exact k1
  · exact band_of_ok (by omega) h1 h6 (hr _ hu') k2
  · exact band_of_ok (by omega) h1 h6 (hr _ hu') k3
  · exact band_of_ok (by omega) h1 h6 (hr _ hu') k4

/-- The placement of a runner of valuation `w ≥ 2`: `c j0 / 7^L` is in band for every `c ≤ 5`. -/
def j0 (L : ℕ) : ℕ := if L = 2 then 8 else 8 * 7 ^ (L - 2) + 1

theorem j0_band {L c : ℕ} (hL : 2 ≤ L) (h1 : 1 ≤ c) (h5 : c ≤ 5) : GridOK L 1 (c * j0 L) := by
  unfold GridOK j0
  obtain ⟨e1, e2⟩ := pow_split hL
  rw [e1, e2]
  have hP : 1 ≤ 7 ^ (L - 2) := Nat.one_le_pow _ _ (by norm_num)
  split_ifs with h2
  · subst h2; interval_cases c <;> norm_num
  · have hP7 : 7 ≤ 7 ^ (L - 2) := by
      calc 7 = 7 ^ 1 := by norm_num
        _ ≤ 7 ^ (L - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize 7 ^ (L - 2) = P at hP hP7
    interval_cases c <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega

theorem j0_unit (L : ℕ) (hL : 2 ≤ L) : ¬ 7 ∣ j0 L := by
  unfold j0
  split_ifs
  · norm_num
  · rw [show 8 * 7 ^ (L - 2) + 1 = 7 * (8 * 7 ^ (L - 3)) + 1 by
      rw [show L - 2 = (L - 3) + 1 by omega, pow_succ]; ring]
    omega

theorem j0_lt (L : ℕ) (hL : 2 ≤ L) : j0 L < 7 ^ L := by
  unfold j0
  obtain ⟨e1, -⟩ := pow_split hL
  rw [e1]
  have hP : 1 ≤ 7 ^ (L - 2) := Nat.one_le_pow _ _ (by norm_num)
  split_ifs with h2
  · subst h2; norm_num
  · omega

/-- **Four units and one runner of valuation `w ≥ 2`, every level `a ≥ w + 2`** (from `AbsP2`). -/
theorem units_valw_all (h : AbsP2) {a w : ℕ} (hw2 : 2 ≤ w) (hwa : w + 2 ≤ a) {U : Finset ℕ} (hc : U.card ≤ 4)
    (hU : U.Nonempty) (hu : ∀ u ∈ U, ¬ 7 ∣ u) {m : ℕ} (hm : ¬ 7 ∣ m) :
    ∃ k, ¬ 7 ∣ k ∧ (∀ u ∈ U, GridOK a k u) ∧ GridOK a k (7 ^ w * m) := by
  obtain ⟨u1, hu1⟩ := hU
  set L := a - w with hLdef
  have hL : 2 ≤ L := by omega
  obtain ⟨b, hb7, hb⟩ := inv_pow7 (hu u1 hu1) (show 1 ≤ a by omega)
  obtain ⟨bm, hbm7, hbm⟩ := inv_pow7 hm (show 1 ≤ L by omega)
  set y0 := j0 L * u1 * bm % 7 ^ L with hy0
  have hy0u : ¬ 7 ∣ y0 := unit_res (by omega)
    (fun h => ((Nat.Prime.dvd_mul (by norm_num)).mp h).elim (j0_unit L hL) (hu u1 hu1)) hbm7
  have hLN : 7 ^ L ≤ 7 ^ (a - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hy0lt : y0 < 7 ^ (a - 2) := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hLN
  have hN7 : 7 ∣ 7 ^ (a - 2) := dvd_pow_self 7 (by omega)
  set B := b * y0 with hB
  have hB7 : ¬ 7 ∣ B := fun h => ((Nat.Prime.dvd_mul (by norm_num)).mp h).elim hb7 hy0u
  have hst : ∀ u ∈ U, UnitSt (B * u % 7 ^ a / 7 ^ (a - 2)) (rvec (B * u % 7 ^ a) (7 ^ (a - 2))) (B * u % 7 ^ a % 49) :=
    fun u hu' => unit_state (by omega) (Nat.mod_lt _ (by positivity)) (unit_res (by omega) hB7 (hu u hu'))
  have hx1 : B * u1 % 7 ^ a = y0 := by
    have hya : y0 < 7 ^ a := lt_of_lt_of_le hy0lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [hB, show b * y0 * u1 = y0 * (b * u1) by ring, Nat.mul_mod, hb, mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt hya]
  have h1st : UnitSt 0 (rvec y0 (7 ^ (a - 2))) (y0 % 49) := by
    have := hst u1 hu1
    rwa [hx1, Nat.div_eq_of_lt hy0lt] at this
  obtain ⟨wv, hwv, hcov⟩ := three_slots hu1 hc
  obtain ⟨c, s, h1, h5, k1, k2, k3, k4⟩ :=
    h _ _ _ _ _ _ _ _ _ _ _ h1st (hst _ (hwv 0)) (hst _ (hwv 1)) (hst _ (hwv 2))
  have h6 : c ≤ 6 := by omega
  have hr : ∀ u ∈ U, c * (B * u % 7 ^ a % 7 ^ (a - 2)) % 7 ^ (a - 2) ≠ 0 :=
    fun u hu' => noncop hN7 (unit_res (by omega) hB7 (hu u hu')) h1 h6
  refine ⟨B * (c * (1 + 7 ^ (a - 2) * s)), unit_inst hB7 h1 h6 hN7, fun u hu' => ?_, ?_⟩
  · rcases hcov u hu' with rfl | rfl | rfl | rfl
    · refine band_of_ok (by omega) h1 h6 (hr _ hu') ?_
      rw [hx1, Nat.div_eq_of_lt hy0lt]; exact k1
    · exact band_of_ok (by omega) h1 h6 (hr _ hu') k2
    · exact band_of_ok (by omega) h1 h6 (hr _ hu') k3
    · exact band_of_ok (by omega) h1 h6 (hr _ hu') k4
  · -- the runner of valuation w is its cofactor at level L, where it sits at c j0 / 7^L
    have hpw := gridOK_pow7 (L := L) (by omega) (B * (c * (1 + 7 ^ (a - 2) * s))) m w
    rw [show L + w = a by omega] at hpw
    rw [hpw]
    have hband := j0_band hL h1 h5
    unfold GridOK at hband ⊢
    have hLa : 7 ^ L ∣ 7 ^ (a - 2) := pow_dvd_pow 7 (by omega)
    have hdiv : 7 ^ L ∣ 7 ^ a := pow_dvd_pow 7 (by omega)
    have one_lt : 1 < 7 ^ L := Nat.one_lt_pow (by omega) (by norm_num)
    have one_lt' : 1 < 7 ^ a := Nat.one_lt_pow (by omega) (by norm_num)
    have eb : b * u1 ≡ 1 [MOD 7 ^ L] :=
      Nat.ModEq.of_dvd hdiv (by unfold Nat.ModEq; rw [hb, Nat.mod_eq_of_lt one_lt'])
    have em : bm * m ≡ 1 [MOD 7 ^ L] := by unfold Nat.ModEq; rw [hbm, Nat.mod_eq_of_lt one_lt]
    have ey : y0 ≡ j0 L * u1 * bm [MOD 7 ^ L] := Nat.mod_modEq _ _
    have eN : 7 ^ (a - 2) * s ≡ 0 [MOD 7 ^ L] := (Nat.modEq_zero_iff_dvd).mpr (dvd_mul_of_dvd_left hLa _)
    have e1 : m * (B * (c * (1 + 7 ^ (a - 2) * s))) ≡ m * (b * (j0 L * u1 * bm) * (c * (1 + 0))) [MOD 7 ^ L] :=
      Nat.ModEq.mul_left m (Nat.ModEq.mul (Nat.ModEq.mul_left b ey) (Nat.ModEq.mul_left c (Nat.ModEq.add_left 1 eN)))
    have e2 : m * (b * (j0 L * u1 * bm) * (c * (1 + 0))) = c * j0 L * ((b * u1) * (bm * m)) := by ring
    have e3 : c * j0 L * ((b * u1) * (bm * m)) ≡ c * j0 L * (1 * 1) [MOD 7 ^ L] :=
      Nat.ModEq.mul_left _ (Nat.ModEq.mul eb em)
    have hmod : m * (B * (c * (1 + 7 ^ (a - 2) * s))) % 7 ^ L = c * j0 L * 1 % 7 ^ L := by
      have := e1.trans (e2 ▸ e3)
      simpa using this
    rw [hmod]; exact hband

end LRC.O7Abs
