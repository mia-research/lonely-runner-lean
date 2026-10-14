import LonelyRunner.LRC.Spec.ParityMixedTwoTwoN

set_option linter.style.longLine false

/-!
# The displacement step M(1,3), and the quarter and eighth levels at one and three (order eight)

2026-10-07 (running log E402, E404).  Continues `ParityMixedTwoTwoN`.  The isolation is taken at the
grid shifts `j/4` (quarter level) or `k/8` (eighth level), displaced by an offset.  **M(1,3)** supplies
the offset: the one reading the shifts hold still (divided down) is clear at `1/8`, and the three
silenced readings (divided down to odd numbers) are clear at `1/4`, so each sits half a lap from its own
image.  The corollaries' instant is the displaced grid instant.

Source proof: the header of `experiments/nN/redo/m13_proof_v1.py` (THE REDUCTION, LEMMA QP, parts a, S,
T, Φ, P; LEMMA ROT of `mixed_lemma_check_v1.py`).  Odd numbers are written `b ≡ 1 (mod 4)`
(`exists_one_mod_four`), sorted `b_lo < b_mid < b_hi`, with `b_mid = b_lo + 4·d₁` and
`b_hi = b_lo + 4·d₂`.  For `4 ∣ c`, `c = 4m`.  The source's `G = gcd(a_mid − a_lo, a_hi − a_mid)` is
`gcd(d₁, d₂)`, and `x = d₁/G`, `N = d₂/G`.

* ROT: `rot_four_dvd`, `rot_one_mod_four` (reused from `ParityMixedTwoTwoN`).  THE REDUCTION, in the
  direction the proof uses: `quarter_of_half`, `finish_half`.
* Lemma QP: `qp_arc` (QP(i)) and `qp_third` (QP(ii)), each carrying the source's tag
  `[PROVISIONAL: counting tool]`.
* Part a: `part_a`.  Part S: `part_S`.  Part T: `part_T` (`t_point`).  Part Φ: `part_Phi` (`phi_k`).
  Part P: `part_P` (`p_choice`, which carries the source's tag `[PROVISIONAL: counting tool]`).
* `exists_one_three_sorted`: the case split a / S / T / Φ / P, exhaustive.  `exists_one_three_distinct`
  and `exists_mixed_one_three_triple` remove the sorting and the sign.
* `exists_mixed_one_three`: M(1,3).  Fewer numbers are padded (`exists_odd_triple_cover`, and `c = 1`
  when `A` is empty), so every case goes through the case split; order four is not used, as in the
  source.
* `lonely_eight_of_quarter_one_three`, `lonely_eight_of_eighth_one_three`: the two corollaries, through
  `lonely_eight_of_quarter_silent` and `lonely_eight_of_eighth_silent`.

Departures from the written proof (same statements, same constructions unless stated):
* THE REDUCTION is proved in the one direction the proof uses (points in one `H_w` give a solution);
  the source's converse and its CHECK 2 are not formalised.
* The modular inverses (`m''⁻¹ mod q` in T, `b'⁻¹ mod m'` in Φ, `x⁻¹ mod N` in P) are the Bézout
  coefficients `Nat.gcdA`, `Int.gcdA`, not reduced mod `q`, `m'`, `N` as in the source.  Another
  representative moves `p = b_lo·τ₀`, but each step uses only the congruence `k` satisfies and holds
  for every `p`, so the conclusion is unchanged.
* The Finset statement (at most one, at most three) is reduced to the source's statement (one `c`,
  three distinct odd `u`) by padding, not by `exists_mixed_le_three`.
* In Φ, `k = −⌊b'x/3⌋·A` is used also when `m' = 1` (the source sets `k = 0` there); both work.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.ParityDescent

open ConstructionN LRC.Descent

/-! ## THE REDUCTION: an aligned half circle and a quarter step -/

/-- **ROT into `H_{1/4}`.**  If `b ≡ 1 (mod 4)` and `b·τ₀ − M` lies in the aligned half circle
`H_w = [f/4, f/4 + 1/2]`, the quarter step `K = 1 − f` puts `b·(τ₀ + K/4)` in `[M + 1/4, M + 3/4]`. -/
theorem quarter_of_half {b : ℤ} (hb : 4 ∣ b - 1) {τ₀ : ℝ} {f M : ℤ}
    (h1 : (f : ℝ) / 4 ≤ (b : ℝ) * τ₀ - M) (h2 : (b : ℝ) * τ₀ - M ≤ (f : ℝ) / 4 + 1 / 2) :
    (4 : ℝ)⁻¹ ≤ circDist ((b : ℝ) * (τ₀ + ((1 - f : ℤ) : ℝ) / 4)) := by
  rw [rot_one_mod_four hb]
  exact LRC.MirrorCentre.circDist_ge_of_window (m := M) (by push_cast; linarith)
    (by push_cast; linarith) (by norm_num)

/-- **THE REDUCTION (the direction used).**  `c` a multiple of `4` clear at `τ₀`, and the three points
`bⱼ·τ₀` (`bⱼ ≡ 1 mod 4`) in one aligned half circle `H_{f/4}` modulo `1`: the quarter step `K = 1 − f`
keeps `c·τ` in place (ROT) and puts every `bⱼ·τ` in `H_{1/4} = [1/4, 3/4]`. -/
theorem finish_half {c : ℕ} (hc : 4 ∣ c) {b₁ b₂ b₃ : ℤ} (hb₁ : 4 ∣ b₁ - 1) (hb₂ : 4 ∣ b₂ - 1)
    (hb₃ : 4 ∣ b₃ - 1) {τ₀ : ℝ} (hτ : (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ₀)) (f M₁ M₂ M₃ : ℤ)
    (h₁ : (f : ℝ) / 4 ≤ (b₁ : ℝ) * τ₀ - M₁ ∧ (b₁ : ℝ) * τ₀ - M₁ ≤ (f : ℝ) / 4 + 1 / 2)
    (h₂ : (f : ℝ) / 4 ≤ (b₂ : ℝ) * τ₀ - M₂ ∧ (b₂ : ℝ) * τ₀ - M₂ ≤ (f : ℝ) / 4 + 1 / 2)
    (h₃ : (f : ℝ) / 4 ≤ (b₃ : ℝ) * τ₀ - M₃ ∧ (b₃ : ℝ) * τ₀ - M₃ ≤ (f : ℝ) / 4 + 1 / 2) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) :=
  ⟨τ₀ + ((1 - f : ℤ) : ℝ) / 4, by rw [rot_four_dvd hc]; exact hτ, quarter_of_half hb₁ h₁.1 h₁.2,
    quarter_of_half hb₂ h₂.1 h₂.2, quarter_of_half hb₃ h₃.1 h₃.2⟩

/-! ## Lemma QP -/

/-- **Lemma QP (i).**  The quarter point `w = ⌊4p⌋/4` satisfies `w ≤ p < w + 1/4`, so every point of the
closed arc `[p, p + 1/4]` lies in `H_w = [w, w + 1/2]`.
`[PROVISIONAL: counting tool; supports: the half circle H_w in parts S, T, Phi and P]` (the source's
tag: QP is the floor function, tagged because E404 tags FIT2, whose content is the same). -/
theorem qp_arc (p : ℝ) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 4⁻¹) :
    ((⌊4 * p⌋ : ℤ) : ℝ) / 4 ≤ p + δ ∧ p + δ ≤ ((⌊4 * p⌋ : ℤ) : ℝ) / 4 + 1 / 2 := by
  have a1 := Int.floor_le (4 * p)
  have a2 := Int.lt_floor_add_one (4 * p)
  constructor <;> linarith

/-- **Lemma QP (ii).**  If `f ≤ 4p ≤ f + 2/3` (so `f = ⌊4p⌋` and `4p − ⌊4p⌋ ≤ 2/3`, hence
`p − f/4 ≤ 1/6`), every point of `[p, p + 1/3]` lies in `H_{f/4}`.
`[PROVISIONAL: counting tool; supports: the half circle H_w in parts S, T, Phi and P]` (the source's
tag, as for QP(i)). -/
theorem qp_third {p : ℝ} {f : ℤ} (h1 : (f : ℝ) ≤ 4 * p) (h2 : 4 * p ≤ f + 2 / 3) {δ : ℝ}
    (h0 : 0 ≤ δ) (hδ : δ ≤ 1 / 3) :
    (f : ℝ) / 4 ≤ p + δ ∧ p + δ ≤ (f : ℝ) / 4 + 1 / 2 := by
  constructor <;> linarith

/-! ## Part a: `4 ∤ c` -/

/-- **Part a** (`4 ∤ c`): `τ = 1/4`.  `‖c/4‖ ≥ 1/4` (`c` odd or `≡ 2 mod 4`), and `‖b/4‖ = 1/4` for
`b ≡ 1 (mod 4)`. -/
theorem part_a {c : ℕ} (hc : ¬ 4 ∣ c) {b₁ b₂ b₃ : ℤ} (hb₁ : 4 ∣ b₁ - 1) (hb₂ : 4 ∣ b₂ - 1)
    (hb₃ : 4 ∣ b₃ - 1) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) := by
  have e : ∀ y : ℝ, y * (1 / 4) = y / 4 := fun y => by ring
  refine ⟨1 / 4, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact le_trans (by norm_num) (quarter_of_not_four_dvd hc)
  · rw [e]; exact quarter_of_one_mod_four hb₁
  · rw [e]; exact quarter_of_one_mod_four hb₂
  · rw [e]; exact quarter_of_one_mod_four hb₃

/-! ## Part S: `b_hi − b_lo ≤ 2c` -/

/-- **Part S** (`4 ∣ c`, `b_hi − b_lo ≤ 2c`, that is `2·d₂ ≤ c`): `τ₀ = 1/(8c)`, so `c·τ₀ = 1/8`; the
points `bⱼ·τ₀ = p + dⱼ/(2c)` (`p = b_lo·τ₀`) lie in `[p, p + 1/4]`; QP(i). -/
theorem part_S {c : ℕ} (hc : 4 ∣ c) (hcpos : 0 < c) {β b₂ b₃ : ℤ} (hβ : 4 ∣ β - 1)
    (hb₂ : 4 ∣ b₂ - 1) (hb₃ : 4 ∣ b₃ - 1) {d₁ d₂ : ℕ} (h₂ : (b₂ : ℝ) = β + 4 * d₁)
    (h₃ : (b₃ : ℝ) = β + 4 * d₂) (hd : d₁ ≤ d₂) (hS : 2 * d₂ ≤ c) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((β : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  set τ₀ : ℝ := 1 / (8 * c) with hτ₀
  set p : ℝ := (β : ℝ) * τ₀ with hp
  have hcτ : (c : ℝ) * τ₀ = 1 / 8 := by rw [hτ₀]; field_simp
  have hτ : (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ₀) := by
    rw [hcτ]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by norm_num) (by norm_num) (by norm_num)
  have hpt : ∀ {b : ℤ} {d : ℕ}, (b : ℝ) = β + 4 * d → d ≤ d₂ →
      (b : ℝ) * τ₀ - ((0 : ℤ) : ℝ) = p + (d : ℝ) / (2 * c) ∧ 0 ≤ (d : ℝ) / (2 * c) ∧
        (d : ℝ) / (2 * c) ≤ 4⁻¹ := by
    intro b d hb hdd
    refine ⟨?_, by positivity, ?_⟩
    · rw [hb, hp, hτ₀]; push_cast; field_simp; ring
    · rw [div_le_iff₀ (by positivity)]
      have h2d : 2 * d ≤ c := by omega
      have : (2 * d : ℝ) ≤ c := by exact_mod_cast h2d
      linarith
  obtain ⟨e₂, d₂0, d₂1⟩ := hpt h₂ hd
  obtain ⟨e₃, d₃0, d₃1⟩ := hpt h₃ le_rfl
  have e₁ : (β : ℝ) * τ₀ - ((0 : ℤ) : ℝ) = p + 0 := by push_cast; ring
  refine finish_half hc hβ hb₂ hb₃ hτ ⌊4 * p⌋ 0 0 0 ?_ ?_ ?_
  · rw [e₁]; exact qp_arc p le_rfl (by norm_num)
  · rw [e₂]; exact qp_arc p d₂0 d₂1
  · rw [e₃]; exact qp_arc p d₃0 d₃1

/-! ## Part T: `G ∤ m` -/

/-- The point `⌊q/2⌋/q` lies in `[1/3, 1/2]` for `q ≥ 2`, so `‖⌊q/2⌋/q‖ ≥ 1/3`. -/
theorem t_point {q : ℕ} (hq : 2 ≤ q) : (3 : ℝ)⁻¹ ≤ circDist (((q / 2 : ℕ) : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have h1 : q ≤ 3 * (q / 2) := by omega
  have h2 : 3 * (q / 2) ≤ 2 * q := by omega
  have h1R : (q : ℝ) ≤ 3 * ((q / 2 : ℕ) : ℝ) := by exact_mod_cast h1
  have h2R : 3 * ((q / 2 : ℕ) : ℝ) ≤ 2 * q := by exact_mod_cast h2
  refine LRC.MirrorCentre.circDist_ge_of_window (m := 0) ?_ ?_ (by norm_num)
  · rw [le_div_iff₀ hqR]; push_cast; linarith
  · rw [div_le_iff₀ hqR]; push_cast; linarith

/-- **Part T** (`c = 4m`, `G = gcd(d₁, d₂) ∤ m`).  `h = gcd(m, G)`, `q = G/h ≥ 2`, `m'' = m/h` (a unit
mod `q`, Bézout `m''A + qB = 1`), `k = ⌊q/2⌋·A`, `τ₀ = k/(4G)`: `c·τ₀ = m''k/q = ⌊q/2⌋/q − ⌊q/2⌋B`, so
`‖c·τ₀‖ ≥ 1/3`; and `(bⱼ − b_lo)·τ₀ = (dⱼ/G)·k` is an integer, so the three points coincide at `p`;
QP(i). -/
theorem part_T {m : ℕ} (hm : 0 < m) {β b₂ b₃ : ℤ} (hβ : 4 ∣ β - 1) (hb₂ : 4 ∣ b₂ - 1)
    (hb₃ : 4 ∣ b₃ - 1) {d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (h₂ : (b₂ : ℝ) = β + 4 * d₁)
    (h₃ : (b₃ : ℝ) = β + 4 * d₂) (hT : ¬ Nat.gcd d₁ d₂ ∣ m) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist (((4 * m : ℕ) : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((β : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) := by
  obtain ⟨G, hG⟩ : ∃ G, G = Nat.gcd d₁ d₂ := ⟨_, rfl⟩
  rw [← hG] at hT
  have hGpos : 0 < G := by rw [hG]; exact Nat.gcd_pos_of_pos_left _ hd₁
  obtain ⟨x₁, hx₁⟩ : G ∣ d₁ := by rw [hG]; exact Nat.gcd_dvd_left d₁ d₂
  obtain ⟨x₂, hx₂⟩ : G ∣ d₂ := by rw [hG]; exact Nat.gcd_dvd_right d₁ d₂
  obtain ⟨h, hh⟩ : ∃ h, h = Nat.gcd m G := ⟨_, rfl⟩
  have hhpos : 0 < h := by rw [hh]; exact Nat.gcd_pos_of_pos_left _ hm
  have hcop0 : Nat.Coprime (m / h) (G / h) := by
    rw [hh]; exact Nat.coprime_div_gcd_div_gcd (by rw [← hh]; exact hhpos)
  have hhm : h ∣ m := by rw [hh]; exact Nat.gcd_dvd_left m G
  obtain ⟨m'', hm''⟩ := hhm
  obtain ⟨q, hq⟩ : h ∣ G := by rw [hh]; exact Nat.gcd_dvd_right m G
  have hcop : Nat.Coprime m'' q := by
    rwa [hm'', hq, Nat.mul_div_cancel_left _ hhpos, Nat.mul_div_cancel_left _ hhpos] at hcop0
  have hq2 : 2 ≤ q := by
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; omega
    have hq1 : q ≠ 1 := by
      rintro rfl
      rw [mul_one] at hq
      exact hT ⟨m'', by rw [hq]; exact hm''⟩
    omega
  have hbez := Nat.gcd_eq_gcd_ab m'' q
  rw [hcop.gcd_eq_one] at hbez
  set A := Nat.gcdA m'' q with hA
  set B := Nat.gcdB m'' q with hB
  have hbezR : (m'' : ℝ) * (A : ℝ) + (q : ℝ) * (B : ℝ) = 1 := by exact_mod_cast hbez.symm
  set s : ℕ := q / 2 with hs
  set k : ℤ := (s : ℤ) * A with hk
  have hGR : (G : ℝ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hhpos.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  set τ₀ : ℝ := (k : ℝ) / (4 * G) with hτ₀
  set p : ℝ := (β : ℝ) * τ₀ with hp
  have hcτ : ((4 * m : ℕ) : ℝ) * τ₀ = ((s : ℕ) : ℝ) / q + ((-((s : ℤ) * B) : ℤ) : ℝ) := by
    have hmR : (m : ℝ) = h * m'' := by exact_mod_cast hm''
    have hGR' : (G : ℝ) = h * q := by exact_mod_cast hq
    have e1 : ((4 * m : ℕ) : ℝ) * τ₀ = (s : ℝ) * ((m'' : ℝ) * A) / q := by
      rw [hτ₀, hk]; push_cast; rw [hmR, hGR']; field_simp
    rw [e1, show (m'' : ℝ) * A = 1 - q * B by linarith]
    push_cast; field_simp; ring
  have hτ : (8 : ℝ)⁻¹ ≤ circDist (((4 * m : ℕ) : ℝ) * τ₀) := by
    rw [hcτ, circDist_add_int]
    exact le_trans (by norm_num) (t_point hq2)
  have hpt : ∀ {b : ℤ} {d x : ℕ}, (b : ℝ) = β + 4 * d → d = G * x →
      (b : ℝ) * τ₀ - (((x : ℤ) * k : ℤ) : ℝ) = p + 0 := by
    intro b d x hb hdx
    rw [hb, hp, hτ₀, hdx]; push_cast; field_simp; ring
  have e₁ : (β : ℝ) * τ₀ - ((0 : ℤ) : ℝ) = p + 0 := by push_cast; ring
  refine finish_half ⟨m, rfl⟩ hβ hb₂ hb₃ hτ ⌊4 * p⌋ 0 ((x₁ : ℤ) * k) ((x₂ : ℤ) * k) ?_ ?_ ?_
  · rw [e₁]; exact qp_arc p le_rfl (by norm_num)
  · rw [hpt h₂ hx₁]; exact qp_arc p le_rfl (by norm_num)
  · rw [hpt h₃ hx₂]; exact qp_arc p le_rfl (by norm_num)

/-! ## Part Φ: `G ∣ m`, `N = 3`, `n = 1` -/

/-- **Part Φ, the choice of `k`.**  For some integer `k`, `4p = β·(x/3 + k)/m` lies within `2/3` above an
integer `f`.  `h = gcd(β, m)`, `b' = β/h`, `m' = m/h` (Bézout `b'A + m'B = 1`), `b'x = 3F + r` with
`0 ≤ r ≤ 2`, `k = −F·A`: then `4p = F·B + r/(3m')`. -/
theorem phi_k (β : ℤ) {m : ℕ} (hm : 0 < m) (x : ℤ) :
    ∃ k f : ℤ, (f : ℝ) ≤ (β : ℝ) * ((x : ℝ) / 3 + k) / m ∧
      (β : ℝ) * ((x : ℝ) / 3 + k) / m ≤ f + 2 / 3 := by
  obtain ⟨h, hh⟩ : ∃ h, h = Int.gcd β m := ⟨_, rfl⟩
  have hhpos : 0 < h := by
    rw [hh]; exact Int.gcd_pos_of_ne_zero_right β (by exact_mod_cast hm.ne')
  obtain ⟨b', hb'⟩ : (h : ℤ) ∣ β := by rw [hh]; exact Int.gcd_dvd_left β (m : ℤ)
  obtain ⟨m', hm'⟩ : (h : ℤ) ∣ (m : ℤ) := by rw [hh]; exact Int.gcd_dvd_right β (m : ℤ)
  have hcop : Int.gcd b' m' = 1 := by
    have h1 := Int.gcd_mul_left (h : ℤ) b' m'
    rw [← hb', ← hm', Int.natAbs_natCast, ← hh] at h1
    exact Nat.eq_of_mul_eq_mul_left hhpos (by rw [mul_one]; exact h1.symm)
  have hm'pos : 0 < m' := by
    have hmZ : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
    have hhZ : (0 : ℤ) < (h : ℤ) := by exact_mod_cast hhpos
    rw [hm'] at hmZ
    exact pos_of_mul_pos_right hmZ hhZ.le
  have hbez := Int.gcd_eq_gcd_ab b' m'
  rw [hcop] at hbez
  set A := Int.gcdA b' m' with hA
  set B := Int.gcdB b' m' with hB
  obtain ⟨F, r, hr0, hr2, he⟩ : ∃ F r : ℤ, 0 ≤ r ∧ r ≤ 2 ∧ b' * x = 3 * F + r :=
    ⟨(b' * x) / 3, (b' * x) % 3, by omega, by omega, by omega⟩
  have hβR : (β : ℝ) = h * b' := by exact_mod_cast hb'
  have hmR : (m : ℝ) = h * m' := by exact_mod_cast hm'
  have heR : (b' : ℝ) * x = 3 * F + r := by exact_mod_cast he
  have hbR : (b' : ℝ) * A + m' * B = 1 := by exact_mod_cast hbez.symm
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hhpos.ne'
  have hm'R : (0 : ℝ) < m' := by exact_mod_cast hm'pos
  have hb2 : (b' : ℝ) * ((x : ℝ) / 3 + -(F * A)) = r / 3 + F * m' * B := by
    linear_combination (1 / 3 : ℝ) * heR - (F : ℝ) * hbR
  have key : (β : ℝ) * ((x : ℝ) / 3 + ((-(F * A) : ℤ) : ℝ)) / m = F * B + r / (3 * m') := by
    rw [hβR, hmR]
    have e2 : (h : ℝ) * b' * ((x : ℝ) / 3 + ((-(F * A) : ℤ) : ℝ)) / (h * m')
        = (b' : ℝ) * ((x : ℝ) / 3 + -(F * A)) / m' := by
      push_cast; field_simp
    rw [e2, hb2]; field_simp; ring
  have hr0R : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr2R : (r : ℝ) ≤ 2 := by exact_mod_cast hr2
  have hm'1 : (1 : ℝ) ≤ m' := by exact_mod_cast hm'pos
  refine ⟨-(F * A), F * B, ?_, ?_⟩
  · rw [key]; push_cast
    have : 0 ≤ (r : ℝ) / (3 * m') := by positivity
    linarith
  · rw [key]; push_cast
    have : (r : ℝ) / (3 * m') ≤ 2 / 3 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith

/-- **Part Φ** (`N = 3`, `n = 1`: `c = 4m`, `d₁ = m·x` with `x ∈ {1, 2}`, `d₂ = 3m`).  `w₀ = x/3`,
`τ₀ = (w₀ + k)/c`: `c·τ₀ = w₀ + k`, so `‖c·τ₀‖ = 1/3`; `(b_hi − b_lo)·τ₀ = x + 3k` (hi coincides with lo);
`(b_mid − b_lo)·τ₀ = x(w₀ + k) ≡ 1/3`; `k` from `phi_k` gives `4p − ⌊4p⌋ ≤ 2/3`; QP(ii). -/
theorem part_Phi {m : ℕ} (hm : 0 < m) {β b₂ b₃ : ℤ} (hβ : 4 ∣ β - 1) (hb₂ : 4 ∣ b₂ - 1)
    (hb₃ : 4 ∣ b₃ - 1) {x : ℕ} (hx : x = 1 ∨ x = 2) (h₂ : (b₂ : ℝ) = β + 4 * (m * x))
    (h₃ : (b₃ : ℝ) = β + 4 * (3 * m)) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist (((4 * m : ℕ) : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((β : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) := by
  obtain ⟨k, f, hf1, hf2⟩ := phi_k β hm (x : ℤ)
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  set τ₀ : ℝ := ((x : ℝ) / 3 + k) / (4 * m) with hτ₀
  set p : ℝ := (β : ℝ) * τ₀ with hp
  have h4p : 4 * p = (β : ℝ) * ((((x : ℤ) : ℝ)) / 3 + k) / m := by
    rw [hp, hτ₀]; push_cast; field_simp
  rw [← h4p] at hf1 hf2
  have hcτ : ((4 * m : ℕ) : ℝ) * τ₀ = (x : ℝ) / 3 + k := by
    rw [hτ₀]; push_cast; field_simp
  have hτ : (8 : ℝ)⁻¹ ≤ circDist (((4 * m : ℕ) : ℝ) * τ₀) := by
    rw [hcτ, circDist_add_int]
    rcases hx with rfl | rfl <;>
      exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by norm_num) (by norm_num) (by norm_num)
  have e₁ : (β : ℝ) * τ₀ - ((0 : ℤ) : ℝ) = p + 0 := by push_cast; ring
  have e₃ : (b₃ : ℝ) * τ₀ - (((x : ℤ) + 3 * k : ℤ) : ℝ) = p + 0 := by
    rw [h₃, hp, hτ₀]; push_cast; field_simp; ring
  have e₂ : (b₂ : ℝ) * τ₀ - (((x : ℤ) * k + ((x : ℤ) - 1) : ℤ) : ℝ) = p + 1 / 3 := by
    rw [h₂, hp, hτ₀]
    rcases hx with rfl | rfl <;> (push_cast; field_simp; ring)
  refine finish_half ⟨m, rfl⟩ hβ hb₂ hb₃ hτ f 0 ((x : ℤ) * k + ((x : ℤ) - 1)) ((x : ℤ) + 3 * k) ?_ ?_ ?_
  · rw [e₁]; exact qp_third hf1 hf2 le_rfl (by norm_num)
  · rw [e₂]; exact qp_third hf1 hf2 (by norm_num) le_rfl
  · rw [e₃]; exact qp_third hf1 hf2 le_rfl (by norm_num)

/-! ## Part P: `G ∣ m`, `N > 2n`, `(N, n) ≠ (3, 1)` -/

/-- **Part P, the choice of `j`.**  `N ≥ 4` and `N ∤ ν`, so `r = ‖ν/N‖ ≥ 1/N`.  `j = 1` if `r ≥ 1/8`;
otherwise `j = ⌈1/(8r)⌉`, so `j·r ∈ [1/8, 1/8 + r) ⊆ [1/8, 1/4)`, and `r < 1/8 ≤ N·r/8` forces `N ≥ 9`,
so `j < N/8 + 1 ≤ N/4`.  In both cases `1 ≤ j`, `4j ≤ N` and `‖ν·j/N‖ = j·r ≥ 1/8`.
`[PROVISIONAL: counting tool; supports: the choice of j in part P (multiples of r against the arc
[1/8, 1/4), the step E404 tags in DE3)]` (the source's tag). -/
theorem p_choice {N : ℕ} (hN : 4 ≤ N) {ν : ℤ} (hν : ¬ (N : ℤ) ∣ ν) :
    ∃ j : ℕ, 1 ≤ j ∧ 4 * j ≤ N ∧ (8 : ℝ)⁻¹ ≤ circDist ((ν : ℝ) * j / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨K, hK⟩ := circDist_eq_abs_sub_some_int ((ν : ℝ) / N)
  set y : ℝ := (ν : ℝ) / N - K with hy
  set r : ℝ := |y| with hr
  have hrN : 1 / N ≤ r := by
    have hne : ν - K * N ≠ 0 := by
      intro h0
      exact hν ⟨K, by linarith⟩
    have h1 : (1 : ℝ) ≤ |((ν - K * N : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |ν - K * N| := Int.one_le_abs hne
      exact_mod_cast this
    have : y = ((ν - K * N : ℤ) : ℝ) / N := by rw [hy]; push_cast; field_simp
    rw [hr, this, abs_div, abs_of_pos hNR]
    exact div_le_div_of_nonneg_right h1 hNR.le
  have hr2 : r ≤ 1 / 2 := by rw [← hK]; exact circDist.le_half _
  have hred : ∀ j : ℕ, circDist ((ν : ℝ) * j / N) = circDist ((j : ℝ) * r) := by
    intro j
    have e : (ν : ℝ) * j / N = (j : ℝ) * y + ((j * K : ℤ) : ℝ) := by
      rw [hy]; push_cast; field_simp; ring
    rw [e, circDist_add_int]
    rcases abs_choice y with h | h
    · rw [hr, h]
    · rw [hr, h, show (j : ℝ) * -y = -((j : ℝ) * y) by ring, circDist.symm_neg]
  have hNr : 1 ≤ (N : ℝ) * r := by
    rw [div_le_iff₀ hNR] at hrN; linarith
  by_cases h8 : (8 : ℝ)⁻¹ ≤ r
  · refine ⟨1, le_rfl, by omega, ?_⟩
    rw [hred]; push_cast; rw [one_mul]
    exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by push_cast; linarith)
      (by push_cast; linarith) (by norm_num)
  · push Not at h8
    have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hrN
    set j := ⌈1 / (8 * r)⌉₊ with hj
    have hj1 : 1 / (8 * r) ≤ j := Nat.le_ceil _
    have hj2 : (j : ℝ) < 1 / (8 * r) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hjr1 : 1 / 8 ≤ (j : ℝ) * r := by
      rw [div_le_iff₀ (by positivity)] at hj1; linarith
    have hjr2 : (j : ℝ) * r < 1 / 8 + r := by
      calc (j : ℝ) * r < (1 / (8 * r) + 1) * r := mul_lt_mul_of_pos_right hj2 hrpos
        _ = 1 / 8 + r := by field_simp
    have hN8 : (8 : ℝ) < N := by nlinarith
    have hjN8 : 1 / (8 * r) ≤ (N : ℝ) / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hjN : 4 * (j : ℝ) ≤ N := by linarith
    refine ⟨j, ?_, by exact_mod_cast hjN, ?_⟩
    · have : (0 : ℝ) < j := by nlinarith
      exact_mod_cast this
    · rw [hred]
      exact LRC.MirrorCentre.circDist_ge_of_window (m := 0) (by push_cast; linarith)
        (by push_cast; linarith) (by norm_num)

/-- **Part P** (`m = G·n`, `d₁ = G·x`, `d₂ = G·N`, `gcd(x, N) = 1`, `n < N`, `N ≥ 4`).  `x̄ = x⁻¹ mod N`
(Bézout `x·x̄ + N·B = 1`), `ν = n·x̄` (not `0 mod N`, as `0 < n < N`), `j` from `p_choice`, `k = x̄·j`,
`τ₀ = k/(4GN)`: `(b_hi − b_lo)·τ₀ = k`, so hi coincides with lo; `(b_mid − b_lo)·τ₀ = xk/N ≡ j/N`, with
`j/N ≤ 1/4`; and `c·τ₀ = nk/N = ν·j/N`, clear at `1/8`; QP(i). -/
theorem part_P {m G n x N : ℕ} (hG : 0 < G) (hmG : m = G * n) (hn : 0 < n) (hnN : n < N)
    (hN : 4 ≤ N) (hcop : Nat.Coprime x N) {β b₂ b₃ : ℤ} (hβ : 4 ∣ β - 1) (hb₂ : 4 ∣ b₂ - 1)
    (hb₃ : 4 ∣ b₃ - 1) (h₂ : (b₂ : ℝ) = β + 4 * (G * x)) (h₃ : (b₃ : ℝ) = β + 4 * (G * N)) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist (((4 * m : ℕ) : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((β : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) := by
  have hbez := Nat.gcd_eq_gcd_ab x N
  rw [hcop.gcd_eq_one] at hbez
  set A := Nat.gcdA x N with hA
  set B := Nat.gcdB x N with hB
  have hbez' : (1 : ℤ) = (x : ℤ) * A + (N : ℤ) * B := by exact_mod_cast hbez
  have hν : ¬ (N : ℤ) ∣ (n : ℤ) * A := by
    rintro ⟨t, ht⟩
    have hdvd : (N : ℤ) ∣ (n : ℤ) := ⟨x * t + n * B, by linear_combination (n : ℤ) * hbez' + (x : ℤ) * ht⟩
    have := Int.le_of_dvd (by exact_mod_cast hn) hdvd
    omega
  obtain ⟨j, hj1, hj4, hjc⟩ := p_choice hN hν
  have hGR : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hbezR : (x : ℝ) * A + (N : ℝ) * B = 1 := by exact_mod_cast hbez'.symm
  set k : ℤ := A * j with hk
  set τ₀ : ℝ := (k : ℝ) / (4 * G * N) with hτ₀
  set p : ℝ := (β : ℝ) * τ₀ with hp
  have hcτ : ((4 * m : ℕ) : ℝ) * τ₀ = (((n : ℤ) * A : ℤ) : ℝ) * j / N := by
    rw [hτ₀, hk, hmG]; push_cast; field_simp
  have hτ : (8 : ℝ)⁻¹ ≤ circDist (((4 * m : ℕ) : ℝ) * τ₀) := by rw [hcτ]; exact hjc
  have e₁ : (β : ℝ) * τ₀ - ((0 : ℤ) : ℝ) = p + 0 := by push_cast; ring
  have e₃ : (b₃ : ℝ) * τ₀ - (k : ℝ) = p + 0 := by
    rw [h₃, hp, hτ₀]; field_simp; ring
  have e₂ : (b₂ : ℝ) * τ₀ - ((-(B * j) : ℤ) : ℝ) = p + (j : ℝ) / N := by
    have e : (b₂ : ℝ) * τ₀ = p + (j : ℝ) * ((x : ℝ) * A) / N := by
      rw [h₂, hp, hτ₀, hk]; push_cast; field_simp
    rw [e, show (x : ℝ) * A = 1 - N * B by linarith]
    push_cast; field_simp; ring
  have hjN : (j : ℝ) / N ≤ 4⁻¹ := by
    rw [div_le_iff₀ hNR]
    have : (4 * j : ℝ) ≤ N := by exact_mod_cast hj4
    linarith
  refine finish_half ⟨m, rfl⟩ hβ hb₂ hb₃ hτ ⌊4 * p⌋ 0 (-(B * j)) k ?_ ?_ ?_
  · rw [e₁]; exact qp_arc p le_rfl (by norm_num)
  · rw [e₂]; exact qp_arc p (by positivity) hjN
  · rw [e₃]; exact qp_arc p le_rfl (by norm_num)

/-! ## The case split -/

/-- **M(1,3) on sorted integers `≡ 1 (mod 4)`.**  The case split a / S / T / Φ / P, exhaustive: `4 ∤ c`
(a); else `b_hi − b_lo ≤ 2c` (S); else `G ∤ m` (T); else `G ∣ m`, `m = G·n`, `N > 2n`, and either
`(N, n) = (3, 1)` (Φ) or not (P, where `N ≥ 4`). -/
theorem exists_one_three_sorted {c : ℕ} (hc : 0 < c) {b₁ b₂ b₃ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) (hb₃ : 4 ∣ b₃ - 1) (h12 : b₁ < b₂) (h23 : b₂ < b₃) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) := by
  by_cases h4 : 4 ∣ c
  swap
  · exact part_a h4 hb₁ hb₂ hb₃
  obtain ⟨m, rfl⟩ := h4
  have hm : 0 < m := by omega
  obtain ⟨d₁, hd₁⟩ : ∃ d : ℕ, b₂ = b₁ + 4 * d := ⟨((b₂ - b₁) / 4).toNat, by omega⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d : ℕ, b₃ = b₁ + 4 * d := ⟨((b₃ - b₁) / 4).toNat, by omega⟩
  have hd₁0 : 0 < d₁ := by omega
  have hd12 : d₁ < d₂ := by omega
  have h₂ : (b₂ : ℝ) = b₁ + 4 * d₁ := by rw [hd₁]; push_cast; ring
  have h₃ : (b₃ : ℝ) = b₁ + 4 * d₂ := by rw [hd₂]; push_cast; ring
  by_cases hS : 2 * d₂ ≤ 4 * m
  · exact part_S ⟨m, rfl⟩ hc hb₁ hb₂ hb₃ h₂ h₃ hd12.le hS
  by_cases hT : Nat.gcd d₁ d₂ ∣ m
  swap
  · exact part_T hm hb₁ hb₂ hb₃ hd₁0 h₂ h₃ hT
  obtain ⟨G, hG⟩ : ∃ G, G = Nat.gcd d₁ d₂ := ⟨_, rfl⟩
  rw [← hG] at hT
  have hGpos : 0 < G := by rw [hG]; exact Nat.gcd_pos_of_pos_left _ hd₁0
  have hcop0 : Nat.Coprime (d₁ / G) (d₂ / G) := by
    rw [hG]; exact Nat.coprime_div_gcd_div_gcd (by rw [← hG]; exact hGpos)
  obtain ⟨n, hn⟩ := hT
  obtain ⟨x, hx⟩ : G ∣ d₁ := by rw [hG]; exact Nat.gcd_dvd_left d₁ d₂
  obtain ⟨N, hN⟩ : G ∣ d₂ := by rw [hG]; exact Nat.gcd_dvd_right d₁ d₂
  have hcop : Nat.Coprime x N := by
    rwa [hx, hN, Nat.mul_div_cancel_left _ hGpos, Nat.mul_div_cancel_left _ hGpos] at hcop0
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, mul_zero] at hn; omega
    · exact h0
  have hN2 : 2 * n < N := by
    by_contra hcon
    push Not at hcon
    apply hS
    rw [hN, hn]
    have := Nat.mul_le_mul_left G hcon
    nlinarith
  have hxN : x < N := by
    rw [hx, hN] at hd12
    exact Nat.lt_of_mul_lt_mul_left hd12
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h0 | h0
    · rw [h0, mul_zero] at hx; omega
    · exact h0
  have h₂' : (b₂ : ℝ) = b₁ + 4 * (G * x) := by rw [h₂, hx]; push_cast; ring
  have h₃' : (b₃ : ℝ) = b₁ + 4 * (G * N) := by rw [h₃, hN]; push_cast; ring
  by_cases hΦ : N = 3 ∧ n = 1
  · obtain ⟨rfl, rfl⟩ := hΦ
    have hGm : G = m := by omega
    rw [hGm] at h₂' h₃'
    exact part_Phi hm hb₁ hb₂ hb₃ (by omega) h₂' (by rw [h₃']; ring)
  · have hN4 : 4 ≤ N := by omega
    exact part_P hGpos hn hn0 (by omega) hN4 hcop hb₁ hb₂ hb₃ h₂' h₃'

/-- **M(1,3) on three distinct integers `≡ 1 (mod 4)`** (sorting `exists_one_three_sorted`). -/
theorem exists_one_three_distinct {c : ℕ} (hc : 0 < c) {b₁ b₂ b₃ : ℤ} (hb₁ : 4 ∣ b₁ - 1)
    (hb₂ : 4 ∣ b₂ - 1) (hb₃ : 4 ∣ b₃ - 1) (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃) :
    ∃ τ : ℝ, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₁ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((b₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((b₃ : ℝ) * τ) := by
  rcases lt_or_gt_of_ne h12 with a | a <;> rcases lt_or_gt_of_ne h13 with b | b <;>
    rcases lt_or_gt_of_ne h23 with e | e
  · obtain ⟨τ, k0, k1, k2, k3⟩ := exists_one_three_sorted hc hb₁ hb₂ hb₃ a e
    exact ⟨τ, k0, k1, k2, k3⟩
  · obtain ⟨τ, k0, k1, k3, k2⟩ := exists_one_three_sorted hc hb₁ hb₃ hb₂ b e
    exact ⟨τ, k0, k1, k2, k3⟩
  · exact absurd (lt_trans a e) (by omega)
  · obtain ⟨τ, k0, k3, k1, k2⟩ := exists_one_three_sorted hc hb₃ hb₁ hb₂ b a
    exact ⟨τ, k0, k1, k2, k3⟩
  · obtain ⟨τ, k0, k2, k1, k3⟩ := exists_one_three_sorted hc hb₂ hb₁ hb₃ a b
    exact ⟨τ, k0, k1, k2, k3⟩
  · exact absurd (lt_trans a b) (by omega)
  · obtain ⟨τ, k0, k2, k3, k1⟩ := exists_one_three_sorted hc hb₂ hb₃ hb₁ e b
    exact ⟨τ, k0, k1, k2, k3⟩
  · obtain ⟨τ, k0, k3, k2, k1⟩ := exists_one_three_sorted hc hb₃ hb₂ hb₁ e a
    exact ⟨τ, k0, k1, k2, k3⟩

/-- **M(1,3) for one reading at `1/8` and three distinct odd readings at `1/4`**, at some `τ > 0`. -/
theorem exists_mixed_one_three_triple {c u₁ u₂ u₃ : ℕ} (hc : 0 < c) (hu₁ : ¬ 2 ∣ u₁)
    (hu₂ : ¬ 2 ∣ u₂) (hu₃ : ¬ 2 ∣ u₃) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) :
    ∃ τ : ℝ, 0 < τ ∧ (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((u₁ : ℝ) * τ) ∧
      (4 : ℝ)⁻¹ ≤ circDist ((u₂ : ℝ) * τ) ∧ (4 : ℝ)⁻¹ ≤ circDist ((u₃ : ℝ) * τ) := by
  obtain ⟨b₁, hb₁, hb₁u, hb₁e⟩ := exists_one_mod_four hu₁
  obtain ⟨b₂, hb₂, hb₂u, hb₂e⟩ := exists_one_mod_four hu₂
  obtain ⟨b₃, hb₃, hb₃u, hb₃e⟩ := exists_one_mod_four hu₃
  have hne : ∀ {u v : ℕ} {a b : ℤ}, u ≠ v → (a = u ∨ a = -(u : ℤ)) → (b = v ∨ b = -(v : ℤ)) →
      4 ∣ a - 1 → 4 ∣ b - 1 → a ≠ b := by
    intro u v a b huv ha hb ha4 hb4 hab
    apply huv
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
  obtain ⟨τ, k0, k1, k2, k3⟩ := exists_one_three_distinct hc hb₁ hb₂ hb₃
    (hne h12 hb₁u hb₂u hb₁ hb₂) (hne h13 hb₁u hb₃u hb₁ hb₃) (hne h23 hb₂u hb₃u hb₂ hb₃)
  set N : ℕ := ⌊|τ|⌋₊ + 1 with hN
  have hNpos : 0 < τ + N := by
    have h1 := Nat.lt_floor_add_one |τ|
    have h2 := neg_abs_le τ
    rw [hN]; push_cast; linarith
  have hshift : ∀ m : ℕ, circDist ((m : ℝ) * (τ + N)) = circDist ((m : ℝ) * τ) := fun m => by
    rw [show (m : ℝ) * (τ + N) = (m : ℝ) * τ + (((m * N : ℕ) : ℤ) : ℝ) by push_cast; ring,
      circDist_add_int]
  exact ⟨τ + N, hNpos, by rw [hshift]; exact k0, by rw [hshift, hb₁e]; exact k1,
    by rw [hshift, hb₂e]; exact k2, by rw [hshift, hb₃e]; exact k3⟩

/-! ## M(1,3) -/

/-- **Padding.**  An odd set `B` with at most three elements lies inside a set of three distinct odd
numbers: `B` itself, filled up with odd numbers above its maximum. -/
theorem exists_odd_triple_cover (B : Finset ℕ) (hB : ∀ b ∈ B, ¬ 2 ∣ b) (hBc : B.card ≤ 3) :
    ∃ u₁ u₂ u₃ : ℕ, ¬ 2 ∣ u₁ ∧ ¬ 2 ∣ u₂ ∧ ¬ 2 ∣ u₃ ∧ u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧
      ∀ b ∈ B, b = u₁ ∨ b = u₂ ∨ b = u₃ := by
  classical
  obtain ⟨M, hle⟩ : ∃ M : ℕ, ∀ b ∈ B, b ≤ M := ⟨B.sup id, fun b hb => Finset.le_sup (f := id) hb⟩
  rcases (show B.card = 0 ∨ B.card = 1 ∨ B.card = 2 ∨ B.card = 3 by omega) with h | h | h | h
  · rw [Finset.card_eq_zero] at h
    refine ⟨2 * M + 1, 2 * M + 3, 2 * M + 5, by omega, by omega, by omega, by omega, by omega,
      by omega, fun b hb => ?_⟩
    rw [h] at hb; simp at hb
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    have ha := hle a (by simp)
    refine ⟨a, 2 * M + 1, 2 * M + 3, hB a (by simp), by omega, by omega, by omega, by omega,
      by omega, fun b hb => ?_⟩
    exact Or.inl (Finset.mem_singleton.mp hb)
  · obtain ⟨a, a', hne, rfl⟩ := Finset.card_eq_two.mp h
    have ha := hle a (by simp)
    have ha' := hle a' (by simp)
    refine ⟨a, a', 2 * M + 1, hB a (by simp), hB a' (by simp), by omega, hne, by omega, by omega,
      fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (Or.inl (Finset.mem_singleton.mp hb))
  · obtain ⟨a, a', a'', h1, h2, h3, rfl⟩ := Finset.card_eq_three.mp h
    refine ⟨a, a', a'', hB a (by simp), hB a' (by simp), hB a'' (by simp), h1, h2, h3,
      fun b hb => ?_⟩
    simpa using hb

/-- **M(1,3).**  At most one positive reading `A` at `1/8` and at most three odd readings `B` at `1/4`
are clear together at some `τ > 0`.  Fewer numbers are padded (`c = 1` when `A` is empty,
`exists_odd_triple_cover` for `B`), so every case goes through the case split; order four is not
used. -/
theorem exists_mixed_one_three (A B : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) (hB : ∀ b ∈ B, ¬ 2 ∣ b)
    (hAc : A.card ≤ 1) (hBc : B.card ≤ 3) :
    ∃ τ : ℝ, 0 < τ ∧ (∀ a ∈ A, (8 : ℝ)⁻¹ ≤ circDist ((a : ℝ) * τ)) ∧
      ∀ b ∈ B, (4 : ℝ)⁻¹ ≤ circDist ((b : ℝ) * τ) := by
  classical
  obtain ⟨c, hc, hcA⟩ : ∃ c : ℕ, 0 < c ∧ ∀ a ∈ A, a = c := by
    rcases Finset.eq_empty_or_nonempty A with hE | ⟨a₀, ha₀⟩
    · exact ⟨1, one_pos, fun a ha => by simp [hE] at ha⟩
    · exact ⟨a₀, hA a₀ ha₀, fun a ha => Finset.card_le_one.mp hAc a ha a₀ ha₀⟩
  obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, h12, h13, h23, hcov⟩ := exists_odd_triple_cover B hB hBc
  obtain ⟨τ, hτ, k0, k1, k2, k3⟩ := exists_mixed_one_three_triple hc hu₁ hu₂ hu₃ h12 h13 h23
  refine ⟨τ, hτ, fun a ha => by rw [hcA a ha]; exact k0, fun b hb => ?_⟩
  rcases hcov b hb with rfl | rfl | rfl
  · exact k1
  · exact k2
  · exact k3

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-- **Quarter level, one and three.**  At most three odd readings, at most one multiple of `4`, at most
three readings `≡ 2 (mod 4)`: the mixed instant is M(1,3) (`exists_mixed_one_three`), and the set is
lonely at the displaced quarter instant `s/4 + j/4`. -/
theorem lonely_eight_of_quarter_one_three {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hodd : (S.filter (fun d => ¬ 2 ∣ d)).card ≤ 3)
    (h4 : (S.filter (fun d => 4 ∣ d)).card ≤ 1)
    (ht : (S.filter (fun d => d % 4 = 2)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set A := (S.filter (fun d => 4 ∣ d)).image (fun d => d / 4) with hAdef
  set B := (S.filter (fun d => d % 4 = 2)).image (fun d => d / 2) with hBdef
  have hAcard : A.card ≤ 1 := le_trans Finset.card_image_le h4
  have hBcard : B.card ≤ 3 := le_trans Finset.card_image_le ht
  have hBodd : ∀ x ∈ B, ¬ 2 ∣ x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have := (Finset.mem_filter.mp hd).2
    omega
  obtain ⟨s, hs, hsA, hsB⟩ := exists_mixed_one_three A B (quot_pos hpos 4 (by norm_num)) hBodd
    hAcard hBcard
  refine lonely_eight_of_quarter_silent hodd ⟨s, hs, fun a ha h4a => ?_, fun d hd hd2 => ?_⟩
  · exact hsA (a / 4) (Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, h4a⟩, rfl⟩)
  · exact hsB (d / 2) (Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, hd2⟩, rfl⟩)

/-- **Eighth level, one and three.**  The parity split for the non-multiples of `8` other than those
`≡ 4 (mod 8)`, at most one multiple of `8`, at most three readings `≡ 4 (mod 8)`: the mixed instant is
M(1,3), and the set is lonely at the displaced eighth instant `(τ + k)/8`. -/
theorem lonely_eight_of_eighth_one_three {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d)
    (hsplit : ParitySplit8 (S.filter (fun d => ¬ 8 ∣ d ∧ d % 8 ≠ 4)))
    (h8 : (S.filter (fun d => 8 ∣ d)).card ≤ 1)
    (h4 : (S.filter (fun d => d % 8 = 4)).card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set A := (S.filter (fun d => 8 ∣ d)).image (fun d => d / 8) with hAdef
  set B := (S.filter (fun d => d % 8 = 4)).image (fun d => d / 4) with hBdef
  have hAcard : A.card ≤ 1 := le_trans Finset.card_image_le h8
  have hBcard : B.card ≤ 3 := le_trans Finset.card_image_le h4
  have hBodd : ∀ x ∈ B, ¬ 2 ∣ x := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have := (Finset.mem_filter.mp hd).2
    omega
  obtain ⟨τ, hτ, hτA, hτB⟩ := exists_mixed_one_three A B (quot_pos hpos 8 (by norm_num)) hBodd
    hAcard hBcard
  refine lonely_eight_of_eighth_silent hsplit ⟨τ, hτ, fun m hm h8m => ?_, fun f hf h4f => ?_⟩
  · exact hτA (m / 8) (Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, h8m⟩, rfl⟩)
  · exact hτB (f / 4) (Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, h4f⟩, rfl⟩)

end LRC.OrderEightN
