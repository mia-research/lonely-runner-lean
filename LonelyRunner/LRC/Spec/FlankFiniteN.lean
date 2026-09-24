import LonelyRunner.LRC.Spec.DoorsN

/-!
# The flank door at four disparities — the decidable layer, scaling, and what remains

2026-09-21.  Exhaustively, the largest disparity hosts a lonely opening whenever the difference
set has **at most four members**, at *every* order `n ≥ 5` (`experiments/nN/three_blockers_v1.out`).
At a flank opening of `e` the disparity `e` itself sits at exactly `1/n` and is never blocked, so
a set of card `m` has `m − 1` **blockers**.  The measured clearance law
(`experiments/nN/clearance_law_v1.out`) is

    blockers k :   3    4    5    6
    least order:   5    8   11   13

and a subject at order `n` has exactly `n − 2` blockers, so rank one holds iff `n ≥ f(n−2)`.
True at `n = 5` (3 blockers, `f(3) = 5`) and false from `n = 6` on: `f` grows like `2k − 1`
while the diagonal can afford only `k + 2`, the two agreeing at exactly `k = 3`.

So the statement to aim at is **not** about `n = 5`.  It is `FourClears`, uniform in `n`;
`n = 5` is the case where `card ≤ 4` is automatic.

**Status.**  Everything here is proved and axiom-clean, with no `sorry`, no `native_decide`.
`FourClears` is **not** proved: it is a `Prop`, and appears only as a hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxRecDepth 4000000

namespace LRC.FlankFinite

open Flanks MomentIterationN LRC.SpecN

instance fact_two_le_five : Fact (2 ≤ 5) := ⟨by norm_num⟩

/-! ## 1. the decidable integer predicate, and the bridge to the reals -/

/-- Flank `e` hosts a lonely opening for the whole-number difference set `ds` at threshold
`1/n` exactly when some `j < e` has `d·(n j + 1) mod n e ∈ [e, (n−1)e]` for every `d ∈ ds`.

The restriction `j < e` is **exhaustive, not a window**: the reading is periodic in `j` with
period exactly `e` (`reading_mod`), so the bounded search decides the unbounded one
(`flankWorks_iff`).  Firewall row two forbids a *bound on when*, and this is not one — but
that has to be proved rather than assumed, and until 2026-09-21 it was not. -/
def flankWorks (n : ℕ) (ds : List ℕ) (e : ℕ) : Bool :=
  (List.range e).any fun j =>
    ds.all fun d =>
      let r := (d * (n * j + 1)) % (n * e)
      decide (e ≤ r) && decide (r ≤ (n - 1) * e)

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **The bridge.**  The decidable predicate yields a genuine lonely opening over the reals,
through `Flanks.clear_at_int_flank_iff_emod`.  This is what makes a `decide` mean something. -/
theorem lonely_of_flankWorks (L : List ℕ) (e : ℕ) (he : 0 < e)
    (h : flankWorks n L e = true) :
    ∃ j : ℕ, ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening n (e : ℝ) j) := by
  have hn2 : 2 ≤ n := Fact.out
  unfold flankWorks at h
  rw [List.any_eq_true] at h
  obtain ⟨j, -, hj⟩ := h
  refine ⟨j, fun d hd => ?_⟩
  rw [List.all_eq_true] at hj
  have hdj := hj d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdj
  obtain ⟨h1, h2⟩ := hdj
  have hb : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hcast : ((d * (n * j + 1)) % (n * e) : ℕ) = (d : ℤ) * ((n : ℤ) * (j : ℤ) + 1) % ((n : ℤ) * (e : ℤ)) := by
    rw [Int.natCast_emod]; push_cast; ring_nf
  have key := (clear_at_int_flank_iff_emod (n := n) (a := (d : ℤ)) hb j).mpr ?_
  · simpa using key
  · refine ⟨?_, ?_⟩
    · have : ((e : ℕ) : ℤ) ≤ (((d * (n * j + 1)) % (n * e) : ℕ) : ℤ) := by exact_mod_cast h1
      rwa [hcast] at this
    · have h2' : (((d * (n * j + 1)) % (n * e) : ℕ) : ℤ) ≤ (((n - 1) * e : ℕ) : ℤ) := by exact_mod_cast h2
      rw [hcast] at h2'
      refine le_trans h2' ?_
      have hne : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      rw [Nat.cast_mul, hne]; ring_nf; omega

/-! ### the search bound `j < e` is exhaustive

Firewall row two (§6A of `MANUSCRIPT_v19`) forbids any result that requires a bound on *when*
an instant falls.  `flankWorks` searches `j < e`, which looks like such a bound and is not: the
integer reading is periodic in the opening index with period exactly `e`, so the bounded search
and the unbounded one have the same answer.  The docstring above claimed this ("exactly when")
from the day the definition was written; only the forward direction was proved.  Both now are. -/

/-- **The reading is periodic in the opening index, with period `e`.**  Adding `e` to the index
adds `d·n·e` to the numerator, and `n·e` divides that. -/
theorem reading_period (n d e j : ℕ) :
    (d * (n * (j + e) + 1)) % (n * e) = (d * (n * j + 1)) % (n * e) := by
  have hrw : d * (n * (j + e) + 1) = d * (n * j + 1) + n * e * d := by ring
  rw [hrw, Nat.add_mul_mod_self_left]

/-- **So the index may be reduced mod `e`.** -/
theorem reading_mod (n d e j : ℕ) :
    (d * (n * (j % e) + 1)) % (n * e) = (d * (n * j + 1)) % (n * e) := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp
  · conv_rhs => rw [← Nat.mod_add_div j e]
    have hrw : d * (n * (j % e + e * (j / e)) + 1)
        = d * (n * (j % e) + 1) + n * e * (d * (j / e)) := by ring
    rw [hrw, Nat.add_mul_mod_self_left]

/-- **The converse of the bridge.**  A lonely opening of the whole-number flank `e` at *any*
index — however large — forces `flankWorks` to fire, because the index reduces mod `e`.

With `lonely_of_flankWorks` this makes the definition's `exactly when` a theorem. -/
theorem flankWorks_of_lonely (L : List ℕ) (e : ℕ) (he : 0 < e) (j : ℕ)
    (h : ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening n (e : ℝ) j)) :
    flankWorks n L e = true := by
  have hb : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have hcast : ∀ d k : ℕ, ((d * (n * k + 1)) % (n * e) : ℕ)
      = (d : ℤ) * ((n : ℤ) * (k : ℤ) + 1) % ((n : ℤ) * (e : ℤ)) := by
    intro d k; rw [Int.natCast_emod]; push_cast; ring_nf
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j % e, List.mem_range.mpr (Nat.mod_lt _ he), ?_⟩
  rw [List.all_eq_true]
  intro d hd
  obtain ⟨h1, h2⟩ := (clear_at_int_flank_iff_emod (n := n) (a := (d : ℤ)) hb j).mp (by
    simpa using h d hd)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [reading_mod]
  constructor
  · have : ((e : ℕ) : ℤ) ≤ (((d * (n * j + 1)) % (n * e) : ℕ) : ℤ) := by rw [hcast]; exact h1
    exact_mod_cast this
  · have h2' : (((d * (n * j + 1)) % (n * e) : ℕ) : ℤ) ≤ ((n : ℤ) * (e : ℤ) - (e : ℤ)) := by
      rw [hcast]; exact h2
    have hn2 : 2 ≤ n := Fact.out
    have hne : (((n - 1) * e : ℕ) : ℤ) = (n : ℤ) * (e : ℤ) - (e : ℤ) := by
      have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      rw [Nat.cast_mul, this]; ring
    have : (((d * (n * j + 1)) % (n * e) : ℕ) : ℤ) ≤ (((n - 1) * e : ℕ) : ℤ) := by
      rw [hne]; exact h2'
    exact_mod_cast this

/-- **The decidable predicate decides the question**, for whole-number difference sets: the
bounded search `j < e` is equivalent to a lonely opening of `e` at any index whatever. -/
theorem flankWorks_iff (L : List ℕ) (e : ℕ) (he : 0 < e) :
    flankWorks n L e = true ↔
      ∃ j : ℕ, ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening n (e : ℝ) j) :=
  ⟨lonely_of_flankWorks L e he, fun ⟨j, hj⟩ => flankWorks_of_lonely L e he j hj⟩

/-! ## 2. the finite check

Scale invariance (§3) means primitivity is not needed, and repeated entries are harmless, so a
single statement over sorted quadruples `a ≤ b ≤ c ≤ e` covers every difference set of card
`≤ 4` with `d_max ≤ 15` — including the collapsed cards.

`15` is the right bound: the `n = 5` tight family (sets with exactly one working opening) is 57
sets, all with `d_max ≤ 15`, stable from `[1,60]` to `[1,200]`, and everything above 15 has two
or more working openings (`experiments/nN/n5_tight_v2.out`). -/

/-- **The finite check at `n = 5`, by `decide`** — kernel-checked, no `native_decide`. -/
theorem four_clears_small :
    ∀ e ≤ 15, ∀ c ≤ e, ∀ b ≤ c, ∀ a ≤ b, 0 < a → flankWorks 5 [a,b,c,e] e = true := by
  decide

/-- The finite check as a statement about the reals. -/
theorem lonely_of_four_small {a b c e : ℕ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hce : c ≤ e) (he15 : e ≤ 15) :
    ∃ j : ℕ, ∀ d ∈ [a,b,c,e], (5 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening 5 (e : ℝ) j) := by
  have he : 0 < e := lt_of_lt_of_le ha (le_trans hab (le_trans hbc hce))
  exact lonely_of_flankWorks (n := 5) [a,b,c,e] e he
    (four_clears_small e he15 c hce b hbc a hab ha)

/-- **The small case for a real difference set.**  If every member of `ds` is one of four whole
numbers `a ≤ b ≤ c ≤ e` with `e ≤ 15`, flank `e` hosts a lonely opening for `ds`. -/
theorem lonely_of_small_cover {ds : Finset ℝ} {a b c e : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (he15 : e ≤ 15)
    (hcov : ∀ d ∈ ds, d = (a : ℝ) ∨ d = (b : ℝ) ∨ d = (c : ℝ) ∨ d = (e : ℝ)) :
    ∃ j : ℕ, Lonely 5 ds (flankOpening 5 (e : ℝ) j) := by
  have he : 0 < e := lt_of_lt_of_le ha (le_trans hab (le_trans hbc hce))
  obtain ⟨j, hj⟩ := lonely_of_flankWorks (n := 5) [a,b,c,e] e he
    (four_clears_small e he15 c hce b hbc a hab ha)
  refine ⟨j, fun d hd => ?_⟩
  rcases hcov d hd with rfl | rfl | rfl | rfl
  · exact hj a (by simp)
  · exact hj b (by simp)
  · exact hj c (by simp)
  · exact hj e (by simp)

/-! ## 3. scaling — the rational case reduces to the whole-number case -/

/-- `flankOpening` scales inversely with the flank. -/
theorem flankOpening_smul {e c : ℝ} (hc : c ≠ 0) (he : e ≠ 0) (j : ℕ) :
    flankOpening n (c * e) j = flankOpening n e j / c := by
  unfold flankOpening; field_simp

/-- **Scaling a difference set scales its flank openings**, in both directions.  So the flank
door is scale-invariant, and a rational difference set reduces to a whole-number one by clearing
denominators. -/
theorem lonely_flank_smul_iff {ds : Finset ℝ} {e c : ℝ} (hc : 0 < c) (he : 0 < e) (j : ℕ) :
    Lonely n (ds.image (fun d => c * d)) (flankOpening n (c * e) j) ↔
      Lonely n ds (flankOpening n e j) := by
  rw [flankOpening_smul hc.ne' he.ne' j]
  exact lonely_smul hc

theorem lonely_flank_smul {ds : Finset ℝ} {e c : ℝ} (hc : 0 < c) (he : 0 < e) (j : ℕ)
    (h : Lonely n ds (flankOpening n e j)) :
    Lonely n (ds.image (fun d => c * d)) (flankOpening n (c * e) j) :=
  (lonely_flank_smul_iff hc he j).mpr h

/-! ## 5. what remains, stated rather than assumed -/

/-- **The candidate.**  At most four disparities: the largest hosts a lonely opening.
`[EMPIRICAL]` — no counterexample in 172,352,957 exhaustive sets at `n = 5`, nor in the
cross-order sweeps `n = 5 … 50`.  **Not proved.**  It is a hypothesis wherever it appears. -/
def FourClears (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 4 → ∀ e ∈ ds, (∀ d ∈ ds, d ≤ e) →
    ∃ j : ℕ, Lonely n ds (flankOpening n e j)

/-- **The reduction.**  `FourClears 5` gives `DoorLargestFlank` at every subject of every
five-runner arrangement, because such a subject has at most four disparities
(`LRC.SpecN.diffSet_card_le`).  So the `n = 5` door reduces to a statement with no `5` in it. -/
theorem doorLargestFlank_of_fourClears (h : FourClears 5) :
    ∀ v : Fin 5 → ℝ, Function.Injective v → ∀ k : Fin 5, DoorLargestFlank v k := by
  classical
  intro v hv k
  have hne := diffSet_nonempty v k
  have hpos := diffSet_pos hv k
  obtain ⟨e, he, hmax⟩ := (diffSet v k).exists_max_image id hne
  have hcard : (diffSet v k).card ≤ 4 := by
    have := diffSet_card_le (n := 5) (v := v) k; omega
  obtain ⟨j, hj⟩ := h (diffSet v k) hpos hcard e he (fun d hd => hmax d hd)
  obtain ⟨i, hi, rfl⟩ := mem_diffSet.mp he
  refine ⟨i, hi, fun i' hi' => ?_, j, ?_⟩
  · exact hmax _ (mem_diffSet.mpr ⟨i', hi', rfl⟩)
  · exact lonelyAt_iff_lonely_diffSet.mpr hj

/-- **And it closes order five**, composing with the ladder in `DoorsN.lean`. -/
theorem lonelyRunnerAtFive_of_fourClears (h : FourClears 5) : LonelyRunnerAtN 5 := by
  refine lonelyRunnerAtN_of_doorFlank (fun v hv k => ?_)
  obtain ⟨i, hi, -, j, hj⟩ := doorLargestFlank_of_fourClears h v hv k
  exact ⟨i, hi, j, hj⟩

/-! ## 4. the ratio-condition region, proved

The exhaustive sweeps found **zero** largest-flank failures inside the ratio condition
`d_max ≤ (n−1)·d_min`, at every order (`experiments/nN/cx_profile_v1.out`).  This is why: the
**last** opening of the flank clears exactly that band.  So the ratio-condition region of
`FourClears` is not conjectural — it is a theorem, at every order and every card. -/

/-- **The last opening of the flank clears exactly the ratio-condition band.**

This is **not a new criterion**: it is `Flanks.clear_at_opening_of_band` — the framework's
general band test, real-valued at every `(flank, opening)` pair — instantiated at `k = e − 1`
with `M = d − 1`.  What is new is only the identification: that instance is exactly the
ratio condition, which is why the exhaustive sweeps found zero largest-flank failures inside it
(`experiments/nN/cx_profile_v1.out`, `last_opening_v1.out`).

At `k = e − 1` the scaled ratio is `(d/e)(n(e−1)+1) = dn − d(n−1)/e`, and the band about
`M = d − 1` reads `nd − n + 1 ≤ dn − d(n−1)/e ≤ nd − 1`, i.e. `e ≤ (n−1)d` and `d ≤ e`. -/
theorem clear_at_last_opening {e d : ℕ} (he : 0 < e)
    (hlo : e ≤ (n - 1) * d) (hhi : d ≤ e) :
    (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening n (e : ℝ) (e - 1)) := by
  have hn2 : 2 ≤ n := Fact.out
  have hn0 : (0 : ℝ) < n := n_pos
  have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | hp
      · simp at hlo; omega
      · exact hp
    exact_mod_cast this
  have hcast : ((e - 1 : ℕ) : ℝ) = (e : ℝ) - 1 := by
    have : 1 ≤ e := he
    push_cast [Nat.cast_sub this]; ring
  -- the two band inequalities, after clearing the division
  have hlo' : (e : ℝ) ≤ ((n : ℝ) - 1) * (d : ℝ) := by
    have h := hlo
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      push_cast [Nat.cast_sub this]; ring
    have : ((e : ℕ) : ℝ) ≤ (((n - 1) * d : ℕ) : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_mul, hc] at this
  have hhi' : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hhi
  refine clear_at_opening_of_band he0 (e - 1) ((d : ℤ) - 1) ?_ ?_ <;>
    rw [hcast] <;> push_cast <;>
    rw [div_mul_eq_mul_div] <;>
    [rw [le_div_iff₀ he0]; rw [div_le_iff₀ he0]] <;>
    nlinarith [hlo', hhi', he0, hd0, hn0, (by exact_mod_cast hn2 : (2:ℝ) ≤ (n:ℝ))]

open Classical in
/-- **The ratio condition gives a lonely opening at the largest flank**, for a whole-number
difference set.  This discharges the region the exhaustive sweeps found free of failures, and
leaves `FourClears` owing only the sets with `d_max > (n−1)·d_min`. -/
theorem lonely_last_of_ratio {S : Finset ℕ} {e : ℕ} (he : 0 < e)
    (hmax : ∀ d ∈ S, d ≤ e) (hratio : ∀ d ∈ S, e ≤ (n - 1) * d) :
    Lonely n (Finset.image (fun d : ℕ => (d : ℝ)) S) (flankOpening n (e : ℝ) (e - 1)) := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
  exact clear_at_last_opening he (hratio d hd) (hmax d hd)

/-! ## 6. the gap criterion — the reduction the margin argument needs

The openings of a flank are equally spaced with gap `1/e`.  So the question "does the union of
the blocked sets miss one of the `e` openings" — a statement about the openings — becomes
"does the lonely set of the blockers contain an interval longer than `1/e`", a statement about
the blockers alone.  Holds at every order and for any number of blockers. -/

/-- **A window longer than `1/e` in the nonnegative reals contains a flank opening of `e`.**
The openings `(j + 1/n)/e`, `j : ℕ`, are equally spaced with gap `1/e`. -/
theorem exists_flankOpening_mem_Ioo {e : ℝ} (he : 0 < e) {x L : ℝ} (hx : 0 ≤ x)
    (hL : 1 / e < L) :
    ∃ j : ℕ, flankOpening n e j ∈ Set.Ioo x (x + L) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hhalf : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  set lo : ℝ := e * x - (n : ℝ)⁻¹ with hlo
  have hlen : 1 < e * L := by rw [div_lt_iff₀ he] at hL; linarith
  have hlo_gt : (-1 : ℝ) < lo := by
    have : (0 : ℝ) ≤ e * x := mul_nonneg he.le hx
    rw [hlo]; linarith
  -- j = ⌊lo⌋ + 1, which is a nonnegative integer
  have hfloor_ge : (0 : ℤ) ≤ ⌊lo⌋ + 1 := by
    have : (-1 : ℤ) ≤ ⌊lo⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    omega
  set j : ℕ := (⌊lo⌋ + 1).toNat with hj
  have hjz : ((j : ℤ)) = ⌊lo⌋ + 1 := by rw [hj]; exact Int.toNat_of_nonneg hfloor_ge
  have hjc : (j : ℝ) = ((⌊lo⌋ : ℝ) + 1) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hjz
    push_cast at this; exact this
  refine ⟨j, ?_, ?_⟩
  · unfold flankOpening
    rw [lt_div_iff₀ he, hjc]
    have := Int.lt_floor_add_one lo
    rw [hlo] at this; linarith
  · unfold flankOpening
    rw [div_lt_iff₀ he, hjc]
    have := Int.floor_le lo
    rw [hlo] at this; linarith

/-- **The gap criterion.**  If every instant in some window of length greater than `1/e` beyond
the origin is lonely for `ds`, then the flank `e` hosts a lonely opening.

This is the reduction the margin argument needs: it replaces "the union of the blocked sets
misses one of the `e` openings" — a statement about the openings — by "the lonely set of the
blockers has a gap longer than `1/e`", a statement about the blockers alone.  It holds at every
order and for any number of blockers. -/
theorem exists_lonely_flankOpening_of_gap {ds : Finset ℝ} {e : ℝ} (he : 0 < e)
    {x L : ℝ} (hx : 0 ≤ x) (hL : 1 / e < L)
    (hwin : ∀ t ∈ Set.Ioo x (x + L), Lonely n ds t) :
    ∃ j : ℕ, Lonely n ds (flankOpening n e j) := by
  obtain ⟨j, hj⟩ := exists_flankOpening_mem_Ioo (n := n) he hx hL
  exact ⟨j, hwin _ hj⟩

end LRC.FlankFinite
