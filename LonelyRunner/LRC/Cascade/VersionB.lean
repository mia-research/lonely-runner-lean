import LonelyRunner.LRC.Cascade.FourDifferences

/-!
# Version B for the proved cases

Part of the cascade artefact (`LRC/Cascade/`).  Each theorem: for every arrangement in the class, an explicit iterate of
the move from the bound `1/(n·m)` is lonely and no positive lonely time precedes it.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## Version B for the proved cases: the iteration terminates with the first isolation time

Each statement: for every arrangement in the class, some iterate of the move from the bound `1/(n·m)` is lonely, and no
positive lonely time precedes it. -/

namespace VersionB

open ConstructionN MomentIterationN TerminationThree TerminationFour ChainBounds NearestState FewDifferences
  FourDifferencesSix

theorem two_diffs {n : ℕ} [Fact (2 ≤ n)] (hn3 : 3 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 2) {m : ℝ} (hm : m ∈ ds) (hmin : ∀ d ∈ ds, m ≤ d) :
    Lonely n ds ((move n ds)^[1] (1 / (n * m))) ∧
      ∀ s, 0 < s → Lonely n ds s → (move n ds)^[1] (1 / (n * m)) ≤ s :=
  first_isolation_of_fixed hpos hm 1 (two_diffs_stop_within_one_move hn3 hpos hcard hm hmin)

theorem three_diffs {n : ℕ} [Fact (2 ≤ n)] (hn4 : 4 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 3) {m : ℝ} (hm : m ∈ ds) (hmin : ∀ d ∈ ds, m ≤ d) :
    Lonely n ds ((move n ds)^[3] (1 / (n * m))) ∧
      ∀ s, 0 < s → Lonely n ds s → (move n ds)^[3] (1 / (n * m)) ≤ s :=
  first_isolation_of_fixed hpos hm 3 (three_diffs_stop_within_three_moves hn4 hpos hcard hm hmin)

theorem four_diffs {n : ℕ} [Fact (2 ≤ n)] (hn6 : 6 ≤ n) {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d)
    (hcard : ds.card ≤ 4) {m : ℝ} (hm : m ∈ ds) (hmin : ∀ d ∈ ds, m ≤ d) :
    Lonely n ds ((move n ds)^[7] (1 / (n * m))) ∧
      ∀ s, 0 < s → Lonely n ds s → (move n ds)^[7] (1 / (n * m)) ≤ s :=
  first_isolation_of_fixed hpos hm 7 (four_diffs_stop_ge_six hn6 hpos hcard hm hmin)

theorem slowest_recursion {n : ℕ} [Fact (2 ≤ n)] (hn9 : 9 ≤ n) (k : ℕ) (hk : 2 ^ (k - 1) ≤ n)
    {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ k) {m : ℝ} (hm : m ∈ ds)
    (hmin : ∀ d ∈ ds, m ≤ d) :
    Lonely n ds ((move n ds)^[2 ^ (k - 1) - 1] (1 / (n * m))) ∧
      ∀ s, 0 < s → Lonely n ds s → (move n ds)^[2 ^ (k - 1) - 1] (1 / (n * m)) ≤ s :=
  first_isolation_of_fixed hpos hm _ (SlowestRecursion.stops_slowest_recursion hn9 k hk hpos hcard hm hmin)

theorem order_three {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 2) {m : ℝ} (hm : m ∈ ds)
    (hmin : ∀ d ∈ ds, m ≤ d) :
    Lonely 3 ds (move 3 ds (1 / ((3 : ℕ) * m))) ∧
      ∀ s, 0 < s → Lonely 3 ds s → move 3 ds (1 / ((3 : ℕ) * m)) ≤ s :=
  three_first_isolation hpos hcard hm hmin

theorem order_four {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 3) {a : ℝ} (ha : a ∈ ds)
    (hmin : ∀ d ∈ ds, a ≤ d) :
    Lonely 4 ds ((move 4 ds)^[3] (1 / ((4 : ℕ) * a))) ∧
      (∀ s, 0 < s → Lonely 4 ds s → (move 4 ds)^[3] (1 / ((4 : ℕ) * a)) ≤ s) ∧
      a * (move 4 ds)^[3] (1 / ((4 : ℕ) * a)) < 3 / 4 :=
  four_first_isolation hpos hcard ha hmin

end VersionB
