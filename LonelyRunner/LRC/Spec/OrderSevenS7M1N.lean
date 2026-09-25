/-!
# n = 7 (Barajas–Serra) — §7 stage 1: the exceptional 5-sets at `N = 49`

Source: `sources_barajas_serra_2008.txt` lines 786–805 (§7).

BS §7 disposes of `|A| = 5, m = 1` by two computer searches, asserted in the
paper without the computation being published. This file carries out the first
**inside the Lean kernel**, by `rfl` on a `Nat`-valued `Bool` computation — no
`native_decide`. Stage 2 is `OrderSevenS7Stage2AllN`.

`stage1_bad_count`: of the 20349 five-element subsets of the 21 residues whose
class mod 7 lies in `{1,2,4}`, exactly 63 admit no multiplier placing every
element in `[7,42]`. (63 = 3 dilation orbits × 21; the three orbit
representatives are BS's `{1,4,11,39,43}`, `{1,4,18,22,29}`, `{1,4,18,44,46}`.)

**The universe is the 21 residues with class mod 7 in `{1,2,4}`** — the `hres`
hypothesis — not all 42 units mod 49. That is where BS's `(1/21)·C(21,5) = 969`
comes from; over all 42 units one gets 48 exceptions instead of 3, matching
nothing in the paper. Getting this wrong yields a plausible but wrong result, so
it is recorded here rather than left implicit.

Written over `List Nat` with `Nat` arithmetic (kernel GMP-accelerated) rather
than `Finset (ZMod 49)`, which cannot even synthesize the `Decidable` instance.
~21s. Keep one heavy `rfl` per module: `lake build` also emits C and overflows
the elaboration stack where `lake env lean` does not.

`stage1_bad_count` is **not** consumed by `intLRC_seven`: the proof needs only
`bad_subset_exc63` (`OrderSevenS7Exc63N`), which bounds the exceptional sets above
by the pinned literals. The count is kept because it is the certification that
the enumeration is complete — that there are exactly 63, i.e. BS's three orbits
and nothing else — which is the fact the paper asserts.
-/

namespace LRC.OrderSevenN
namespace Section7M1

/-! ## Stage 1 — `N = 49` -/

/-- The 21 residues mod 49 whose class mod 7 lies in `{1,2,4}`. -/
def S21 : List Nat :=
  (List.range 49).filter (fun x => x % 7 == 1 || x % 7 == 2 || x % 7 == 4)

/-- `lam` places every element of `T` in the arc `[7,42]` mod 49, i.e. gives
every element circular distance `≥ 1/7` at `N = 49`. -/
def okFor (lam : Nat) (T : List Nat) : Bool :=
  T.all (fun t => let v := (lam * t) % 49; 7 ≤ v && v ≤ 42)

/-- Some multiplier in the residue-`{1,2,4}` set works for `T`. -/
def solvable (T : List Nat) : Bool := S21.any (fun lam => okFor lam T)

/-- All 20349 five-element subsets of `S21`, as strictly increasing lists. -/
def subs5 : List (List Nat) :=
  S21.flatMap fun a => (S21.filter (a < ·)).flatMap fun b =>
  (S21.filter (b < ·)).flatMap fun c => (S21.filter (c < ·)).flatMap fun d =>
  (S21.filter (d < ·)).map fun e => [a, b, c, d, e]

/-- The subsets admitting no good multiplier. -/
def bad : List (List Nat) := subs5.filter (fun T => !solvable T)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
/-- **BS §7 stage 1, kernel-verified.** Exactly 63 of the 20349 five-subsets
admit no good multiplier — three dilation orbits of size 21. -/
theorem stage1_bad_count : bad.length = 63 := by rfl


end Section7M1
end LRC.OrderSevenN
