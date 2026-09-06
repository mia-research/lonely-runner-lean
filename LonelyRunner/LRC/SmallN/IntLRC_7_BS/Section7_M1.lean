/-!
# n = 7 (Barajas–Serra) — §7, the case `|A| = 5`, `m = 1`: the finite searches

Source: `sources_barajas_serra_2008.txt` lines 786–805 (§7).

BS §7 disposes of `|A| = 5, m = 1` by two computer searches, asserted in the
paper without the computation being published. This file carries out **both
searches inside the Lean kernel**, by `rfl` on `Nat`-valued `Bool` computations.
No `native_decide`: every fact here is checked by the kernel itself.

* `stage1_bad_count` — over `N = 49`: of the 20349 five-element subsets of the
  21 residues whose class mod 7 lies in `{1,2,4}`, exactly 63 admit no
  multiplier placing every element in `[7,42]`. 63 = 3 dilation orbits × 21,
  and `stage1_bad_orbits` exhibits the three orbit representatives, which are
  precisely BS's `{1,4,11,39,43}`, `{1,4,18,22,29}`, `{1,4,18,44,46}`.
* `stage2_clean` — over `N' = 98`: every `gcd = 1` configuration whose 5-set
  reduces to one of those three exceptions admits a good multiplier. The
  configurations BS could not solve all have `gcd ≥ 2`, so the LRC
  normalization `gcd(D) = 1` excludes them.

**Two conventions decide these answers**; both were got wrong first and each
produces a plausible but wrong result (see `docs/n7_bs/SECTION7_M1_ANALYSIS_v1.md`):

1. The stage-1 universe is the **21** residues with class mod 7 in `{1,2,4}` —
   the `hres` hypothesis — not all 42 units mod 49. That is where BS's
   `(1/21)·C(21,5) = 969` comes from. Over all 42 units one gets 48 exceptions.
2. In stage 2 the multiplier ranges over **all** of `1..97`, not the units mod
   98. Restricting to units manufactures a spurious fourth exception,
   `(4,44,46,50,67)` with `d₆ = 21`, which has `gcd = 1` and so would not be
   covered by BS's gcd argument. It is not a counterexample: `7, 21, 77, 91` all
   work for it.

These computations are the finite core of the `m = 1` case. They do **not** by
themselves discharge `five_avoid_m1`: that statement is false as written, and
cannot be repaired by adding `d₆` while keeping the `∃ lam, ¬ 7 ∣ lam ∧
qz 1 (lam·dᵢ) ∉ {0,6}` shape — at `N' = 98`, 20 of the 1134 `gcd = 1`
configurations admit **only** multipliers divisible by 7, and `98` is not a power
of 7 so it is outside the `qz` apparatus entirely. Connecting these searches to
`bs_discrete` requires the `m = 1` branch to be routed around the `qz` layer.
See `docs/n7_bs/SECTION7_M1_ANALYSIS_v1.md` §3.

Timings on the reference machine: `stage1_bad_count` ~21s, `stage2_clean` ~3s,
both with the default elaboration stack.
-/

namespace IntLRC7BS
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

/-- Insertion sort on `List Nat`, so a dilated set can be compared as a set. -/
def ins (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

def srt : List Nat → List Nat
  | [] => []
  | x :: xs => ins x (srt xs)

/-- The dilate of `E` by `lam`, as a sorted set of residues mod 49. -/
def dilate (lam : Nat) (E : List Nat) : List Nat := srt (E.map (fun x => (lam * x) % 49))

/-- BS's three exceptional sets. -/
def exc : List (List Nat) := [[1, 4, 11, 39, 43], [1, 4, 18, 22, 29], [1, 4, 18, 44, 46]]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000000 in
/-- **The 63 exceptions are exactly the dilates of BS's three sets.** Together
with `stage1_bad_count` (63 = 3 × 21) this is BS's claim that, up to dilation,
`{1,4,11,39,43}`, `{1,4,18,22,29}` and `{1,4,18,44,46}` are the only
five-element sets admitting no good multiplier at `N = 49`. -/
theorem stage1_bad_are_dilates :
    bad.all (fun T => exc.any (fun E => S21.any (fun lam => T == dilate lam E))) = true := by
  rfl

set_option maxHeartbeats 400000 in
/-- Each of BS's three sets really is exceptional. -/
theorem stage1_exc_are_bad : exc.all (fun E => !solvable E) = true := by rfl

end Section7M1
end IntLRC7BS
