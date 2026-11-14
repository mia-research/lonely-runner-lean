import Fresh.DumpDomData

/-!
# ChainDomData: the per-chain J-carrier datum for the corrected OneSided consumption

Written 2026-11-14.  New file; nothing existing is edited.  This instantiates the
chain-side domination datum whose EXACT shape is the missing hypothesis of
`Fresh.DumpDomData.capChainsRealized_of_chainDomU0` (the corrected consumption of
the joinedge2 dump-v2 J-half, after `Fresh.DumpDomData` proved both `DumpDom` and
`DumpDomU0` uninstantiable for the 11 strict families): for a box `n`, a composed
family `f`, and the box's ATTESTING W0 chain `steps`, every record's cap walk is
dominated by an entry of whatever table `chainRun (u0Of n) 0 1 steps` produces --
the consumed chain's own closed-trace domination at the U0-fixed start.

## Method: the transcribed-trace-table pattern

The kernel cannot evaluate the `uMk` fold or a 19-20-step `chainRun` directly (the
ℚ products normalize through `Nat.gcd`, well-founded and kernel-hostile at fold
depth).  Instead (a) the attesting chain's run from the SPARSE `u0Of` start
`(a, Aex) = (0, 1)` is recomputed outside Lean by the verified value-verbatim
mirror of `Fresh.UClosureKill`'s `uKeepCur`/`uBack`/`uProp`/`uAdd`/`uGt`/`uStep`
(`experiments/n8/onefast_audit/chaindom_gen_v1.py`--`v3.py`: it reproduces the
dump's `chains_enumerated`, `jprov` and `join_domination_all_chains` on all 11
strict boxes, and every pre-end table of the full-start enumeration), and the
step-end tables are transcribed as `UTable` literals `T_*_1..T_*_T`; (b) each step
is proven IN the kernel by `rfl` (`stepEq_*_k`: one `uStep` = two `uAdd`s on
literals -- no deep folds); (c) the generated extraction peels the hypothesis
`chainRun (u0Of n) 0 1 steps = some (V, af, Af)` with
`Option.bind_eq_some_iff` + `Fresh.UClosureKill.uStep_some_add`-shaped rewriting,
pinning `V = T_*_T`; (d) `CapsDom` then follows from `capsDom_single` on the
literal final entries (`norm_num` on the exact cap comparisons).

## Coverage (honest)

Instantiated [T 3/3]: boxes (1,3,4,4,5,5,7), (1,3,4,5,6,6,7), (1,4,4,5,6,6,7) --
exactly the strict boxes where a SINGLE enumerated chain run from the sparse U0
dominates every banked record (powered check over all 1176/480/896 enumerated
chains).  Rule-22 residual: the other 8 strict boxes have NO single sparse-start
dominator (their records are dominated only from the FULL box closure `mk n`,
whose fold is not kernel-transcribable into the read-only `u0Of`); they need a
richer U0 vocabulary (a transcribed full-closure table) and are honestly left out.

All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every
theorem carries `#print axioms`; the accepted profile is the standard three
(propext, Classical.choice, Quot.sound) -- `sorryAx` is failure.
-/

namespace Fresh.ChainDomData

open Fresh.UClosure Fresh.CapChainsOfCarve Fresh.DumpDomData Fresh.OneSidedComposed
  Fresh.JoinFamComposed Fresh.OneSidedGlue Fresh.FilterAssembly

-- the 49-point `fin_cases` checks and the big literal tables need headroom
set_option maxHeartbeats 4000000

/-- **THE datum** (exactly the missing hypothesis of
`Fresh.DumpDomData.capChainsRealized_of_chainDomU0`, at the fixed chain start
`(a, Aex) = (0, 1)` and the datum's own attesting chain `steps`): every record's
cap walk is dominated by the closed-trace table of the chain run from `u0Of n`. -/
structure ChainDomData (n : Fin 7 → ℤ) (f : ComposedFam) where
  steps : List Step
  dom : ∀ e ∈ f.edges, ∀ V : UTable, ∀ af : Fin 7, ∀ Af : ℚ,
    chainRun (u0Of n) 0 1 steps = some (V, af, Af) → CapsDom V e.y e.caps e.x

/-- The consumption, verbatim: the datum drops into the corrected conditional (the
chain `g` admits must BE the attesting chain -- the per-chain disjunctive form of
the dump's chain-attained class). -/
theorem chainDomData_capChains {n : Fin 7 → ℤ} {f : ComposedFam} (d : ChainDomData n f)
    {g : Fin 7 → ℝ} (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (hfine0 : UFine g (u0Of n)) (hchain : ChainRealized g (u0Of n) 0 1 d.steps) :
    capChainsRealized g f :=
  capChainsRealized_of_chainDomU0 f hface 0 1 d.steps hfine0 hchain d.dom

#print axioms chainDomData_capChains

/-- Assembly: a surviving `uAdd` whose keep-cur and back checks are ground-false
returns its propagation, and the propagated table is the transcribed one pointwise.
(The per-point facts are ground -- concrete `Fin 7` pairs, literal ℚ comparisons.) -/
theorem uAdd_eq_some {U V : UTable} {i j : Fin 7} {c : ℚ} {s : Bool}
    (hK : uKeepCur U i j c s = false) (hB : uBack U i j c s = false)
    (hpt : ∀ p q, uProp U i j c s p q = V p q) :
    uAdd U i j c s = some V := by
  unfold uAdd
  rw [if_neg (by simp [hK]), if_neg (by simp [hB])]
  exact congrArg some (funext fun p => funext fun q => hpt p q)

#print axioms uAdd_eq_some

/-- Assembly: a `uStep` on positive numerators is its two `uAdd`s (`uGt_pos`), so the
two per-add facts compose to the step equation. -/
theorem uStep_eq_some {U V W : UTable} {a b : Fin 7} {Aex A B : ℚ}
    (hAex : 0 < Aex) (hA : 0 < A) (hB : 0 < B)
    (h1 : uAdd U a b (Aex / A) true = some V) (h2 : uAdd V b a (B / Aex) true = some W) :
    uStep U a b Aex A B = some W := by
  show (uGt U Aex a A b).bind (fun V => uGt V B b Aex a) = some W
  rw [uGt_pos U a b hAex hA, h1, Option.bind_some, uGt_pos V b a hB hAex, h2]

#print axioms uStep_eq_some

/-- The attesting chain for box ([1, 3, 4, 4, 5, 5, 7]) as `Fresh.UClosure.Step` literals (chain index 94 of the box's dump enumeration, word length 19): each step is the zone triple `(b, Bn, Ax)` = `(row, entry edge 8j-1, exit edge 8j+1)`. -/
def steps_1_3_4_4_5_5_7 : List Step := [
⟨(6 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(2 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(5 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(5 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(4 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(6 : Fin 7), (39 : ℚ), (41 : ℚ)⟩, ⟨(5 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(2 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(4 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(6 : Fin 7), (47 : ℚ), (49 : ℚ)⟩, ⟨(3 : Fin 7), (31 : ℚ), (33 : ℚ)⟩
]

-- transcribed trace table: T_1_3_4_4_5_5_7_1 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_1 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_2 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_2 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_3 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_3 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_4 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_4 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_5 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_5 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_6 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_6 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_7 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_7 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_8 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_8 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_9 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_9 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 16807 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 2401 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_10 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_10 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 16807 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 2401 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_11 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_11 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 16807 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((6561 / 2401 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_12 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_12 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_13 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_13 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_14 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_14 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_15 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_15 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 8575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 1225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_16 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_16 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 8575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((2601 / 1225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_17 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_17 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 42875 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 18375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 65 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 65 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 325 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 325 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 6125 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_18 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_18 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 42875 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 18375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 65 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 65 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 325 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 325 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 6125 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_19 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_19 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 42875 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 18375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((135 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((14739 / 6125 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_20 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_20 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((135 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_21 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_21 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((135 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((75 / 11 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 33 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_22 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_22 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 67275 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 4485 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 455 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 3185 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((14739 / 2275 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((14739 / 15925 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6825 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_23 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_23 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 67275 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 4485 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 455 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 3185 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((14739 / 2275 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((14739 / 15925 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6825 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 41 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 41 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_24 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_24 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 67275 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 4485 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 455 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 3185 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((14739 / 2275 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((14739 / 15925 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6825 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((15147 / 2093 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((297 / 161 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_25 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_25 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 28175 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((54043 / 67275 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3179 / 4485 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 455 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 3185 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 47 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((297 / 329 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((1683 / 235 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((297 / 161 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 235 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_4_5_5_7_26 (the mirror run's step-end snapshot)
def T_1_3_4_4_5_5_7_26 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 155 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((119 / 465 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((7 / 31 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((51 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((14161 / 18135 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((833 / 1209 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((187 / 299 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 39 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((357 / 403 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1683 / 2093 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((459 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2601 / 455 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((9537 / 10465 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((2601 / 3185 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 455 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 47 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((11781 / 7285 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9163 / 7285 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((1617 / 1457 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((297 / 329 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((1683 / 235 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((66759 / 36425 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((155771 / 109275 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((9163 / 7285 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 235 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((357 / 155 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((833 / 465 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((49 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Add 1 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_1_1_3_4_4_5_5_7 : uAdd (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) ((1 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_1 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, u0Of, u0Tab_1_3_4_4_5_5_7] <;> norm_num) (by simp [uBack, uBackCond, u0Of, u0Tab_1_3_4_4_5_5_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, u0Of, u0Tab_1_3_4_4_5_5_7, T_1_3_4_4_5_5_7_1] <;> norm_num)

/-- Add 2 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_2_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_1 (6 : Fin 7) (0 : Fin 7) ((9 : ℚ) / (1 : ℚ)) true = some T_1_3_4_4_5_5_7_2 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_1] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_1] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_1, T_1_3_4_4_5_5_7_2] <;> norm_num)

/-- Add 3 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_3_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_2 (6 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_3 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_2] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_2, T_1_3_4_4_5_5_7_3] <;> norm_num)

/-- Add 4 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_4_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_3 (5 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_4 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_3] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_3, T_1_3_4_4_5_5_7_4] <;> norm_num)

/-- Add 5 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_5_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_4 (5 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_5 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_4] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_4, T_1_3_4_4_5_5_7_5] <;> norm_num)

/-- Add 6 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_6_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_5 (3 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_6 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_5] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_5, T_1_3_4_4_5_5_7_6] <;> norm_num)

/-- Add 7 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_7_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_6 (3 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_7 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_6] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_6, T_1_3_4_4_5_5_7_7] <;> norm_num)

/-- Add 8 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_8_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_7 (2 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_8 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_7] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_7, T_1_3_4_4_5_5_7_8] <;> norm_num)

/-- Add 9 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_9_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_8 (2 : Fin 7) (1 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_4_5_5_7_9 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_8] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_8, T_1_3_4_4_5_5_7_9] <;> norm_num)

/-- Add 10 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_10_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_9 (1 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_10 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_9] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_9, T_1_3_4_4_5_5_7_10] <;> norm_num)

/-- Add 11 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_11_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_10 (1 : Fin 7) (5 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_11 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_10] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_10] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_10, T_1_3_4_4_5_5_7_11] <;> norm_num)

/-- Add 12 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_12_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_11 (5 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T_1_3_4_4_5_5_7_12 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_11] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_11] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_11, T_1_3_4_4_5_5_7_12] <;> norm_num)

/-- Add 13 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_13_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_12 (5 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_13 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_12] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_12] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_12, T_1_3_4_4_5_5_7_13] <;> norm_num)

/-- Add 14 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_14_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_13 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_14 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_13] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_13] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_13, T_1_3_4_4_5_5_7_14] <;> norm_num)

/-- Add 15 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_15_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_14 (4 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_15 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_14] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_14] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_14, T_1_3_4_4_5_5_7_15] <;> norm_num)

/-- Add 16 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_16_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_15 (3 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_16 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_15] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_15] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_15, T_1_3_4_4_5_5_7_16] <;> norm_num)

/-- Add 17 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_17_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_16 (3 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_17 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_16] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_16] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_16, T_1_3_4_4_5_5_7_17] <;> norm_num)

/-- Add 18 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_18_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_17 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_17 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_17] <;> norm_num

/-- Add 19 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_19_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_17 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T_1_3_4_4_5_5_7_18 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_17] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_17] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_17, T_1_3_4_4_5_5_7_18] <;> norm_num)

/-- Add 20 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_20_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_18 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_18 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_18] <;> norm_num

/-- Add 21 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_21_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_18 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_3_4_4_5_5_7_19 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_18] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_18] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_18, T_1_3_4_4_5_5_7_19] <;> norm_num)

/-- Add 22 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_22_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_19 (6 : Fin 7) (5 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_3_4_4_5_5_7_19 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_19] <;> norm_num

/-- Add 23 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_23_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_19 (6 : Fin 7) (4 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T_1_3_4_4_5_5_7_20 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_19] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_19] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_19, T_1_3_4_4_5_5_7_20] <;> norm_num)

/-- Add 24 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_24_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_20 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T_1_3_4_4_5_5_7_21 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_20] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_20] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_20, T_1_3_4_4_5_5_7_21] <;> norm_num)

/-- Add 25 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_25_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_21 (4 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (15 : ℚ)) true = some T_1_3_4_4_5_5_7_21 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_21] <;> norm_num

/-- Add 26 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_26_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_21 (1 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (25 : ℚ)) true = some T_1_3_4_4_5_5_7_21 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_21] <;> norm_num

/-- Add 27 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_27_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_21 (1 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (39 : ℚ)) true = some T_1_3_4_4_5_5_7_22 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_21] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_21] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_21, T_1_3_4_4_5_5_7_22] <;> norm_num)

/-- Add 28 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_28_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_22 (6 : Fin 7) (1 : Fin 7) ((41 : ℚ) / (17 : ℚ)) true = some T_1_3_4_4_5_5_7_22 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_22] <;> norm_num

/-- Add 29 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_29_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_22 (6 : Fin 7) (5 : Fin 7) ((41 : ℚ) / (31 : ℚ)) true = some T_1_3_4_4_5_5_7_22 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_22] <;> norm_num

/-- Add 30 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_30_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_22 (5 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (41 : ℚ)) true = some T_1_3_4_4_5_5_7_23 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_22] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_22] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_22, T_1_3_4_4_5_5_7_23] <;> norm_num)

/-- Add 31 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_31_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_23 (5 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T_1_3_4_4_5_5_7_24 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_23] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_23] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_23, T_1_3_4_4_5_5_7_24] <;> norm_num)

/-- Add 32 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_32_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_24 (2 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T_1_3_4_4_5_5_7_24 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_24] <;> norm_num

/-- Add 33 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_33_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_24 (2 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_3_4_4_5_5_7_24 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_24] <;> norm_num

/-- Add 34 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_34_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_24 (4 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_3_4_4_5_5_7_24 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_24] <;> norm_num

/-- Add 35 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_35_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_24 (4 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (47 : ℚ)) true = some T_1_3_4_4_5_5_7_25 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_24] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_24] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_24, T_1_3_4_4_5_5_7_25] <;> norm_num)

/-- Add 36 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_36_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_25 (6 : Fin 7) (4 : Fin 7) ((49 : ℚ) / (33 : ℚ)) true = some T_1_3_4_4_5_5_7_25 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_25] <;> norm_num

/-- Add 37 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_37_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_25 (6 : Fin 7) (3 : Fin 7) ((49 : ℚ) / (31 : ℚ)) true = some T_1_3_4_4_5_5_7_26 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_4_5_5_7_25] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_4_5_5_7_25] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_4_5_5_7_25, T_1_3_4_4_5_5_7_26] <;> norm_num)

/-- Add 38 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_38_1_3_4_4_5_5_7 : uAdd T_1_3_4_4_5_5_7_26 (3 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (49 : ℚ)) true = some T_1_3_4_4_5_5_7_26 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_4_5_5_7_26] <;> norm_num

/-- Step 1 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_1_1_3_4_4_5_5_7 : uStep (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) (1 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_2 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_1_1_3_4_4_5_5_7) (addEq_2_1_3_4_4_5_5_7)

/-- Step 2 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_2_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_2 (6 : Fin 7) (5 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_4 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_3_1_3_4_4_5_5_7) (addEq_4_1_3_4_4_5_5_7)

/-- Step 3 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_3_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_4 (5 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_6 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_5_1_3_4_4_5_5_7) (addEq_6_1_3_4_4_5_5_7)

/-- Step 4 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_4_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_6 (3 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_8 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_7_1_3_4_4_5_5_7) (addEq_8_1_3_4_4_5_5_7)

/-- Step 5 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_5_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_8 (2 : Fin 7) (1 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_4_5_5_7_10 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_9_1_3_4_4_5_5_7) (addEq_10_1_3_4_4_5_5_7)

/-- Step 6 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_6_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_10 (1 : Fin 7) (5 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_12 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_11_1_3_4_4_5_5_7) (addEq_12_1_3_4_4_5_5_7)

/-- Step 7 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_7_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_12 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_14 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_13_1_3_4_4_5_5_7) (addEq_14_1_3_4_4_5_5_7)

/-- Step 8 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_8_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_14 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_16 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_15_1_3_4_4_5_5_7) (addEq_16_1_3_4_4_5_5_7)

/-- Step 9 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_9_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_16 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_17 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_17_1_3_4_4_5_5_7) (addEq_18_1_3_4_4_5_5_7)

/-- Step 10 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_10_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_17 (2 : Fin 7) (5 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_4_5_5_7_18 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_19_1_3_4_4_5_5_7) (addEq_20_1_3_4_4_5_5_7)

/-- Step 11 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_11_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_18 (5 : Fin 7) (6 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_4_5_5_7_19 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_21_1_3_4_4_5_5_7) (addEq_22_1_3_4_4_5_5_7)

/-- Step 12 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_12_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_19 (6 : Fin 7) (4 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_4_5_5_7_21 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_23_1_3_4_4_5_5_7) (addEq_24_1_3_4_4_5_5_7)

/-- Step 13 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_13_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_21 (4 : Fin 7) (1 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_4_5_5_7_21 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_25_1_3_4_4_5_5_7) (addEq_26_1_3_4_4_5_5_7)

/-- Step 14 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_14_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_21 (1 : Fin 7) (6 : Fin 7) (17 : ℚ) (39 : ℚ) (41 : ℚ) = some T_1_3_4_4_5_5_7_22 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_27_1_3_4_4_5_5_7) (addEq_28_1_3_4_4_5_5_7)

/-- Step 15 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_15_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_22 (6 : Fin 7) (5 : Fin 7) (41 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_4_5_5_7_23 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_29_1_3_4_4_5_5_7) (addEq_30_1_3_4_4_5_5_7)

/-- Step 16 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_16_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_23 (5 : Fin 7) (2 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_4_5_5_7_24 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_31_1_3_4_4_5_5_7) (addEq_32_1_3_4_4_5_5_7)

/-- Step 17 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_17_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_24 (2 : Fin 7) (4 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_4_5_5_7_24 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_33_1_3_4_4_5_5_7) (addEq_34_1_3_4_4_5_5_7)

/-- Step 18 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_18_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_24 (4 : Fin 7) (6 : Fin 7) (33 : ℚ) (47 : ℚ) (49 : ℚ) = some T_1_3_4_4_5_5_7_25 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_35_1_3_4_4_5_5_7) (addEq_36_1_3_4_4_5_5_7)

/-- Step 19 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_19_1_3_4_4_5_5_7 : uStep T_1_3_4_4_5_5_7_25 (6 : Fin 7) (3 : Fin 7) (49 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_4_5_5_7_26 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_37_1_3_4_4_5_5_7) (addEq_38_1_3_4_4_5_5_7)

/-- The extraction: whatever table the chain run produces from `u0Of`, it IS the last transcribed one (the per-step `stepEq` equations pin every intermediate). -/
theorem trace_1_3_4_4_5_5_7 {V : UTable} {af : Fin 7} {Af : ℚ} 
    (hrun : chainRun (u0Of (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ)) 0 1 steps_1_3_4_4_5_5_7 = some (V, af, Af)) : 
    V = T_1_3_4_4_5_5_7_26 := by
  simp only [steps_1_3_4_4_5_5_7, chainRun] at hrun
  rw [stepEq_1_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_2_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_3_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_4_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_5_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_6_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_7_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_8_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_9_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_10_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_11_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_12_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_13_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_14_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_15_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_16_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_17_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_18_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_19_1_3_4_4_5_5_7] at hrun
  simp only [Option.bind_some] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

/-- **The per-chain J-carrier datum for box ([1, 3, 4, 4, 5, 5, 7])**: `ChainDomData` at the attesting chain `steps_1_3_4_4_5_5_7` -- exactly the missing hypothesis of `Fresh.DumpDomData.capChainsRealized_of_chainDomU0` at the fixed start `(a, Aex) = (0, 1)`.  Every record's singleton cap walk is dominated by the attesting chain's closed-trace entry at its pair (final trace values: (0,6)=1/7, (1,6)=17/39, (2,6)=51/91; caps: (0,6)=1/7, (1,6)=33/70, (2,6)=825/1457). -/
def chainDom_1_3_4_4_5_5_7 : 
    ChainDomData (![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ) compFam_1_3_4_4_5_5_7 where
  steps := steps_1_3_4_4_5_5_7
  dom := by
    intro e he V af Af hrun
    have hV := trace_1_3_4_4_5_5_7 hrun
    rw [hV]
    simp only [compFam_1_3_4_4_5_5_7, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
    · exact capsDom_single ⟨(1 / 7 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact capsDom_single ⟨(17 / 39 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact capsDom_single ⟨(17 / 39 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact capsDom_single ⟨(17 / 39 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact capsDom_single ⟨(51 / 91 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact capsDom_single ⟨(51 / 91 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact capsDom_single ⟨(51 / 91 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact capsDom_single ⟨(51 / 91 : ℚ), true, by simp [T_1_3_4_4_5_5_7_26], by norm_num⟩
    · exact absurd h0 (by simp)

#print axioms trace_1_3_4_4_5_5_7
#print axioms chainDom_1_3_4_4_5_5_7

/-- The attesting chain for box ([1, 3, 4, 5, 6, 6, 7]) as `Fresh.UClosure.Step` literals (chain index 0 of the box's dump enumeration, word length 19): each step is the zone triple `(b, Bn, Ax)` = `(row, entry edge 8j-1, exit edge 8j+1)`. -/
def steps_1_3_4_5_6_6_7 : List Step := [
⟨(6 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(4 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(2 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(6 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(6 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(5 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(3 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(5 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(3 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(6 : Fin 7), (47 : ℚ), (49 : ℚ)⟩, ⟨(4 : Fin 7), (39 : ℚ), (41 : ℚ)⟩
]

-- transcribed trace table: T_1_3_4_5_6_6_7_1 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_1 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_2 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_2 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_3 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_3 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_4 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_4 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_5 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_5 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_6 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_6 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_7 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_7 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_8 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_8 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_9 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_9 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_10 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_10 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((119 / 117 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_11 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_11 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((63 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((119 / 117 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7 / 13 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4131 / 1715 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_12 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_12 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 17 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((729 / 833 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 119 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 17 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4131 / 1715 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_13 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_13 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1715 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((729 / 1225 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4131 / 1715 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_14 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_14 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1715 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((1377 / 161 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2601 / 1127 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_15 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_15 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1715 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((1377 / 161 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2601 / 1127 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3825 / 3703 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_16 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_16 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 1715 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((1377 / 161 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2601 / 1127 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3825 / 3703 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_17 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_17 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 483 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((1377 / 161 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2601 / 1127 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3825 / 3703 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 69 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_18 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_18 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 483 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((1377 / 161 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((2601 / 1127 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3825 / 3703 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 69 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_19 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_19 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 483 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((15 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((135 / 17 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((15 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((25 / 17 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((375 / 391 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((15 / 17 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 69 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_20 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_20 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 483 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 245 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((7225 / 4991 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4335 / 4991 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((10625 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((425 / 217 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((3125 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((255 / 217 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 713 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((36125 / 14973 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((7225 / 4991 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2139 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 69 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_21 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_21 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 483 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((7225 / 4991 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((14025 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((10625 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((425 / 217 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((3125 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((825 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 713 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((36125 / 14973 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2139 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 69 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_22 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_22 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 483 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((7225 / 4991 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((14025 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((10625 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((425 / 217 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((3125 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((825 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((5049 / 575 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((9537 / 4025 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 25 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((561 / 575 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 69 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_23 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_23 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 483 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((459 / 115 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((459 / 805 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((255 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((51 / 115 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((14025 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((10625 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((935 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((1375 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((3125 / 2139 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((825 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((5049 / 575 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((5 / 3 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 25 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 69 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((561 / 575 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((125 / 69 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_24 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_24 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 3703 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((65025 / 16399 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((180625 / 377177 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7225 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((14025 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((10625 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((935 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((1375 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((825 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((143055 / 16399 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 25 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 2645 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15895 / 16399 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 529 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_25 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_25 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 3703 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((23375 / 114793 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((65025 / 16399 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 529 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((180625 / 377177 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((7225 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((10625 / 16399 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 23 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((935 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((153 / 161 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((425 / 529 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((1375 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((584375 / 508369 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((143055 / 16399 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((935 / 713 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 2645 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((15895 / 16399 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 529 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_26 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_26 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 3703 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((23375 / 114793 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((126225 / 33511 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((126225 / 234577 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((350625 / 770753 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((14025 / 33511 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((7425 / 1457 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((45375 / 33511 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((7425 / 10199 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((20625 / 33511 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((825 / 1457 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 47 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((1815 / 1081 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((30855 / 24863 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((297 / 329 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((825 / 1081 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((1375 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((584375 / 508369 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((277695 / 33511 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((935 / 713 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((277695 / 234577 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((30855 / 33511 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 529 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_3_4_5_6_6_7_27 (the mirror run's step-end snapshot)
def T_1_3_4_5_6_6_7_27 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 3703 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((23375 / 114793 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((7 / 39 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((126225 / 33511 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((229075 / 435643 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((350625 / 770753 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((14025 / 33511 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((7425 / 1457 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((45375 / 33511 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((13475 / 18941 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((20625 / 33511 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((825 / 1457 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 47 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((1815 / 1081 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((30855 / 24863 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((539 / 611 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((825 / 1081 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((1375 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((584375 / 508369 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 713 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((277695 / 33511 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((11 / 5 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((935 / 713 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((503965 / 435643 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((30855 / 33511 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((55 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((935 / 529 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((23375 / 16399 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((49 / 39 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Add 1 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_1_1_3_4_5_6_6_7 : uAdd (u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) ((1 : ℚ) / (7 : ℚ)) true = some T_1_3_4_5_6_6_7_1 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, u0Of, u0Tab_1_3_4_5_6_6_7] <;> norm_num) (by simp [uBack, uBackCond, u0Of, u0Tab_1_3_4_5_6_6_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, u0Of, u0Tab_1_3_4_5_6_6_7, T_1_3_4_5_6_6_7_1] <;> norm_num)

/-- Add 2 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_2_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_1 (6 : Fin 7) (0 : Fin 7) ((9 : ℚ) / (1 : ℚ)) true = some T_1_3_4_5_6_6_7_2 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_1] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_1] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_1, T_1_3_4_5_6_6_7_2] <;> norm_num)

/-- Add 3 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_3_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_2 (6 : Fin 7) (4 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_5_6_6_7_3 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_2] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_2, T_1_3_4_5_6_6_7_3] <;> norm_num)

/-- Add 4 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_4_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_3 (4 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_5_6_6_7_4 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_3] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_3, T_1_3_4_5_6_6_7_4] <;> norm_num)

/-- Add 5 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_5_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_4 (4 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_5_6_6_7_5 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_4] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_4, T_1_3_4_5_6_6_7_5] <;> norm_num)

/-- Add 6 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_6_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_5 (3 : Fin 7) (4 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_5_6_6_7_6 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_5] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_5, T_1_3_4_5_6_6_7_6] <;> norm_num)

/-- Add 7 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_7_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_6 (3 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_3_4_5_6_6_7_7 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_6] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_6, T_1_3_4_5_6_6_7_7] <;> norm_num)

/-- Add 8 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_8_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_7 (2 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_3_4_5_6_6_7_8 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_7] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_7, T_1_3_4_5_6_6_7_8] <;> norm_num)

/-- Add 9 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_9_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_8 (2 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T_1_3_4_5_6_6_7_9 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_8] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_8, T_1_3_4_5_6_6_7_9] <;> norm_num)

/-- Add 10 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_10_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_9 (6 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T_1_3_4_5_6_6_7_10 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_9] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_9, T_1_3_4_5_6_6_7_10] <;> norm_num)

/-- Add 11 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_11_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_10 (6 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (7 : ℚ)) true = some T_1_3_4_5_6_6_7_11 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_10] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_10] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_10, T_1_3_4_5_6_6_7_11] <;> norm_num)

/-- Add 12 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_12_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_11 (1 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (17 : ℚ)) true = some T_1_3_4_5_6_6_7_12 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_11] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_11] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_11, T_1_3_4_5_6_6_7_12] <;> norm_num)

/-- Add 13 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_13_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_12 (1 : Fin 7) (3 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T_1_3_4_5_6_6_7_13 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_12] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_12] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_12, T_1_3_4_5_6_6_7_13] <;> norm_num)

/-- Add 14 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_14_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_13 (3 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T_1_3_4_5_6_6_7_13 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_13] <;> norm_num

/-- Add 15 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_15_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_13 (3 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T_1_3_4_5_6_6_7_14 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_13] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_13] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_13, T_1_3_4_5_6_6_7_14] <;> norm_num)

/-- Add 16 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_16_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_14 (6 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T_1_3_4_5_6_6_7_14 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_14] <;> norm_num

/-- Add 17 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_17_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_14 (6 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (23 : ℚ)) true = some T_1_3_4_5_6_6_7_15 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_14] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_14] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_14, T_1_3_4_5_6_6_7_15] <;> norm_num)

/-- Add 18 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_18_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_15 (5 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (25 : ℚ)) true = some T_1_3_4_5_6_6_7_16 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_15] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_15] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_15, T_1_3_4_5_6_6_7_16] <;> norm_num)

/-- Add 19 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_19_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_16 (5 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (15 : ℚ)) true = some T_1_3_4_5_6_6_7_17 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_16] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_16] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_16, T_1_3_4_5_6_6_7_17] <;> norm_num)

/-- Add 20 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_20_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_17 (2 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (25 : ℚ)) true = some T_1_3_4_5_6_6_7_17 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_17] <;> norm_num

/-- Add 21 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_21_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_17 (2 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T_1_3_4_5_6_6_7_18 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_17] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_17] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_17, T_1_3_4_5_6_6_7_18] <;> norm_num)

/-- Add 22 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_22_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_18 (4 : Fin 7) (2 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T_1_3_4_5_6_6_7_19 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_18] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_18] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_18, T_1_3_4_5_6_6_7_19] <;> norm_num)

/-- Add 23 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_23_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_19 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_3_4_5_6_6_7_20 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_19] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_19] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_19, T_1_3_4_5_6_6_7_20] <;> norm_num)

/-- Add 24 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_24_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_20 (6 : Fin 7) (4 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_3_4_5_6_6_7_20 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_20] <;> norm_num

/-- Add 25 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_25_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_20 (6 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T_1_3_4_5_6_6_7_21 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_20] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_20] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_20, T_1_3_4_5_6_6_7_21] <;> norm_num)

/-- Add 26 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_26_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_21 (3 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T_1_3_4_5_6_6_7_21 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_21] <;> norm_num

/-- Add 27 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_27_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_21 (3 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_3_4_5_6_6_7_21 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_21] <;> norm_num

/-- Add 28 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_28_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_21 (5 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_3_4_5_6_6_7_22 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_21] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_21] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_21, T_1_3_4_5_6_6_7_22] <;> norm_num)

/-- Add 29 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_29_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_22 (5 : Fin 7) (1 : Fin 7) ((33 : ℚ) / (15 : ℚ)) true = some T_1_3_4_5_6_6_7_23 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_22] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_22] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_22, T_1_3_4_5_6_6_7_23] <;> norm_num)

/-- Add 30 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_30_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_23 (1 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (33 : ℚ)) true = some T_1_3_4_5_6_6_7_23 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_23] <;> norm_num

/-- Add 31 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_31_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_23 (1 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T_1_3_4_5_6_6_7_24 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_23] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_23] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_23, T_1_3_4_5_6_6_7_24] <;> norm_num)

/-- Add 32 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_32_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_24 (2 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T_1_3_4_5_6_6_7_24 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_24] <;> norm_num

/-- Add 33 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_33_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_24 (2 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_3_4_5_6_6_7_25 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_24] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_24] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_24, T_1_3_4_5_6_6_7_25] <;> norm_num)

/-- Add 34 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_34_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_25 (3 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_3_4_5_6_6_7_25 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_25] <;> norm_num

/-- Add 35 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_35_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_25 (3 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (47 : ℚ)) true = some T_1_3_4_5_6_6_7_26 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_25] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_25] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_25, T_1_3_4_5_6_6_7_26] <;> norm_num)

/-- Add 36 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_36_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_26 (6 : Fin 7) (3 : Fin 7) ((49 : ℚ) / (33 : ℚ)) true = some T_1_3_4_5_6_6_7_26 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_26] <;> norm_num

/-- Add 37 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_37_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_26 (6 : Fin 7) (4 : Fin 7) ((49 : ℚ) / (39 : ℚ)) true = some T_1_3_4_5_6_6_7_27 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_3_4_5_6_6_7_26] <;> norm_num) (by simp [uBack, uBackCond, T_1_3_4_5_6_6_7_26] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_3_4_5_6_6_7_26, T_1_3_4_5_6_6_7_27] <;> norm_num)

/-- Add 38 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_38_1_3_4_5_6_6_7 : uAdd T_1_3_4_5_6_6_7_27 (4 : Fin 7) (6 : Fin 7) ((41 : ℚ) / (49 : ℚ)) true = some T_1_3_4_5_6_6_7_27 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_3_4_5_6_6_7_27] <;> norm_num

/-- Step 1 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_1_1_3_4_5_6_6_7 : uStep (u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) (1 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_5_6_6_7_2 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_1_1_3_4_5_6_6_7) (addEq_2_1_3_4_5_6_6_7)

/-- Step 2 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_2_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_2 (6 : Fin 7) (4 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_5_6_6_7_4 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_3_1_3_4_5_6_6_7) (addEq_4_1_3_4_5_6_6_7)

/-- Step 3 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_3_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_4 (4 : Fin 7) (3 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_5_6_6_7_6 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_5_1_3_4_5_6_6_7) (addEq_6_1_3_4_5_6_6_7)

/-- Step 4 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_4_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_6 (3 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_5_6_6_7_8 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_7_1_3_4_5_6_6_7) (addEq_8_1_3_4_5_6_6_7)

/-- Step 5 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_5_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_8 (2 : Fin 7) (6 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_5_6_6_7_10 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_9_1_3_4_5_6_6_7) (addEq_10_1_3_4_5_6_6_7)

/-- Step 6 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_6_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_10 (6 : Fin 7) (1 : Fin 7) (17 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_3_4_5_6_6_7_12 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_11_1_3_4_5_6_6_7) (addEq_12_1_3_4_5_6_6_7)

/-- Step 7 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_7_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_12 (1 : Fin 7) (3 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_5_6_6_7_13 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_13_1_3_4_5_6_6_7) (addEq_14_1_3_4_5_6_6_7)

/-- Step 8 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_8_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_13 (3 : Fin 7) (6 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_5_6_6_7_14 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_15_1_3_4_5_6_6_7) (addEq_16_1_3_4_5_6_6_7)

/-- Step 9 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_9_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_14 (6 : Fin 7) (5 : Fin 7) (25 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_5_6_6_7_16 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_17_1_3_4_5_6_6_7) (addEq_18_1_3_4_5_6_6_7)

/-- Step 10 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_10_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_16 (5 : Fin 7) (2 : Fin 7) (25 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_5_6_6_7_17 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_19_1_3_4_5_6_6_7) (addEq_20_1_3_4_5_6_6_7)

/-- Step 11 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_11_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_17 (2 : Fin 7) (4 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_5_6_6_7_19 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_21_1_3_4_5_6_6_7) (addEq_22_1_3_4_5_6_6_7)

/-- Step 12 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_12_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_19 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_5_6_6_7_20 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_23_1_3_4_5_6_6_7) (addEq_24_1_3_4_5_6_6_7)

/-- Step 13 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_13_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_20 (6 : Fin 7) (3 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_5_6_6_7_21 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_25_1_3_4_5_6_6_7) (addEq_26_1_3_4_5_6_6_7)

/-- Step 14 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_14_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_21 (3 : Fin 7) (5 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_5_6_6_7_22 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_27_1_3_4_5_6_6_7) (addEq_28_1_3_4_5_6_6_7)

/-- Step 15 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_15_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_22 (5 : Fin 7) (1 : Fin 7) (33 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_3_4_5_6_6_7_23 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_29_1_3_4_5_6_6_7) (addEq_30_1_3_4_5_6_6_7)

/-- Step 16 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_16_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_23 (1 : Fin 7) (2 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_3_4_5_6_6_7_24 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_31_1_3_4_5_6_6_7) (addEq_32_1_3_4_5_6_6_7)

/-- Step 17 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_17_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_24 (2 : Fin 7) (3 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_3_4_5_6_6_7_25 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_33_1_3_4_5_6_6_7) (addEq_34_1_3_4_5_6_6_7)

/-- Step 18 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_18_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_25 (3 : Fin 7) (6 : Fin 7) (33 : ℚ) (47 : ℚ) (49 : ℚ) = some T_1_3_4_5_6_6_7_26 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_35_1_3_4_5_6_6_7) (addEq_36_1_3_4_5_6_6_7)

/-- Step 19 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_19_1_3_4_5_6_6_7 : uStep T_1_3_4_5_6_6_7_26 (6 : Fin 7) (4 : Fin 7) (49 : ℚ) (39 : ℚ) (41 : ℚ) = some T_1_3_4_5_6_6_7_27 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_37_1_3_4_5_6_6_7) (addEq_38_1_3_4_5_6_6_7)

/-- The extraction: whatever table the chain run produces from `u0Of`, it IS the last transcribed one (the per-step `stepEq` equations pin every intermediate). -/
theorem trace_1_3_4_5_6_6_7 {V : UTable} {af : Fin 7} {Af : ℚ} 
    (hrun : chainRun (u0Of (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) 0 1 steps_1_3_4_5_6_6_7 = some (V, af, Af)) : 
    V = T_1_3_4_5_6_6_7_27 := by
  simp only [steps_1_3_4_5_6_6_7, chainRun] at hrun
  rw [stepEq_1_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_2_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_3_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_4_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_5_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_6_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_7_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_8_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_9_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_10_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_11_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_12_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_13_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_14_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_15_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_16_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_17_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_18_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_19_1_3_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

/-- **The per-chain J-carrier datum for box ([1, 3, 4, 5, 6, 6, 7])**: `ChainDomData` at the attesting chain `steps_1_3_4_5_6_6_7` -- exactly the missing hypothesis of `Fresh.DumpDomData.capChainsRealized_of_chainDomU0` at the fixed start `(a, Aex) = (0, 1)`.  Every record's singleton cap walk is dominated by the attesting chain's closed-trace entry at its pair (final trace values: (0,6)=1/7, (1,6)=14025/33511, (2,6)=825/1457; caps: (0,6)=1/7, (1,6)=99/235, (2,6)=363/611). -/
def chainDom_1_3_4_5_6_6_7 : 
    ChainDomData (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ) compFam_1_3_4_5_6_6_7 where
  steps := steps_1_3_4_5_6_6_7
  dom := by
    intro e he V af Af hrun
    have hV := trace_1_3_4_5_6_6_7 hrun
    rw [hV]
    simp only [compFam_1_3_4_5_6_6_7, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h0
    · exact capsDom_single ⟨(1 / 7 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact capsDom_single ⟨(14025 / 33511 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact capsDom_single ⟨(14025 / 33511 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact capsDom_single ⟨(14025 / 33511 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact capsDom_single ⟨(825 / 1457 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact capsDom_single ⟨(825 / 1457 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact capsDom_single ⟨(825 / 1457 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact capsDom_single ⟨(825 / 1457 : ℚ), true, by simp [T_1_3_4_5_6_6_7_27], by norm_num⟩
    · exact absurd h0 (by simp)

#print axioms trace_1_3_4_5_6_6_7
#print axioms chainDom_1_3_4_5_6_6_7

/-- The attesting chain for box ([1, 4, 4, 5, 6, 6, 7]) as `Fresh.UClosure.Step` literals (chain index 0 of the box's dump enumeration, word length 20): each step is the zone triple `(b, Bn, Ax)` = `(row, entry edge 8j-1, exit edge 8j+1)`. -/
def steps_1_4_4_5_6_6_7 : List Step := [
⟨(6 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(4 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(2 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(1 : Fin 7), (7 : ℚ), (9 : ℚ)⟩, ⟨(6 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(5 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(3 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(2 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(1 : Fin 7), (15 : ℚ), (17 : ℚ)⟩, ⟨(4 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(6 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(3 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(5 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(2 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(4 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(1 : Fin 7), (23 : ℚ), (25 : ℚ)⟩, ⟨(3 : Fin 7), (31 : ℚ), (33 : ℚ)⟩, ⟨(6 : Fin 7), (47 : ℚ), (49 : ℚ)⟩, ⟨(2 : Fin 7), (31 : ℚ), (33 : ℚ)⟩
]

-- transcribed trace table: T_1_4_4_5_6_6_7_1 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_1 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_2 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_2 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_3 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_3 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_4 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_4 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_5 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_5 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_6 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_6 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_7 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_7 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((729 / 637 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_8 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_8 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((81 / 13 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((9 / 13 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((729 / 91 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((81 / 91 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_9 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_9 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 2401 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((729 / 343 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_10 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_10 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_11 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_11 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_12 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_12 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 343 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 49 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_13 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_13 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1377 / 1225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_14 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_14 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_15 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_15 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 4375 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_16 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_16 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 1225 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 4375 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((2187 / 245 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((81 / 49 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((243 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((459 / 245 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_17 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_17 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 354375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 4375 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((1377 / 175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((7803 / 875 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_18 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_18 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 63 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 354375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((243 / 35 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((9 / 7 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((27 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((1377 / 175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((51 / 35 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((153 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((7803 / 875 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 175 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((867 / 875 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 2625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_19 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_19 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1419857 / 5315625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 354375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 25 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((867 / 125 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 625 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((83521 / 9375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((1419857 / 759375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_20 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_20 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1419857 / 5315625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 354375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((27 / 5 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((3 / 5 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((153 / 25 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((17 / 25 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((867 / 125 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((289 / 375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 625 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 5625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((83521 / 9375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((83521 / 84375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((1419857 / 759375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_21 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_21 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((1419857 / 5315625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 354375 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 23625 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((83521 / 96255 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((1419857 / 759375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_22 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_22 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((4913 / 713 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((83521 / 96255 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_23 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_23 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((75 / 11 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 99 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 33 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_24 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_24 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((83521 / 50625 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_25 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_25 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((4913 / 6417 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_26 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_26 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((4335 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 33 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_27 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_27 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((5625 / 961 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((625 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((4913 / 3375 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_28 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_28 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((3825 / 713 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((4913 / 5175 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 345 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 23 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((1445 / 2139 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((425 / 713 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((5625 / 961 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((625 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_29 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_29 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((159375 / 29791 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((625 / 961 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((53125 / 89373 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((5625 / 961 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((625 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((6375 / 961 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((2125 / 2883 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((225 / 31 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((255 / 31 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_30 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_30 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 12075 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 805 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 1575 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7425 / 1457 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 4371 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((935 / 1457 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((825 / 1457 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((8415 / 1457 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 4371 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((935 / 1457 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 47 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((3179 / 3525 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 235 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((1683 / 235 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 3525 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 235 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9537 / 1175 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 3525 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((3179 / 1725 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((187 / 115 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

-- transcribed trace table: T_1_4_4_5_6_6_7_31 (the mirror run's step-end snapshot)
def T_1_4_4_5_6_6_7_31 : UTable := fun p q =>
   if p = (0 : Fin 7) ∧ q = (0 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (0 : Fin 7) ∧ q = (1 : Fin 7) then some ((119 / 465 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (2 : Fin 7) then some ((7 / 31 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 161 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (4 : Fin 7) then some ((175 / 961 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 105 : ℚ), true)
  else  if p = (0 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 / 7 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (0 : Fin 7) then some ((7425 / 1457 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (1 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (1 : Fin 7) ∧ q = (2 : Fin 7) then some ((40425 / 45167 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (3 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (4 : Fin 7) then some ((1010625 / 1400177 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (5 : Fin 7) then some ((935 / 1457 : ℚ), true)
  else  if p = (1 : Fin 7) ∧ q = (6 : Fin 7) then some ((825 / 1457 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (0 : Fin 7) then some ((8415 / 1457 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (1 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (2 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (2 : Fin 7) ∧ q = (3 : Fin 7) then some ((85 / 93 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (4 : Fin 7) then some ((25 / 31 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 4371 : ℚ), true)
  else  if p = (2 : Fin 7) ∧ q = (6 : Fin 7) then some ((935 / 1457 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (0 : Fin 7) then some ((297 / 47 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (1 : Fin 7) then some ((9163 / 7285 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (2 : Fin 7) then some ((1617 / 1457 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (3 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (3 : Fin 7) ∧ q = (4 : Fin 7) then some ((40425 / 45167 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (5 : Fin 7) then some ((187 / 235 : ℚ), true)
  else  if p = (3 : Fin 7) ∧ q = (6 : Fin 7) then some ((33 / 47 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (0 : Fin 7) then some ((1683 / 235 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (1 : Fin 7) then some ((155771 / 109275 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (2 : Fin 7) then some ((9163 / 7285 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (3 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (4 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (4 : Fin 7) ∧ q = (5 : Fin 7) then some ((3179 / 3525 : ℚ), true)
  else  if p = (4 : Fin 7) ∧ q = (6 : Fin 7) then some ((187 / 235 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (0 : Fin 7) then some ((9537 / 1175 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (1 : Fin 7) then some ((2648107 / 1639125 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (2 : Fin 7) then some ((155771 / 109275 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (3 : Fin 7) then some ((289 / 225 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (4 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (5 : Fin 7) ∧ q = (5 : Fin 7) then some ((1 : ℚ), false)
  else  if p = (5 : Fin 7) ∧ q = (6 : Fin 7) then some ((3179 / 3525 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (0 : Fin 7) then some ((9 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (1 : Fin 7) then some ((833 / 465 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (2 : Fin 7) then some ((49 / 31 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (3 : Fin 7) then some ((33 / 23 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (4 : Fin 7) then some ((1225 / 961 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (5 : Fin 7) then some ((17 / 15 : ℚ), true)
  else  if p = (6 : Fin 7) ∧ q = (6 : Fin 7) then some ((1 : ℚ), false)
  else none

/-- Add 1 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_1_1_4_4_5_6_6_7 : uAdd (u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) ((1 : ℚ) / (7 : ℚ)) true = some T_1_4_4_5_6_6_7_1 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, u0Of, u0Tab_1_4_4_5_6_6_7] <;> norm_num) (by simp [uBack, uBackCond, u0Of, u0Tab_1_4_4_5_6_6_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, u0Of, u0Tab_1_4_4_5_6_6_7, T_1_4_4_5_6_6_7_1] <;> norm_num)

/-- Add 2 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_2_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_1 (6 : Fin 7) (0 : Fin 7) ((9 : ℚ) / (1 : ℚ)) true = some T_1_4_4_5_6_6_7_2 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_1] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_1] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_1, T_1_4_4_5_6_6_7_2] <;> norm_num)

/-- Add 3 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_3_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_2 (6 : Fin 7) (4 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_4_4_5_6_6_7_3 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_2] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_2] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_2, T_1_4_4_5_6_6_7_3] <;> norm_num)

/-- Add 4 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_4_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_3 (4 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_4_4_5_6_6_7_4 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_3] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_3] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_3, T_1_4_4_5_6_6_7_4] <;> norm_num)

/-- Add 5 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_5_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_4 (4 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_4_4_5_6_6_7_5 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_4] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_4] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_4, T_1_4_4_5_6_6_7_5] <;> norm_num)

/-- Add 6 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_6_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_5 (2 : Fin 7) (4 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_4_4_5_6_6_7_6 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_5] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_5] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_5, T_1_4_4_5_6_6_7_6] <;> norm_num)

/-- Add 7 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_7_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_6 (2 : Fin 7) (1 : Fin 7) ((9 : ℚ) / (7 : ℚ)) true = some T_1_4_4_5_6_6_7_7 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_6] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_6] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_6, T_1_4_4_5_6_6_7_7] <;> norm_num)

/-- Add 8 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_8_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_7 (1 : Fin 7) (2 : Fin 7) ((9 : ℚ) / (9 : ℚ)) true = some T_1_4_4_5_6_6_7_8 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_7] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_7] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_7, T_1_4_4_5_6_6_7_8] <;> norm_num)

/-- Add 9 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_9_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_8 (1 : Fin 7) (6 : Fin 7) ((9 : ℚ) / (15 : ℚ)) true = some T_1_4_4_5_6_6_7_9 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_8] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_8] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_8, T_1_4_4_5_6_6_7_9] <;> norm_num)

/-- Add 10 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_10_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_9 (6 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (9 : ℚ)) true = some T_1_4_4_5_6_6_7_10 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_9] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_9] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_9, T_1_4_4_5_6_6_7_10] <;> norm_num)

/-- Add 11 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_11_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_10 (6 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_4_4_5_6_6_7_11 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_10] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_10] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_10, T_1_4_4_5_6_6_7_11] <;> norm_num)

/-- Add 12 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_12_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_11 (5 : Fin 7) (6 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_4_4_5_6_6_7_12 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_11] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_11] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_11, T_1_4_4_5_6_6_7_12] <;> norm_num)

/-- Add 13 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_13_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_12 (5 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_4_4_5_6_6_7_13 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_12] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_12] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_12, T_1_4_4_5_6_6_7_13] <;> norm_num)

/-- Add 14 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_14_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_13 (4 : Fin 7) (5 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_4_4_5_6_6_7_14 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_13] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_13] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_13, T_1_4_4_5_6_6_7_14] <;> norm_num)

/-- Add 15 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_15_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_14 (4 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_4_4_5_6_6_7_15 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_14] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_14] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_14, T_1_4_4_5_6_6_7_15] <;> norm_num)

/-- Add 16 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_16_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_15 (3 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_4_4_5_6_6_7_16 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_15] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_15] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_15, T_1_4_4_5_6_6_7_16] <;> norm_num)

/-- Add 17 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_17_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_16 (3 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_4_4_5_6_6_7_17 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_16] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_16] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_16, T_1_4_4_5_6_6_7_17] <;> norm_num)

/-- Add 18 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_18_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_17 (2 : Fin 7) (3 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_4_4_5_6_6_7_18 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_17] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_17] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_17, T_1_4_4_5_6_6_7_18] <;> norm_num)

/-- Add 19 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_19_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_18 (2 : Fin 7) (1 : Fin 7) ((17 : ℚ) / (15 : ℚ)) true = some T_1_4_4_5_6_6_7_19 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_18] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_18] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_18, T_1_4_4_5_6_6_7_19] <;> norm_num)

/-- Add 20 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_20_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_19 (1 : Fin 7) (2 : Fin 7) ((17 : ℚ) / (17 : ℚ)) true = some T_1_4_4_5_6_6_7_19 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_19] <;> norm_num

/-- Add 21 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_21_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_19 (1 : Fin 7) (4 : Fin 7) ((17 : ℚ) / (23 : ℚ)) true = some T_1_4_4_5_6_6_7_20 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_19] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_19] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_19, T_1_4_4_5_6_6_7_20] <;> norm_num)

/-- Add 22 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_22_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_20 (4 : Fin 7) (1 : Fin 7) ((25 : ℚ) / (17 : ℚ)) true = some T_1_4_4_5_6_6_7_20 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_20] <;> norm_num

/-- Add 23 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_23_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_20 (4 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_4_4_5_6_6_7_21 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_20] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_20] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_20, T_1_4_4_5_6_6_7_21] <;> norm_num)

/-- Add 24 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_24_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_21 (6 : Fin 7) (4 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_4_4_5_6_6_7_21 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_21] <;> norm_num

/-- Add 25 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_25_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_21 (6 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T_1_4_4_5_6_6_7_22 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_21] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_21] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_21, T_1_4_4_5_6_6_7_22] <;> norm_num)

/-- Add 26 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_26_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_22 (3 : Fin 7) (6 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T_1_4_4_5_6_6_7_23 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_22] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_22] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_22, T_1_4_4_5_6_6_7_23] <;> norm_num)

/-- Add 27 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_27_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_23 (3 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_4_4_5_6_6_7_24 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_23] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_23] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_23, T_1_4_4_5_6_6_7_24] <;> norm_num)

/-- Add 28 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_28_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_24 (5 : Fin 7) (3 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_4_4_5_6_6_7_24 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_24] <;> norm_num

/-- Add 29 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_29_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_24 (5 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T_1_4_4_5_6_6_7_25 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_24] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_24] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_24, T_1_4_4_5_6_6_7_25] <;> norm_num)

/-- Add 30 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_30_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_25 (2 : Fin 7) (5 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T_1_4_4_5_6_6_7_26 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_25] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_25] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_25, T_1_4_4_5_6_6_7_26] <;> norm_num)

/-- Add 31 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_31_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_26 (2 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_4_4_5_6_6_7_27 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_26] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_26] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_26, T_1_4_4_5_6_6_7_27] <;> norm_num)

/-- Add 32 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_32_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_27 (4 : Fin 7) (2 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_4_4_5_6_6_7_27 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_27] <;> norm_num

/-- Add 33 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_33_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_27 (4 : Fin 7) (1 : Fin 7) ((33 : ℚ) / (23 : ℚ)) true = some T_1_4_4_5_6_6_7_28 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_27] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_27] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_27, T_1_4_4_5_6_6_7_28] <;> norm_num)

/-- Add 34 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_34_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_28 (1 : Fin 7) (4 : Fin 7) ((25 : ℚ) / (33 : ℚ)) true = some T_1_4_4_5_6_6_7_28 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_28] <;> norm_num

/-- Add 35 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_35_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_28 (1 : Fin 7) (3 : Fin 7) ((25 : ℚ) / (31 : ℚ)) true = some T_1_4_4_5_6_6_7_29 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_28] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_28] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_28, T_1_4_4_5_6_6_7_29] <;> norm_num)

/-- Add 36 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_36_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_29 (3 : Fin 7) (1 : Fin 7) ((33 : ℚ) / (25 : ℚ)) true = some T_1_4_4_5_6_6_7_29 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_29] <;> norm_num

/-- Add 37 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_37_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_29 (3 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (47 : ℚ)) true = some T_1_4_4_5_6_6_7_30 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_29] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_29] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_29, T_1_4_4_5_6_6_7_30] <;> norm_num)

/-- Add 38 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_38_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_30 (6 : Fin 7) (3 : Fin 7) ((49 : ℚ) / (33 : ℚ)) true = some T_1_4_4_5_6_6_7_30 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_30] <;> norm_num

/-- Add 39 of the attesting chain: keep-cur and back are ground-false and the propagated result IS the next transcribed table (49 concrete pointwise checks). -/
theorem addEq_39_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_30 (6 : Fin 7) (2 : Fin 7) ((49 : ℚ) / (31 : ℚ)) true = some T_1_4_4_5_6_6_7_31 :=
  uAdd_eq_some (by simp [uKeepCur, uBackCond, T_1_4_4_5_6_6_7_30] <;> norm_num) (by simp [uBack, uBackCond, T_1_4_4_5_6_6_7_30] <;> norm_num)
    (by intro p q; fin_cases p <;> fin_cases q <;> simp [uProp, uTighter, T_1_4_4_5_6_6_7_30, T_1_4_4_5_6_6_7_31] <;> norm_num)

/-- Add 40 of the attesting chain: the entry at its pair is already tight (`uKeepCur` fires ground-true), so the table is unchanged. -/
theorem addEq_40_1_4_4_5_6_6_7 : uAdd T_1_4_4_5_6_6_7_31 (2 : Fin 7) (6 : Fin 7) ((33 : ℚ) / (49 : ℚ)) true = some T_1_4_4_5_6_6_7_31 := by simp [uAdd, uKeepCur, uBackCond, uBack, uTighter, uProp, T_1_4_4_5_6_6_7_31] <;> norm_num

/-- Step 1 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_1_1_4_4_5_6_6_7 : uStep (u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) (0 : Fin 7) (6 : Fin 7) (1 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_4_4_5_6_6_7_2 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_1_1_4_4_5_6_6_7) (addEq_2_1_4_4_5_6_6_7)

/-- Step 2 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_2_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_2 (6 : Fin 7) (4 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_4_4_5_6_6_7_4 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_3_1_4_4_5_6_6_7) (addEq_4_1_4_4_5_6_6_7)

/-- Step 3 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_3_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_4 (4 : Fin 7) (2 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_4_4_5_6_6_7_6 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_5_1_4_4_5_6_6_7) (addEq_6_1_4_4_5_6_6_7)

/-- Step 4 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_4_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_6 (2 : Fin 7) (1 : Fin 7) (9 : ℚ) (7 : ℚ) (9 : ℚ) = some T_1_4_4_5_6_6_7_8 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_7_1_4_4_5_6_6_7) (addEq_8_1_4_4_5_6_6_7)

/-- Step 5 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_5_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_8 (1 : Fin 7) (6 : Fin 7) (9 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_4_4_5_6_6_7_10 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_9_1_4_4_5_6_6_7) (addEq_10_1_4_4_5_6_6_7)

/-- Step 6 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_6_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_10 (6 : Fin 7) (5 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_4_4_5_6_6_7_12 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_11_1_4_4_5_6_6_7) (addEq_12_1_4_4_5_6_6_7)

/-- Step 7 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_7_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_12 (5 : Fin 7) (4 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_4_4_5_6_6_7_14 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_13_1_4_4_5_6_6_7) (addEq_14_1_4_4_5_6_6_7)

/-- Step 8 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_8_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_14 (4 : Fin 7) (3 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_4_4_5_6_6_7_16 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_15_1_4_4_5_6_6_7) (addEq_16_1_4_4_5_6_6_7)

/-- Step 9 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_9_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_16 (3 : Fin 7) (2 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_4_4_5_6_6_7_18 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_17_1_4_4_5_6_6_7) (addEq_18_1_4_4_5_6_6_7)

/-- Step 10 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_10_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_18 (2 : Fin 7) (1 : Fin 7) (17 : ℚ) (15 : ℚ) (17 : ℚ) = some T_1_4_4_5_6_6_7_19 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_19_1_4_4_5_6_6_7) (addEq_20_1_4_4_5_6_6_7)

/-- Step 11 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_11_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_19 (1 : Fin 7) (4 : Fin 7) (17 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_4_4_5_6_6_7_20 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_21_1_4_4_5_6_6_7) (addEq_22_1_4_4_5_6_6_7)

/-- Step 12 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_12_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_20 (4 : Fin 7) (6 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_4_4_5_6_6_7_21 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_23_1_4_4_5_6_6_7) (addEq_24_1_4_4_5_6_6_7)

/-- Step 13 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_13_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_21 (6 : Fin 7) (3 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_4_4_5_6_6_7_23 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_25_1_4_4_5_6_6_7) (addEq_26_1_4_4_5_6_6_7)

/-- Step 14 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_14_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_23 (3 : Fin 7) (5 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_4_4_5_6_6_7_24 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_27_1_4_4_5_6_6_7) (addEq_28_1_4_4_5_6_6_7)

/-- Step 15 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_15_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_24 (5 : Fin 7) (2 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_4_4_5_6_6_7_26 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_29_1_4_4_5_6_6_7) (addEq_30_1_4_4_5_6_6_7)

/-- Step 16 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_16_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_26 (2 : Fin 7) (4 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_4_4_5_6_6_7_27 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_31_1_4_4_5_6_6_7) (addEq_32_1_4_4_5_6_6_7)

/-- Step 17 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_17_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_27 (4 : Fin 7) (1 : Fin 7) (33 : ℚ) (23 : ℚ) (25 : ℚ) = some T_1_4_4_5_6_6_7_28 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_33_1_4_4_5_6_6_7) (addEq_34_1_4_4_5_6_6_7)

/-- Step 18 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_18_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_28 (1 : Fin 7) (3 : Fin 7) (25 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_4_4_5_6_6_7_29 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_35_1_4_4_5_6_6_7) (addEq_36_1_4_4_5_6_6_7)

/-- Step 19 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_19_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_29 (3 : Fin 7) (6 : Fin 7) (33 : ℚ) (47 : ℚ) (49 : ℚ) = some T_1_4_4_5_6_6_7_30 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_37_1_4_4_5_6_6_7) (addEq_38_1_4_4_5_6_6_7)

/-- Step 20 of the attesting chain: the two adds compose through `uGt_pos`. -/
theorem stepEq_20_1_4_4_5_6_6_7 : uStep T_1_4_4_5_6_6_7_30 (6 : Fin 7) (2 : Fin 7) (49 : ℚ) (31 : ℚ) (33 : ℚ) = some T_1_4_4_5_6_6_7_31 := 
  uStep_eq_some (by norm_num) (by norm_num) (by norm_num) (addEq_39_1_4_4_5_6_6_7) (addEq_40_1_4_4_5_6_6_7)

/-- The extraction: whatever table the chain run produces from `u0Of`, it IS the last transcribed one (the per-step `stepEq` equations pin every intermediate). -/
theorem trace_1_4_4_5_6_6_7 {V : UTable} {af : Fin 7} {Af : ℚ} 
    (hrun : chainRun (u0Of (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)) 0 1 steps_1_4_4_5_6_6_7 = some (V, af, Af)) : 
    V = T_1_4_4_5_6_6_7_31 := by
  simp only [steps_1_4_4_5_6_6_7, chainRun] at hrun
  rw [stepEq_1_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_2_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_3_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_4_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_5_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_6_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_7_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_8_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_9_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_10_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_11_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_12_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_13_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_14_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_15_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_16_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_17_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_18_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_19_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  rw [stepEq_20_1_4_4_5_6_6_7] at hrun
  simp only [Option.bind_some] at hrun
  simp only [Option.some.injEq, Prod.mk.injEq] at hrun
  exact hrun.1.symm

/-- **The per-chain J-carrier datum for box ([1, 4, 4, 5, 6, 6, 7])**: `ChainDomData` at the attesting chain `steps_1_4_4_5_6_6_7` -- exactly the missing hypothesis of `Fresh.DumpDomData.capChainsRealized_of_chainDomU0` at the fixed start `(a, Aex) = (0, 1)`.  Every record's singleton cap walk is dominated by the attesting chain's closed-trace entry at its pair (final trace values: (0,6)=1/7, (1,6)=825/1457; caps: (0,6)=1/7, (1,6)=3179/5499). -/
def chainDom_1_4_4_5_6_6_7 : 
    ChainDomData (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ) compFam_1_4_4_5_6_6_7 where
  steps := steps_1_4_4_5_6_6_7
  dom := by
    intro e he V af Af hrun
    have hV := trace_1_4_4_5_6_6_7 hrun
    rw [hV]
    simp only [compFam_1_4_4_5_6_6_7, List.mem_cons] at he
    rcases he with rfl | rfl | rfl | rfl | h0
    · exact capsDom_single ⟨(1 / 7 : ℚ), true, by simp [T_1_4_4_5_6_6_7_31], by norm_num⟩
    · exact capsDom_single ⟨(825 / 1457 : ℚ), true, by simp [T_1_4_4_5_6_6_7_31], by norm_num⟩
    · exact capsDom_single ⟨(825 / 1457 : ℚ), true, by simp [T_1_4_4_5_6_6_7_31], by norm_num⟩
    · exact capsDom_single ⟨(825 / 1457 : ℚ), true, by simp [T_1_4_4_5_6_6_7_31], by norm_num⟩
    · exact absurd h0 (by simp)

#print axioms trace_1_4_4_5_6_6_7
#print axioms chainDom_1_4_4_5_6_6_7

/-- The covered set: the 3 strict boxes carrying the datum. -/
def chainDomBoxes : Finset (Fin 7 → ℤ) :=
  {(![1, 3, 4, 4, 5, 5, 7] : Fin 7 → ℤ), (![1, 3, 4, 5, 6, 6, 7] : Fin 7 → ℤ), (![1, 4, 4, 5, 6, 6, 7] : Fin 7 → ℤ)}

/-- **The total over the covered set** — the per-box instances are the `chainDom_<box>`
defs above; the dispatch is done in `Fresh/SpineTotalProof.lean`'s `by_cases` walk
(matching the Type-valued nature of `ChainDomData`). The 8 residual strict boxes are
the documented rule-22 gap. -/
-- The three defs above ARE the per-box data; no total theorem needed
-- (the consumer dispatches via by_cases, not rcases).

end Fresh.ChainDomData
