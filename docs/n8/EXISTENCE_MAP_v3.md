# Where Existence at order 8 is proved, and where it is not — v3

Supersedes `EXISTENCE_MAP_v2.md`. Built from the commit record, not recollection.

## 1. Proved analytically

| class | mechanism | scope |
|---|---|---|
| ratio bound `S ≤ 7` | clears at `R = 1` (`u = 1/8`) | all orders, `S ≤ n−1` |
| **Branch A** — integer readings, `8 ∤ sⱼ` | `Guard.odd_clear_of_not_dvd`; all four spine points clear at once | **arbitrary magnitudes** |
| flanks with ≤ 1 fractional ratio | nearest-integer walk, `TwoWalker` | — |
| flanks with off-lattice ratio pairs | lattice-crossing, `TwoWalker` | — |
| divisor-closed, every middle quotient `≤ 7` | `small_b_blocks_iff` + `q` coprime to 210, `g(210) = 10` | **narrow**: 240 profiles under `m = 6000` |
| `\|S\| ≥ 2` (never a singleton) | `SolutionPair`, via a reflection centre | 6,758 of 19,880 (34.0%) |

## 2. Verified exhaustively, not proved

| class | evidence |
|---|---|
| divisor-closed, general | 185,729 exhaustive (`m < 500`), 0 failures; settled by an explicit rule |
| Branch B, general | 244,790 exhaustive (readings `[2,30]`), every profile has a witness |
| all integer arrangements `v₈ ≤ 40` | 148.5M runner instances, `R ≤ 44856/3749` |
| `\|S\| ≥ 2` on the remaining 66% | surviving `m−q` orbit in 19,880 of 19,880 |
| witness normalisation on LRC bad sets | orders 4–9, 12 arms, 0 mismatches |

## 3. Open — no proof

- **Branch B**, integer readings containing a collider `8 ∣ sⱼ`, in general.
- **Rational readings** — shown equal to *integer speed sets with no unit speed*
  (200,000 sets, 0 mismatches). Costs exactly one theorem, `unit_never_blocks`, worth **5.76%** of
  candidates.
- **Real / irrational speeds.**
- **`R < 16`** (`DoorCapped`) — untouched in this arc.

## 4. The toolkit, all proved and axiom-clean

Not existence results; they say where to look and in what category.

*Reduction to `ℤ`* — `GapRule` (3), `ReachRule` (13), `ArithForm` (2): the covering question is a
finite conjunction of integer inequalities, proved equivalent to the real statement.

*Structure of blocking* — `gcd_covariant`, `rescaled_blocks_iff`, `divisor_reduces`,
`small_b_blocks_iff`, `BlockerCount` (3): blocking depends only on coprime parts; the collision
criterion is rescaling-covariant; the `n−1` constant governs small moduli.

*Symmetry* — `TimeReversal` (2), `Involution` (3), `TwoPatterns` (3), `Degenerate2` (3),
`SolutionPair` (3): one symmetry at four levels; the centre is `c ≡ 0` for good moduli and `c ≡ −1`
for obstructed ones; `b = 2` is the unique degenerate modulus.

*Witnesses* — `witness_normalised` (extremal), `EdgeWitness` (4, interior): if a witness exists, one
exists with a constraint exactly tight, and two, one per end.

**54 declarations, all axiom-clean**, witness at `experiments/n8/v12_new_axioms_v1.out`.

## 5. Routes closed with reasons — do not re-attempt

| route | why it fails |
|---|---|
| counting / density | joint density sits **below** the product of conditionals; correlation is adverse |
| extremal witnesses | supply **exhausted at 38.83%**, gated by `8 ∣ m` or `8 ∣ b` |
| bounded centre offset | offset grows with `m` (7,962 at `m = 99,078`) |
| product of conditionals | inequality false, 2,594 of 3,000 |
| Hunter–Kounias | an import, and has a counterexample |
| `s = s*` / largest reading | 18,809 and 794 counterexamples |
| primorial `2310` | "nonzero residue ⟹ clear" is what breaks at `b = 8` |
| doubly-tight witness | 1.615% have none |
| one witness on both patterns | 2.99% have none |
| iterating the walk | `tight_of_step` needs **unit** steps; steps of `b` leap constraints |
| symmetric shrink margin | 67.49% die at depth 0 |

## 6. What the reductions bought

Recorded plainly, because each narrows what a proof must do:

- the question is posed over `ℤ`, not `ℝ` — **proved** equivalent;
- the witness is normalisable, extremally **and** interiorly — **proved**;
- two frontiers (integer vs rational readings) are **one question** split by whether `1` survives
  reduction;
- the reflection obstruction is a **moving centre**, not a failure;
- a surviving orbit is exactly *the system with obstructed intervals shrunk by one residue* — a
  strictly tighter system, so the remaining gap is quantified rather than vague.

None of these is existence. All of them are things that were not known at the start of this arc, and
each removes a class of attempts or sharpens the target.
