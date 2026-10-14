# `B ∩ I_A ≠ ∅` — what is true, what is false, and where the content sits

2026-09-07. Continues `ESCAPE_COVERAGE_v3.md`, which named `B ∩ I_A ≠ ∅` as the target.
Scripts: `experiments/n8/bcap_{slack_v1,slack_v2,bound_v1,run_theorem_v1}.py`. Exact
integers and `Fraction` only; no float anywhere in any of the four, reporting included.

## 1. Retraction — the target as I stated it is false

`ESCAPE_COVERAGE_v3.md` §4 named the target as *"prove `B ∩ I_A ≠ ∅` for the §§10–11
configurations"*, unrestricted. **That statement is false.** Over 7 077 hard-case tuples at
speeds `≤ 16`, `min |B ∩ I_A| = 0`, attained at exactly one tuple per arm:

| arm | `T` | `n L_A` | `\|B\|` | `\|I_A\|` |
|---|---|---|---|---|
| 10.1 | `{1,4,5,6,7,11,13}` | 8 | 2 | 6 |
| 11.1 | `{1,2,3,4,5,7,12}` | 32 | 10 | 18 |

Those are precisely **the two non-AP tight instances** of `TIGHT_INSTANCES_v1.md` — the
`M(T) = 1/8` extremals. Both are covered by Lemma 5.2-D instead, which is why the coverage
run still reported residual 0; the two facts are consistent, and v3's coverage figures stand.

## 2. What survives, and it is the useful form  `[EMPIRICAL — 0 violations, 7 077 tuples]`

> **Claim A.** `B ∩ I_A = ∅` ⟹ **no speed of `T` is divisible by `n = 8`.**

Zero violations over all 7 077 hard-case tuples at speeds `≤ 16` — including the 4 900 that
*do* carry a multiple of 8. Equivalently:

> **Conjecture C.** If some speed of `T` is divisible by `8`, then `B ∩ I_A ≠ ∅`.

**This is worth having because its complement is a one-liner we already own.** If *no* speed
is divisible by 8 then `‖v·(r/8)‖ = |vr mod 8|/8 ≥ 1/8` for every `r` coprime to 8, so
`t = r/8` is a witness — the `q = 8` rung of the witness ladder, equivalently Lemma 5.2-D at
`v₁ = 1`, equivalently Theorem 5.2-SR. **So LRC(8) follows from Conjecture C**, and the
split is exactly the one `TIGHT_INSTANCES_v1.md` §6 reached from the other direction: every
tight instance sits in the one-line case.

## 3. Two candidate strengthenings, both killed

**Quantitative bound — FALSE.** The two extremal `5.2-D`-failing cases have
`|B ∩ I_A| = L_A` exactly (`2` with `L_A = 2`; `4` with `L_A = 4`; density `1/8` each),
which suggested `|B ∩ I_A| ≥ L_A` whenever `8` divides some speed. **384 violations** at
speeds `≤ 16`, worst margin `−494` at `T = {1,2,3,4,5,6,16}` (`|B ∩ I_A| = 22`,
`L_A = 24`). Over-generalised from two points; the check caught it.

**Run-length theorem — PROVED, sound, and nearly vacuous.**

> Let `R` be the largest cyclic run of consecutive indices in the complement of `I_A`. Each
> `α₀ ∈ I_G` contributes to `B` a block of at least `⌊(L_A p − 1)/L_G⌋ + 1` consecutive
> `β`-values, so if `⌊(L_A p − 1)/L_G⌋ ≥ R` then `B ∩ I_A ≠ ∅`.  `[PROVED]`

Verified sound: **0 over-claims** — it never fires on a tuple whose intersection is empty.
For the 10.1 arm `R = 2` always (the complement is `β mod 8 ∈ {0,7}`, runs of exactly 2), so
the condition reads `V ≥ 2L_G + 1`. It fires **0 of 1 828** times on that arm and **2 of
5 249** on the other.

**Why, and this is the useful diagnosis.** `L_G = lcm(v₁..v₆)` is an lcm of six speeds and
dwarfs `L_A p = V ≤ 7v₆`. So `⌊(L_A p − 1)/L_G⌋ = 0`: **every band is thinner than one
`β`-cell.** `B` is not a union of wide intervals; it is essentially the image of

    α₀  ↦  ⌊ L_A · (α₀ p mod n L_G) / L_G ⌋ ,      α₀ ∈ I_G,

a set of `≈ |I_G|` near-points. Its size comes from having **many** bands, not wide ones, so
any argument that thickens a single band cannot work. Run-length is the wrong handle.

## 4. Where the content actually sits

`B ∩ I_A ≠ ∅` is an **equidistribution** statement: does a structured set `I_G` of density
`μ(G) ≈ (3/4)⁶ ≈ 0.18`, pushed through multiplication by `p` and rescaled from `Z/(nL_G)`
into `Z/(nL_A)`, meet a set `I_A` of density `μ(A) = 3/4`? Generically it must — missing
entirely needs every one of `|I_G|` images to land in a quarter-density complement. The
failures are adversarial alignments, and the data say they occur **only** at tight
instances, which the ladder already settles.

So the next object is not a bound on `|B|`, but: **why does a multiple of 8 among the speeds
prevent the alignment?** That is Conjecture C, and it is now the single statement standing
between our own machinery and an analytic `n = 8`.

## 5. Ledger

`n = 8` is not proved. Decided cells 2 of 135 (unchanged; different line). Retracted: v3
§4's unrestricted target. Established: Claim A / Conjecture C at speeds `≤ 16`; the
run-length theorem (proved, sound, near-vacuous); the falsity of `|B ∩ I_A| ≥ L_A`; and that
LRC(8) follows from Conjecture C.
