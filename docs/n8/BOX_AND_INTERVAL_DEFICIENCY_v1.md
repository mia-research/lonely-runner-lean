# The box check, settled — and the interval-deficiency theorem that replaces the phase sweep

2026-09-08. Continues `QUOTIENT_TRANSLATE_ENGINE_v1.md` §5–§6. Script
`experiments/n8/box_and_deficiency_v1.py`. Exact `Fraction` on every decision path; float
appears only as a rejection pre-filter in §1 and **every survivor is re-decided exactly**.

## 1. The box check — the answer is that the class is empty  `[PROVED — exhaustive]`

The question left open was whether the sign-range box `a_j ∈ (j−1, j+1)` survives on the
**residual class**: tuples carrying a multiple of 8, which is what the witness ladder
leaves. Rather than test the box, enumerate the objects it would apply to.

`M(T) ≥ 1/8` always, since LRC(8) is true; so **tight** (`M(T) = 1/8`) is equivalent to
*the closed bad sets `[(8k−1)/8v, (8k+1)/8v]` cover `[0,1]`*, which is an exact interval
computation. Candidates are filtered by `gcd(T) = 1` and the witness ladder (for each
`q ∈ {2,…,7}` some speed is divisible by `q`, else `t = 1/q` gives `M ≥ 1/q > 1/8`).

Exhaustive over speeds `≤ 44`: **12 743 536** candidates, **3** tight instances, and
**none** of them carries a multiple of 8. (Same three at `≤ 26`, from 197 294 candidates.)

**The float pre-filter is provably sound, not merely tolerated.** Every interval endpoint
is `(8k±1)/(8v)`, so any gap between consecutive bad intervals is
`[v(8k'−1) − v'(8k+1)] / (8vv')` — an integer over `8vv'`. A **nonzero** gap is therefore
at least `1/(8·43·44) = 1/15136 ≈ 6.6×10⁻⁵`, five orders above the `10⁻⁹` tolerance, while
a tight instance has gap exactly `0`. So the filter rejects exactly the non-tight tuples and
cannot discard a tight one; the survivors are re-decided exactly regardless.

| tight instance | `a_i = 7e_i/e_7` | box `a_j ∈ (j−1,j+1)`, `j=2..6` |
|---|---|---|
| `{1,2,3,4,5,6,7}` | `(1,2,3,4,5,6,7)` | holds |
| `{1,2,3,4,5,7,12}` | `(7/12, 7/6, 7/4, 7/3, 35/12, 49/12, 7)` | **fails at `j = 3,4,5,6`** |
| `{1,4,5,6,7,11,13}` | `(7/13, 28/13, 35/13, 42/13, 49/13, 77/13, 7)` | **fails at `j = 5`** |

This reproduces `TIGHT_INSTANCES_v1.md` §5's table independently, and it answers the
question posed there:

> **On the residual class the box question is vacuous — there is nothing in the class.**
> No tight instance at `n = 8` carries a multiple of 8, exhaustively over speeds `≤ 44`.

`TIGHT_INSTANCES_v2.md` §1 has the same conclusion over the narrower with-8 candidate set
to `≤ 34`, and `HALVING_AND_TIGHT_WITNESS_v1.md` §4 reached `≤ 44` for the residual class
with a float first stage. This is the **wider** set — all tight instances, no divisibility
restriction — carried to `≤ 44` with the pre-filter's soundness proved above, and it gives
the box its answer directly rather than by inheritance.

**Closure grade.** Object: the global sign-range box at `n = 8`. Observable: the `a`-vector
of an extremal configuration. Power: exhaustive over speeds `≤ 44`, exact (sound pre-filter). Scope: that
range — one-sided, as always: a tight instance above 44 would not have been seen. **The box is false as stated** — two explicit counterexamples, not a null — and on
the class where it might have been repaired there is nothing to repair it against. So the
`2^5` sign-class decomposition has no `n = 8` analogue to run on. A *per-cycle* form is
not excluded; it is simply unconstrained by any object now in evidence. This is a scoped
refutation of a specific statement, not a claim that the `W_ref` route is closed.

## 2. Why the phase sweep is the wrong object, and what replaces it

`QUOTIENT_TRANSLATE_ENGINE_v1.md` §5 named the next object as an averaging inequality over
the phase sweep of `σ₀`. Working it out, that route is **dominated**: averaging `|K_v|` over
an interval reproduces exactly the plain measure bound `Σ_v |A_v ∩ G_H| < |G_H|`, which is
the `7/4` slack that defeats every counting argument here. The translates and the modulus
`q` were doing no work in it.

What does work is the same interval, used with the **component** structure instead of the
measure — the step that already made TOP_GAP work, generalised off the top of the tuple.

**Theorem (interval deficiency).** `[PROVED, given LRC(7)]`
*Let `T` be 7 distinct positive integers, `H ⊆ T` any subset with `h = |H| ≤ 6`, and
`L = T \ H`. Put*

    η = (1/(h+1) − 1/8)/max(H),      ℓ = 2η.

*Then `T` has the LR property whenever*

    Σ_{v ∈ L}  (⌊ℓ v⌋ + 1) / (4v)   <   ℓ.

*Proof.* `LRC(h+1)` gives `t₀` with `‖v t₀‖ ≥ 1/(h+1)` for all `v ∈ H`. For `|δ| ≤ η`,
`‖v(t₀+δ)‖ ≥ 1/(h+1) − η·max(H) = 1/8`, so `J = [t₀−η, t₀+η]` is good for every `v ∈ H`.
The bad set of `v ∈ L` has components of length `1/(4v)` at period `1/v`, so `J` meets at
most `⌊ℓv⌋+1` of them and `|A_v ∩ J| ≤ (⌊ℓv⌋+1)/(4v)`. If the sum is `< ℓ = |J|` the
`L`-speeds cannot cover `J`, and any uncovered point of `J` is lonely for all of `T`. ∎

`H` is an **arbitrary** subset. Taking `H` = the six smallest and dropping the floor term
returns `1/(4v₇) < 1/(28v₆)`, i.e. `v₇ > 7v₆` — **TOP_GAP exactly**. The cases `|L| ≥ 2`
are new.

**The single-gap ladder** (`H` = the `7−k` smallest, floor terms dropped):

| `\|L\|` | condition ⟹ LR property | `ℓ` |
|---|---|---|
| 1 | `1/v₇ < 1/(7v₆)` — i.e. `v₇ > 7v₆` | `1/(28 v₆)` |
| 2 | `1/v₆ + 1/v₇ < 1/(3 v₅)` | `1/(12 v₅)` |
| 3 | `1/v₅ + 1/v₆ + 1/v₇ < 3/(5 v₄)` | `3/(20 v₄)` |
| 4 | `Σ_{i≥4} 1/v_i < 1/v₃` | `1/(4 v₃)` |

`|L| ≥ 4` effectively never fires: four terms each at least `1/(4v)` already exhaust `ℓ`.

## 3. Relation to the lacunary literature — a different hypothesis

Rosenfeld §8 surveys the lacunary results: Ruzsa–Tuza–Voigt, Pandey `2(k+1)/(k−1)`,
Barajas–Serra `2`, Dubickas `1 + 8e log k/k`, Czerwiński, and his own Corollary 10 giving
`1 + 3e log(k+1)/(k+1)` — for `k = 7`, a ratio of `8^{3e/8} ≈ 8.4`. **All of them require
`v_{j+1}/v_j` to be large for _every_ `j`.** `[CITED — read from the PDF]`

The ladder above requires **one** gap, at one position, with the rest of the tuple
arbitrary. The two hypotheses are incomparable: Barajas–Serra's all-ratios-`≥2` does not
imply `v₇ > 7v₆`, and `v₇ > 7v₆` says nothing about the other six ratios. The `|L| = 1` row
is elementary and may well be known; `TOP_GAP_v1.md` §2 already carries that caveat and it
is inherited here for the whole ladder.

## 4. Verification  `[PROVED — exact, end-to-end]`

Every firing case builds the witness and checks it against all seven speeds exactly.

| test | result |
|---|---|
| `|L|=1`, `{1,2,3,4,5,6,43}` | fires, `ℓ=1/168`, budget `1/172`; `t = 595/4128`, `min‖vt‖ = 93/688` ✓ |
| `|L|=1`, `{1,2,3,4,5,6,42}` (`v₇ = 7v₆` exactly) | **does not fire** — the boundary control |
| `|L|=2`, `{1,2,3,4,5,61,401}` | fires; `t = 3821/24060` ✓ |
| `|L|=3`, `{1,2,3,4,41,97,601}` | fires; `t = 219/1202` ✓ |
| random one-gap tuples, `|L|=1` | fired 1747/3000, **1747** witnesses verified |
| random one-gap tuples, `|L|=2` | fired 2451/3000, **2451** verified |
| random one-gap tuples, `|L|=3` | fired 2594/3000, **2594** verified |

6 792 witnesses, zero failures, and the `v₇ = 7v₆` control correctly declines to fire.

## 5. A defect found in this session's own artifact, and what it cost

The first run of §4 **failed on all three named cases**, and the cause is worth recording
because it is exactly the Boundary Set Method's subject.

`{1,2,3,4,5,6}` is the tight instance of `LRC(7)`: its lonely set at level `1/7` is a
**single point**, not an interval. The first implementation complemented the bad sets as
*closed* intervals and merged them on contact, which (i) deleted that point and (ii)
manufactured a spurious "good" component at `t = 0`, a point that is bad for every speed.
The construction then returned `t < 0` and the witness check caught it.

Fix: complement the bad sets as **open** intervals and merge only on **strict** overlap, so
a touch point survives and an interior point does not. A `t₀`-is-lonely assertion was added
at the point of use; it is the check that would have caught this immediately.

The same latent pattern was in `dyadic_engine_v1.py`. That version was *conservative* —
it dropped isolated points but never invented one — so its published results were not
affected; it has been corrected anyway and **re-run: every number in
`QUOTIENT_TRANSLATE_ENGINE_v1.md` is unchanged** (0 bound violations over `q ≤ 48`, 2 799
witnesses, 55% profile cut, 7% sharpness), and the new assertion never fired.

## 6. Ledger

`[PROVED — exhaustive, speeds ≤ 44]` exactly three tight instances at `n = 8`, none
carrying a multiple of 8; the box fails on two of them. Pre-filter soundness proved, not
assumed.
`[PROVED, given LRC(7)]` the interval-deficiency theorem and the four-row ladder; the
`|L| = 1` row is TOP_GAP recovered.
`[VERIFIED — 6 792 exact witnesses]` §4, boundary control included.
`[CITED]` the lacunary results of §3, read from the source PDF.
`[CORRECTED]` §2 — the phase-sweep averaging proposed in `QUOTIENT_TRANSLATE_ENGINE_v1.md`
§5 is dominated by the plain measure bound and is not the next object.

**`n = 8` is not proved and no cell is decided.** What the two sessions now hold, from
`LRC(7)` alone: a 2-adic profile constraint killing 55% of profiles, a divisibility
multiplicity cap at every prime `≥ 7`, a single-gap ladder on the size profile, and a
settled answer that the sign-range box has no `n = 8` form.
