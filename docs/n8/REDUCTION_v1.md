# LRC(8) reduced to one arithmetic statement — and two independent lines converge on it

2026-09-07. Consolidates `BCAP_ATTACK_v1.md` (agent-produced, verified below),
`BCAP_STRUCTURE_v1.md`, `ESCAPE_COVERAGE_v{1,2,3}.md`, `HALVING_AND_TIGHT_WITNESS_v1.md`
and `TIGHT_INSTANCES_v1.md`. Exact arithmetic throughout; no float on any path.

## 1. The equivalence that collapses it  `[PROVED; independently re-verified]`

**Theorem A.** *For every `n ≥ 3`, all finite `S_G, S_A`, every `p ≥ 1`:*

    B ∩ I_A ≠ ∅   ⟺   Good(S_G ∪ p·S_A, lcm) ≠ ∅.

*Route:* `Good(S,L)` is exactly the set of `nL`-cells wholly inside
`Λ(S) = {t : {ut} ∈ [1/n, 1−1/n) ∀u∈S}` — the cell criterion does not depend on position
within the cell. `B` is then the set of `nL_A`-cells meeting `p·Λ(S_G)`, so intersecting
with `I_A` says `p·Λ(S_G) ∩ Λ(S_A) ≠ ∅`, i.e. `Λ(S_G ∪ pS_A) ≠ ∅`.

**Corollary A1.** Equivalently `g(S_G ∪ p·S_A) > 1/n`, with `g` the max–min gap — **strict**.

**Verified here, not taken on report.** Independent re-implementation: 0 mismatches over
1 715 hard-case tuples at speeds `≤ 14`. And the merged set is not an abstraction — for both
Theorem 10.1 (`S_A = {q}`, `p·q = V`) and Theorem 11.1, `S_G ∪ p·S_A = T` **exactly**,
checked on tuples from both arms.

**Consequence, verified directly: `B ∩ I_A = ∅ ⟺ M(T) = 1/8`.** Zero mismatches over the
same 1 715 tuples. The fine-cell criterion succeeds precisely when the tuple is **not**
tight, and fails precisely when it is.

**Why:** `I_G`, `I_A` retain only cells whose *open interior* is good, and at a tight
instance every witness sits at a cell endpoint. Theorem 5.2-P is blind to measure-zero
witnesses by construction. That is not a defect; it is the reason the criterion cannot be
pushed past the extremal boundary.

## 2. The reduction

Write `Good(T) := Good(T, lcm T)`. For a 7-set `T` at `n = 8`:

- **Case 1 — no speed divisible by 8.** Then `‖v·(r/8)‖ = |vr mod 8|/8 ≥ 1/8` for every `r`
  coprime to 8, so `M(T) ≥ 1/8`.  `[PROVED, one line]`
- **Case 2 — some speed divisible by 8, and `Good(T) ≠ ∅`.** Theorem A gives
  `B ∩ I_A ≠ ∅`, and the manuscript's §§10–11 construction returns the fine-cell midpoint,
  a rational witness with `‖v t‖ ≥ 1/8` for all seven speeds.  `[PROVED given Theorems
  6.1/7.1/10.1/11.1; 7 077 such certificates built and verified exactly, 0 failures]`

> **Therefore LRC(8) can fail only for a tuple that carries a multiple of 8 **and** has
> `Good(T) = ∅`.**

`Good(T) = ∅` forces `M(T) ≤ 1/8`, so such a tuple is either a counterexample or exactly
tight. Hence:

> **REDUCTION.  LRC(8) follows from: no tight instance at `n = 8` contains a multiple of 8
> — and no tuple carrying a multiple of 8 has `Good(T) = ∅` with `M(T) < 1/8`.**

## 3. The convergence

**`HALVING_AND_TIGHT_WITNESS_v1.md` §5 owed item 1 is the same statement.** It reads:
*"Prove `r = 1`… 'No tight instance contains a multiple of `n`' is equivalent to 'every
tight instance has witness denominator exactly `n`'."* Reached there from the witness
ladder; reached here from the general-`n` manuscript's fine-cell machinery. **Two
independent routes, one arithmetic question.**

What §3 of that file already has towards it, unchanged: for a tight `T` with witness
`t* = p/q` in lowest terms and extremal pair `a, b`, — `q | a+b`, `n | q`, and with
`r := q/n`, `r | a`, `r | b`, `a₁p ≡ 1` and `b₁p ≡ −1 (mod n)`; and if a multiple of `n` is
present then `r ∤ d₁` and `q ≥ 2n`. **What is missing is one thing:** a reason the band
condition `|vp mod± nr| ≥ r` cannot hold for all seven speeds when `r ≥ 2`.

Supporting evidence already on record: ten tight instances enumerated exhaustively at
`n = 3…8`, **none** containing a multiple of `n`, **all** with witness denominator `n`; and
at `n = 8` directly, 8 165 718 residual 7-sets with speeds `≤ 44`, **zero tight**. All
one-sided searches — they can only over-report.

## 4. Two further items from the attack, not yet folded in

**Theorem B `[PROVED]`.** If `p·c ≥ n L_G`, where `c` is the longest cyclic run in `I_G`,
then `B` is everything. This **strictly extends the manuscript's easy case** `p ≥ n L_G`
whenever `c ≥ 2`. Worth adding to §5.2; note escape (i) was shown vacuous in the hard case
(`ESCAPE_COVERAGE_v1` §1), so the extension's value there needs measuring before it is
claimed.

**An open discrepancy, flagged not adjudicated `[OWED]`.** 24 LRC-shape counterexamples to
the unrestricted claim reportedly fall inside the range Remark 5.2-P states it scanned
(`n ≤ 7`, `|S_G| ≤ 3`, `|S_A| ≤ 2`, `p ≤ 19`) — e.g. `n = 5`, `S_G = {1,3}`, `S_A = {1,2}`,
`p = 2` — while Remark 5.2-V's table records 0 counterexamples at `δ = 0`. The likely cause
is an unstated filter in `LonelyRunner/scripts/phase5_residue_structure.py`. **That script
must be re-run against those 24 configurations before either record is amended.** No claim
is made here that the harness is wrong.

## 5. Ledger

`n = 8` is **not proved**. Decided cells 2 of 135 (unchanged; different line). What changed:
the target is no longer "prove `B ∩ I_A ≠ ∅`" — that is equivalent to strict LRC and false at
tight instances — but the single arithmetic statement of §3, which two independent lines of
this project now both require and neither has proved.
