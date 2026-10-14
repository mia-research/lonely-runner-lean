# The ≤34 sweep, discharged exactly — and where the goal actually stands

2026-09-07. Discharges the first owed item of `TIGHT_INSTANCES_v1.md` §7. Script
`experiments/n8/tight_with8_v1.py`, which **audits clean: 0 float-capable sites**.

## 1. Result

**No 7-set carrying a multiple of 8 is tight, at speeds ≤ 34.**
`[EMPIRICAL — exhaustive over the stated range, exact rational arithmetic]`

Candidates: `gcd = 1`, every `q ∈ {2,…,7}` divides some speed (else `M ≥ 1/q > 1/8`, so not
tight), and some speed divisible by 8 — **966 714** of them. Ten independent shards; the
per-shard tested counts sum to exactly 966 714, so coverage is complete. **TIGHT: 0.**

`HALVING_AND_TIGHT_WITNESS_v1.md` §4 reached speeds ≤ 44 for the narrower *residual* class
using a float first stage. This is the wider candidate set, exact throughout, no float at
any point including reporting. One-sided as always: a tight instance above 34 would not have
been seen.

## 2. The mechanism, not another exclusion

At `n = 8` every unit is self-inverse, so a speed `v ≡ u (mod 8)` owns the complementary
pair `{u, 8−u}`. An **even** speed has `‖v·r/8‖ = |vr mod 8|/8 ≥ 1/4` at every witness —
slack `1/4`, never tight. So tightness is two-stage:

- the **odd** speeds, hitting all four unit classes, pin `{1,3,5,7}/8` at exactly `1/8` and
  leave a positive-measure residue;
- the **even** speeds exist only to cover that residue.

Measured on the three known tight instances: `{1,2,3,4,5,6,7}` and `{1,2,3,4,5,7,12}` have
the *identical* odd part `{1,3,5,7}` and hence the identical residue `31/140` — they are one
odd configuration with two different even covers (`{2,4,6}` and `{2,4,12}`), not two
independent coincidences. `{1,4,5,6,7,11,13}` has five odd speeds, still exactly the four
classes, residue `105/572`.

**A multiple of 8 kills all four witnesses at once** (`‖8w·(r/8)‖ = ‖wr‖ = 0`), so such a
tuple could only be tight at a witness of denominator `8r` with `r ≥ 2` — which is
`HALVING_AND_TIGHT_WITNESS_v1` §3's reduction, reached here as a mechanism rather than as a
further hypothesis.

## 3. Where the goal stands — the quantitative frame  `[the important part]`

MSS Theorem A is now verified against both source PDFs (`MSS_THEOREM_A_VERIFIED_v1.md`,
grade SUPPORTED-WITH-DELTA, unconditional). Consuming it:

| | value | orders |
|---|---|---|
| bound on a counterexample's product | `< 7.33 × 10⁵⁴` | **54** |
| what our witness ladder forces, `lcm(2..8) ∣ ∏v` | `840` | **2** |
| Rosenfeld's 27 primes close it | `1.826 × 10⁵⁵` | margin `2.492` |

> **Our machinery supplies 2 of the 54 orders of magnitude. The shortfall is ~52.**

Every structural result this project holds at `n = 8` — the witness ladder, Theorem P and
P″, the fine-cell criterion, the tight-instance mechanism above — is **qualitative**. None
of them forces a prime to divide `∏v`. A proof must force ~52 orders of magnitude of prime
divisors, and the only known mechanism is Lemma 6/7.

**And this explains why the ladder stops at 8.** The ladder *is* Lemma 7 for `q ≤ n`,
provable in one line because `1/q ≥ 1/n` there. At `q > n` the inequality reverses. The
ladder is not a weak version of Lemma 7 — it is exactly the sub-range where Lemma 7 is
trivial, and it is maximal.

## 4. What therefore advances the goal

Only work that forces primes. Concretely, the 27-prime × 5-sector ledger — **135 cells, 2
decided**:

1. **Sector `x = 3` at `p = 163`**, by the untried inversion named in
   `HANDOVER_2026_09_07b` §6.1: enumerate the coarse side (`C(81,3) = 85 320`, small) and
   ask what the non-coarse speeds must supply, with the pair-type structure as a *branching*
   rule. This decides cells.
2. **Run the `x = 5` and `x = 4` sector decisions at primes other than 163.** Their inputs
   were measured `p`-specific (`P_UNIFORMITY_v1.md`) but the decisions themselves have never
   been attempted elsewhere; small primes are orders of magnitude cheaper.
3. Structural work only where it feeds 1 or 2. What today contributed there: the 2-adic cap
   table, pair types and `x ≥ 1` forcing are now **uniform in `p`**; `U_min(1)` and
   `U_min(2)` have closed forms; and the `|D| ≥ U_min` filter route is measured shut at all
   27 primes.

## 5. Ledger

`n = 8` is not proved. Decided cells **2 of 135**. Discharged: the `≤34` sweep. Still owed
from `HALVING` §5: prove `r = 1`; and whether `inf{M(T) : T residual} > 1/8`.
