# The general-`n` manuscript at `n = 8`: two escapes cover 99.99%, and the residual is three tuples

2026-09-07. Executes `PREREG_ESCAPE_COVERAGE_v1.md`. Script:
`experiments/n8/escape_coverage_v1.py`. Exact integer/`Fraction` throughout.

## 0. Why this was run

`lrc_proof_allN_v11_8.md` is conditional on exactly one hypothesis, Conjecture 5.2-H, and
Theorems 10.1/11.1 each list **four** unconditional escapes from it. Nobody had instantiated
the manuscript at `n = 8` — it contains three mentions of `n = 8`, none of them an
instantiation.

## 1. Two of the four escapes are vacuous in the hard case

**Theorem 10.1 `[PROVED]`.** `L = lcm(v₁..v₆) ≥ v₆`, so `8L ≥ 8v₆ > 7v₆ ≥ V ≥ p` — escape
**(i)** `p ≥ n·L` can never hold. And `p/v_max ≤ V/v₆ ≤ 7` with `1/q ≤ 1`, so escape
**(iv)**'s left side is `≤ 8` against a threshold `n(n−1)/2 = 28`. Both hold for every
`n ≥ 4`. Verified: 0 firings over 100 165 sampled hard-case tuples.

**Theorem 11.1 `[EMPIRICAL only]`.** Its escapes are taken over `S_ind` — the slow runners
**not** divisible by `p` — so `lcm(S_ind)` and `max(S_ind)` can be far smaller and **the
proof does not transfer**. Measured: 0 firings of either over 97 503 tuples at `B = 24`.
Not proved; larger speeds could permit it.

So at `n = 8` the manuscript rests on **(ii) Lemma 5.2-D** and **(iii) Theorem 5.2-P** alone.

## 2. Coverage — exhaustive, Theorem 10.1 arm

| speed bound | 10.1 arm | (ii) Lemma 5.2-D | (iii) Thm 5.2-P | **coverage** | residual |
|---|---|---|---|---|---|
| 12 (pilot) | 169 | 40.24% | 97.63% | 99.41% | 1 |
| 16 | 1 828 | 45.08% | 99.34% | 99.89% | 2 |
| 20 | 23 086 | 37.49% | 99.90% | **99.99%** | **3** |

Pilot marginals both sat inside `[1%, 99%]`, so the main run proceeded as specified.

**Controls.** Both escapes are constructive, so the pipeline builds each firing escape's own
witness — `t* = 1/(8v₁)` for Lemma 5.2-D, the fine-cell midpoint `(2m″+1)/(2M)` with
`M = n L_G L_A p` for Theorem 5.2-P — and verifies `‖v_j t‖ ≥ 1/8` in `Fraction` for all
seven speeds. **0 failures at every bound.** That converts "the predicate fired" (a proxy)
into "a certificate exists" (the object).

## 3. The residual, listed  `[the whole of it at `B ≤ 20`]`

| `T` | `V` | `p` | `q` | `M(T)` | tight? |
|---|---|---|---|---|---|
| `{1,2,4,5,7,8,12}` | 12 | 3 | 4 | `4/19 ≈ 0.211` | no |
| `{1,3,5,7,11,13,16}` | 16 | 2 | 8 | `8/29 ≈ 0.276` | no |
| `{1,4,5,7,11,16,18}` | 18 | 3 | 6 | `6/29 ≈ 0.207` | no |

All three have `v₁ = 1` and `p ∈ {2,3}` — matching the manuscript's own Remark 5.2-P, whose
53 residual LRC-shape inputs "all have `p ∈ {2,3}`". Independent arrival at the same
signature.

**And none is anywhere near tight.** `M` runs `0.207–0.276` against the `1/8 = 0.125`
threshold — roughly double. So **the residual is not where the difficulty is; it is where
the criteria are weak.** That is consistent with Remark 5.2-P's own observation that the
pigeonhole bound is one-sided (every counterexample fails it, but many positives do too).

## 4. Scope — attaches to every number above

- **The Theorem 11.1 arm is entirely unmeasured.** At `B = 20` it holds 21 602 tuples
  against the 10.1 arm's 23 086 — about 48% of the hard case. Abstaining on it is **not** a
  closure of it.
- Exhaustive for `gcd = 1` 7-sets with speeds `≤ 20`; nothing extends beyond. `B = 24` was
  running when this was written.
- Compute-cap exclusions (`L_G > 10⁶`): **0** at every bound run, so the cap did not bite.
- `n = 8`, integer speeds, threshold `1/8`, Theorem 10.1's configuration
  (`k_G = 6`, `k_A = 1`).

## 5. What this does and does not establish

**Does not prove `n = 8`.** Coverage of a *sufficient* condition is not a proof of the
conclusion, and by the manuscript's Remark 5.2-G (line 1104) the residual is exactly where
the argument reduces to *the LRC inductive step at `n` itself*. Three uncovered tuples are
three instances of LRC(8), not three gaps in a proof of it.

**Does establish**, for the first time, that our own conditional general-`n` manuscript is
unconditional at `n = 8` on **99.99% of the Theorem 10.1 arm**, with the exceptions
enumerable and enumerated; that two of its four listed escapes cannot fire there at all
(proved for 10.1, measured for 11.1); and that the residual signature `v₁ = 1`, `p ∈ {2,3}`
reproduces the manuscript's independently obtained one.

**The next object** is the Theorem 11.1 arm, which is half the hard case and has never been
measured.

## 6. Ledger

Decided cells: 2 of 135 (unchanged; this is the general-`n` line, not the Rosenfeld sector
count). `n = 8` is not proved.
