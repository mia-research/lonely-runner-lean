# Correction to `INTERFERENCE_v1` — two claims retracted, one stands

2026-09-11. Script `experiments/n8/ok_interference_audit_v1.py`. Self-audit prompted by the
question "is it?" put to the summary claim *"the amplitude is fixed and only the phase is
free"*. It is not.

---

## 1. RETRACTED — "every tuple carries the same interference energy"

`INTERFERENCE_v1` §2 compared the **mean** unsigned sum of the hardest fifth (`0.26778`)
against the easiest fifth (`0.26019`) and called a 3% gap constancy. Looking at the
distribution instead of two group means:

| `K` | `maxsupp` | mean | stdev | **CV** | min | max | **max/min** |
|---|---|---|---|---|---|---|---|
| 3 | 3 | 0.15348 | 0.03941 | **0.257** | 0.09293 | 0.33141 | **3.57** |
| 4 | 4 | 0.26628 | 0.05644 | **0.212** | 0.18934 | 0.54438 | **2.88** |
| 4 | 5 | 0.34222 | 0.06871 | 0.201 | 0.24756 | 0.69301 | 2.80 |
| 5 | 5 | 0.41260 | 0.08317 | 0.202 | 0.29412 | 0.83265 | 2.83 |

The unsigned sum varies by a factor of **2.8–3.6** across tuples, with a coefficient of
variation around `0.20`. **The amplitude is not fixed.** Two quintile means agreed to 3%
while the underlying spread was 20% and the range nearly 3×; the comparison hid exactly what
it needed to show.

And the mean **grows with the cutoff** — `0.153, 0.266, 0.342, 0.413` — as it must, since
`AB_SPLIT_v1` §A2 proves the absolute series **diverges**. There is no limiting amplitude to
be constant.

## 2. RETRACTED — "their difference predicts at 0.9362"

`net = m₂ + m₃ + m₄ + m₅` **is** the signed truncated sum. Verified identical to `10⁻¹²` at
every truncation tested. The parity split is a *decomposition* of that sum, not a new
statistic, and presenting it as a predictor implied otherwise.

Worse, the comparison was not like-for-like: `0.8735` was computed at `maxsupp = 4`, the
`0.9362` at `maxsupp = 5`. Like for like:

| `K` | `maxsupp` | `Spearman(\|G\|, signed) = Spearman(\|G\|, net)` |
|---|---|---|
| 3 | 3 | `+0.8874` |
| 4 | 3 | `+0.8874` |
| 4 | 4 | `+0.8666` |
| 4 | 5 | `+0.9563` |
| 5 | 5 | `+0.9420` |

Non-monotonic, spread `0.087`. **The figure is a property of the cutoff.** And a truncated
tail correlating with the full tail is expected, not a finding.

Parity split as a predictor: even alone `+0.3676`, odd alone `+0.5702`, signed `+0.9563`.
**The split explains; it does not predict.**

## 3. STANDS — the sign law, and what it explains

Unaffected, because it is a derivation and not a measurement:

> `f̂(k) < 0` exactly for `|k| ≡ 1,2,3 (mod 8)`; a short resonance has every `|k_j| ≤ 3`, so
> **`sign(∏ f̂(k_j)) = (−1)^{|supp k|}`.** Odd-support destructive, even-support
> constructive. `[PROVED]`

And its consequences stand:

- **The wrong-sign puzzle is resolved.** `2·7 = 14` has support 2 (constructive,
  `+243/16384`); `6 + 7 = 13` has support 3 (destructive, `−81/8192`). Opposite sides of the
  ledger — which is why `RESONANCE_FACTOR_v1` §4's "two lowest-height families" carried no
  information.
- **Relation count is one-sided.** It counts 3-term relations, i.e. odd-support mass alone,
  which ranks at `+0.5702` against `+0.9563` for the signed total. Its non-monotonicity is
  what a one-sided ledger looks like. (Qualitative; the numbers are truncation-dependent.)
- **Height is blind to support parity**, so it cannot place a term on either side.

## 4. The pattern in these errors

Three retractions this session — the circular `Σα_v < 1`, the uncontrolled window search,
and now this — share one shape: **a summary statistic was reached for as the result, when
the result was the derivation.** In each case the derivation survived and the statistic did
not. The specific fault here was comparing two group means and not looking at the spread.

Standing rule to add: **a claim of constancy requires the spread, not two group means; and a
correlation from a truncated series requires the figure at two or more cutoffs before it is
quoted.**

## 5. Ledger

`[RETRACTED]` `INTERFERENCE_v1` §2 ("same interference energy") and §3's presentation of
`net` as a predictor at `0.9362`.
`[STANDS]` `INTERFERENCE_v1` §1 (the sign law) and §4 (the three explanations), on the
strength of §3 above.
`[PROVED]` the audit tables of §1 and §2 here.

`n = 8` is **not proved**, and this correction does not change its status.
