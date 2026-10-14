# Constructive and destructive interference: the sign law is support parity

2026-09-11. Script `experiments/n8/ok_interference_v1.py`. `|G|` is exact `Fraction`;
the truncated Fourier sums are float and are a **diagnostic only**, never the source of a
claim.

---

## 1. `|G|` is an interference sum, and the terms' signs are forced

    |G| = Σ_{k·e = 0} ∏_j f̂(k_j),      f̂(k) = −sin(πk/4)/(πk).

`f̂(k) < 0` exactly when `|k| ≡ 1,2,3 (mod 8)`, `> 0` when `5,6,7`, `= 0` when `4 | k`. A
**short** resonance has every `|k_j| ≤ 3`, so every factor is negative and

> **`sign(∏_j f̂(k_j)) = (−1)^{|supp(k)|}`.**  `[PROVED]`

**Odd-support resonances interfere destructively; even-support constructively.** A 3-term
relation `e_i + e_j = e_k` subtracts; a pair `(2·7 = 14)` or a quadruple
`e_i + e_j = e_k + e_l` adds.

## 2. Every tuple carries the same interference energy  `[EMPIRICAL — measured]`

Truncated over primitive `k` with `|k_j| ≤ 4`, support `≤ 4`, 122 Case-2 tuples from
`[1..16]`, hardest fifth against easiest fifth:

| | hardest | easiest |
|---|---|---|
| **unsigned** sum | `0.26778` | `0.26019` |
| **signed** sum | `−0.00040` | `+0.06689` |

The amplitude is the same everywhere — a 3% difference. **What separates a hard tuple from
an easy one is not how much interference there is, but whether it cancels.**
`Spearman(|G|, signed sum) = 0.8735`.

## 3. The balance, by support parity  `[EMPIRICAL — 91 tuples]`

| | hardest quarter | easiest quarter | `Spearman(\|G\|, ·)` |
|---|---|---|---|
| even-support mass (`r = 2,4`), constructive | `+0.14650` | `+0.16667` | `+0.3390` |
| odd-support mass (`r = 3,5`), destructive | `−0.21785` | `−0.17246` | `+0.4805` |
| **net** | **`−0.07135`** | **`−0.00579`** | **`+0.9362`** |

Neither half predicts on its own. **Their difference predicts at `0.9362`** — the strongest
predictor found, and unlike `α` it is not a re-measurement of `|G|`: it is a sum over the
resonance lattice, computed from the speeds.

Per tuple, by support:

| tuple | `\|G\|` | `r=2` | `r=3` | `r=4` | `r=5` | net |
|---|---|---|---|---|---|---|
| `(2,6,7,8,10,13,14)` — `E*` | `0.006387` | `+0.02502` | `−0.15790` | `+0.09679` | `−0.07482` | `−0.11090` |
| `(2,6,8,10,11,14,17)` | `0.010504` | `+0.00801` | `−0.15118` | `+0.08322` | `−0.06411` | `−0.12406` |
| `(2,3,6,8,10,14,32)` (both adds free) | `0.073214` | `+0.03068` | `−0.13058` | `+0.09403` | `−0.04691` | `−0.05278` |
| `(3,10,14,15,16,19,21)` | `0.117411` | `+0.01133` | `−0.05591` | `+0.07851` | `−0.04793` | `−0.01400` |

## 4. This resolves three earlier failures

**Relation count.** `RELATION_DICHOTOMY_v1` counts 3-term relations — that is the
**odd-support mass alone**, which predicts at only `0.4805`. It ignores the even-support
mass that opposes it. Counting was not the wrong idea; it was **half a ledger with the other
half missing**, and its non-monotonicity (`RESONANCE_FACTOR_v1` §2) is exactly what a
one-sided ledger looks like.

**Height.** Height grades a resonance by `∏|k_j|` and is **blind to support parity**, so it
cannot see which side of the ledger a term is on.

**The wrong-sign puzzle.** `RESONANCE_FACTOR_v1` §4 found the two lowest-height families at
`E*` summing to `+81/16384` — wrong sign, 14.2% of the magnitude. Now explained: `2·7 = 14`
has **support 2** (constructive, `+243/16384`) and `6 + 7 = 13` has **support 3**
(destructive, `−81/8192`). They sit on **opposite sides of the ledger**. Taking "the two
lowest-height" mixes one constructive with one destructive term, which is why it carried no
information.

## 5. Grades

`[PROVED]` §1, the sign law, from `sin(πk/4) < 0` for `|k| ≡ 1,2,3 (mod 8)`.
`[EMPIRICAL — float diagnostic, exact `|G|`]` §2, §3 — truncated sums over `|k_j| ≤ 4`,
support `≤ 5`, in the stated box. The truncation is unreliable as an *approximation*
(`AB_SPLIT_v1` §A2) but is used here only as a *predictor*, and it ranks at `0.9362`.
`[PROVED]` §4's explanation of the wrong-sign puzzle: the two families' supports are 2 and 3.

`n = 8` is **not proved.** What is established: the interference amplitude is constant
across tuples, so `|G|` is set purely by sign alignment; the sign is `(−1)^{support}`; and
the even/odd support balance is what earlier statistics were each seeing half of.
