# Mapping the witness: the critical family, and a witness map with a proof

*Version 1, 2026-09-20. Pre-registered in `PREREG_WITNESS_PERTURBATION_v1.md`. Produces the first
exhibited witness map of the kind `Spec/Target.lean`'s discharge criterion asks for — for one named
family, not in general.*

---

## 1. The witness decomposes by the Chinese remainder theorem

For disparity `d` at flank `e`, with `g = gcd(d,e)`, `c = e/g`, `d' = d/g`, and `A = 8k+1`:

> **`d·A mod 8e ∈ [e,7e]  ⟺  d'·A mod 8c ∈ [c,7c]`**

`d·A = g·d'·A` and `8e = 8gc`, so the condition divides through by `g`. `[PROVED — two lines;
confirmed on 98,400 (d,e,k) triples, zero mismatches]`

The condition therefore depends only on the **reduced ratio `d/e`** — denominator `c`, numerator mod
`8c` — and not on magnitude, and not on residues mod 8. Since `A = 8k+1`, each disparity constrains
`k` modulo `c_d = e/gcd(d,e)` through an allowed set `A_d ⊆ ℤ/c_d`, so

> **the witness set at flank `e` is `⋂_d { k : k mod c_d ∈ A_d }` — a CRT intersection.**

`[PROVED; confirmed on 2,800 (set, flank) pairs, zero mismatches]` The flank names the moduli.

**Three consequences.** `c_d = 1` exactly when `e | d`, and the constraint is then all-or-nothing:
clear at every opening iff `8 ∤ d/e` — the framework's `integer_ratio_clear_iff`, recovered as the
`c = 1` case. **A flank dies outright when some disparity is `8`× a multiple of it.** Pairwise
coprime moduli give independence by CRT, so a witness exists iff every `A_d` is nonempty (59/59; a
theorem, not a find); with shared factors that rule still holds 2,634 of 2,741 times, and those 107
failures are where the constraints interact. And flank `e` has exactly `e` openings (Theorem 15H), so
a large `e` supplies both more `k` and a wider spread of `c_d` — which accounts for the measured rank
concentration without making "take the largest" a rule, which it is not.

## 2. The critical family

Exhaustive over all **18,564,316** primitive 7-subsets of `[1,40]`
(`experiments/n8/witness_map_sband_v1.out`), with `S(ds)` the set of supporting flanks:

| `\|S\|` | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| sets | **2** | 250 | 11,262 | 206,897 | 1,631,203 | 5,641,644 | 11,073,058 |

`|S| = 0` **never occurs**, and `|S| = 1` occurs exactly twice: `(2,3,4,5,6,7,16)` and
`(2,3,4,5,6,7,32)`. `[VERIFIED — exhaustive, exact integer arithmetic]` These are the **critical
sets**: one flank away from `|S| = 0`, which would refute the conjecture at eight runners.

**The classification.** For the base `{2,3,4,5,6,7}`, `|S| = 1` exactly when `16 | x`. Flank 2 dies
precisely when `8 | x/2`, and that is `16 | x`; the halves at `x ≡ 8 (mod 16)` — `8, 24, 40, 56` —
all give `|S| = 2`. Confirmed at `x = 16, 32, 48, 64, 80, …, 32768`. The base matters: `{1,…,6}`,
`{3,…,8}`, `{1,3,5,7,9,11}` and `{2,3,5,7,11,13}` with the same additions give `|S| = 3…5`.

## 3. The family does not thin

For every member, the number of witnesses at the sole flank is **exactly `x/8`** — a density of
exactly `1/8`, the threshold constant, at `x = 16` through `32768` and at every non-power-of-two
multiple of 16 tested. The minimum over `x = 16, 32, …, 4096` is 2, attained at `x = 16`. So the
critical family is critical in the count of flanks and **not** in the count of witnesses: it holds a
fixed proportion rather than approaching failure.

## 4. The closed form, and its proof

> **For `ds = {2,3,4,5,6,7,x}` with `16 | x`, the witness set at flank `x` is exactly**
> **`[x/16, x/8) ∪ [7x/8, 15x/16)`, and `(e,k) = (x, x/16)` is its least element.**

212 values of `x`, zero mismatches on the full set for `x ≤ 4096` and zero failures of the map
throughout (`witness_closedform_v1.out`).

**It is not merely measured.** Put `k = x/16`, so `A = 8k+1 = x/2 + 1`. For `d ∈ {2,…,7}`,
`d·A = dx/2 + d`, and `7·A = 7x/2 + 7 < 8x` whenever `x ≥ 2`, so no reduction occurs and

* `d·A ≥ x` because `d/2 ≥ 1`;
* `d·A ≤ 7x` because `d ≤ (14−d)x/2`, binding at `d = 7`, which needs `x ≥ 2`.

For `d = x`: `16 | x` makes `x/2 ≡ 0 (mod 8)`, so `A ≡ 1 (mod 8)` and `x·A mod 8x = x`, the left
endpoint of `[x,7x]` — admissible because the threshold is **closed**, which is Theorem 6.16.

Every constraint holds for `x ≥ 2`, with no case analysis. `[PROVED — elementary; confirmed over
x = 16 … 47,984 step 16, zero violations]` **This belongs in `Flanks.lean` as a lemma, not in a
script.**

## 5. What this is, and what it is not

**It is** an instance of exactly the object `Spec/Target.lean`'s discharge criterion names: an
explicit map from the difference set to `(e,k)`, with a proof that its opening is clear — not a
search, not a cap, not a count. And it covers the hardest family the exhaustive band contains.

**It is not** the general witness map. It covers one base with one parameter. `witness_lonely` in the
criterion quantifies over every injective `v` and every `k`, and nothing here approaches that.

**What it settles about method.** The route map → pattern → rule → closed form → proof ran end to
end on the extremal family and ended in a proof rather than a measurement. That is evidence the
method reaches, not evidence the conjecture is close.

## 6. Next

Organise the families. The base `{2,…,7}` is one; the others measured give `|S| = 3…5` and have not
been classified. The governing data is now known to be the profile `(c_d, A_d)`, which lives in a far
smaller space than the 7-sets, so the mapping should continue there rather than over difference sets.
