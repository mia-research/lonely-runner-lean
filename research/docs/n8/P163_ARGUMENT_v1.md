# Replacing the `p = 163` search with an argument — attempt 1

2026-09-07. Target: the 32-hour verification of Lemma 7 at `k = 7`, `p = 163`
(`N = 1304`, `H = 652`). Not achieved. Three findings, one of which corrects the
framing of everything earlier in this line.

## 1. The framing correction: covering is *not* the obstruction

Every analysis so far in this session — window/grid, three-distance, the `j`-chain
— treated Lemma 7 as a **covering** problem. It is not, at the primes that
matter.

**At `k = 6, p = 31`** (a prime where Lemma 7 *applies*, i.e. no bad cover
exists), greedy finds a complete cover of `{1,…,108}`:

    {7, 14, 21, 28, 35, 42}

all six multiples of `7`. It covers everything. What kills it is the **gcd
condition**: `N = 217 = 7·31`, and every 5-subset has `gcd(R ∪ {N}) = 7 ≠ 1`.

**At `k = 7, p = 163`**, the same thing. Greedy finds a complete 7-cover:

    {8, 32, 40, 48, 56, 88, 104}

all multiples of `8`. Covering `{1,…,652}` with 7 speeds is **easy**. The search
is hard because of the gcd side condition, not the covering.

This reverses the emphasis of `D7_ATTACK_v1`–`v5`. The rigidity results there
(three-distance, exact window widths) are about the covering half, which is the
half that is *not* binding.

## 2. The gcd condition at `p = 163`, in closed form

`N = 1304 = 2³ · 163`, so the only primes that can spoil `gcd(R ∪ {N}) = 1` are
`2` and `163`. Since every admissible speed satisfies `v ≤ 652` and `163 ∤ v`,
the prime `163` never divides a whole subset. So the condition is purely 2-adic:

> `gcd(R ∪ {N}) = 1` for every 6-subset `R` of `T`
> ⟺ no 6-subset of `T` is entirely even
> ⟺ **`T` contains at least 2 odd speeds.**

So the `p = 163` verification is exactly:

> **Show that no 7 speeds in `{1,…,652} \ 163ℤ`, at least two of them odd, cover
> `{1,…,652}` under `j·v mod 1304 ∈ [0,163) ∪ (1141,1304)`.**

That is a materially simpler specification than the subset-gcd form — one
sentence, one parity condition — and it is the form any implementation
(including a Lean one) should use.

## 3. Why it still resists: odd speeds are not weaker, only differently placed

The natural hope after §2 is that odd speeds cover less, giving a counting
contradiction. They do not. Coverage size is essentially constant across 2-adic
classes:

| class | count | coverage size |
|---|---|---|
| `v` odd | 324 | **162** |
| `v ≡ 2 (mod 4)` | 162 | 163 |
| `v ≡ 4 (mod 8)` | 81 | 162 |
| `8 ∣ v` | 81 | **164** |

Best possible total with 2 odd + 5 multiples of 8 is `2·162 + 5·164 = 1144`
against 652 targets — slack `1.75×`. **Counting fails again**, by the same
constant factor identified in `D7_ATTACK_v1` §3.

Greedy with two odd speeds forced does fail to complete (leftover 2–4 targets
across several starts), which is suggestive but is not a proof — greedy is not
exact.

## 4. Tool built

`experiments/n8/prefix_bound_v1.py` computes the minimum number of speeds needed
to cover only a **prefix** `{1,…,J}`. If that minimum ever exceeds `k`, no bad
cover exists and the search collapses. Validated at `k=6, p=23` (bad cover
exists; prefix minimum 5 ≤ 6) and `k=6, p=31` (prefix minimum 5 ≤ 6 even at
`J = H`) — the latter is precisely the observation that made §1 visible, since
`p = 31` has no bad cover despite being fully coverable.

**The prefix route is therefore dead on its own**: covering a prefix, or even the
whole range, never exceeds `k`. Any argument must involve the parity condition.

## 5. Status

- §1 and §2: **established**, with explicit witnesses.
- §3: measured; counting is refuted at this prime, not merely unproven.
- §4: tool built and validated; the route it was built for is closed.
- **The `p = 163` search is not replaced.** What has changed is that the question
  is now correctly posed — a parity-constrained covering problem — rather than
  the covering problem the earlier documents were attacking.

## 6. Next

The live question is narrow and concrete:

> Why can 7 speeds cover `{1,…,652}` when all are multiples of 8, but not when
> two are odd?

For `8 ∣ v`, `j·v mod 1304 = 8·(j·(v/8) mod 163)`, so the whole configuration
collapses to a covering problem in `ℤ/163` by dilates of a 41-element arc — a
much smaller object (163 residues, not 652 targets). Odd speeds do not collapse
this way; they see the full `ℤ/1304`. **That asymmetry, not size, is where the
obstruction lives**, and it is the first thing to examine.
