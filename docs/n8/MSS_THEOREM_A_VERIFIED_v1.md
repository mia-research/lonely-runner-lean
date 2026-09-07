# MSS Theorem A — citation verified against the source

2026-09-07. Both source PDFs were on disk; SHA-256 recomputed, matched `source_integrity.md` (pub.
`ee0093ef…6ef0b7`, arXiv v2 `b3c07d88…a97d114`, Rosenfeld `7f8c8907…f643a5`). None of this is from
memory or a secondary summary. **GRADE: SUPPORTED-WITH-DELTA** (§6).

## 1. Theorem A, verbatim

*Forum of Mathematics, Sigma* **13** (2025) e164, p. 3, doi:10.1017/fms.2025.10107, preceded on the
same page by its definition:

> To state our bound, for each subset `S ⊆ [n] := {1, . . . , n}` let us denote `v_S := gcd(v_i : i ∈ S)`.
>
> **Theorem A.** *Suppose that LRC is true for n runners. Then, LRC is true for `n + 1` runners with
> integral positive velocities `0, v_1, . . . , v_n` satisfying `gcd(v_1, . . . , v_n) = 1` and*
> `∑_{S ⊆ [n]} v_S > ( (n+1) choose 2 )^{n−1}.`

arXiv:2411.06903v2 (21 Jun 2025) p. 3 carries the same sentence **word for word**; both extracted and
compared. Hypotheses: **H1** LRC true for `n` runners (MSS runner-count, §3); **H2** `v_i` positive
integers, tuple `0, v_1,…,v_n`; **H3** `gcd(v_1,…,v_n) = 1`; **H4** the strict sum inequality.
Conclusion: LRC holds for that `(n+1)`-runner instance.

## 2. The delta, item by item

| point | source | our / Rosenfeld transcription | status |
|---|---|---|---|
| range of sum | **all** `S ⊆ [n]`, all `2^n` subsets | `S ⊆ {1,…,k}` | identical |
| empty subset | included; `v_∅ = 0` by Lemma 2.2 ("Note the special case `v_∅ = vol(Z_[n]) = 0`") | not mentioned | inert |
| inequality | strict `>` | strict `>` | identical |
| threshold | `binom(n+1,2)^{n−1}` | `binom(k+1,2)^{k−1}` | identical |
| `gcd = 1` | present ("needed for our proof but is not relevant in practice") | present | identical |
| distinctness | **not required** by Thm A (only Thm B needs distinct velocities) | applied to a set | special case |

Quantifiers: pointwise in `n`, no uniformity claimed or used — no drift. Conditionality: none on either
side (§5). No hypothesis dropped, none added; the only discrepancy is the label in H1.

## 3. Convention trap — our record CONFIRMED

MSS fix the convention on p. 2: "we refer to Conjecture A as 'LRC for `n + 1` runners'", where
Conjecture A has `n` velocities. So **runners = velocities + 1**, and H1 "LRC is true for `n`
runners" means **LRC for `n − 1` velocities** — one weaker than the `n`-velocity conclusion, which
is what makes it an induction step rather than a tautology.

Rosenfeld's §1 defines the LR property for a set of size `k` with separation `1/(k+1)`, so his `k`
counts **speeds**. His Theorem 2 transcribes MSS verbatim: "If the lonely runner conjecture holds
for `k`, then it holds for `k + 1` for all `k`-tuple…". Read literally in his own convention that
hypothesis is one step **stronger** than MSS supply, and "holds for `k + 1`" does not name its own
conclusion object (a `k`-tuple). **His proof is unaffected**: §4 opens "We rely on the fact that
the lonely runner conjecture was already proven for **7 runners**" (6 speeds, Barajas–Serra), and
Lemmas 5, 6, 7 each read "Let `k ≥ 3` be an integer such that the lonely runner conjecture holds
for `k − 1`" (speeds). Both are the correct weaker hypothesis; all four passages read directly.

**Use this form (speeds).** *Let `k ≥ 2`. If LRC holds for all `(k−1)`-tuples of speeds, then every
`k`-tuple of positive integers `v_1,…,v_k` with `gcd(v_1,…,v_k) = 1` and
`∑_{S ⊆ [k]} gcd(v_i : i ∈ S) > binom(k+1,2)^{k−1}` (empty term `= 0`) has the LR property.* Do
**not** transcribe Rosenfeld's Theorem 2 verbatim.

## 4. Corollary 3 and the contradiction — arithmetic verified

Corollary 3 (verbatim): "If the lonely runner conjecture holds for `k`, then it holds for `k + 1` for
all `k`-tuple … such that `∏ v_i ≥ [ binom(k+1,2)^{k−1} / k ]^k`", from
`∑_{S⊆[k]} gcd({v_i : i ∈ S}) > ∑_i v_i ≥ k (∏_i v_i)^{1/k}`, "the last inequality is simply the AM–GM
inequality". The **first** inequality is strict because non-singleton subsets contribute at least
`2^k − 1 − k > 0` (MSS footnote: `∑_S v_S ≥ v_1 + ⋯ + v_n + 2^n − n − 1`); that recovers Thm A's strict
`>` from a non-strict `≥`. Sound. Computed exactly (integers / `Fraction`):

- `binom(8,2)^6 = 28^6 = 481 890 304`; `481 890 304 / 7 = 68 841 472` exactly; `68 841 472^7 =`
  `7 327 419 168 521 772 511 452 064 099 917 025 275 122 589 812 798 783 488 ≈ 7.3274 × 10^54` —
  Rosenfeld's printed `< 7,4 × 10^54` is **correct**
- `lcm({2,…,8} ∪ S) = 3·5·7·8·∏_{p∈S} p ≈ 1.82599 × 10^55` for his 27 primes `{31,…,163}`, matching
  his `≈ 1.82 × 10^55`; recomputed independently by iterated `lcm` — both routes agree exactly
- margin `1.82599×10^55 / 7.32742×10^54 = **2.49199**` — our record's "about 2.49" is **correct**

Cosmetic only: the contrapositive gives `P < (B/k)^k` strictly; Rosenfeld's eq. (1) writes `P ≤`.
The contradiction with `1.82 × 10^55` is unaffected.

## 5. Unconditionality

Theorem A is **unconditional**, proved via the equivalent Theorem A' in Section 3 ("In this section,
we prove Theorem A' (and thus Theorem A)"; contents: "Theorems A' (hence Theorem A) … are proved,
respectively, in Sections 3, 4 and 5"). The Lonely Vector Problem attaches only to Theorem B / sLRC —
the abstract marks it "except in this case". A keyword scan of the whole of Section 3 (arXiv v2, 442
lines) returns **zero** occurrences of "LVP" or "Lonely Vector". The only assumption in the argument
is Conjecture A' in dim `n − 2`, which is H1 restated zonotopally. Peer reviewed: received 30 Nov
2024, revised and accepted 20 Jun 2025.

## 6. Verdicts

(1) **Statement verbatim** — published + arXiv v2, both read from PDF. SUPPORTS. (2) **Delta** —
none in hypotheses, sum range, strictness or threshold. SUPPORTS. (3) **Convention trap** —
CONFIRMED exactly as our record has it. SUPPORTS. (4) **Corollary 3 arithmetic** — `7.327 × 10^54`,
`1.826 × 10^55`, margin `2.492`; all three of our record's figures correct. SUPPORTS.
(5) **Unconditional** — yes. SUPPORTS.

**GRADE: SUPPORTED-WITH-DELTA** — delta = the runners-vs-speeds label in H1 only, a labelling artefact
of Rosenfeld's transcription, not a defect in MSS Theorem A, touching neither his proof nor ours. Our
`THEOREM2_CITATION_VERIFIED_v1.md` is confirmed on every point, and `[CITED — MSS 2025, Thm A]`
stands; the hypothesis it needs for `k = 7` is LRC for 6 speeds = `intLRC 7`, which this project owns.
**Residual, unchanged:** Theorem A's own proof (Section 3, zonotopal, via Theorem A') has **not** been
read line by line. Accepted on peer review; `[CITED]`, not `[PROVED]`.
