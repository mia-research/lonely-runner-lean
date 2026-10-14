# The `V = 2^k` gap was an artefact of the union bound — it dissolves

2026-09-07. **Supersedes the conclusion of `ESCAPE_COVERAGE_v2.md`.** Script:
`experiments/n8/escape_direct_v{1,2}.py`. Exact integers and `Fraction` only; no float
anywhere in these two files, reporting included.

## 1. Retraction

`ESCAPE_COVERAGE_v2.md` §3 concluded: *"the unconditional reach of our own general-`n`
manuscript fails essentially only when the largest speed `V` is a power of 2"*, and named
Theorem 11.1's pigeonhole at `V = 2^k` as the next object. **That located where the
pigeonhole COUNT fails, and reported it as where the difficulty is. It is not.** The gap
closes completely once the criterion is sharpened to what Theorem 5.2-P's own proof
actually requires.

## 2. Theorem 5.2-P′ — the hypothesis the proof actually uses

The manuscript's proof of Theorem 5.2-P (L648–656) reads:

> *"By the pigeonhole principle … if `|B| + |I_A| > n L_A`, then `B ∩ I_A ≠ ∅`. Choose any
> `β₀ ∈ B ∩ I_A` … hence is a joint-good fine cell … The midpoint of `F_{m″}` is the
> required witness."*

The cardinality inequality is used **only** to force `B ∩ I_A ≠ ∅`. So:

> **Theorem 5.2-P′.** Under the hypotheses of Theorem 5.2-P, if `B ∩ I_A ≠ ∅` then
> `G ∩ {t : {pt} ∈ A} ≠ ∅`.

Same proof, weaker hypothesis, so strictly stronger as a criterion; the witness
construction is unchanged. The manuscript already records that the count is lossy —
Remark 5.2-P (L668–674): *"3 158 positive inputs (8.3%) still satisfy the conjecture's
conclusion even when pigeonhole fails — these witnesses arise from arithmetic alignment
between `B` and `I_A` that exceeds what the union bound guarantees."*

## 3. Effect — exhaustive, `gcd = 1` 7-sets, speeds `≤ 16`, hard case

| | arm | (ii) 5.2-D | (iii) count | **(iii′) intersection** | coverage | residual |
|---|---|---|---|---|---|---|
| Theorem 10.1 | 1 828 | 824 | 1 816 | **1 827** | **1 828/1 828** | **0** (was 2) |
| Theorem 11.1 | 5 249 | 891 | 4 019 | **5 248** | **5 249/5 249** | **0** (was 1 212) |

**Certificates, not just predicates.** For **every** covered tuple the run builds the
witness — `t* = 1/(8v₁)` for Lemma 5.2-D, the fine-cell midpoint `(2m″+1)/(2M)` with
`M = n L_G L_A p` otherwise — and verifies `‖v t‖ ≥ 1/8` in `Fraction` against **all seven
speeds of `T`**, which is LRC(8) for that tuple outright.

    certificates verified : 1 828 + 5 249 = 7 077
    certificate failures  : 0

## 4. What this establishes, and what it does not

**Establishes.** LRC(8) holds, with an explicit exactly-verified rational witness, for every
`gcd = 1` hard-case 7-tuple with speeds `≤ 16` — 7 077 of them — through our own
manuscript's architecture, with **no appeal to Conjecture 5.2-H and none to Rosenfeld**.
Theorems 6.1 and 7.1 cover the non-hard cases unconditionally, so the range is complete.

**Does not establish LRC(8).** Speeds are unbounded; this is an exhaustive verification over
a range, not an analytic proof. `B = 20` was running when this was written.

**And it relocates the analytic target, better than before.** The thing to prove is now

> `B ∩ I_A ≠ ∅` for the §§10–11 configurations,

a statement about two explicitly defined subsets of `{0,…,nL_A−1}` — rather than the
cardinality inequality, which is a union bound that these data show is far from necessary
(it misses 1 229 of 7 077 tuples that the intersection test covers). Proving it would make
the manuscript unconditional at `n = 8`, and the statement is not `n`-specific.

## 5. Ledger

Decided cells 2 of 135 (unchanged; different line). `n = 8` is not proved. Retracted:
`ESCAPE_COVERAGE_v2` §3's identification of `V = 2^k` as the locus of difficulty — it is the
locus of the union bound's failure, and the difficulty is not there.
