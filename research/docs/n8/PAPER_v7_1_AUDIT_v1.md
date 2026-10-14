# Audit of `PAPER_v7_1.md` — logical flow, internal coherence, mathematical correctness

*Version 1, 2026-09-22. Every mathematical claim that can be checked was checked by independent
computation, not by reading the paper's own prose. Artefact:
`experiments/n8/paper_v7_1_audit_v1.py`, output `paper_v7_1_audit_v1.out`.*

---

## A. Verified — 34 mechanical checks, 33 pass and the one failure was the audit's own bug

| group | checks | result |
|---|---|---|
| **§7.1 worked example** — disparity set, bound, all three step tables, who is in the way at each step, both moves, halting, no earlier lonely instant, the certificate `(7,1)`, R1 and R3 failing, R6 firing at `q=6` and its readings, `M=1, c=7` | 18 | all pass |
| **Theorem 10** (modular criterion) against direct real-arithmetic computation, `n = 5,6,7,8`, all integer sets from `[1,15]`, all flanks, all `j ≤ e+2` | 1 | 0 mismatches |
| **Theorem 10's periodicity** in `j` with period `e` | 1 | 0 violations |
| **Theorem 8 / R1**, `n = 4…8`, all sets from `[1,19]` | 1 | 0 counterexamples |
| **R6 is an equivalence** for `2 ≤ q ≤ n` | 1 | 0 counterexamples |
| **R3's witness** `a = e·(e⁻¹ mod n)` is a valid opening index and clears | 1 | 0 failures |
| **§14.3 identity** `(s·(8m+1)) mod 8s = s` | 1 | 0 failures |
| **§14.4 reflection identity** `s(8−x) − 8k = −(sx − 8(s−k))` | 1 | 0 failures |
| **§14.6 window** `(8q+1)/7 ≤ b ≤ 8q+1`, and `q=1` clearing `b ≤ 9` and failing from `b = 10` | 3 | exact |
| **Corollary 3** — exactly `n−1` simultaneously lonely never occurs; every other count in `{0,…,n−2} ∪ {n}` is attained | 1 | 0 instances of `n−1` |
| **Observation 16** — cascade length `2κ+1`/`2κ+2` on `(1, 5κ−2, 5κ, 10κ−2)`, independently simulated | 1 | verified `3 ≤ κ ≤ 15`; `R` runs 1.73 → 1.55, consistent with `→ 3/2` |
| **Layer 1 grade hygiene** — no `[EMPIRICAL]`, `[VERIFIED]`, `[OPEN]`, `[CITED]` or the word "measured" anywhere in §§2–8 | 1 | clean, 13 results |

Final state of the artefact: **36/36 pass**, the last three checks being Finding 4 stated as a result.

**Two bugs in the audit itself, both caught by cross-checking, both recorded here rather than
quietly fixed.** (i) The blocker check used `s*sk` where the band's lower bound is `sk`. (ii) After
that was fixed, section F still disagreed with a standalone run — because section D rebinds `n = 5`
for the `{1,2,3,5}` example and section F inherited it, so an order-8 check was running at order 5.
The script now fixes `n = 8` explicitly at that point and prints the order it used. Both bugs
produced *false alarms*, not false clearances; neither changes a finding below.

---

## B. Findings, most severe first

### Finding 1 — six results are stated with no argument, while §17 disclaims that the formalisation is one

**Theorems 1, 2, 5, 6, 11 and 13 carry no proof, no proof sketch and no citation.** What follows each
is interpretation of the statement, not justification of it:

* **Theorem 1** is followed by *"The converse needs only the two flanking pairs"* — a remark about the
  proof's shape, not the proof.
* **Theorem 2** is followed by nothing.
* **Theorems 5 and 6** are followed by a paragraph drawing consequences.
* **Theorem 11 (Construction)** is followed by *"So a fixed point is not merely a lonely instant"* —
  a reading of the conclusion.
* **Theorem 13** says *"The proof is uniform in the order"*, which asserts that a proof exists without
  giving it, and does not even record that it follows from Theorems 11 and 12.

(Observation 16 is excluded: it declares itself `[VERIFIED — … not formalised]` at its statement, and
that is honest.)

This collides with §17, which states that the formalisation *"is a verification of the stated claims
and their dependencies. It is not part of the mathematical argument, and nothing below should be read
as requiring it."* For these six there **is** no argument in the paper, so the Lean development is the
only witness — which is precisely what §17 disclaims.

**This is the one finding that blocks submission.** A referee cannot take six theorems on the
strength of a formalisation the paper says is not part of the argument. Either the proofs go in, or
§17 stops disclaiming. Theorem 2 is one line; Theorem 13 is two, given 11 and 12. Theorems 1, 5, 6 and
11 need real paragraphs.

### Finding 2 — §12 contradicts §11 on its own worked example

§12 uses `{1,2,3,5}` at `n = 5` and says: *"the rules do reach it — the flank `e = 3` works at
`j = 2`, and so does `e = 5` at `j = 1`. **What is missing is a rule that names which.**"*

But §11's own table says R4 reaches `M = 1` when the multiple is the largest disparity, and this set
satisfies every one of R4's hypotheses — verified:

```
  n = 5 is prime;  M = 1;  the multiple 5 IS the largest disparity;  no other disparity divisible by 5
  R4's witness r = 1 gives a = 6, i.e. the flank e = 5 at j = 1 — which clears.   [all checked]
```

So R4 **does** name the flank, and names exactly the certificate the sentence says exists. The claim
is false for this example.

**What survives.** The section's actual point — that the recursion does not close because `{5}`
descends and `{1,2,3}` does not — is intact and correct. Only the "no rule names which" sentence is
wrong. It is load-bearing, though: the map made this example the centre of §12.

Fix: either state that R4 names it and the example illustrates the *recursion's* failure rather than
the rules', or find a middle-region set that no rule reaches and use that.

### Finding 3 — Theorem 14 takes a minimum over a possibly empty set

```
    R  =  min { R ≥ 1  :  ∀ i,  s_i·R  mod n  ∈  [1, n−1] }
```

If the clear set is empty this minimum does not exist — and its non-emptiness is exactly what the
conjecture asserts and what Layer 2 is trying to establish. As written, a definition in §13
presupposes the conclusion of §18.

The fix is available and costs nothing: Theorem 12 supplies the hypothesis. State it as *"if the
subject is lonely, then `R = min{…}`"*, or define `R` on the clear set and note that Layer 1 makes
non-emptiness equivalent to loneliness.

### Finding 4 — the `n − 3` blocker bound is true but is missing its hypothesis

Stated in §14.3, restated in §15, and again in §18's summary of the reduction, always unqualified.
Checked over every 7-element profile from `[1,25]` with `s₁ = 1`:

| candidates admitted | max blockers |
|---|---|
| all `m ≥ 0` | **6** — exceeds the bound |
| `R = (8m+1)/s_k ≥ 1` | **6** — still exceeds |
| `R mod 8 ∈ [1,7]` | **5** — equals `n − 3`, and tight |

And *"the unit reading never blocks"* is **equivalent** to `R mod 8 ∈ [1,7]` — verified, 0 mismatches
over `s_k < 40`, `m < 60`. So the bound holds exactly on candidates whose ratio lies in an admissible
band, which is every candidate that could be an answer, and fails outside them.

The claim is therefore correct on the cases that matter and wrong as stated. It needs six words: *at a
candidate whose ratio lies in an admissible band*. Note that §18 repeats it inside the paper's summary
of what the reduction achieves, so the omission propagates to the paper's final claim.

### Finding 5 — §16 lists R1–R7 wholesale as general `n`

R4 carries the prime hypothesis. §10's table marks it *(`n` prime)*; §16's general-`n` bullet does
not. Minor, and a clause fixes it.

---

## C. Logical flow — no findings

The two-layer structure holds. Layer 1 is free of grades and of empirical language; the chain in §8
is assembled only from results stated before it; §9 does the job it was added for; §13's
reparameterisation is introduced after the certificate it reparameterises; §13.1 explains the choice
of `R` over cascade length at the point where a reader would ask. §3 is marked a precursor and the §8
chain does not route through it. No dangling cross-references.

---

## D. What the audit did not cover

* The 109 results imported by citation into §§14–15 were **not** re-derived; their grades are taken
  from Palelei (2026b) §§13F, 14I and 15S as the map directs. Four spot-identities were checked
  (§14.3, §14.4, §14.6 twice) and all hold.
* The Lean development was not rebuilt. §17's axiom and `sorry` claims rest on the gates, not on this
  audit.
* Findings 1–5 are defects of the paper, not of the underlying mathematics. Nothing in this audit
  contradicts a result; Findings 2–4 are a false sentence, a missing hypothesis and a missing
  qualifier respectively, and Finding 1 is an absence of written proofs.
