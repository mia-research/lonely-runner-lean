# Cross-check of the paper against the Lean tree and the manuscript

*Version 1, 2026-09-22. Target: `PAPER_v7_1.md`. Purpose: establish that every declaration the paper
names exists, that every citation of Palelei (2026b) resolves, and that nothing is invented.
Corrections applied in `PAPER_v7_2.md`.*

---

## 1. Lean — every declaration the paper names

Extracted all 45 declaration names from §17's crosswalk and searched every `.lean` file in the
repository, excluding `.lake/` and `archive/`.

```
  in the gated LonelyRunner/ tree : 44
  in experiments/ only            :  1      RBand.R_avoids_bad_bands  (Theorem 15)
  not found anywhere              :  0
```

**No hallucinated declarations.** `sorry`, `native_decide`, `unsafe`, `admit` across the 23 files
carrying them: **0, 0, 0, 0**.

**A false alarm from the check itself, recorded.** The first pass reported seven declarations —
`lonely_of_fixed`, `first_isolation_of_fixed`, `first_isolation_as_zone_run`,
`flank_at_first_isolation`, `bound_le_of_lonely`, `iterate_le_of_lonely`, `exists_fixed_of_lonely`,
i.e. the whole of Theorems 11 and 12 — as living only under `archive/`. They do not: the script
printed the first filesystem hit, and all seven are in the gated tree at `LRC/Cascade/Iteration.lean`.
The script now excludes `archive/` and classifies by tree.

**Finding L1 — one declaration sits outside the gates.** `RBand.R_avoids_bad_bands`, carrying
Theorem 15, is in `experiments/n8/RBand_v1.lean`, not in the gated tree. This is consistent with
Palelei (2026b), which places §11's artefacts in the development directory by design, but §17 as
written implied gate coverage for everything in its table. Corrected in v7.2, which names the
exception.

---

## 2. Lean — does a declaration say what the paper says it says

Checked the statement the audit of `PAPER_v7_1` had flagged as under-hypothesised. The Lean:

```lean
theorem self_never_blocks {sk A : ℤ} (hk : 0 < sk) (q : ℤ) (hA : A = 8 * q + 1) :
    ¬ blocks sk A sk

theorem unit_never_blocks {sk A : ℤ} (hk : 0 < sk) (h1 : sk ≤ A) (h7 : A ≤ 7 * sk) :
    ¬ blocks 1 A sk
```

**Finding L2 — confirmed, and it originates upstream.** `self_never_blocks` is unconditional.
`unit_never_blocks` carries `sk ≤ A ≤ 7·sk` — exactly `1 ≤ R ≤ 7`, the first band, and exactly the
hypothesis the audit derived independently by enumeration. Both Palelei (2026b) §14C and the paper
state the resulting `n − 3` bound **without** it:

> *"**The blocker count at any candidate is at most `n − 3`.** (0 cases, `sₖ < 400` …)"*

So the formalisation is right and both prose documents drop the hypothesis. The paper reproduced the
manuscript faithfully; the defect is the manuscript's. Corrected in v7.2 in all three places the
bound appears (§14.3, §15, §18), using the Lean statement's own form.

---

## 3. The manuscript — do the citations resolve

Every citation of Palelei (2026b) in the paper, checked against `MANUSCRIPT_v20.md`:

```
  sections cited : 24   missing: 0     (§6A, §13, 13A, 13D, 13F, 14A–14I, 15, 15D–15S)
  theorems cited : 31   missing: 0     (13.1–13.10, 14.1–14.26, 15.1–15.73 endpoints)
```

**No hallucinated citations.** Content fidelity spot-checked on five claims the paper leans on, each
against the manuscript's own wording:

| paper says | manuscript |
|---|---|
| the seven edge-witness results are order-agnostic | *"Those **seven** apply to any finite system of congruence-interval constraints, at any order"* |
| small moduli forbid at most two residues each | §15P's heading, verbatim |
| `53/462` is not a floor beyond readings ≤ 40 | *"exact and exhaustive **for readings ≤ 40** and is not a floor beyond that range"* |
| shadowing needs the gcd-weighted count to reach `e` | Theorem 15.50, verbatim |
| blocker count `≤ n − 3` | §14C — but see Finding L2 |

---

## 4. Findings introduced by this session's own edits

**Finding L3 — a citation corrupted by the v7.1 renumbering.** §17 read:

> *"Theorem 4 is Palelei (2026, Theorem 4)"*

It should read *Palelei (2026a, Theorem 3.1)*. Two compounding errors, both mine: the `2026 → 2026a`
split missed this instance because the citation was wrapped across a line, and the consecutive
renumbering then rewrote the **cited** `Theorem 3.1` as `Theorem 4` because its protection pattern
required the `a`. The result was a citation pointing at a theorem number that does not exist in the
cited work. Corrected in v7.2.

**Finding L4 — content dropped when §17 was rewritten.** v6's §14 carried:

> *"Three artefacts carry it, each built by an explicit gate; the largest holds 4,759 theorems, of
> which 283 are structural and the remainder are generated instances of a single criterion applied to
> an enumerated family."*

This did not survive into v7's §17. It is the paper's only statement of the scale of the development
and of gate coverage. Restored in v7.2, extended with Finding L1's exception.

---

## 5. Corrections applied in `PAPER_v7_2.md`

| # | correction | source |
|---|---|---|
| L3 | citation restored to Palelei (2026a, Theorem 3.1) | this check |
| L4 | artefact-and-gate sentence restored | this check |
| L1 | the one declaration outside the gated tree named | this check |
| L2 / audit F4 | `n − 3` bound given its first-band hypothesis, §14.3, §15, §18 | Lean `unit_never_blocks` |
| audit F3 | Theorem 14 given the loneliness hypothesis its minimum requires | audit v1 |
| audit F3b | `R < 16` restated so it does not presuppose existence | audit v1 |
| audit F5 | R4's prime hypothesis noted in §16 | audit v1 |

## 6. Still open — these need the author, not a script

**Audit F1.** Six results — Theorems 1, 2, 5, 6, 11, 13 — are stated with no argument, while §17
disclaims that the formalisation is part of the mathematical argument. The Lean exists and is clean,
so the mathematics is not in doubt; what is missing is written proof in the paper. Either the proofs
go in or §17 stops disclaiming.

**Audit F2.** §12 says of `{1,2,3,5}` that *"what is missing is a rule that names which"*, but R4's
hypotheses hold for it and R4 names the flank `e = 5` at `j = 1` — the very certificate the sentence
offers. §11's own table already says R4 reaches this case. The section's real point, that the
recursion does not close, is unaffected.
