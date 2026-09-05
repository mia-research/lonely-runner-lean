# CORRECTION — `ANALYSIS_semaev_cm_yield_mechanism_v1.md` mis-applied the LFD literature (extension-field → prime-field). Conclusion survives on a corrected, more fundamental basis.

**Date:** 2026-08-13. Prompted by a user challenge to verify the literature. Verification done by direct
source check (WebSearch + eprint abstracts), i.e. the `citation-verifier` function performed inline.
**Nature of the error:** a `[CITED]` claim inherited from `ANALYSIS_external_literature_survey_reconciliation_v1.md`
and propagated without checking; it is a **wrong application**, not a wrong conclusion.

---

## 1. The defective claim

`ANALYSIS_...v1 §2` stated: *"modern consensus (Last Fall Degree / CM-regularity — Huang–Kosters–Yang–Yeo;
Caminata–Gorla; Semaev–Tenti) shows the solving degree stays exponentially large **for prime-field
curves**"*, and hung "yield ≠ lever" on it.

## 2. What the literature actually says (checked)

- **Summation-polynomial index calculus is an EXTENSION-field technique.** Gaudry–Diem built it via Weil
  descent for `E(𝔽_{q^n})`; it is efficient "only for elliptic curves over non-prime finite fields of very
  small extension degree n" (the summation polynomials grow over-exponentially in n). Prime fields have **no
  subfield / no Weil descent**, so they are the hard, non-competitive case. `[CITED — verified 2026-08-13]`
- **The FFD/LFD debate is about `𝔽_{2^n}` / Weil-descent systems, NOT prime fields.** The
  `O(2^{n^{1/2+o(1)}})` first-fall-degree complexity claim and its refutation (Petit–Quisquater → Kosters–Yeo;
  Huang et al.; Semaev–Tenti Macaulay analysis) are all char-2 / extension-field statements. Caminata–Gorla
  (solving degree / last fall degree, eprint 2021/1611) is a **general** framework, not a "prime-field stays
  exponential" theorem. `[CITED — verified 2026-08-13]`
- **Prime-field summation-poly index calculus exists but is not competitive with generic √p.** Semaev's
  "naive" method; Petit et al.; Amadori–Pintore–Sala 2017 (eprint 2017/609) — the last "outperforms Semaev's
  original and Petit et al." by reducing to **one** Gröbner basis, but claims **no** advantage over Pollard
  rho. No known subexponential prime-field ECDLP. `[CITED — verified 2026-08-13]`
- **secp256k1 is a prime field.** Therefore the extension-field LFD results do not bound its Semaev-system
  solving degree, and citing them "for prime-field curves" is a category error.

## 3. ⚠ SELF-CORRECTION (2026-08-13, same day) — §3/§4 below committed a SECOND, worse error

An earlier revision of this correction wrote: *"prime-field index calculus is non-competitive with generic
√p in the first place, THEREFORE R1's CM yield cannot be a lever."* **That is suppression-by-declaration**
— the exact failure the core-bias memory names. It uses "**no KNOWN** competitive prime-field index
calculus" (the state of the art / a failed literature search) as if it were a **proof of impossibility**,
and it is **circular**: R1 is precisely the investigation of whether the CM/μ₆ structure changes the
prime-field picture, so citing the prime-field picture's current non-competitiveness to dismiss R1 begs the
question. Counter-prior: *"Not found is a failed search, never an absence."* The lever enquiry is **NOT
closed.** The corrected §3/§4 follow.

### 3′. What is actually established vs open

**Established (checked):**
- The LFD citation is extension-field (§2). Do not cite it for prime-field secp.
- **Yield is one factor among several** in index-calculus total cost
  `≈ (relations needed) × (attempts/relation = 1/yield) × (cost/attempt) + (linear algebra)`. A yield
  advantage is **necessary-not-sufficient** for a lever — it lowers the relation-collection factor but the
  net complexity depends on the full balance. `[structural, true]`
- No competitive prime-field summation-poly index calculus is **currently known** (Semaev/Petit/APS 2017 do
  not beat √p). `[CITED — a failed search, NOT a proof of absence]`

**OPEN (not closed by any of the above):**
> Does R1's CM yield advantage — which **grows** with `|V|` (~log, poss. poly) — lower the **total**
> prime-field ECDLP cost enough to matter, i.e. is it a lever or a contributor to one? Neither "yield is
> one factor" nor "no known competitive framework" answers this. It requires **measuring the total cost**
> with the CM enhancement, not declaring the framework non-competitive.

## 4. The lever question is TESTABLE — restored (not retracted)

`ANALYSIS_...v1 §4` mis-billed **P2 (solving degree under μ₆)** as "the" lever probe on the wrong (LFD)
basis. The correct framing: the lever test is the **COST probe** (the R1 plan's "consequential question,
§4"): measure the **total relation-collection cost** for j0 vs #E-matched non-CM at matched work, across
`|V|`, and see whether the growing yield advantage produces a **net** speedup (fewer Gröbner solves ×
cost each + linear algebra). **P2 (solving-degree-under-μ₆) and P1 (yield=Frobenius mechanism) are
COMPONENTS of that cost accounting, kept as live sub-probes — not closures.** None of these is retracted;
what is retracted is the *declaration that the answer is "no."*

## 5. What is untouched

- **The empirical R1 result** (`RESULT_semaev_cm_relation_yield_v4.md`, A1: CM yield grows ~log|V|) is
  unaffected — it is a measured, model-scale fact and its grade does not depend on this literature.
- **P1** (yield-mechanism = Frobenius/Weil point-count, testable on existing v4 data) is unaffected; but its
  grade in `ANALYSIS_...v1 §1/§3` should read **`[HEURISTIC — testable]`**, not `[DERIVED]`: the
  character-sum representation of the count is exact, but the claim that the CM Frobenius produces a
  *systematic mean* bias (vs a fluctuation) is a hypothesis P1 tests, not a derivation.

## 6. Source-level flag

`ANALYSIS_external_literature_survey_reconciliation_v1.md §3` carries the same loose phrasing ("stays
exponentially large for prime-field curves", graded `[CITED — verified from training]`). That attribution
should be corrected there too: the LFD result is extension-field; the correct prime-field statement is
"no competitive index calculus known (generic √p is best)." Flagged for a `citation-verifier` pass on that
survey line before it is cited again.

**Meta-lesson (for memory):** an inherited `[CITED]` tag is not verification. A conclusion can be right
while its cited basis is wrong (refuting a mechanism ≠ refuting the claim), and the fix is to re-derive the
conclusion on a checked basis, not to keep the broken citation because the headline survived.
