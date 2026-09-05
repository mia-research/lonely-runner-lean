# REFERENCE — external methodology imports (searched 2026-08-01)

**Status: reference only.** Nothing here is adopted, and nothing here grades or re-grades any
claim in this corpus. Banked for future review at the user's request.

**Provenance:** web search conducted 2026-08-01 during the process review of session
`local_55348e2f`. This file answers *"how do other fields conclude rigorously"* — the
**problem-domain** axis. It is **not** the process/recording axis (narrative closure
overwriting the record); that search is separate.

---

## 1. Blind analysis — nuclear & particle physics

The only technique found that acts on the **generator** of bias rather than filtering its
output. The analyst works with the answer hidden (random offset added to the result, or a
"hidden signal box"), and commits to the conclusion **before unblinding**.

- Motivating problem, in their words: experimenter bias is "frequently unconscious and can
  take quite subtle forms."
- Named failure mode — **stopping bias**: continuing to analyse, find mistakes, or improve the
  analysis *until the result agrees with expectations*. Described as probably the most common
  bias in the field.
- Empirical tell: the Particle Data Group's record shows measured values drifting over time
  **but never by more than one standard deviation** — the signature of tuning-to-expectation.
- Three implementation families: (i) set selection cuts without seeing their effect on the
  result; (ii) search for rare processes without seeing the result; (iii) BABAR's hidden
  signal box. Encryption by adding a fixed random offset, or by transforming a variable.

**Fit to this corpus:** the harness already constructs real-vs-constructed arms and matched
permutation nulls. Blinding = label the arms with a hidden key, write the conclusion, unblind
afterwards. Cheap.

- <https://www.pp.rhul.ac.uk/~cowan/stat/annurev.nucl.55.090704.pdf>
- <https://arxiv.org/pdf/2311.13542>

## 2. E-values / safe anytime-valid inference

An e-value is a continuous measure of evidence, valid **regardless of how often the data are
inspected or how the sampling plan changes**. `1/E` behaves like a conservative p-value.
Optional stopping is permitted; the stopping time need not be pre-specified.

**Fit:** supplies a quantity that can **increase** with further work. Every gate currently in
this project (matched null, firing control, OOS retest, forced-statistic pre-screen,
closure-grade) is a filter and can only remove. An e-process gives a lever a *state* rather
than a verdict — e.g. an in-sample flicker that fails OOS is "e went to 3 then fell", not
"dead".

- <https://arxiv.org/pdf/2210.01948>
- <https://arxiv.org/html/2603.24421>

## 3. Equivalence testing (TOST) with a pre-specified SESOI

A non-significant result reports insufficient precision. Only a test *designed* to support
equivalence can claim absence. Pre-specify the smallest effect size of interest, then run two
one-sided tests against equivalence bounds.

**Fit:** this is the grade the vocabulary lacks. Not "the lane is null" but
`[BOUNDED: |effect| < δ at power π, scope Σ]` — a **magnitude**, which is what
`feedback_negative_bias_enlarge_nulls` already insists a bound is. Stating δ requires stating
the scope, so scope substitution becomes hard to write.

- <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC5502906/>
- <http://daniellakens.blogspot.com/2016/05/absence-of-evidence-is-not-evidence-of.html>
- <https://arxiv.org/pdf/2305.04587> (replication of null results: absence of evidence vs evidence of absence)

## 4. Multiverse / specification-curve analysis

Enumerate every defensible decision node (here: prime range, readout, width, statistic, null
construction), run **all** of them, and report the surface rather than one point. Three steps:
identify the justified/valid/non-redundant specification set; display graphically so
consequential decisions are visible; conduct joint inference across specifications.
Formalised by Simonsohn, Simmons & Nelson (2020). A registration tool exists.

**Fit:** the established form of an "uncovered scope" block.

- <https://bookdown.org/mike/data_analysis/specification-curve-analysis.html>
- <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC12567067/>
- <https://journals.plos.org/plosone/article?id=10.1371%2Fjournal.pone.0339452>

## 5. Claim–evidence binding (the "composer", already specified elsewhere)

Google's **Chain-of-Evidence** / **Science One** framework: every claim carries a recorded
evidence chain (*completeness*) and each chain must genuinely support its claim
(*correctness*). Numerical claims trace to a recorded output; method claims to an
implementation; conclusion claims derive from supporting claims through verifiable reasoning.
Related: **PaperTrail** (decomposes answers and sources into discrete claims),
**FactReview** (execution-based claim verification; output is claim-level labels with linked
evidence, not free-form critique), **Agent-Native Research Artifacts** (typed,
machine-traversable claim–evidence bindings).

**Fit:** read this spec before building any local claim-composer.

- <https://research.google/blog/science-one-framework-a-verifiable-autonomous-research-framework-via-chain-of-evidence/>
- <https://arxiv.org/pdf/2605.26340>
- <https://arxiv.org/html/2602.21045v1>
- <https://arxiv.org/html/2604.04074v1>
- <https://arxiv.org/pdf/2604.24658>

## 6. Process forms with no code

- **Registered reports / results-blind review** — acceptance decided on the protocol with
  results blinded; publication guaranteed once the protocol is accepted, so "no positive or
  challenging results are necessary." Translated: *an item is done when its protocol executes,
  whatever it returns* — which severs "the turn produced value" from "the turn produced a
  verdict."
- **Adversarial collaboration** (Kahneman) — parties (1) articulate each other's positions in
  good faith, (2) **agree ex ante on methods both sides accept as a fair test with the
  potential to change their minds**, (3) publish jointly regardless of outcome. The missing
  element here is (2): nothing is committed in advance about what would move either side.
- **Preregistration with temporal commitment** — timestamped external record (e.g.
  aspredicted.org) proving the analysis plan preceded data access.

- <https://en.wikipedia.org/wiki/Registered_report>
- <https://web.sas.upenn.edu/adcollabproject/about/>
- <https://arxiv.org/pdf/2606.27687> ("Mitigating LLM-based p-Hacking by Preregistering for the Next LLM")

## 7. The relevant negative result

*Quantifying and Mitigating Premature Closure in Frontier LLMs* (arXiv 2605.15000). Defines
premature closure as "inappropriate commitment under uncertainty: providing an answer,
recommendation, or guidance when the safer response would be clarification, abstention,
escalation, or refusal." Measured false-action rates **55–81%** (MedQA) and **53–82%**
(AfriMed-QA) when correct answers were removed; ~30% on open-ended HealthBench, 78% on
physician-authored adversarial queries.

**The load-bearing part:** the only mitigation tested was safety-oriented **prompting**. It
reduced the rate and **residual failure persisted**. No structural intervention was tested.

This corroborates CLAUDE.md §2b (instruction-based correction ≈ 0 on this project) from an
independent source, and it is the reason structural routes are preferred over better wording.

- <https://arxiv.org/abs/2605.15000>

---

## What this file does NOT cover

The **recording layer** — narrative drive overwriting the faithful record of what a run
returned. Different literature (summarisation faithfulness, structured/constrained
generation, agent observability and trace logging, self-report unfaithfulness). Searched
separately; see the companion file.
