# Specialist agent design — evidence from the last several sessions (2026-07-17)

## The finding that should drive the design

**There are 17 `feedback_*` memories on the books. Each precisely describes a failure mode. Every
one of those failure modes recurred anyway.**

| memory | age | what happened anyway |
|---|---|---|
| `self_cert_words_audit_trigger` | pre-existing | I wrote "**genuinely** uniform" and "**Genuine** arithmetic coupling" into master v2 — **minutes after writing the ban into that same document myself** |
| `distinguish_proved_from_closed` | 2026-06-15 | H4 (a month later) converted 5 open frontiers into a closure |
| `proof_not_test` (★ recurring) | 2026-07-13 | master v1 tagged first-fall degree `[PROVED, general m]` on an unproven implication |
| `conditional_negatives` + `scope_negatives_tightly` | 2026-07-10 | master v1: "door map (**each shut**)"; "transfers no advantage" (widened from `Hom=0`) |
| `negative_bias_enlarge_nulls` | 2026-07-17 (same day) | the closure frame was already sitting in the master while the memory was being written |

**Instruction-based correction has a measured track record on this project: ~0.** Writing an 18th
memory, or building an agent whose job is "be more careful and remember the rules", is the
intervention that has already failed 17 times. It fails because the bias is not a knowledge deficit
— I *know* the rules, I *wrote* several of them — it is a generative prior that operates below the
level the rule addresses.

## What actually caught things today

Every catch was mechanical. Not one was caught by careful reading.

| catch | mechanism |
|---|---|
| Semaev "typo" refuted | script: 1406/1406 vs 0/1406 |
| `(1−π)−1` misparse refuted | script: `N(1−π)=1−t+p=n` exactly |
| Sextant digits | exact rational `t²/2p−1` |
| Frame provenance (enters at H4) | grep across all handovers |
| **Frontier liquidation (5→0)** | **item-by-item trace** |
| My own compile dropping H3's phrase | diff: 12/12 phrase check |
| Self-cert words in my own v2 | grep |
| Stale banner (`6007` vs `100003`) | scan |
| `C_T` anomaly dissolved | matched surrogate |
| Drill v1's junk-row fit | the surrogate, not a better fit |

## The critical refinement: mechanical is not sufficient — it must be OBJECT-level

**My tag count was mechanical and it was wrong.** It reported "master carries *more* `[PROVED]` tags
than H3, same `[HEURISTIC]` — no degradation", while 5 frontiers had been liquidated. It measured a
**proxy** (tag tokens) instead of the **object** (each open item). The master had preserved H2's
stale panel list, which made the proxy look healthy.

So the design rule is not "use scripts". It is:

> **Every agent must name the OBJECT it tracks and check that object directly — never a correlate
> of it.** An agent that reports a count, a ratio, or a score without naming what object that number
> stands for is reproducing the tag-count failure.

## Assessment of the three proposed agents

### 1. Memory drafter — **YES, strongest case, but reframe as adversarial**
Evidence: my memory file *this session* was wrong on first write and would have taught future
sessions "the external critique was wrong" — entrenching the exact failure it was recording. Memory
is uniquely dangerous: it is load-bearing across sessions, never re-derived, and **never audited**.
It is the one artifact that propagates bias forward with compounding.

Reframe: its job is not to *write* memories well. It is to ask **"what would a future session
DO WRONG because of this memory?"** and to check the memory against the *artifacts* (scripts, diffs),
not the session narrative. **It must not be shown the conversation** — the narrative is the
contaminant.

### 2. Careful drafter — **YES, but the framing is wrong; make it a COMPILE-DIFF agent**
The H3→H4 degradation was **not carelessness**. It was **summarization**. Compression is lossy, and
the loss is *not random*: it preferentially drops caveats, because caveats are the least narrative
content in the source. A "careful drafter" made of the same model, summarizing the same corpus, has
the same prior and produces H4 again.

What actually worked was the compile rule + a mechanical loss report (`37/37 script refs`,
`12/12 H3 phrases`). Reframe: **output a LOSS REPORT, not prose** — every predecessor open item,
retraction, and caveat, with where it landed. Much of this should be a **script**, not an agent.

The notation half of the request is real and separable: `(1−π)−1` cost an entire external analysis
because `−1` read as an exponent. That is a **linter** (ambiguous notation, banned words, stale
numbers), not a judgment task.

### 3. Experiment designer — **YES, but reframe as PRE-REGISTRATION**
Evidence: drill v1 had a silent filter (8 primes → 3), two junk rows (n=146, n=3353), and produced
`p^(−0.36)` — an exponent that reads as *intermediate, therefore interesting*. It was an artifact.
I caught it, but only after running.

The mechanism that matters is **ordering**: specify the statistic, the matched control, and the
power calculation **before seeing data**. Post-hoc, any exponent can be rationalized. Reframe:
**pre-registration** — the agent's artifact is a written test spec (statistic / control / power /
scope / what result would falsify) produced *before* the run, checked against the run afterward.

## What is missing: a CITATION VERIFIER — **ADD, highest immediate value**

Not proposed, but the evidence is strong:
- Appendix C lists **6 cited inputs, all marked "verify before relying", and NONE verified.**
- **Boneh–Shparlinski was already mis-cited** — used to support a `⟺` it does not prove.
- **Lange–Shparlinski uniformity in `(b,c)` is load-bearing for Part V-2 AND the whole `T_y` bound**,
  and nobody has read the paper. It is §X.2, the top open item in the master.
- CLAUDE.md §5 already names this as a recurring, expensive failure: *"Three separate times a
  'hard/research-grade' obstacle dissolved the moment the paper's own treatment was read."*

This is a distinct skill (locate the theorem, check its hypotheses match our use, report the delta)
and it is the current bottleneck. **Highest expected value of the four.**

## What NOT to build

**A general adversarial reviewer.** GLM-5.2 *was* exactly that: asked to find overclaiming, it
produced four confident, well-structured, entirely false findings — while being right in thesis.
CLAUDE.md §3 already names it: *"reviewers asked for issues will manufacture them."* A red-team
agent with no decidable-artifact requirement manufactures findings and costs more to refute than to
run. If adversarial review happens, it must be constrained to **findings verified by a script the
agent itself ran and reports.**

## The binding rules for all four agents

1. **Decidable artifact.** Output a script, diff, count, or spec — never a judgment. "This looks
   overclaimed" is not a finding; "this claim's own script grades it CITED, the doc says PROVED" is.
2. **Object-level, not proxy.** Name the object tracked. No scores standing in for things.
3. **Context isolation.** Never show an agent the session narrative or the document's framing — only
   the raw material + the criteria. The frame is invisible from inside; isolation is the only defense
   against it, and it is the actual mechanism by which a subagent helps (not "more care").
4. **Power and scope on every number.** (Anomaly-Drill rule 2–3.)
5. **A finding the agent could not have gotten wrong is worth more than ten it might have.**

## Risk to state plainly

Four agents made of the same model share the same prior. **More agents = more surfaces for the same
bias**, unless rules 1–3 bind. The reason to expect these to work where 17 memories did not is
*not* that they are better instructed — it is that (a) they are forced to emit a checkable artifact,
and (b) they are structurally denied the narrative. If either property is dropped, expect the
failure to recur.
