# Review of `PAPER_v7_4.md` — what is missing from the manuscript, and framing

*2026-09-23. Target `PAPER_v7_4.md` (13,683 words) against `MANUSCRIPT_v20.md` (48,317).
Checks run mechanically; each finding names the object it was checked against.*

---

## 1. The major gap: §0 is absent entirely

`MANUSCRIPT_v20` opens with **§0, "What a proof is in this framework"**. The paper contains
**none** of it — zero occurrences of "what a proof", "A proof is", "foreign shape", "obligation".

§0 states the framework's own completion criterion:

> **A proof is a finite list of cases. Each case is a condition on the difference set together with
> a proof that `(e, k)` exists on that condition. The list closes when the conditions are jointly
> exhaustive.**

and its ground:

> exhibiting a flank and an opening index is not evidence *for* the conjecture. It **is** the
> conjecture, restated in the framework's own objects.

**Why this is the biggest finding.** Without §0 the paper's §10 reads as seven unrelated sufficient
conditions and §11 as a report on how much they happen to reach. With §0 they read as what they are:
**§10 is the list of cases; §11 is the exhaustiveness argument, with two of three regions of an
exhaustive trichotomy closed.** That is a materially stronger and more coherent account of the same
material, and it is the author's, not an interpretation.

§0 also carries three things a referee will otherwise demand, and which the framework refuses on
stated grounds:

| §0 item | consequence for the paper |
|---|---|
| **"A case proved is proof of that case."** Partial results are real here in a way they are not under a cap | R1–R7 are not partial credit; each is a closed case |
| **"Existence is all that is owed, not a formula."** Discharge by pigeonhole, contradiction, induction or construction | pre-empts "but you have no closed form for `e`" |
| **Three foreign shapes** — a cap, a move count, a uniform theorem — each *more* than is owed | pre-empts the three strengthenings a referee is most likely to ask for |

And one distinction that is subtle, load-bearing, and nowhere in the paper: **pigeonhole and residue
counts are admissible as *tools*; what is banned is covering as a *statement form* — forming a
complement and showing it empty.** §0 records that this was misread "for most of the work recorded
in §16, at cost."

**Recommendation.** §0's content belongs in the paper's §9, which currently states the existence
question but not the framework's criterion for answering it. It is roughly a page and it changes the
reading of §§10–11.

---

## 2. Smaller omissions

**§3's clear-interval bound.** `Proposition 3.1`: each in-the-way zone has width `1/(4s)` and
consecutive zones are separated by a **closed clear interval of width `3/(4s)`**. `[PROVED —
blocked_width, clear_width]`. The paper's §2.1 gives the boundary discipline qualitatively and never
quantifies it. This is the quantitative form of the paper's own foundational section, it is proved,
and it costs two lines. Checked: no occurrence of `1/(4s)` or `zone has width`.

**§12, depth as a function on the profile space.** Absent. Flagged as a decision in the section map
(Part E.2), not resolved.

**§6A the firewall, and §5 no external dependency.** Absent, and this is defensible for a submission
— they are the project's self-discipline apparatus rather than mathematics. But §0's foreign-shapes
table is the part of that apparatus a *referee* needs, and it should travel even if the rest does not.

---

## 3. Framing

**3.1 The paper's story is weaker than its material.** As written, §§10–12 say: here are seven rules,
here is what they reach, here is a trichotomy with an open middle. With §0 in place the same sections
say: the proof form is a finite exhaustive case list; here are the cases; here is the exhaustive
partition they are being fitted to; two of its three regions are closed. The second is both more
accurate and more compelling.

**3.2 §9 is the natural home and is currently thin.** It states the universal quantifier correctly
and stops. It should state what discharging it would consist of, which is §0.

**3.3 The title is now supported by material the paper does not contain.** `Deformations of Global
Isolation` promises the deformation account; §3 delivers the `φ(n)` law and the perturbation
criterion, then hands off to the cascade. The measurements of 2026-09-22 (§4 below) are the
deformation account and are not in either document.

---

## 4. Findings of 2026-09-22 not yet in the manuscript

These are **mine, ungraded, and not in `MANUSCRIPT_v20`**. They belong there before the paper, per
the standing order. Exact rational arithmetic throughout; artefacts in `experiments/nN/`.

| finding | artefact | status |
|---|---|---|
| At the AP, **six of eight subjects have positive-measure isolation**; only the two extremes are measure zero (`|L|` = 0, 1.75, 2.92, 6.67, 6.67, 2.92, 1.75, 0 on `(0,20]`) | `global_vs_individual_v1.py` | `[VERIFIED — exact, one arrangement]` |
| **Fragility is a property of the coincidence, not of isolation**: the global set is measure zero before and after perturbation, while individual sets are robust | same | follows from the above + Theorem 6 |
| **Deformation opens the extremes**: their minimum `|L|` rises `0.10 → 0.69 → 0.71 → 1.27` as deviations grow toward a full gap | `transport_full_gap_v1.py` | `[EMPIRICAL — 200 draws per level]` |
| **The AP's reading is literally reusable nearby**: the same instants remain lonely under deformation, transport holding to ~`1/10` of a gap and failing by `1/4` | `transport_v1.py`, `transport_full_gap_v1.py` | `[EMPIRICAL]` |

The first two directly support the title and explain why the two extreme subjects are the hard ones
— which §16 already says on other grounds (*"both extreme subjects of every arrangement carry the
full `n − 1` disparities"*).

---

## 5. What is already sound

Sixteen numbered results, each with a proof (v7.4's addition). §17's disclaimer is now true. All ten
caveats from the section map are present and verified. No dangling cross-references. Citations to
Palelei (2026a/2026b) resolve — 24 sections and 31 theorem numbers checked, 0 missing. Every Lean
declaration named in §17 exists; 44 of 45 in the gated tree, the exception named.
