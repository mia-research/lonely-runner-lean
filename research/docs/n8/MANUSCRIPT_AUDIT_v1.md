# Audit: the version chain, and what the manuscript is missing

2026-09-13. Owner's instruction, following two corrections in one session.

---

## 1. The version chain: nothing was dropped

Mechanical, `diff` over `MANUSCRIPT_v1 → v2 → v3 → v4`.

| | v1→v2 | v2→v3 | v3→v4 |
|---|---|---|---|
| lines removed | 8 | 1 | 12 |
| lines added | 19 | 41 | 20 |

**Every removed line is either the version stamp or text replaced in place by a corrected
version of itself.** They are listed in full in the commit messages: the `four → six` and
`81 → 79` counts (v2), the §11 insertion (v3), the abstract's part-7 error and the
`twenty → twenty-three` gate count (v4).

Structural checks:

- **Headings**: `v1` and `v4` are identical except that `v4` adds `## 11. Data and code
  availability`. Nothing removed.
- **Numbered results**: every `Prop`, `Thm` and `Cor` appearing in `v1` still appears in
  `v4`. None missing.
- **Word count**: 4,173 → 4,306 → 4,620 → 4,734, monotonically increasing.

**The versioning discipline held. Information was added, never dropped.** That is not the
problem.

---

## 2. The problem: the manuscript never contained the material in the first place

The manuscript covers `SKETCH_v7` §§1–7a and §§8–9. **Four sections of the sketch have no
counterpart in it at all** — verified by term search, not by reading impression:

| sketch section | term | manuscript | sketch |
|---|---|---|---|
| **§7b** the mixed reading, AP for the lower and grid for the higher | "mixed reading" | **0** | 3 |
| | "AP for the lower" | **0** | 2 |
| | "tier" | **0** | 2 |
| **§7c** the cascade | "cascade" | **0** | 4 |
| | "ceiling" | **0** | 6 |
| | "enlarged" | **0** | 9 |
| **§7d** the three regimes | "three regimes" | **0** | 2 |
| | "window-widening" | **0** | 4 |
| | **"irrational"** | **0** | **11** |
| **§10** the joint | "the joint" | **0** | 2 |

**These four are precisely the material that would have prevented this session's two
errors.** §7c is the cascade, whose absence produced the false counterexample. §7d is the
treatment of fractional and irrational speeds, whose absence produced my failure to
reproduce the owner's point about them.

---

## 3. The fractional point, now sourced

The owner: *"any fractional speed will not isolate in the first cycle ever. Moreover ap
dmin and cycle time is proportional to the fractions resolution."*

I tested this against the manuscript's window and did not reproduce it — the window returned
for every runner of `(1, 2, 3.123, 4, 5, 6, 7, 8)`. **That test was not wrong; it was aimed
at the wrong object, and `SKETCH_v7` §7d reconciles the two.**

- §7d's **window-widening lemma**: if the other six differences are multiples of `h`, their
  good set is `1/h`-periodic, and the window `[1/(8m), 7/(8m)]` has length `3/(4m)`, so it
  contains a **full period** whenever `m ≤ 3h/4`. A small `d_min` — which is what a
  fractional speed produces — makes the window **wide**, not narrow. That is why my window
  test returned.
- The owner's "first cycle" is the **intact pack's** cycle, period 1 — not the `d_min`
  window. §7d's worked example, `δ = √2/100`: `r1`'s first isolation is at **`71/8 =
  8.875`**, the ninth cycle of the pack. `DELAYED_ISOLATION_v1` measures it directly — a gap
  of `1/100` pushes the first isolation past **twelve cycles**.
- And the proportionality is confirmed in the example I ran: for `3123/1000` the AP lattice
  is `g = 1/1000`, the AP cycle time is **1000** and its instant is at **`t = 125`** — both
  scaling with the denominator, exactly as stated.

**So the owner's statement and my measurement are about different cycles, and §7d is the
section that says so. It is not in the manuscript.**

---

## 4. What this means for the manuscript

The manuscript is internally consistent and its results are proved. What it is **not** is a
description of the framework as the sketch now has it. In particular:

1. **§7.1's procedure is a reduction** — one lattice, one window, interval search. The
   framework's search is §7c's three tiers over `t = p/(8D)`. A reader implementing §7.1
   implements something else, which is what happened here.
2. **§7.3's Claim is stated about §7.1's procedure.** Whether it is the claim the framework
   makes depends on which search is meant, and the manuscript does not offer the choice.
3. **§1.3 says the construction "confines its evaluation to that first window"**, recorded
   as "a choice, not the target". §7d shows the evaluation is not so confined: the three
   regimes, the widened window and the enlarged step are all outside it.
4. **Nothing in the manuscript tells the reader that fractional or irrational speeds behave
   differently.** §7d and `DELAYED_ISOLATION_v1` both do.

---

## 5. Recommendation, not an action

**Nothing has been changed.** The manuscript is the owner's and the decision about scope is
his. Two coherent options, and they are different papers:

- **Keep the reduction and say so.** Retitle §7 to make explicit that it presents one tier
  of the framework, state §7.3's Claim about that tier, and add a section pointing at the
  cascade and the three regimes as the framework's actual search. Smallest change; the
  existing proofs and the Lean artefact stand untouched.
- **Bring §§7b–7d in.** Larger paper, and it would need the `[VERIFIED]` and `[CLAIMED]`
  grades of the sketch carried across honestly — §7c's cascade is `[VERIFIED — descriptive]`
  with an exhibited failure case, §7d's lemma is `[PROVED, given nonemptiness]` with an
  LRC(7) debt, and §10 is `[CLAIMED]`.

The second is the honest description of the framework. The first is the honest description
of what is proved. **They should not be blended.**
