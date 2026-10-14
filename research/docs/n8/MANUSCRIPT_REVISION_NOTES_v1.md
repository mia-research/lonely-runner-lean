# Manuscript revision notes

2026-09-13. Against `MANUSCRIPT_v1.md`. Owner review received; two must-fixes applied,
remainder recorded for the full revision.

---

## Applied

| | item | resolution |
|---|---|---|
| **1** | **Prop 3.3 baseline hole.** The statement said "no single **other** reading", the proof covered only `s′ ≥ σ`, and the baseline `s_1 = 1` escapes when `σ > 1`. Owner's counterexample: `σ = 8` from `(0, 1, 9, …)`, where `σ`'s clear interval `[57/64, 63/64]` lies wholly inside the baseline's zone `(7/8, 9/8)`. | Statement now excludes the baseline. **The Lean declaration `no_solo_closure` already carried `σ ≤ s′`** — checked — so this was prose-only, as the owner predicted. Added the reason the exclusion costs nothing: the baseline has **no zone inside the window at all**, since the zones of `s = 1` are `((8k−1)/8, (8k+1)/8)` and meet `[1/8, 7/8]` in neither direction. That is how §1.3 defines the window, so the counterexample sits outside where the proposition is used. |
| **2** | **§7.3 undersold the sweep.** "Nothing above `v_8 = 20` is covered" was stale. | Updated to `v_8 ≤ 40`: 18,564,316 arrangements, 148,514,528 runner-instances, zero failures, exact rationals. Added the location distribution and the worst witness. The bounded-family caveat is kept and re-pointed at 40. |
| **3** | Duplicate 85-theorem sentence in the abstract. | Cut. |
| **4** | "Six of seven parts" without the 2(b) nuance. | Abstract now says the seventh is cited to prior work, not re-derived, and is the only external dependency. |
| **5** | §1.2 used "reading" unglossed. | Glossed in place as *the set of instants at which every other runner is simultaneously clear of it*. |

**Both must-fix figures were verified independently before being written in**, not taken
from the review: the record was located, its counts re-derived (`8 × 18,564,316 =
148,514,528`; `C(40,7) − 18,564,316 = 79,244` gcd-removals), and the worst witness
recomputed from the speeds — `V = (0, 3, 10, 16, 18, 22, 33, 38)`, `d_min = 5`,
`u* = 245/304`.

## Open for the full revision

**A. Data availability — the evidence is in a different repository.** The `v_8 ≤ 40`
record is `~/ZCodeProject/lrc-n8/results/exhaustive_exact_vmax40.json`, with its generator
at `scripts/exhaustive_exact.py` in that same tree. It is **not** in this repository, and
the Lean development is. A submission needs both reachable from one place with a SHA-256
per artefact. This is the largest outstanding item and it is logistical, not mathematical.

**B. The witness index is 0-based.** The record's `u_max_runner: 7` denotes the **eighth**
runner, speed 38. One-based `r7` is speed 33, which returns at `u = 1/8`. The manuscript
now says "the eighth runner" to avoid the ambiguity; anyone quoting the JSON directly
should note it.

**C. The title.** `Bounding` collides with §6.1, whose point is that bounding arguments
cannot close this. The two senses differ — §6.1 rules out bounding *how little the
obstructions amount to*, while the title means the framework *supplies* bounds — but a
skimming referee meets the collision before the distinction.

*Recommendation:* **`A Local Framework for Eight Lonely Runners`.** Locality is the
paper's organising idea — §1.1 is entirely about it, the three objects are local, the
whole contribution is that it is per-runner — and it carries no collision. Left unchanged
pending the owner's decision, since `Bounding` was a deliberate choice.

**D. Not yet drafted.** A data-availability section; a statement of the Lean toolchain and
mathlib revision; and whether §6's negative results warrant their own short note, since
they are the part most useful to other people working on the problem.

---

**Unchanged by this review:** every grade. Parts 1–6 `[PROVED]`, 2(b) cited, part 7
`[CLAIMED]` and unstated, LRC(8) not proved.
