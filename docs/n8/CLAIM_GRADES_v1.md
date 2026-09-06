# Re-grading the 2026-09-06/07 n=8 claims

The session summary and `D7_ATTACK_v1–v5` / `P163_ARGUMENT_v1` state several
results at a higher grade than the evidence carries. This file restates each at
the grade it earns. Nothing here retracts a computation; what changes is the
scope and the strength of the words around it.

Grades: **PROVED** (derivation or exhaustive finite check) / **VERIFIED-INSTANCE**
(holds at the specific parameters tested) / **EMPIRICAL** (measured, no proof) /
**CITED** / **ASSERTED**.

---

| # | As written | Grade earned | Restatement |
|---|---|---|---|
| 1 | "Barajas–Serra 2008 is **fully machine-verified**, §7 included." | PROVED for the *theorem*; overclaim for the *paper* | `intLRC_seven` is proved in Lean, zero `sorry`, axioms `[propext, Classical.choice, Quot.sound]`, no `native_decide`. The paper's route is followed **except at §6.5 L727–732**, which is arithmetically unusable and is closed in our tree by an argument not from the paper. So: the **result** is machine-verified; the paper is verified *apart from one branch we replaced*. |
| 2 | "**Seven routes closed**, each with a reason." | mixed; mostly EMPIRICAL or VERIFIED-INSTANCE | Seven routes were **attempted and did not yield**, with a specific obstruction identified for each. Only the `j = tp` chain ("it is Lemma 4") is a derivation. "Counting" means *one* density bound is off by ≈1.75–2 **at the primes measured**, not that no counting argument exists — and §4 of `COLLAPSE_Z163_v1` now explains that factor rather than treating it as slack. |
| 3 | "It isn't a reduction, it's **the problem**. **Don't re-attack it** in full generality." | PROVED (implication) + ASSERTED (the instruction) | The implication *"Lemma 6 for all large `p`" ⟹ LRC for `k`* follows from Rosenfeld's own logic and was checked numerically at `p = 101, 1009`. It makes D7-in-general **at least as hard as** LRC for `k`. "Don't re-attack" is advice, not a finding; the finite-`p` version is a different statement and is open. |
| 4 | "**Covering is NOT the obstruction** — the gcd condition is." | overclaim; **now corrected** | Inferred from two witnesses (`k=6,p=31`; `k=7,p=163`). `COLLAPSE_Z163_v1` §4 supersedes it: `f(8,163) = 7` exactly, i.e. the cheapest cover uses all `k` speeds. **Covering is the obstruction; the gcd condition selects which covering problem must be solved.** |
| 5 | "The prefix route is therefore **dead** on its own." | VERIFIED-INSTANCE | Prefix minimum stays `≤ k` at `(6,23)` and `(6,31)`. That is two primes, not a theorem about prefixes. |
| 6 | "Counting **is refuted**, not merely unproven." | EMPIRICAL, scoped | The specific density count fails by 1.75× at `p = 163` and ≈2× at the earlier primes. A different counting scheme is not excluded. |
| 7 | "The asymmetry is **structural**, not quantitative." | was ASSERTED; **now PROVED** | Upgraded, not softened. The 2-adic cap table and the adjacent-vs-opposite pair classification (`COLLAPSE_Z163_v1` §2) derive the asymmetry and are verified exhaustively over all 648 admissible speeds × 163 classes. |
| 8 | "It is **the only route not yet closed**." | inherits #2 and #4 | Reads as "six or seven avenues are shut". What is true: one route was carried further than the others. With #4 corrected, the covering routes are not shut. |

## Standing correction to the method

Items 2, 4, 5, 6 and 8 are the same move: **a null or a non-yield written up as a
closure.** Item 4 is the one that cost something — it redirected the line away
from covering for the rest of the session, and it was wrong. Item 7 is the
opposite move and is the one that paid: an asymmetry that had been *asserted*
turned out to be provable, and proving it produced the `x = 5` decision.

Closure is a graded claim: to write *dead / refuted / closed / not the
obstruction*, name the object, the class of observable, the power and the scope,
or state it at the grade the evidence carries.
