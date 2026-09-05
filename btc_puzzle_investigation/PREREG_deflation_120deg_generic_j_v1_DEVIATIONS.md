# DEVIATIONS — `PREREG_deflation_120deg_generic_j_v1.md`

**Date:** 2026-08-01. **Status of the spec: WITHDRAWN BEFORE DATA. The run was never executed.**
**Gate:** `experiment-designer`, run pre-data as CLAUDE.md §2 requires. Verdict: 13 defects,
3 layers clean. Full audit in this file's §2.

---

## 1. Why it was withdrawn — the decisive defect (gate's M-5)

**T3 (`e₃ = εp·e₁`) and T4 (`e₄ = p²`) are FORCED under the premises the spec itself carries, so
neither can discriminate `j`.**

`ANALYSIS_n1_charpoly_collapse_v1.md` §1 derives `e₃ = εp·e₁` and `e₄ = p²` from the closure
`α ↦ ε·ᾱ` plus purity `|α|² = p`. That derivation uses only: `(x,y) ↦ (x,−y)` is inversion on `E`;
`χ₂^{(k)}(−1) = ε^k`; `h_k ∈ ℤⁿ`; Weil purity. **None of these mentions `j`.**

**Verified, not merely argued.** The underlying symmetry `h_k[−d] = ε^k·h_k[d]` was measured directly:

| curve class | primes | `h₁[−d] = ε·h₁[d]` | `h₂[−d] = h₂[d]` |
|---|---|---|---|
| `j = 0` | 43, 67, 79, 127 | 4/4 | 4/4 |
| generic `j`, `ε = −1` | 43, 67, 79, 127 | 4/4 | 4/4 |
| generic `j`, `ε = +1` | 73, 97, 109 | 3/3 | 3/3 |
| `j = 1728`, even `n` | 43, 67 | 2/2 | 2/2 |

Universal — including the even-`n` curves where T2 **fails**. So the closure is automatic and
`j`-independent (and strictly weaker than the `e₂` relation, which is what T2 tests).

**Consequences the spec did not state, all correct:**
- §7 row 1 would have fired with probability 1, and §8's falsification condition is unsatisfiable.
- The only conjunct carrying `j`-content is `e₂` — **already measured**, 30/30
  (`RESULT_jclass_B_relevance_check_v1.md`). The spec proposed to answer a question its own
  premises had already closed, using statistics that could not fail.
- What T3/T4 would actually test is **purity at every embedding** — the `[CITED]`, untested item A3
  of `ANALYSIS_n1_charpoly_collapse_v1.md` §4. That is a real open object, but it is not the object
  the spec named, and a pass would have been reported as evidence about `j`-specificity.

**This is my error and it is a specific one:** the automaticity of the closure was derived in-session
*before* the spec was written, and the spec was then built as though it had not been. The gate caught
what I had already established and failed to apply.

## 2. The full defect list (gate output, condensed)

**Clean layers — recorded so a clean result is visible as clean:** Newton's identities in §3 (signs
and denominators independently re-derived and matched); exact-arithmetic compliance of the reused
code path (no float in the signal path); the `j=1728` and `j=0`-supersingular structural exclusions
(both claims verified correct).

**Blocking defects, in the gate's priority order:**

| id | defect |
|---|---|
| **F-5** | The plant control **cannot fire**. `h₃[d] += 1` breaks divisibility by 3, so it yields `MODEL-FAIL` — which §5.4 counts as neither pass nor fail. Fix: plant `+3` / `+4`. |
| **F-1** | The frozen sampling rule (`j ∉ {0,1728}`, `n` odd) **excludes A0** (`j=0`) and **A3** (even `n`) — both controls unpopulatable by the spec's own rule. |
| **M-3/M-4** | *"Differ by a constant vector"* is the wrong equality convention for **composite `n`**: the correct condition is `Φ_n(x) \| w(x)`, and the constants have rank 1 of `n − φ(n)`. **Live on 8 of 18 curves in the prior primary arm** (`n ∈ {55,65,85,121,123,175,189}`). A spurious FAIL was directly reachable, and §8 makes one curve sufficient. Fix: work in `ℤ[x]/Φ_n(x)` and test for zero. |
| **M-5** | T3/T4 forced (§1 above). |
| **F-2** | `ε=+1` branch of T4: 3 curves, 1 prime, **0 control curves** — the identical single-branch coverage hole that `ANALYSIS_120deg_exact_factorization_certificate_v1.md` §3 had just found one layer down. |

**Also raised and accepted:** M-2 (`*` vs `∘` ambiguity in the Newton block), M-6 (T3/T4 not
independent conjuncts — both follow from the single pairing premise, so the diagnostic signature is
*both* failing), M-7 (cost stated for the cheapest cell; `p=67` `V₄` is 5.9× larger; the `sqrt_tab`
would need ~3.6 GB — the real failure mode is `MemoryError`, not a clean abstention), F-3 (6 of 13
primes carry no A0, so rows 1–3 are reachable by an empty-control path), F-4 (A3 is a demonstrated
firing control for T2 but only an *assumed* one for T3/T4), F-6 (outcome table not exhaustive —
no row for ABSTAIN, `MODEL-FAIL`, or an `ε`-split), F-7 (falsifier unsatisfiable at the 6 uncontrolled
primes), F-9 (power redefined as coverage, then no coverage number given; *"with certainty"* is a
quantifier error), F-10 (`SEED = 20260801` names no RNG, no call sequence, no arm order).

## 3. What replaces it

**Nothing, for the `j`-specificity question — it is already answered** to the extent this conjunction
can answer it. See `CORRECTION_deflation_overreach_v1.md` for the correctly-scoped statement and for
the real open objects this exercise surfaced (purity at every embedding; the `μ₆` action on the cell
index, which no statistic in the withdrawn spec projects onto).

**A future spec that wants T3/T4 must name a different object**: not *"is the 120° law `j`-specific"*
(closed), but *"does purity at every embedding hold at generic `j`"* — with the forcedness of the
`e₃`/`e₄` conjuncts stated up front, so a pass is not read as evidence it cannot be.
