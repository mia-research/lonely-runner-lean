# Lean vs v11.5 manuscript — drift report

**Session:** 2026-05-26 (continued)
**Manuscript:** `lrc_proof_allN_v11_5.md` (== `lrc_proof_v11_draft.md`, May 22 20:35)
**Lean:** `LonelyRunner/LonelyRunner/LRC/*.lean` (build clean, 2485 jobs)

## Headline

The Lean is **not** trying to prove what v11.5 states. The drift is **corrective**, not
inadvertent: v11.5's Theorem 5.2 is **false as stated**, and v11.5's proof contains a
structural error. Lean restricted the statement to a sound form, but its alternative
proof (`joint_fine_cell_exists`) is also false (today's finding). Both v11.5 and Lean
need rework.

---

## Statement-level drift: v11.5 Theorem 5.2 vs Lean `theorem52_nonempty_structured`

| Aspect | v11.5 (§5.2, line 328) | Lean (Theorem52_Weyl.lean:1512) | Drift |
|---|---|---|---|
| Slow speeds distinctness | Required (v₁,…,v_k distinct) | Not required | Lean strictly weaker; OK |
| Type of A | Arbitrary closed set with μ > 0 | Restricted: `jointGoodSet A_speeds n` | **Drift — Lean restricts because v11.5's general claim is FALSE** |
| p hypothesis | `p` prime | `1 < p` + `gcd(p, L_G) = 1` | Equivalent in practice (call sites pass prime) |
| G measure hypothesis | `dens(G) > 0` | `μ(G ∩ [0,1)) > 0` | Equivalent for periodic G |
| Period of G asserted? | **"G has period 1/L"** (line 351, 577) | Not asserted | **Lean correctly avoids the false period claim** |

### Why the A-restriction is correct, not drift

`memory/lean_theorem52_manuscript_flaw_2026_05_25.md` records a counterexample to
v11.5's stated form: `n=5, speeds=(1,2), p=3, A=[0.45, 0.55]` — the closed set A has
positive measure but no `t ∈ G` has `{pt} ∈ A`. Lean verified this in code + numerically
(10M samples). So v11.5 Theorem 5.2 is **literally false** as written.

The restriction `A = jointGoodSet A_speeds n` matches *exactly* what §10.1 and §11.1 of
v11.5 actually use (Lean's Option A reformulation). This is sound; the drift was
corrective.

### Why the period claim matters

v11.5 line 351 ("Fix s_0 ∈ G ∩ [0, 1/L), which exists since dens(G) > 0 and G has
period 1/L. The shifted sequence … lies entirely in G by 1/L-periodicity.") is the
load-bearing step of v11.5's proof. But:

- For G_s = ⋂ᵢ {t : ‖vᵢt‖ ≥ 1/n}, each Gᵢ has period **1/vᵢ**, not 1/L.
- The intersection G_s has period lcm{1/vᵢ} = **1/gcd(vᵢ)**.
- After §2.2 GCD normalisation, `gcd(all speeds incl. V) = 1`, but `gcd(slow speeds alone)`
  may be `d > 1` (e.g., slow speeds {2, 4, 6}, V = 1 → gcd(all) = 1, gcd(slow) = 2).
- So G_s has period 1/d in general, NOT 1/L.

When `d < L` (typical), v11.5's Step 2 of the Thm 5.2 proof is unsound — there might
be no `s_0 ∈ G ∩ [0, 1/L)`, and the shifted sequence `s_0 + k/L` may leave G.

v11.5 §10.1 line 577 also makes the same false claim ("G_s is periodic with period 1/L"),
but §10.1's STEP 4 only uses Theorem 5.2's CONCLUSION, not its proof. So §10.1's logical
structure is sound provided Thm 5.2's conclusion is true for its specific inputs. The
question is whether anyone has actually proved that.

---

## Proof-level drift: §10/§11 chain

| Manuscript step | v11.5 mechanism | Lean equivalent | Status |
|---|---|---|---|
| **§10.1 Step 1** μ(G_s) > 0 | Lemma 4.1 + H(n-1) | `lemma41_positive_measure` + periodicity bridge | ✓ proved |
| **§10.1 Step 2** Fundamental Identity reformulation | Lemma 2.1 | `circDist_fundamental` / `DI_goodSet_rewrite` | ✓ proved |
| **§10.1 Step 3** Measure of A = (n-2)/n; gcd(p, L) = 1 | direct + hypothesis | `setA_DI_pos_measure_in_unit` + `hcop` | ✓ proved |
| **§10.1 Step 4** Apply Theorem 5.2 | Reference to Thm 5.2 | `theorem52_nonempty_DI` → `theorem52_nonempty_structured` → **`joint_fine_cell_exists` SORRY** | ✗ blocked |
| **§10.1 Step 5** Verify slow + V | Trivial from Step 4 | done in `theorem101_DI` after the sorry | ✓ proved |
| **§11.1 Step 1–3** analogous | Lemma 4.1 + H(n-r) + H(r+3) | Various | ✓ proved |
| **§11.1 Step 4** Apply Theorem 5.2 | Reference | `theorem52_nonempty_ModDI` → same sorry | ✗ blocked |

The Lean chain MATCHES v11.5 exactly at every step except the "Apply Theorem 5.2" step,
where the Lean introduces a new intermediate (`joint_fine_cell_exists`) not in v11.5.

That intermediate is what we proved FALSE today (681 LRC-like counterexamples). So:

- **Lean's reformulation is faithful to v11.5's USAGE pattern** (same inputs, same
  conclusion expected).
- **Lean's INTERMEDIATE strategy fails** (joint fine cell route is broken).
- **v11.5's strategy ALSO fails** (period 1/L is wrong).

Neither the manuscript nor the Lean has a working proof of the Step 4 conclusion.

---

## What we actually need (the working hypothesis)

Both v11.5 §10.1 and §11.1 STATEMENTS are believed true (consistent with LRC for the
relevant n). They both reduce to:

> ∃ t ∈ G_s such that ∀ j: ‖vⱼ t‖ ≥ 1/n AND ‖V t‖ ≥ 1/n.

This is just LRC for `(v₁, …, v_{n-2}, V)` at threshold `1/n`, but with the hard-case
hypothesis. The "Apply Thm 5.2" step in v11.5 (and `theorem52_nonempty_DI` in Lean) is
an attempted inductive reduction; both inductions are currently broken.

For Lean specifically: per the previous audit, even Option D (interval-witness
pigeonhole using Lemma 4.1's explicit δ) is blocked by the DI hard-case hypothesis
`V ≤ (n-1)·V_slow_max` — the inequality goes the wrong way.

---

## Recommendations

### For the manuscript (v11.6 or v12)

1. **Restrict Theorem 5.2's statement** to match what §10/§11 actually need:
   the closed A must come from the jointGoodSet structure of a single integer-speed
   family. The general "any closed A" form is false; do not state it.

2. **Replace Theorem 5.2's proof.** The irrational perturbation + Weyl + 3-distance
   route depends on the wrong "G has period 1/L" claim. Sound replacements:
   - Use period 1/gcd(slow speeds), and adjust the arithmetic of Step 2 accordingly.
     (Likely still works but requires re-derivation of the bound K.)
   - Or fold Theorem 5.2 into Theorems 10.1 / 11.1 — prove the DI / ModDI conclusion
     directly via a single argument that doesn't separate the joint condition.

3. **Remove the false "period 1/L" assertion from §10.1 line 577 and §11.1.** These
   don't affect logical soundness of §10/§11 (Step 4 only uses Thm 5.2's conclusion),
   but they perpetuate the same error and should be corrected.

### For the Lean

1. **Decide on the right intermediate**: either prove a sound (restricted) Theorem 5.2,
   or skip it entirely and write Theorems 10.1 / 11.1 directly.
2. **Remove `joint_fine_cell_exists` as the gateway lemma** — it's known false.
   Either replace with a stronger-hypothesis form provable from interval witnesses
   (only works when `V > (n-1)·V_slow_max`, i.e. the LSR case which Thm 7.1 already
   handles) or replace the entire reduction.
3. **Audit theorem101_DI and theorem111_ModDI to see if a direct proof using H(n-1)
   and Lemma 4.1's interval witness is feasible without going through Theorem 5.2.**

---

## Bottom line for this session

We are NOT proving v11.5's literal Theorem 5.2 (because it's false). We're proving a
restricted version that matches v11.5's USAGE, and we just discovered that even the
restricted version's proof strategy is broken.

The drift is corrective and well-documented; the deeper issue is that **the manuscript's
proof of Theorem 5.2 itself contains a structural flaw** that has been masked by the
fact that nobody re-derived the period of G carefully.

This is a manuscript-level finding, not just a formalisation gap.
