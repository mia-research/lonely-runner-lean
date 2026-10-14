# v11.5 → v11.6 patch summary

**Files:**
- Source: `lrc_proof_allN_v11_5.md` (782 lines, May 22 2026)
- Patched: `lrc_proof_allN_v11_6.md` (886 lines, May 26 2026, +104 lines)

## Patches applied

### 1. Header + new "Changelog" section (added)

- Version bumped 11.3 → 11.6.
- Date updated to 2026-05-26.
- New Changelog explains the period-correction errata and points to the empirical evidence (`LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md`).

### 2. §5.2 Theorem 5.2 — statement restated, proof corrected

**Statement change:**
- Restricted `A` from "any closed set with $\mu(A) > 0$" to "good set for an integer-speed family $u_1, \ldots, u_\ell$".
- This matches what §§10–11 actually use.
- The original (general) form is empirically FALSE — see new Remark 5.2-B with explicit counterexample (`n=5`, slow=(1,2), `p=3`, `A=[0.45, 0.55]`).

**Proof change (Step 2):**
- "G has period 1/L" replaced with "G has fundamental period 1/d where d = gcd(v_1,...,v_k)".
- Shift sequence is now `s_0 + k/d` instead of `s_0 + k/L`.
- Three-distance / Weyl argument adjusted: `d` base values at spacing `1/d` instead of `L` at `1/L`.
- Effective bound: $K \leq d \cdot \lceil 1/\mu(A) \rceil \cdot C(j)$ with `C(j)` from Erdős–Turán (polynomial in `j`).
- Total witness interval length $[0, B]$ remains finite, so the compactness argument in Step 3 still applies.

**New remarks added:**
- 5.2-A: explains why the structural restriction on A is necessary, and notes both call sites satisfy it.
- 5.2-B: explicit counterexample to the v11.5 general statement.
- 5.2-C: empirical-validity scope — 20,403 LRC-realisable hard-case inputs verified, 0 failures; notes 2 boundary-only cases.

### 3. §10.1 Step 1 — period parenthetical corrected

- "$G_s$ is periodic with period $1/L$ where $L = \operatorname{lcm}(v_1,\ldots,v_{n-2})$"
  → "$G_s$ is periodic with fundamental period $1/d$ where $d = \gcd(v_1,\ldots,v_{n-2})$".
- Inline note clarifies that this does not affect the proof (Step 4 only uses Theorem 5.2's conclusion).

### 4. §10.1 Step 4 — Theorem 5.2 invocation made structural

- Old: "(period $1/L$, $\operatorname{dens}(G_s) > 0$ from Step 1)"
- New: "($\mu(G_s \cap [0,1)) > 0$ from Step 1, fundamental period $1/d$ with $d = \gcd(\ldots)$, prime $p$, integer-speed target set $A$ defined by the single speed family $(u_1) = (q)$..."
- Makes the application of the restricted Theorem 5.2 fully explicit.

### 5. §11.1 Step 3 — period for $G_{\rm ind}$ corrected

- "$1/L_{\rm ind}$" → "$1/d_{\rm ind}$ where $d_{\rm ind} = \gcd(S_{\rm ind})$".
- Inline note clarifying coprimality with `L_ind` is still what Theorem 5.2 requires (the gcd correction is about the period of `G_ind`, not the coprimality condition).

### 6. §11.1 Step 4 — Theorem 5.2 invocation made structural

- Analogous to §10.1 Step 4 fix.
- Explicitly identifies `A`'s structure as `jointGoodSet(w_1, ..., w_r, q)` from `r+1` integer speeds.

## What did NOT change

- All theorem **statements** other than Theorem 5.2 are unchanged.
- Theorems 6.1, 7.1, 10.1, 11.1, 12.1: conclusions identical.
- Lemmas 2.1, 4.1, 9.1, 9.2, 9.3: unchanged.
- §3 base cases, §6 BSR, §7 LSR: unchanged.
- References (§13): unchanged.

## Remaining gaps (out of scope for v11.6)

1. **Effective Erdős–Turán bound** for $C(j)$ in the new Theorem 5.2 Step 2 is asserted but not derived in full. The bound exists in the literature (e.g., Kuipers–Niederreiter §2.5) but a self-contained derivation would strengthen the manuscript.

2. **Boundary-witness handling**: the 2 known LRC-realisable boundary-only cases are noted in Remark 5.2-C but the proof of Theorem 5.2 uses interior-of-$G$ in Step 2 (`s_0 \in G \cap [0, 1/d)`). The case where $G$ has no interior points in `[0, 1/d)` (boundary-only) needs either (a) extending Lemma 4.1 to provide interior witnesses, or (b) handling boundary cases separately. Empirically rare (2/20,403).

3. **Formal verification (Lean)**: the corresponding Lean refactor (`Theorem52_Weyl.lean`) needs to:
   - Restrict the `joint_fine_cell_exists` hypothesis to LRC-shape (eliminates 681 abstract counterexamples).
   - Or replace the fine-cell reduction with a direct interval-witness argument (matching v11.6 Step 2).
   - Add explicit boundary-witness clause (Fix 3 from the empirical findings).

These are separate work items; this manuscript revision focuses on the analytical errors only.

## Verification

- File parses as valid markdown.
- All §0–§13 sections present (verified by `diff` on section headers).
- No remaining "period $1/L$" claims (verified by grep — only occurrence is in changelog explaining the correction).
- Empirical scope (Remark 5.2-C) is independently checkable via `LonelyRunner/scripts/phase1_conclusion_check.py`.
