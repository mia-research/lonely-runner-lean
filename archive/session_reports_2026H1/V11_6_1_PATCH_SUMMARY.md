# v11.6 → v11.6.1 patch summary

**Files:**
- Source: `lrc_proof_allN_v11_6.md` (887 lines, May 26 2026)
- Patched: `lrc_proof_allN_v11_6_1.md` (986 lines, May 26 2026, +99 lines)

**Driver:** mid-session audit + DeepSeek follow-up investigation into the explicit Erdős–Turán bound.

## Patches applied

### 1. Header + new "Changelog (v11.6 → v11.6.1)" section (added)

- Version bumped 11.6 → 11.6.1.
- New changelog at the top of the file explaining the three corrections below.

### 2. §1 Introduction outline — stale "period $1/L$" parenthetical removed

- Old (line 93, inherited from v11.5): "Weyl equidistribution on the slow-runner good set (period $1/L$, $\gcd(p,L)=1$) produces the required time."
- New: "(fundamental period $1/d$ where $d = \gcd$(slow speeds); $\gcd(p, L) = 1$ where $L = \operatorname{lcm}$(slow speeds))".
- Cosmetic but the only remaining "(period $1/L$)" assertion in the file outside the changelog/erratum text.

### 3. §5.2 Step 1 — irrationality bookkeeping corrected

- Old: text checked "$\alpha_j / L$ is irrational" before invoking Theorem 5.1.
- New: text checks "$\alpha_j / d$ is irrational" — the actually-required condition, since $G$ is $1/d$-periodic (corrected in v11.6 Step 2). A parenthetical note explains why the old text was logically muddled (both irrationals are true, but the proof's hypothesis is keyed to the period denominator).
- Adds an explicit cross-reference: "(see Step 2 for the period derivation)".

### 4. §5.2 — new Lemma 5.2-D + Corollary 5.2-E + Remark 5.2-F

Inserted after Remark 5.2-C (~lines 511–586).

**Lemma 5.2-D (Coprime-$n$ Explicit Witness).** For distinct positive integer
speeds $v_1, \ldots, v_{n-1}$ and $n \ge 3$, if every $v_j \bmod (n v_1) \in
[v_1, (n-1) v_1]$, then $t^* = 1/(n v_1)$ is an LRC certificate. Proof: ~5 lines
of fractional-part arithmetic.

**Special-case remark** for $v_1 = 1$ reduces the hypothesis to "$n \nmid v_j$
for every $j$" and the witness to $t^* = 1/n$.

**Verification table** showing both LRC-realisable boundary-only cases from
`EMPIRICAL_FINDINGS_2026_05_26.md` satisfy the lemma's hypothesis with the
explicit residue computation.

**Corollary 5.2-E** states the Main Theorem may invoke Lemma 5.2-D directly in
place of Theorem 5.2 when the witness located by the perturbation argument
lies at a boundary point and the speeds satisfy 5.2-D's hypothesis.

**Remark 5.2-F** clarifies the lemma's status: not required for the proof
(the closedness-limit in Theorem 5.2 Step 3 already handles boundary
witnesses), but useful for (i) robustness, (ii) Lean parity with Fix 3 of
the empirical-findings document, (iii) transparency about the structure of
the boundary-only cases. Notes the lemma's hypothesis is *not* universally
satisfiable.

## What did NOT change

- All theorem statements except Theorem 5.2 itself remain as in v11.6.
- §5.2 Theorem 5.2 — statement and proof structure unchanged (the explicit
  Erdős–Turán bound investigation by DeepSeek returned Option (B):
  polynomial growth in $j$, exact exponent not derived; v11.6's existing
  language already reflects this honestly).
- §10.1 / §11.1 — unchanged (already fixed in v11.6).

## DeepSeek investigation outcome (Step 2 explicit bound — Task #1)

DeepSeek-R1:14b with `--thinking` was run for ~15 min with a 5KB structured
prompt asking for the explicit $C(j)$ bound. The thinking trace
(`reports/v11_6_step2_investigation/deepseek_thinking.log`, 172 lines)
shows real engagement with the Erdős–Turán inequality and the structure of
$\|h\alpha_j/d\|$ for quadratic-irrational shifts, but truncates at the
4096-token limit before reaching a closed-form result. The formal Answer
(`deepseek_answer.md`, 53 lines) concludes **Option (B)**: polynomial growth
in $j$ with unspecified exponent $\alpha > 0$, uniform $B$ requires
$j$-range truncation.

**Decision** (per CLAUDE.md auditor protocol):

> [DeepSeek] says: Option (B) — $C(j) = O(j^\alpha)$ for unspecified $\alpha > 0$;
> uniform $B$ requires truncation; explicit constants deferred to future work.
>
> Decision: Accepting partially. The verdict aligns with v11.6's existing
> narrative ("polynomial in $j$"). The explicit exponent is *not* nailed
> down — DeepSeek's rough back-of-envelope inside its thinking trace
> suggested $D_N \sim O(j^{1/2})$ but relied on a likely-too-loose lower
> bound on $\|h\alpha_j/d\|$. Not strong enough evidence to drive a Step 2
> patch.

## Remaining gaps (out of scope for v11.6.1)

1. **Explicit $C(j)$ exponent in Theorem 5.2 Step 2.** DeepSeek's
   investigation was inconclusive (token-limited). Options for closing this:
   - Re-run DeepSeek with a tighter prompt focused on the partial-quotient
     bound for $\sqrt{2}/(2jd)$ specifically.
   - Generate a Codex empirical harness to measure $C(j)$ growth numerically
     for representative LRC speed families, then back out the exponent.
   - Pivot to an alternative perturbation $\alpha_j = p + \xi/j$ with
     $\xi = \sqrt{2}$ (suggested by DeepSeek Section 5) which has the
     simplest possible CF, and re-do the analysis.

2. **Uniform $B$ truncation argument.** Currently sketched in v11.6 Step 2
   final paragraph; DeepSeek confirmed truncation is the right path but
   did not formalise it.

3. **Lean refactor.** Unchanged from v11.6 status — separate work item.

## Verification

- File length: 986 lines (vs 887 in v11.6, +99 = changelog 19 + Lemma 5.2-D and
  Corollary 5.2-E and Remark 5.2-F ~75 + step 1 expansion ~5).
- Verified: all theorem statements except Theorem 5.2 remain identical to v11.6.
- Verified: Lemma 5.2-D applies to both LRC-realisable boundary-only cases
  identified in `EMPIRICAL_FINDINGS_2026_05_26.md` (residue tables computed
  explicitly in the manuscript).
- No new "$1/L$" assertions; remaining occurrences are in changelog/erratum
  context only.
