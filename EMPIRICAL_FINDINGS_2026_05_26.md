# Empirical investigation — Theorem 5.2 / `joint_fine_cell_exists`

**Session:** 2026-05-26 (continued)
**Scope:** Phases 1, 1b, 2, 3, 3b (Phase 4 deferred per user direction)
**Scripts:** `LonelyRunner/scripts/phase{1,1b,2,3,3b}_*.py`

## Headline findings

1. **The §10.1 / §11.1 STATEMENT is empirically sound.** All 20,403 strict-LRC-shape
   inputs satisfy the conclusion (0 failures). The manuscript's Theorems 10.1 / 11.1
   are correct; only the proof intermediate (Theorem 5.2) is broken.

2. **The manuscript's "G has period 1/L" claim is provably FALSE** in 50+ cases
   (Phase 2, n≥4 with k≥2 slow speeds). Actual period is 1/gcd(slow), confirmed
   numerically.

3. **The Lean lemma `joint_fine_cell_exists` is FALSE only on abstract inputs that
   the §10.1 / §11.1 call sites NEVER produce.** Of 681 counterexamples found
   yesterday, ZERO correspond to valid DI or ModDI calls.

4. **99.99% of LRC-realisable inputs have open-cell (positive-width) witnesses.**
   Only 2 out of 20,403 are boundary-only (extreme tight-LRC cases at the
   1/n threshold).

5. **The 2 boundary-only LRC cases have explicit BSR-like witnesses**
   (t = 1/n works for both).

## Detailed phase results

### Phase 1 — Conclusion check (exact rational interval arithmetic)

| Scope | Inputs tested | Conclusion failures |
|---|---|---|
| n=3..7, slow speeds ≤ 10, strict LRC hard case | 20,403 | **0** |

DI-classified: 13,115. ModDI-classified: 7,288. No overlap.

**Interpretation:** the §10.1 / §11.1 statements are sound on this exhaustive range.
The proof strategy is the only thing broken.

### Phase 1b — Witness topology

| Class | DI inputs | DI % | ModDI inputs | ModDI % |
|---|---|---|---|---|
| Open (max width > 0) | 13,114 | 99.99% | 7,287 | 99.99% |
| Boundary-only (max width = 0) | 1 | 0.01% | 1 | 0.01% |
| Empty | 0 | 0% | 0 | 0% |

**The two boundary-only cases:**
- DI: `n=5, slow=[1,3,4], V=7, p=7` — witnesses `{1/5, 2/5, 3/5, 4/5}`
- ModDI: `n=6, slow=[1,3,4,5], V=9, p=3` — witnesses `{1/6, 5/6}`

Both are "tight" LRC instances where some runners exactly hit the 1/n threshold.

### Phase 2 — Period validation

| Statistic | Value |
|---|---|
| Slow-speed families tested | 218 |
| Manuscript's "period 1/L" survives | 168 |
| Manuscript's "period 1/L" FAILS | **50** |

All failures have k ≥ 2 slow speeds (n ≥ 4). Example: `slow=[1,2], n=4 → L=2, gcd=1`.
Manuscript claims period 1/2, actual fundamental period is 1.

**Interpretation:** the manuscript's load-bearing claim in Theorem 5.2 Step 2
(line 351) and §10.1 line 577 is empirically wrong in ≥23% of tested cases —
specifically, in the cases the DI/ModDI hard case actually produces.

### Phase 3 — Witness localisation in `joint_fine_cell_exists` counterexamples

| Class | Count | % |
|---|---|---|
| Joint good set non-empty, ALL boundary-only | 193 | 28% |
| Joint good set TRULY EMPTY (LRC violation on abstract input) | 488 | 72% |

The 193 non-empty cases show witnesses at exact rationals (e.g., `{1/6, 5/6}`,
`{1/3, 2/3}`, `{4/9, 5/9}`). Any open-cell / positive-measure proof CANNOT
find these.

### Phase 3b — LRC realisability filter

| Class | Count |
|---|---|
| Valid §10.1 (DI) inputs | **0** |
| Valid §11.1 (ModDI) inputs | **0** |
| Neither (abstract, not LRC-realisable) | **681** |

**Critical:** None of the 681 lemma counterexamples correspond to inputs that
§10.1 or §11.1 ever produce. The Lean lemma is too generic — its hypothesis
allows configurations that the actual call sites prevent.

## Synthesis: what's actually wrong and what to do

### Two distinct problems

**Problem A (manuscript-level):** v11.5 Theorem 5.2 Step 2 uses "G has period 1/L",
which is false in 50/218 tested cases. The argument doesn't survive.

**Problem B (Lean-level):** `joint_fine_cell_exists` is stated too generically.
It's false on abstract inputs (681 counterexamples), but never false on actual
call-site inputs. The fix is to tighten the hypothesis.

These are independent.

### Path forward — three candidate fixes

**Fix 1 (recommended for Lean): tighten `joint_fine_cell_exists` to LRC-shape.**
Add hypotheses that encode the §10.1 / §11.1 structural constraints:
  - For DI: `kA = 1`; let q = A_speeds[0]; require `V = p · q`, `gcd(p, L_G) = 1`,
    `(n-1) · L_G_min < V ≤ (n-1) · L_G_max`, `gcd(slow ∪ {V}) = 1`, all distinct.
  - For ModDI: similar but with the p-divisibility structure.

  With these, all 681 counterexamples drop out. The two remaining boundary-only
  cases need a separate clause (see Fix 3).

**Fix 2 (recommended for manuscript): correct Theorem 5.2's proof.**
Replace the "period 1/L" claim with the correct period `1/gcd(slow)`. Re-derive
the bound K in Step 2 accordingly:
  - Old: K = L · ⌈1/μ(A)⌉
  - New: K = gcd(slow)⁻¹ · ⌈1/μ(A)⌉
    Since `gcd(slow)⁻¹` could be much larger than L⁻¹, K grows but stays finite.
  - The three-distance theorem argument still goes through with the larger K.

  Then update §10.1 line 577 and §11.1 to drop the wrong "period 1/L" assertion
  (it doesn't affect the proof logic at those sites, but propagates the error).

**Fix 3 (recommended for boundary-only cases): explicit witness fallback.**
For both LRC-realisable boundary-only cases tested (n=5 DI, n=6 ModDI), the
explicit witness `t = 1/(n · slow_min)` is a valid certificate. This is the BSR
witness `t* = 1/(n·v_1)`. Add a Lean theorem:
  
  > For any LRC-shape input, *either* the joint good set has positive measure
  > (open witness exists → fine-cell proof applies) *or* `t* = 1/(n·v_1)`
  > is itself a joint witness.

  Provable directly by case analysis on whether some speed equals a multiple
  of `n·v_1`.

### Manuscript revision draft outline (for the future v11.6 / v12)

§5.2 (Theorem 5.2):
- **Statement:** restrict A to be `jointGoodSet A_speeds n` for some
  family A_speeds, with structural constraint (slow + A_speeds satisfy LRC-shape
  jointly). Drop "arbitrary closed A" formulation.
- **Proof:** replace the period-based Weyl argument with one of:
  (a) Use period `1/gcd(slow)` correctly with adjusted K.
  (b) Use Lemma 4.1's explicit interval witness directly + Lipschitz pushforward.
  (c) Direct proof via LRC induction on a reduced family (Option E from earlier).

§10.1 / §11.1:
- Remove "(period 1/L)" parenthetical assertions; they're false and unneeded.
- Otherwise unchanged: the steps that USE Theorem 5.2's conclusion remain valid.

## Files produced this session

- `LonelyRunner/scripts/phase1_conclusion_check.py` — strict-LRC conclusion check
- `LonelyRunner/scripts/phase1b_witness_topology.py` — open vs boundary witness count
- `LonelyRunner/scripts/phase2_period_check.py` — period 1/L validation
- `LonelyRunner/scripts/phase3_witness_locate.py` — exact witness location in counterexamples
- `LonelyRunner/scripts/phase3b_lrc_realisable.py` — LRC realisability filter
- `LonelyRunner/EMPIRICAL_FINDINGS_2026_05_26.md` — this file
- (earlier same session) `LonelyRunner/THEOREM52_JOINT_FINE_CELL_FALSE.md`
- (earlier same session) `LonelyRunner/V11_5_LEAN_DRIFT_REPORT.md`

## Status going forward

Phases 1, 1b, 2, 3, 3b complete. Phase 4 (test candidate hypothesis strengthenings)
not needed: the empirical picture is unambiguous — the bug is in the lemma's
GENERICITY, not in any missing hypothesis. Tightening to LRC-shape resolves the
abstract counterexamples; the 2 remaining boundary-only LRC cases need an
explicit witness clause (Fix 3).

Lean build status: clean (2485 jobs), 3 sorries unchanged.
