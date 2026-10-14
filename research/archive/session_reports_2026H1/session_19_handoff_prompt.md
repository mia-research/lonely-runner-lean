# Session 20 Start Prompt — LRC Proof, Math Ex

## Mandatory First Step
Read ONLY these two files before doing anything else:
1. `/Users/trentpalelei/Desktop/Math Ex/session_state.md` — current status and next 3 tasks
2. `/Users/trentpalelei/Desktop/Math Ex/lrc_small_cases_analytic_closure_2026-03-13.md` — what was proved in Session 19

Do NOT read the main proof file until you know which section you need.

---

## Project Context (Brief)

You are one of two AI agents working on a proof of the Lonely Runner Conjecture (LRC) for all n.
- **Canonical proof file**: `lrc_proof_v6_3_preprint.md` (724 lines, 62KB), in `/Users/trentpalelei/Desktop/Math Ex/`
- **Tier 1 (x₀ ≥ 1): COMPLETE** for all n, all branches
- **Tier 2 (x₀ ≥ φ(n)): PARTIAL** — 3 open items remain

**Your role**: Close proof gaps analytically. Investigate every exception to understand WHY it occurs, not just branch around it.

**Token discipline**: ALWAYS write proofs to files. NEVER paste long proofs inline. Read at most 80 lines per file section. This session ran out of tokens due to over-reading — avoid that.

---

## What Was Done in Session 19 (2026-03-13)

Three analytic closures achieved:

### 1. Theorem B3b Step 4 — CLOSED
- **Was**: "small L covered by Appendix A.3"
- **Now**: Lemma B3b-LB proves L ≥ 2e_min always (via: E_fix contains largest power-of-2 M₂ ≤ n-1, gcd(M₂,p)=1, so if L=e_min then M₂·p ≤ e_min ≤ n-p, giving p < 2, contradiction)
- **Location of proof**: `lrc_small_cases_analytic_closure_2026-03-13.md` §1
- **v6.3 edit needed**: Replace Step 4 escape with "by Lemma B3b-LB, L ≥ 2e_min"

### 2. Proposition 10.3 Route A — Sharpened threshold
- **Was**: L ≥ n(n-1)(φ(n)+1)
- **Now**: L ≥ n(n-1)φ(n) (exact, via Lemma SC-EXACT for |I_d ∩ ℤ|)
- **Location**: `lrc_small_cases_analytic_closure_2026-03-13.md` §2
- **v6.3 edit needed**: Update Prop 10.3 Route A threshold and add Lemma SC-EXACT

### 3. Proposition 10.3 Route B, n=4 — CLOSED
- **Was**: Enumeration for n=4, M ∈ {3,4,5}
- **Now**: Lemma CD-4 proves ∪_{e∈E_non} bad ≠ ℤ₄ at every e_d-transparent fibre → x₀ ≥ 2M ≥ 6 > 2 = φ(4)
- **Location**: `lrc_small_cases_analytic_closure_2026-03-13.md` §3

---

## Next 3 Tasks (Priority Order)

### Task 1: Prove Lemma CD-n for n=6 (HIGH PRIORITY)
**What it is**: Coverage Deficiency for composite n=6 in the dropped-unit case.

**Statement to prove**: For n=6, E_non with residues {1,...,5}\{d} (one unit d∈{1,5} dropped, all non-units {2,3,4} present): for any fibre b ∈ B_div with e_d transparent — ∪_{e∈E_non} bad(e, ⌊eb/L⌋, 6) ≠ ℤ₆.

**Approach**:
- Units in E_non = {5} (if d=1) or {1} (if d=5). One unit, three non-units.
- Non-unit e=2: bad(2,t,6) = {−t/2, −t/2+3} if 2|t, else {−(t+1)/2, −(t+1)/2+3}. Always a pair {a,a+3}.
- Non-unit e=3: bad(3,t,6) = {0,2,4} if 3|t, {1,3,5} if 3|(t+1), else ∅.
- Non-unit e=4: bad(4,t,6) = pairs {a,a+?} (computed in closure file §3.4)
- Unit e=5 (or e=1): bad(e,t,6) = {t,t+1} mod 6.
- Show: the union of these bad sets (with floor states linked through fibre b) cannot cover all 6 residues.

**Key structural fact**: The floor states t_e = ⌊eb/L⌋ for e ∈ E_non are NOT independent — they are all determined by a single fibre b. The achievability constraint prevents "worst-case" floor state combinations.

**If stuck**: Check whether r_d = −d^{-1} (the Sole Cover residue) is always uncovered. For d=1: r_d = 5. For e∈E_non: can bad(e,t_e,6) contain 5? Unit 5: bad(5,t,6)={t,t+1} mod 6. Contains 5 iff t=5 or t=4. At t_5 ∈ {4,5}: floor(5b/L)=4 or 5. But at those fibres, e_d = 6·k has a specific floor. Trace through the constraints.

**Write result to**: `lrc_cd6_proof_2026-03-13.md`

---

### Task 2: Verify Prop 9.4 Route B empty for n ≥ 11
**What it is**: Show that for prime n ∈ {11,13,17,19,23,29}, the Route B range M ∈ {1,...,M₀-1} is EMPTY (M₀ = 1) for all valid tuples.

**Approach**:
- M₀ = ⌈n²(n-1)/(L₀(n-2))⌉ = 1 iff L₀ ≥ n²(n-1)/(n-2) ≈ n².
- E_fix has n-3 runners from {1,...,n-1}. With |E_fix| = n-3 ≥ 8 for n ≥ 11: L₀ ≥ lcm of 8 distinct integers.
- Need: for n=11, show every valid E_fix (8 runners from {1,...,10}) satisfies lcm(E_fix) ≥ 121·10/9 ≈ 134. Minimum lcm of 8 distinct elements from {1,...,10}: lcm(1,2,3,4,5,6,7,8) = 840 >> 134. ✓
- For each n: compute lcm_min(n) = min over all valid E_fix configurations, check ≥ n².

**Quick check**: lcm(1,...,8) = 840 ≥ 11² = 121. ✓ So for n=11, Route B is always empty.

**Write result to**: A note in `lrc_small_cases_analytic_closure_2026-03-13.md` §4 (append to file).

---

### Task 3: Edit v6.3 to incorporate B3b-LB and SC-EXACT
**What it is**: Targeted edits to `lrc_proof_v6_3_preprint.md`.

**Specific edits**:
1. §10.2 B3b Step 4 (line ~533): Replace "small L covered by Appendix A.3" with "by Lemma B3b-LB (below), L ≥ 2e_min for all valid B3b tuples."
2. Add Lemma B3b-LB text after Theorem B3b proof.
3. §10.2 Proposition 10.3 (line ~498-500): Update Route A to "M ≥ (n-1)φ(n)" and add one-line Lemma SC-EXACT.
4. §10.2: Add "(n=4 Route B closed by Lemma CD-4; see lrc_small_cases_analytic_closure_2026-03-13.md)"
5. §12 open items: Remove B3b "small L" from open list. Update Prop 10.3 note to reflect n=4 closure.

**Do NOT**: Rewrite or restructure the proof. Make targeted insertions only. Verify the lines in the file before editing.

---

## Key Files Reference

| File | Purpose |
|------|---------|
| `session_state.md` | Current status, next 3 tasks (READ FIRST each session) |
| `lrc_proof_v6_3_preprint.md` | Canonical proof (724 lines) — read by section only |
| `lrc_proof_status.md` | Per-section proof status table |
| `lrc_small_cases_analytic_closure_2026-03-13.md` | Session 19 work — B3b closure, Prop 10.3 |
| `lrc_8_2c_nonunit_closure_2026-03-12.md` | Session 18 work — Thm 8.2c non-unit closure |
| `reports/tier1_audit_2026-03-12.md` | Tier 1 audit findings |

---

## Session Discipline Rules
1. Read session_state.md first — always.
2. Read at most 80 lines per file section. Use offset/limit parameters.
3. Write all proofs to files, never inline in chat.
4. After each proof step, write the result to a file immediately.
5. Responses must be SHORT — output findings, not re-derivations.
6. End every session by updating session_state.md with completed work and next 3 tasks.
