# LRC Proof Status — Per-Section Table

> **✅ STATUS UPDATE — 2026-04-29: Tier 1 PROVED.**
> Theorem 12.1 Case B closed 2026-04-29 via Silence Fibre construction (Lemmas 12.2/12.3) in `lrc_proof_v10_15.md`. **Theorem A ($x_0 \geq 1$ for all $n \geq 3$) is now proved unconditionally.**
> Canonical file: **`lrc_proof_v10_15.md`**.
>
> Prior error history: v11.2 line had five confirmed errors (Lemma 2.5 iff false). v10.12 had ERR-C-01/02/03. All repaired through v10.13 → v10.15 rebuild. The table below (pre-override v6.3 ledger) is superseded; see `session_state.md` for current per-branch status.

---

**Canonical file:** `lrc_proof_v10_15.md` (2026-04-29) — Tier 1 COMPLETE, Theorem A proved.
**Predecessor (pre-Case-B):** `lrc_proof_v10_13.md`
**Override review:** `lrc_whole_project_review_2026-04-18.md` (2026-04-18)

## Tier Summary
| Tier | Claim | Status |
|---|---|---|
| **Tier 1** | x₀(E) ≥ 1 (LRC) | ✅ **PROVED** (`lrc_proof_v10_15.md`, 2026-04-29) — all branches closed. Theorem A unconditional. Key final step: Theorem 12.1 Case B via Silence Fibre (Lemmas 12.2/12.3). |
| **Tier 2** | x₀(E) ≥ φ(n) | ⚠️ PARTIAL — analytic bounds in §9.3b, §9.3f now unconditional (Tier 1 complete). Remaining open: Proposition 10.5 (prime $n$, $x_0 \geq \varphi(n)$). |

## Section Status Table

| § | Title | Status | Key Lemmas | Notes |
|---|---|---|---|---|
| 1 | Introduction | ✅ Stable | Theorem A (x₀≥1 only) | Quantitative status explicitly listed |
| 2 | Irrational Branch | ✅ Stable | Thm 2.1 | |
| 3 | Case 1: No Speed Divisible by n | ✅ Stable | Thm 3.1 | x₀≥φ(n) unconditional |
| 4 | Case 2: Sole Cover Bijection | ✅ Stable | SCB | |
| 5 | Structural Lemmas | ✅ Stable | B3B, Transparency | |
| 6 | Prime n, One Divisible Runner | ✅ Stable | — | x₀≥φ(n) |
| 7 | Prime n, Multiple Divisible Runners | ✅ Stable | Thms 7.2, 7.3 | x₀≥φ(n) |
| 8 | Z0S + Dropped-Runner Targeting | ✅ Stable | **Thm 8.2c** (NEW), Relay Inv, CRT-G, PP-T2 | Core Tier 1 engine |
| 9 | Prime n, Large L: Analytic Counting Bridge | ✅ Stable | ACB | x₀≥φ(n) |
| 10 | Composite n: Run Cap / Near-Complete Templates | ✅ Stable | — | B2 rewritten via Thm 8.2c |
| 11 | Composite n, Multiple Divisible Runners | ✅ Stable | CRT-G | |
| 12 | Proof of Main Theorem + Open Items | ✅ Stable | — | Honest open item list |
| 13 | Global Mechanism: Coverage Transport Capacity | ✅ Stable | — | |
| App A | Computational Evidence | ✅ Updated | A.2 honest re GG2; A.7 tracks Thm 8.2c | |

## Key Lemmas / Theorems (v6.3)
- **Thm 8.2c (Dropped-Runner Targeting)**: NEW in v6.2/6.3. For composite n≥4 with dropped non-unit d, gives targeted isolated z=0 event → Tier 1 analytic for all multi-prime U-FORCE tuples.
- **Relay Invariant (Lemma RI)**: Every chamber has an uncovered residue under U-FORCE. Used for GG1 full-chamber safety.
- **CRT-G**: Tier 1 analytic (via Thm 8.2c) + full-chamber in GG1 sub-case only.
- **PP-T2**: Tier 2 conditional on **PL-KINDEP** (group-separation step).
- **PL-KINDEP**: Open — needs group-separation made explicit.

## Remaining Quantitative Open Items (v6.3, §12)
1. **GG2 quantitative upgrade**: Tier 1 done (Thm 8.2c). Need chamberwise/density statement for Tier 2. Old universal-chamber claim had counterexamples; replaced by this targeted goal.
2. **PL-KINDEP**: Floor-state independence between mod-p groups in PP-T2. Joint-density bound needs group-separation step made explicit.
3. **Relay RI, m≡1 (mod p) step**: Computationally verified (532 events, 0 failures); full analytic proof still needed for complete Tier 2 program.

## Version History
| Version | File | Date | Change |
|---|---|---|---|
| v5.17 | archive/v5_drafts/ | 2026-03-11 | Final v5 before preprint |
| v6.0 | archive/ | 2026-03-11 | First preprint |
| v6.1 | archive/ | 2026-03-11 | GG-TRANS + PL-KBIJ attempt (superseded) |
| v6.2 | lrc_proof_v6_2_preprint.md | 2026-03-12 | Thm 8.2c introduced; B2 rewritten |
| v6.3 | lrc_proof_v6_3_preprint.md | 2026-03-12 | Tier 1 complete; open items explicit |
| v7.0–7.3 | lrc_proof_v7_0–7_3_preprint.md | 2026-03-13 | v7 restructure: §2 blueprint, v7 naming, §13 cleanup |
| v7.4 | lrc_proof_v7_4_preprint.md | 2026-03-14 | 4 exposition fixes: §13 "analytically" clarified, §9.3b polynomial value at n=45 explicit, §2 Lemma T3 cited, §9.2c uniqueness justified. Structurally complete. |
| v7.5 | lrc_proof_v7_5_preprint.md | 2026-03-14 | 13 external-review fixes (see Session 21). |
| v7.6 | lrc_proof_v7_6_preprint.md | 2026-03-14 | 3 surgical fixes from second-round reviews (Kimi/Gemini/ChatGPT). |
| v10.11 | lrc_proof_v10_11.md | 2026-04-18 | CT.1-FINAL; prime-n dropped-unit proved. |
| v10.12 | lrc_proof_v10_12.md | 2026-04-18 | ERR-C-01/02/03 identified post-release. |
| v10.13 | lrc_proof_v10_13.md | 2026-04-24 | ERR-C-01 fixed (Lemma 11.3a'); composite dropped-unit proved. |
| v10.14 | lrc_proof_v10_14.md | 2026-04-28 | Sub-case B2b analysis; Case B still OPEN. |
| **v10.15** | **lrc_proof_v10_15.md** | **2026-04-29** | **CANONICAL. Theorem 12.1 Case B PROVED (Lemmas 12.2/12.3 — Silence Fibre). Theorem A ($x_0 \geq 1$) proved unconditionally. Tier 1 COMPLETE.** |
