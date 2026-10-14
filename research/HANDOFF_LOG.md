# Handoff Log

Append-only. One entry per work block, per account. The next session reads the
**last three entries** before doing anything else.

This file exists because the memory layer and the artifact layer sync
differently. `MEMORY.md` and the nested indexes are shared on disk and stay
current — a session can read what another session *concluded*. Nothing records
what is *finished* versus *half-written*, and nothing survives a session that
dies before it can summarise itself.

## Rules

1. **Append only.** Never edit an earlier entry. The single exception: you may
   flip your own `STATUS` line and extend your own `IN FLIGHT` line while your
   block is live.
2. **Write the header before you work, not after.** A session that runs out of
   tokens never reaches its own summary. An entry that stays `OPEN` is the
   signal that this happened.
3. **This file is exempt from the CLAUDE.md §1 versioning rule.** Never create
   `HANDOFF_LOG_v2.md`. Versioning a log destroys the property that makes it
   work.
4. **Fields name objects, not judgments** (CLAUDE.md §2b). `IN FLIGHT:
   POSITIVE_FINDINGS_MASTER_v5.md — §7 panel unwritten` is an entry.
   `IN FLIGHT: master needs polish` is not.
5. **`OWED` is the CLAUDE.md §2a ledger.** A gate that could not run goes here
   with the date attempted and the reason. It stays until an entry discharges
   it by name.

## Entry format

```
## YYYY-MM-DD · <account> · <short label>
STATUS:      OPEN | CLOSED
CHANGED:     <paths or areas touched>            | none
OWED:        <gate — date attempted — why>       | none
IN FLIGHT:   <named artifact — what remains>     | none
DO NOT REDO: <dead end — where it is written up> | none
LEDGER:      <git sha> | UNCOMMITTED: <why>
```

`STATUS: OPEN` left behind by a finished session means that session died
mid-flight. Treat its `IN FLIGHT` line as unverified — check the artifact
before building on it.

---

## 2026-08-24 · Claude Code · L-mono GKR routes A+B (citation gate DISCHARGED; ζ₃-rigidity reduced to a named gap)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/RESULT_lmono_gkr_moment_fingerprint_v2.md` (supersedes v1 —
             CORRECTS v1 §2's negative-bias overreach: the cells DO exclude the independent SL₂×SL₂
             alternative via the coset-restricted 4th moment (diagonal 2 vs independent 7; measured
             1.84→2), and the exact 120° law does so directly (100% of Frobenii in a measure-zero
             locus). v1 conflated the full-group number 12 (needs j=0, unmeasurable) with the coset
             statistic (measurable). `lmono_gkr_coset_discriminator_v1.py`);
             `btc_puzzle_investigation/lmono_routeB_geom_iso_certificate_v1.py` (route B: det(W_a)=ζ₆p
             CONSTANT in a + tr(W')=ζ₃tr(W) + irreducible, 968 cells/8 primes, all PASS → W'≅W
             geometrically, μ₃ ARITHMETIC, G_geom⁰=SL₂);
             `btc_puzzle_investigation/RESULT_lmono_gkr_argument_v1.md` (capstone: routes A+B unified as
             a `[VERIFIED-scope — reduction]`; S1 Larsen→SL₂, S2 coset-moment excludes independent, S3
             GKR→W'≅W⊗L, S4 det-const→L geom-trivial/μ₃ arithmetic, S5 Deligne-equidist coset→T1/T2/T3;
             {±1}=GKR centre fibre-product (FKM Rmk 2.5)).
OWED:        `citation-verifier` — **DISCHARGED this session.** 4 Katz/GKR theorems verified vs primary
             sources: Larsen LAMMLF Thm 1.1.6 (SUPPORTS; non-finiteness horn killed by the at-scale
             continuous semicircle), Kummer μ₃ (SUPPORTS), GKR ESDE 1.8.2 via FKM (SUPPORTS-W-EXTRA:
             dual branch OK by SL₂ self-duality; needs geom-irred/purity/Goursat-adapted), Deligne
             GKM Thm 3.6 (SUPPORTS-W-EXTRA: our G_arith⊋G_geom IS the coset form; weight-0 norm). Minor
             residual: ESDE 1.8.2 verified via FKM reproduction not the AM-124 original (not free).
             `compile-diff` — not triggered (no master v15 fold).
IN FLIGHT:   none. THE remaining gap (RESULT_..._argument_v1 §4): the SHEAF CONSTRUCTION — realize the
             a-family as a lisse sheaf on a geometrically-connected base + G_geom constant in p
             (specialization). This is the uniformity the prize needs and finite-prime data cannot give;
             it is the genuine hard core, unchanged by this session's evidence. Next brick.
DO NOT REDO: (1) the cell-moment "can't discriminate" claim (fingerprint_v1 §2) — corrected in v2, cells
             DO exclude independent. (2) the ω-route for W'≅W (PLAN §5B) — BLOCKED by PLAN §3 (ω is
             cross-cell); use Frobenius-trace rigidity (route-B certificate). (3) re-running the
             citation gate on these 4 theorems — discharged, verdicts in RESULT_..._argument_v1 §2.
LEDGER:      repo at f71f72a; new artifacts untracked. Two other-account Sage jobs still running at
             session end (NOT killed); L-mono §7.3 (a=0 unification) still blocked on anew_sorder_sweep.
             Katz PDFs downloaded to the session scratchpad (LAMMLF/GKM/arizona34/bigimage/FKM/AWS).

---

## 2026-08-24 · Claude Code · L-mono GKR sub-bricks 1 + 2 (rank-4 eigenvalue derivation + moment fingerprint)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/RESULT_lmono_gkr_rank4_eigenderiv_v1.md` (new — sub-brick 1:
             discharges the NOTE's owed symbolic re-derivation. Rank-4 spectrum = tensor form
             W⊕(W⊗ψ), ψ=scalar ζ₃; tensor-trace identity V₁=−(1+ζ₃)tr(W)=−ζ₆tr(W); half-trace
             reduction Im(V₁)/(2√p)=−cos θ [p≡3], Re/(2√p)=−cos θ [p≡1]. The NOTE's −sin(θ+π/3)
             slip corrected: sin(θ+π/3)=cos(θ−π/6), error was only the overall sign. `[VERIFIED —
             exact symbolic + decidable]`);
             `lmono_gkr_rank4_eigenderiv_v1.py` (STAGE A abstract 40k×4primes×both arms; STAGE B
             REAL V₁(a) via D2 module, all 672 cells / 6 primes / both arms — every residual ≤3.7e-14;
             g=2 W-plane found 672/672);
             `btc_puzzle_investigation/RESULT_lmono_gkr_moment_fingerprint_v1.md` (new — sub-brick 2:
             exact GKR fingerprint M₁₁=2,M₂₂=12,M₄₀=10 for G=SL₂·μ₃·{±}; discriminator = det-masked
             |tr|⁴ = 12 (candidate diagonal) vs 8 (independent SL₂×SL₂) — the ONLY low moment that
             separates them, both share M₁₁=2. LOAD-BEARING SCOPE: cells realize j∈{1,2} only, NEVER
             j=0, so cell data samples ⟨|tr|⁴⟩→C₂=2 and CANNOT read the M₂₂=12 discriminator — pinning
             diagonal-vs-independent needs the geometric Kummer variation (route A/Katz) or route B
             sheaf-iso, not the j-fixed cell statistics. `[VERIFIED — exact]`);
             `lmono_gkr_moment_fingerprint_v1.py` (exact integer moments + 4M Haar MC, agree; 5 models).
OWED:        `citation-verifier` on the Katz/GKR rigidity statements — NOT yet triggered (no citation
             grade promoted this session; owed before sub-brick 4 writes the GKR proof). `compile-diff`
             before any master v15 fold — not triggered (no master touched).
IN FLIGHT:   none — both bricks closed and self-contained. Sub-brick 3/4 (the GEOMETRIC moment /
             sheaf-iso that actually pins G_geom=G) is the next brick; sub-brick 2 §2–3 relocates the
             gap precisely to it. NOTE: the "match FFT-measurable cell statistics" framing of PLAN §7.1
             item 1 is now known INSUFFICIENT alone (the j-coset finding) — the completion is route
             A-geometric or route B, not the cell moments.
DO NOT REDO: the cell-moment match as a group-pinning step — RESULT_..._fingerprint_v1 §2 proves it
             samples only the j=±1 coset and misses M₂₂; it confirms consistency, never diagonality.
LEDGER:      repo held at f71f72a per standing state; four new artifacts left untracked alongside the
             backlog. Two other-account Sage jobs (`anew_sorder_sweep_v1`, `d2_nonabelian_sweep_v2`)
             still running at session end — NOT killed; L-mono §7.3 (a=0 unification) still blocked on
             the S-visibility sweep.

---

## 2026-08-21 · Claude Code · A_new two-prong — Prong 1 closed, Brick E p=43 = scoped null
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/RESULT_anew_supersingularity_step3_gap_and_cartier_route_v3.md`
             (new — Prong 1: `A_new` supersingular/superspecial ∀ p≡3 mod4 ⊇ secp, `[PROVED — reviewed,
             3 routes]`; BOTH v2 caveats resolved — Caveat 1 a-fortiori for Hom=0, Caveat 2
             citation-verified vs original Oort 1975 Thm 2+Rmk 3 = polarization-free; Aug-18 "pending
             operator check" degradation corrected);
             `PREREG_brick_e_cd_degree_v1.md` (+`.sha256` 71c2a985, +`_DEVIATIONS.md` D1) — SUPERSEDED;
             `PREREG_brick_e_cd_degree_v1_GATE_REVIEW.md` + `_v2_GATE_REVIEW.md` (isolated
             experiment-designer: R1 found F1–F5, R2 cleared the QR-half μ₃ design);
             `brick_e_degree_fitter_v1.py` (exact CRT/Hensel degree fitter — engine unit-tests pass);
             `brick_e_anew_Lpoly_v1.sage` (|A_new(F_p²)|=3²·631², √−1∉any divisor; xcheck |Jac(F_43)|=58683);
             `PREREG_brick_e_cd_degree_v2.md` (+`.sha256` **e3fe35d0** — FROZEN, frame-gate CLEARED, run
             authorized); `brick_e_run_v1.py` (null generator + degree stat + controls i/iii — run OK);
             `_DEVIATIONS.md` D2 (μ₃-covariance DEGREE FLOOR = 10 at p=43; null pinned 13-14; control-ii
             plant corrected to the degree-10 covariant poly, FIRES π=0);
             `brick_e_ctrl_iv_rho_identity_v1.sage` (control iv: φ([−d]G)=±ρφ([d]G) 30/30, non-QR 15/15);
             `RESULT_brick_e_cd_degree_v1.md` (p=43 read: D_obs=14=generic, π=1.0, scoped NULL); this file.
OWED:        Control (iii) calibration must be VALIDATED at the first powered rung (p≥163, where the
             null D-histogram has spread) — the code is fixed (`brick_e_run_v1.py`: correct KS + a
             degeneracy gate that reports INAPPLICABLE when D has ≤2 values), but it has only ever been
             run on the degenerate p=43 rung where it is inapplicable, so it has NOT yet actually fired.
             Prong-1 `citation-verifier` (Oort no-pp) DISCHARGED 2026-08-20; Brick-E `experiment-designer`
             R1+R2 DISCHARGED. `compile-diff` owed only before a future master promotion (not yet
             triggered). [2 earlier gate attempts died on session limit; both re-run and completed after
             reset — no gate left unavailable.]
IN FLIGHT:   THE LADDER (next session, clean task — nothing half-written). p=43 cycle done:
             `RESULT_brick_e_cd_degree_v1.md` — **3 of 4 controls fired (i,ii,iv); control (iii)
             calibration BROKEN + INAPPLICABLE** (statistic 2-valued at p=43 ⇒ p-value can't be Uniform;
             my "CALIBRATED 0.002" was a buggy KS, true KS 0.998 — DEVIATIONS D3, caught by the banned
             "honest" word-diagnostic). Real read D_obs=14=generic (full Lagrange interpolant), π=1.0 vs
             matched μ₃-null ⇒ **NEAR-VACUOUS null** (rules out strong D≤12; can't resolve D=13; a
             one-bit observation, not a powered null). NOT a closure. NEXT:
             generalize `lbe_dlog.sage` to the ladder {67,79,163,211,547} (parameterize p,β; Pohlig–
             Hellman for the A_new dlog if |A_new(F_p)| large), run the 4 controls per rung, then the
             frozen statistic. First POWERED rung p=163 (reps=23). Degree-stability at the ceiling across
             ≥2 powered rungs retires the Brick E low-degree channel WITH power; a sub-floor D at any
             rung is a signal to chase.
DO NOT REDO: (1) `A_new` supersingularity — PROVED 3 routes, both caveats resolved (`RESULT_…v3`).
             (2) The full-group F_{p²} Brick-E domain — ill-posed (√−1∉|A_new(F_p²)|; non-QR half =
             ρ·(QR half), no independent content) → use the QR-half scalar arm. (3) The μ₆-null —
             unnecessary; μ₃ is matched on the QR-half (R2 gate, 3 grounds). (4) p=331/307/367/379/439
             as ladder rungs — n=#E composite (379: n=343=7³ despite 6|n−1).
LEDGER:      UNCOMMITTED: repo at f71f72a per standing state; new artifacts untracked alongside backlog.

---

## 2026-08-16 · ZCode (account C) · Downloads D2/mod-6 batch audit
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/AUDIT_d2_bridge_mod6_reduction_v1.md` (new;
             §8 addendum added same day after user challenge),
             `btc_puzzle_investigation/audit_d2_bridge_reduction_v1.py` (new;
             one prose line erratum-fixed same day, hash 0782d9…fd60b),
             `btc_puzzle_investigation/NOTE_core_gate_exact_carry_region_v1.md`
             (new — core-gate carry PROVED: hexagon region, Pr[c=0]=3/4 exact,
             sharp threshold 3/16; upgrades RESULT_linchpin_s_gate_v2 empirical
             numbers to proof-grade; P145 added: first real key with certified
             NONZERO carry, c = −ω),
             `btc_puzzle_investigation/core_gate_carry_proof_v1.py` (new),
             `btc_puzzle_investigation/NOTE_glv_orbit_carry_conservation_v1.md`
             (new — carry closed form {0,±ω} with exact 3/4-1/8-1/8 law; orbit
             conservation ω²c(X)+ωc(βX)+c(β²X)=0 and trichotomy; s orbit-
             invariance + exact trace shift; complete exact joint law of the
             public orbit invariants; passport of all 6 exposed puzzles;
             ramified-prime-3 structural remark),
             `btc_puzzle_investigation/glv_orbit_carry_conservation_v1.py` (new),
             `btc_puzzle_investigation/RESEARCH.md` (2026-08-16 entry prepended,
             items 6-7 added same day),
             this file
OWED:        none
IN FLIGHT:   none
DO NOT REDO: Downloads "D2 bridge / Core Gate / mod-6" reduction claims —
             net 0 bits; two source arithmetic errors (n≡1 not 2 mod 3;
             λ≡2 not 1 mod 3) banked in AUDIT_d2_bridge_mod6_reduction_v1.md
             §1; y-LSB=d mod 2 falsified at N=8000; their sandbox check is the
             d₀=d, c=0 tautology. Same object as OPEN_d2_congruence_law_v1.md
             (already CLOSED NULL). NOTE: the batch's own Aug-13 source docs
             (d2-lang-torsor-puzzle-verification.md §4) concede the circularity
             verbatim; the Aug-16 rewrite re-asserts it with degraded algebra
             and a circular Case-2 "BDD escape" (MI spike = H(pubkey) by their
             own parenthetical) — see AUDIT §8. Still unread of the batch:
             eisenstein-core-gate-verification.md, eisenstein-core-gate-p135.md,
             l1-lemma-rhombus-verification.md, isotypic-trace-carry-reproduction.md,
             joint-semaev-* — geometry/carry content already covered exactly
             elsewhere; read before citing them directly.
LEDGER:      UNCOMMITTED: repo held at f71f72a per standing state; new
             artifacts left untracked alongside the backlog.

---

## 2026-08-05 · account B · handoff protocol + backlog triage
STATUS:      CLOSED
CHANGED:     `.gitignore` (working tree only — 2.9 GB of generated CSV/JSONL/NPZ
             excluded so it cannot be staged by accident); this file;
             `docs/handoff_protocol_v1.md` (draft, not yet folded into CLAUDE.md)
OWED:        none
IN FLIGHT:   `docs/handoff_protocol_v1.md` — proposed CLAUDE.md §12, awaiting
             review before it is folded in. CLAUDE.md itself NOT edited (it
             already carries 83 uncommitted lines from account A).
DO NOT REDO: (1) MCP registry search for memory/handoff/sync/shared-context
             connectors — returned zero results, no MCP exists for this.
             (2) Committing the untracked backlog — five batched commits were
             made and then fully reset at user request (`git reset --mixed
             f71f72a`). Files all intact on disk; nothing was lost; nothing was
             pushed. One batch had silently moved the `LonelyRunner` submodule
             pin d041205 → 20d03dc, which is why it was reverted. Do not re-run
             a blanket `git add -A` in this repo without checking the gitlink.
LEDGER:      UNCOMMITTED: repo deliberately left at f71f72a, unchanged from
             session start apart from the `.gitignore` working-tree edit.

### Standing state as of this entry

- **Parent repo:** last commit `f71f72a` (2026-07-17). 1,732 untracked entries.
  Of those, ~2,475 files / 34 MB are source (`.md`/`.py`/`.tex`/`.lean`); the
  rest is regenerable data. The backlog is still unledgered — the btc index
  points at artifacts (e.g. `POSITIVE_FINDINGS_MASTER_v5.md`, written 11:54
  today) that git has no record of.
- **`CLAUDE.md`:** 83 uncommitted lines — the §2 agent-gate table, §2a
  gate-unavailable branch, §2b agent rationale. The instruction channel both
  accounts rely on exists only on this disk.
- **Lean tree (`LonelyRunner/`, separate repo):** idle since 2026-07-09. HEAD
  `20d03dc` (Jul 8). Carries a 480-line uncommitted diff across four
  `IntLRC_7_BS` files from Jul 9, never built or committed. Parent repo pins
  `d041205` (Jul 2), so the parent's record is four commits stale. Untouched
  this session.
- **Memory drift, open:** `feedback_suppression_bias_asymmetric_2026_08_02.md`
  declares it supersedes the symmetric framing of
  `feedback_dont_pre_evaluate_shut_thinking_2026_07_11`. The supersession landed
  in the new file and the `MEMORY.md` top block only. The superseded phrase
  ("**Corollary: symmetric rigor**") is still live in `MEMORY.md:92`,
  `feedback_INDEX.md:8`, and as the section header of the 07-11 file itself.
  Not yet fixed — routes through `memory-drafter` per CLAUDE.md §2.

---

## 2026-09-01 · Claude Code · roadmap-v3 avenue audit + Brick D2 reduction (secp's class)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/RESULT_jacobi_rationality_reduction_v1.md` (new);
             `jacobi_rationality_gate_v1.py` + `.log`, `jacobi_rationality_reduction_v1.py` + `.log` (new).
OWED:        (a) prove **(C2)** `S(χ₃χ₄) = −(2|p)(−3|p)·S(χ₃)` — the whole residual of
             `RESULT_jacobi_closed_form_m_law_v4.md` §2 at `p ≡ 7 mod 12`; suggested tool = Hasse–Davenport
             product relation, `m=2`, `ρ=χ₂`, on the Cayley parametrization of `U = ker N`. (b) write out
             **(C3)** (elementary; only the write-up owed). (c) the `p ≡ 11 mod 12` half — `θ` trivial there,
             L1 inapplicable, needs a different route; NOT secp's class. (d) `citation-verifier` if
             Hasse–Davenport is used in a written proof; `compile-diff` if folded into a master.
IN FLIGHT:   none.
DO NOT REDO: **The 2026-09-01 avenue list is stale on five of six items** — it restates
             `ROADMAP_REDIRECT_v3.md` (2026-08-18) as if unexecuted. Do not re-run:
             (1) Brick B in every part — N16 `|u−v|≤½ == build.eps` DISCHARGED 08-18 (200000/200000,
             conjugate-basis mechanism `BP_SECP = A_SP − B_SP`), re-verified first-hand 08-21
             (`NOTE_v14_item9_n16_state_v1.md`); `eis(X)` public-route `[PROVED — reduction]`
             ECDLP-equivalent via the 2-D DLP on `{G,φ(G)}` (`RESULT_eis_carry_2d_dlp_reduction_v1.md`);
             CM-lattice unfolding = powered bounded null `< 9e−4` bits, and the amicable partner is
             STRUCTURALLY vacuous because `π_n − 1 = −π_p` — the second equation IS the first
             (`RESULT_cm_lattice_unfolding_v1.md`). (2) Brick A — `RESULT_e3_owed_measurement_v1.md`
             08-18, MC-corrected, `p_FWER=0.083`, bounded. (3) Brick C — `RESULT_weight1_phase_ramp_v1.md`
             08-21: the literal object has NO public per-point realization `[STRUCTURAL]`. (4) Brick D1 —
             `(†) Σχ₂(s)sgn(ρs mod p−s) = 3h(−p)` is **already PROVED** (`RESULT_fld_dagger_proof_v1.md`,
             07-24, via Berndt–Evans/Goldstein–Razar, NOT generalized Dedekind sums); note `FLD = 0`
             at `p ≡ 7 mod 24` (68/68), i.e. `|FLD|=6h` is **vacuous at secp's class**.
             (5) "D2 affine readability, written but never run" — `PREREG_D2_lang_hypergeometric_relin_v1.md`
             is PRE-RUN but **gated out**, not neglected: `RESULT_D2_lang_rationality_gate_v1.md` (08-09)
             shows the registered Lang realization is Frobenius-trivial (`(F−1)[P⁺−P⁻] = 0` exactly,
             7 primes), so its arms have identically-zero input. Genuinely open and unrun: **LBE v2**
             (`PREREG_localized_bit_extraction_v2.md`, "Status: PRE-DATA") and the **L-mono sheaf
             construction** (per the 2026-08-24 entries).
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; new artifacts on disk only.

---

## 2026-09-01 · Claude Code · document-layer repair (the stale-review defect)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/ROADMAP_REDIRECT_v4.md` (new — supersedes v3);
             `btc_puzzle_investigation/RESEARCH.md` (navigation banner correcting the ordering
             contract; backfill entries for `2026-08-18` and `2026-08-19/20`; session entry `(d)`).
OWED:        `compile-diff` — **attempted 2026-09-01, UNAVAILABLE**: `Agent type 'compile-diff' not
             found`; the project agents (`compile-diff`, `experiment-designer`, `citation-verifier`,
             `memory-drafter`) are NOT loaded in this session's harness. ROADMAP_REDIRECT_v4 is
             therefore tagged `[PROVISIONAL — compile-diff unavailable]` in its grade slot with a
             §5 self-audit naming its uncovered **frame** rows; no grade is promoted by it. Gate is
             owed on v4 AND on the `POSITIVE_FINDINGS_MASTER_v19` that v4 §0 D-3 requires.
             `experiment-designer` — owed before E3-chirality or LBE v2 collects data (same reason).
             `memory-drafter` — the PRNG-boundary persist v3 already owed.
             **NOT DONE: `POSITIVE_FINDINGS_MASTER_v19`.** D-3 is diagnosed, not repaired.
IN FLIGHT:   none.
DO NOT REDO: The three document-layer defects are diagnosed with evidence in `ROADMAP_REDIRECT_v4.md`
             §0 — **D-1** v3 frozen at 2026-08-18 13:09, the hour its own bricks began discharging,
             never superseded, and the only document describing the brick programme (primary cause of
             the stale-avenue review); **D-2** `RESEARCH.md` claimed "Newest first" but is newest-first
             only to ~line 370, then append-at-bottom `08-21 → 09-01`, plus a total hole at
             `2026-08-17…08-20` (the Brick A/B window) — banner + backfill applied; **D-3** no master
             has ever consumed the brick programme (v18 has ZERO occurrences of "Brick A–E" or any
             brick artifact and states "No grade is moved"; v17 mentions only `lmono_gkr` twice).
             Also: my own first draft of v4 **failed** the mechanical loss check — it silently dropped
             v3's **D3** (citation sweep), **§0(I)** counter-prior, **§2** working method and **§3**
             guardrails. Restored in v4 §4. A status successor sheds its predecessor's framing by
             default unless the diff is actually run; do not skip it next time.
             Tightening now on record: v3's guardrail carved out ONE exception to the N18 island
             keyspace-pruning ban — the CM-lattice / amicable second-equation question. Brick B(ii)
             closed it (`π_n−1 = −π_p`), so **N18 has no live exception at all.**
             Concurrency: another account appended `Session 2026-09-01 (b) — E3 SPLITS` to RESEARCH.md
             mid-session, **re-opening Brick A** (chirality `ODD = b−c`, 99.3rd pctile vs the frozen
             null, but POST-HOC and ungraded). Folded into v4 §1 Brick A and §3.4. Two entries today
             both carry the label `(b)`; disambiguate by title.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-01 · Claude Code · Brick D2 CLOSED at secp's class (J = −p PROVED)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/RESULT_jacobi_sign_law_proved_secp_class_v1.md` (new);
             `jacobi_hd_closure_v1.py` (new); `ROADMAP_REDIRECT_v4.md` §1 Brick D + §3 item 2
             updated to CLOSED; `RESEARCH.md` session entry `(e)`.
OWED:        `citation-verifier` — attempted 2026-09-01, **UNAVAILABLE** (project agents not loaded).
             Two standard Hasse–Davenport relations are invoked (lifting `s=2`, product `m=2`); the
             RESULT carries `[PROVISIONAL — citation-verifier unavailable]` in its grade slot with a
             §5 self-audit. Both relations are numerically witnessed in-script, so the exposure is
             the citations' exact hypotheses, not their truth. Also still owed from earlier blocks:
             `compile-diff` on `ROADMAP_REDIRECT_v4.md` and on the unwritten
             `POSITIVE_FINDINGS_MASTER_v19`; `experiment-designer` before E3-chirality / LBE v2.
IN FLIGHT:   none.
DO NOT REDO: `J(χ₃,χ₄) = −p` at `p ≡ 7 mod 12` is **proved**, not empirical — do not re-open it as a
             measurement. Structure of the proof: rationality is the hard half and is regime-specific
             (it needs `χ₃` AND `χ₂` to be norm-lifts, i.e. `3 | p−1`); the **sign is free and
             regime-independent** via `J ≡ −1` mod a prime above 3. Do NOT look for a sign argument —
             there isn't one to find, the sign was never the difficulty. `p ≡ 11 mod 12` is NOT
             closed (rationality does not extend there; §1's method provably fails, witnessed as the
             B/F column failures) — but it is not secp's class. The earlier same-day reduction
             (`RESULT_jacobi_rationality_reduction_v1.md`, the (C2) statement) is SUPERSEDED as an
             open question but retained as the trail; its `g(χ₄) = (2|p)·p` derivation is load-bearing
             for the closure and still stands.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-01 · Claude Code · self-audit of this session's own output (honesty flags)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/AUDIT_session_2026_09_01_honesty_flags_v1.md` (new);
             `RESULT_jacobi_sign_law_proved_secp_class_v1.md` (F2 dependency stated, F3 citation
             exposure reduced); `ROADMAP_REDIRECT_v4.md` §1 header (F6).
OWED:        **NEW, and the most important one: first-hand verification of
             `RESULT_jacobi_closed_form_m_law_v4.md` §1** (the reduction from the Jacobi sign law to
             the m-law). Today's closure proves that file's §2; the m-law consequence inherits §1's
             `[PROVED]` grade UNAUDITED, from a file that already carries a self-audit confessing an
             inflated tally and hypothesis-confirming-itself configurations. Until that check runs,
             "the m-law is a theorem" must travel with its dependency named.
             Unchanged and still owed: `citation-verifier` (2 HD relations), `compile-diff`
             (`ROADMAP_REDIRECT_v4` + the unwritten `POSITIVE_FINDINGS_MASTER_v19`),
             `experiment-designer` (E3-chirality, LBE v2), `memory-drafter` (PRNG boundary).
IN FLIGHT:   none.
DO NOT REDO: **CORRECTION to my own earlier entry today** (the Brick D2 closure block). Its
             `DO NOT REDO` line reads "Do NOT look for a sign argument — there isn't one to find."
             **That is wrong and is retracted.** There IS a sign argument: §2 of
             `RESULT_jacobi_sign_law_proved_secp_class_v1.md`, the congruence `J ≡ −1` mod a prime
             above 3, and it is what makes the law hold in BOTH regimes. The correct statement is
             only that the sign is *not the hard half* — rationality is. Do not read the earlier line
             as licence to skip §2. (Append-only: the earlier entry is left intact per rule 1.)
             Also corrected: my opening claim that the user's avenue list was "stale on five of six
             items" was **overstated** — honest score is two of six fully stale, the rest partially
             stale or live (`AUDIT_..._honesty_flags_v1.md` §F1). The document-layer defect finding
             (D-1/D-2/D-3) is independently evidenced and stands.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-01 · Claude Code · N8/M21 sharpened to a pointwise identity
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/NOTE_n8_pointwise_convolution_v1.md` (new);
             `n8_pointwise_convolution_v1.py` + `.log` (new); `ROADMAP_REDIRECT_v4.md` §3.1
             (M21/N8 citation correction + the advance); `RESEARCH.md` entry `(f)`.
OWED:        The twist comparison itself — **N8, still open**. Concretely: show
             `Σ_{Fix(Frob)} w = Σ_{Fix(φ∘Frob)} w` for `w(Q) = χ₂(y_Q·y_{R−Q})`, `φ(Q) = R−Q`,
             at every rational `R ≠ O`. Finite, elementary, no ℓ-adic input required.
             `compile-diff` if folded into a master.
IN FLIGHT:   none.
DO NOT REDO: **Cite the identity as M21** (`POSITIVE_FINDINGS_MASTER_v12`, 1171 μ₆-orbit cells,
             11 primes 43≤p≤1303); the mechanism question is **N8**, open since v12. It is NOT new —
             the 2026-09-01 (b) RESEARCH entry's "New high-priority open item" is wrong on that word
             and `RESULT_rho_branch_convention_v1.md` §7 already self-corrects. Do not re-derive it a
             third time; M21 sits at ~line 1400 of a 1671-line master that the v13–v18 delta chain
             does not surface — that is the root cause and it is a DOCUMENT defect (see the v4 §0
             D-3 entry), not a mathematical one.
             What IS new and should be built on: the identity is **pointwise**
             (`h₂ = h₁⋆h₁ − 2·leg·p·δ₀`, zero at every `d≠0`), it holds at **composite `n`** (103,
             139, 151, 193) where the μ₆-cell framework does not obviously apply, and both sides are
             the SAME weight over two Frobenius-stable loci. Do NOT attack it through the Fourier
             form `V₂ = V₁²−2·leg·p` — that form hides the localization at `d=0` and drags in the
             cyclotomic field for nothing.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-02 · Claude Code · F2 discharged; m-law downgraded to "theorem modulo one empirical bridge"
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/mlaw_s1_firsthand_check_v1.py` (new);
             correction headers on `RESULT_jacobi_sign_law_proved_secp_class_v1.md`,
             `ROADMAP_REDIRECT_v4.md` §1 Brick D, `AUDIT_session_2026_09_01_honesty_flags_v1.md` §F2;
             `RESEARCH.md` entry `2026-09-02 (a)`.
OWED:        **NEW: prove `m = Re(S)/p`** — Weil/Lefschetz point counting on `C : w⁴ = x³+B` over
             `F_{p²}`; `#C(F_{p²})` expands into character sums whose `χ₄`-terms are the `A_new`
             block. Well-posed, needs no GKR/sheaf input. Until then the m-law is NOT a theorem.
             Unchanged: N8 twist comparison; `compile-diff` (v4 + unwritten master v19);
             `citation-verifier` (2 HD relations); `experiment-designer` (E3-chirality, LBE v2);
             `memory-drafter` (PRNG boundary). All four project agents remain unloaded.
IN FLIGHT:   none.
DO NOT REDO: `RESULT_jacobi_closed_form_m_law_v4.md` **§1 is verified first-hand and exact** (14
             primes, `Z[ζ₁₂]`): `(★)`, `χ₄` trivial on `F_p^*`, `χ₃(−1)=1`, and the cube-count
             `#{x:x³=u} ∈ {3,0}`. Do not re-audit §1.
             **DOWNGRADE — read before repeating yesterday's headline.** "The m-law is a theorem" is
             TOO STRONG. What is proved is the **closed form of the character sum `S`**
             (`S = −2p` on cubic residues, `+p` otherwise, at `p ≡ 7 mod 12`, scale-immune). The step
             `m = Re(S)/p` is introduced in `RESULT_mu4_eigenvalue_individual_v1.md` as a **"Firing
             control — an independent route to the same integer"**, graded 155/155 OOS + 30/30
             in-sample. That is `[EMPIRICAL]` at high weight, NOT a derivation. A firing control in
             one file had become a load-bearing axiom in another file's headline.
             **Standing rule proposed:** auditing the dependency you doubted is not auditing the
             chain. When a proof is claimed to yield a consequence, trace EVERY link between them —
             the unflagged ones are where controls get silently promoted to premises.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-02 · Claude Code · the m-law is a THEOREM at p ≡ 7 mod 12 (Lefschetz bridge proved)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/RESULT_mlaw_theorem_secp_class_v1.md` (new);
             `mlaw_lefschetz_bridge_v1.py` + `.log` (new); discharge boxes on
             `RESULT_jacobi_sign_law_proved_secp_class_v1.md` and `AUDIT_..._honesty_flags_v1.md` §F2;
             `ROADMAP_REDIRECT_v4.md` §1 Brick D; `RESEARCH.md` entry `2026-09-02 (b)`.
OWED:        `citation-verifier` — attempted, unavailable — on three standard facts, named in the
             RESULT §5: Weil/Grothendieck–Lefschetz for curves; `w⁴=f`, `deg f=3`, `gcd(4,3)=1` is
             smooth genus-3 with ONE point at infinity; Poincaré reducibility (`Jac(C) ~ E × A_new`,
             traces additive). Arms A2/A3 witness the first two numerically.
             H1 at `p ≡ 11 mod 12` still `[EMPIRICAL]` — steps 1–3 apply, `J = +p` unproved there.
             Unchanged: N8 twist comparison; `compile-diff` (v4 + unwritten master v19);
             `experiment-designer` (E3-chirality, LBE v2); `memory-drafter`. All agents still unloaded.
IN FLIGHT:   none.
DO NOT REDO: **`m = Re(S)/p` is PROVED** — do not re-open it as a firing control or re-measure the
             155/155 agreement. Proof: `a_new(2) = −2Re(S)` by the quartic-character count on
             `C : w⁴=x³+B` over `F_{p²}`, plus `b₁=0`, plus Newton.
             **`b₁ = 0` is DERIVED, not assumed** — at `p ≡ 3 mod 4`, `gcd(4,p−1)=2` so
             `#C(F_p) = #E(F_p)`. `RESULT_mu4_eigenvalue_individual_v1.md` §1 invokes the "μ₄
             argument" without proof; it is one line of point counting and is now written down.
             **The m-law H2 is a THEOREM at `p ≡ 7 mod 12` and is SCALE-IMMUNE** (an identity in `p`,
             valid at `2²⁵⁶`). Do not re-cite it as `[EMPIRICAL, 26 OOS primes]`.
             Process note worth keeping: this morning's entry DOWNGRADED the m-law after finding the
             firing control; this afternoon proved it. The downgrade is what turned a vague unease
             into a well-posed problem that closed in one sitting. Correcting yourself precisely is
             the cheapest way to find the next theorem.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-02 · Claude Code · N8 scoped: the identity holds on ONE branch and is false on the other
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/NOTE_n8_branch_confinement_v1.md` (new);
             `n8_branch_confinement_v1.py` (new); correction header on
             `NOTE_n8_pointwise_convolution_v1.md`; `ROADMAP_REDIRECT_v4.md` §3.1 scoped;
             `RESEARCH.md` entry `2026-09-02 (c)`.
OWED:        N8 itself — still open, now with its hypothesis named. `compile-diff` if folded into a
             master. Unchanged: H1 (`p≡11 mod 12`) Jacobi sign; master v19; `experiment-designer`
             (E3-chirality, LBE v2); `citation-verifier`. All four project agents still unloaded.
IN FLIGHT:   none.
DO NOT REDO: **M21 / N8 is NOT a general identity.** It holds on the `m = +1` branch and is FALSE on
             `m = −2` (group-indexed test: `p = 19, 223, 331, 367`, `f` acquires a 21–29-value spread
             off `O`, not a constant). Do not attempt to prove it as stated without the branch
             hypothesis — **any proof must invoke `E[2] ⊄ E(F_p)`; one that does not is wrong.**
             **Why nobody saw this:** `h₁[d] = χ₂(y_{[d]G})` is dlog-indexed, so it presupposes a
             CYCLIC `E(F_p)`; and `m = −2` ⟺ `7` a cubic residue ⟹ `x³+7` splits ⟹ `E[2]` rational
             ⟹ non-cyclic. **The instrument could never represent the failing branch.** M21's 1171
             cells and every later test are all `m = +1`. Converse is false (199, 271, 379 are
             non-cyclic via odd torsion, still `m=+1`) — do not state the biconditional.
             **CORRECTION to my own `NOTE_n8_pointwise_convolution_v1.md` (2026-09-01):** its §2
             "far more is true" is wrong — the pointwise form adds exactly ONE Fourier coefficient,
             and that coefficient is VACUOUS (`f̂(0) = 2mp`, equal to the claimed `2p` iff `m=1`,
             which cyclicity forces). Its §3 "not a cell artefact" is weaker than written: the
             composite-`n` primes are composite but still cyclic. §4's reformulation stands.
             secp: prime order ⟹ cyclic ⟹ `m=+1` FORCED — the measured `m=1` at secp is now a
             consequence, not an observation.
             **Standing rule proposed:** an instrument that cannot represent part of its domain will
             report a law that holds only on the part it can see. Audit the INDEXING SCHEME for
             domain restriction before generalising any measured identity. (Companion to the
             `ρ_p` convention-dependence rule from 2026-09-01 (b).)
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-02 · Claude Code · N8 hypothesis pinned to "#E(F_p) odd" (self-correction within the session)
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/n8_hypothesis_discriminator_v1.py` (new); self-correction box
             on `NOTE_n8_branch_confinement_v1.md` §6; `ROADMAP_REDIRECT_v4.md` §3.1 sharpened;
             `RESEARCH.md` entry `2026-09-02 (d)`.
OWED:        N8 still open. `compile-diff` if folded into a master. Unchanged otherwise.
IN FLIGHT:   none.
DO NOT REDO: **The N8/M21 hypothesis is `#E(F_p)` ODD** (= `E(F_p)[2]` trivial = `x³+7` irreducible
             mod `p`). **NOT** "not-full-2-torsion" — that was my own error earlier in this same
             session, corrected in `NOTE_n8_branch_confinement_v1.md` §6. The discriminating family
             is `p ≡ 11 mod 12`: `p ≡ 2 mod 3` makes `x↦x³` a bijection, so `x³+7` has exactly ONE
             root, so there is exactly one rational 2-torsion point and `n` is even — `E[2] ⊄ E(F_p)`
             holds and the identity **FAILS anyway** (7 primes tested, 5–19 distinct values off `O`).
             A SINGLE rational 2-torsion point breaks it.
             **The identity's home is WIDER than `p ≡ 7 mod 12`:** `p = 61, 97` (`≡1 mod 12`, `n` odd)
             satisfy it. And the whole `p ≡ 11 mod 12` arm is EXCLUDED. Do not describe N8 as a
             `p≡7 mod 12` statement.
             **Where a proof should start** (do not re-derive): `ψ(P)=χ₂(y_P)` vanishes exactly at `O`
             and at rational 2-torsion points, so `n` odd ⟺ `ψ` is `{±1}`-valued off `O` ⟺ mult-by-2
             is a bijection on `E(F_p)` ⟺ `φ(Q)=R−Q` has exactly one rational fixed point per `R`.
             Also already derived: parametrising lines through `−R` by slope `λ` gives
             `y_P·y_{P'} = y_R² + 3x_R y_R λ + 3x_R²λ² + y_R λ³`, so `(h₁⋆h₁)[R] = Σ_λ χ₂(cubic)` —
             another elliptic point count. Suggestive, not a closure.
             secp has prime order ⇒ `n` odd ⇒ secp is inside the identity's domain.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-02 · Claude Code · N8 reduced to one Weil sum; R=O proved
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/NOTE_n8_twist_reduction_v1.md` (new);
             `n8_twist_reduction_v1.py` + `.log` (new); `ROADMAP_REDIRECT_v4.md` §3.1;
             `RESEARCH.md` entry `2026-09-02 (d)`.
OWED:        **`W(R) := Σ_{x∈F_p} χ₂(g_R(x)·(x³+B)) = 0` for `R ≠ O`. That is now ALL of N8.**
             Unchanged: H1 (`p≡11 mod12`) Jacobi sign; master v19; `compile-diff`;
             `citation-verifier`; `experiment-designer` (E3-chirality, LBE v2). Agents still unloaded.
IN FLIGHT:   none.
DO NOT REDO: **Branch condition is `#E(F_p)` ODD**, not merely "cyclic" — (c)'s phrasing was implied
             but blunt. Odd `n` ⟹ mult-by-2 is an automorphism ⟹ every `R` has a UNIQUE rational
             half `A₀=((n+1)/2)R`. That uniqueness is what the whole argument runs on and what fails
             at `m=−2`. Use the odd form.
             **`R = O` is PROVED** (`−(n−1)` on `E` vs `+(n′−1)` on `E'`, difference exactly `2p`).
             Do not re-derive; and note the `2p` is NOT an error term — it is `p≡3 mod4` acting with
             opposite sign on the curve and its twist.
             **Do not attack N8 as a two-loci comparison** (the framing in
             `NOTE_n8_pointwise_convolution_v1.md` §4). Translate by `A₀` first: both sides become
             χ₂-sums of the ONE even function `G_R(C)=y_{A₀+C}y_{A₀−C}`, over `E(F_p)` and over the
             QUADRATIC TWIST `E'(F_p)`. `G_R` even ⇒ descends to the x-line ⇒ the whole thing is the
             single Weil sum `W(R)`. Bookkeeping trap: `E'(F_p)` MUST include its identity, else every
             `R≠O` is off by exactly `+1`.
             **Next step is one-variable:** `W(R)` is `±1` over `p` terms vanishing EXACTLY (not
             `O(√p)`) ⇒ look for a fixed-point-free involution on `P¹` pairing opposite signs, or show
             `u² = g_R(x)(x³+B)` has Frobenius trace 0. Do not look for an `O(√p)` bound — the
             vanishing is exact and a Weil bound will not give it.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-02 · Claude Code · N8: involution hypothesis refuted; μ₃ structure found
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/NOTE_n8_mu3_structure_v1.md` (new); correction headers on
             `NOTE_n8_twist_reduction_v1.md` §5 and `ROADMAP_REDIRECT_v4.md` §3.1;
             `RESEARCH.md` entry `2026-09-02 (e)`.
OWED:        **Exhibit the μ₃ action on `u² = D_R(x)` for general `R`** — equivalently prove
             `L(t)` is a polynomial in `t³`, or that `Jac` has CM by `Z[ω]`. That closes N8 and
             yields `s₂ = 0` free. Unchanged: H1 (`p≡11 mod12`); master v19; `compile-diff`;
             `citation-verifier`; `experiment-designer`. Agents still unloaded.
IN FLIGHT:   none.
DO NOT REDO: **DO NOT search for an involution.** My own `NOTE_n8_twist_reduction_v1.md` §5 and the
             matching handoff line called the exact vanishing "the signature of a fixed-point-free
             involution". **REFUTED** — exhaustive search over ALL Möbius involutions at 3 (p,R)
             cases finds none. Reasoning error on record: exact vanishing of a ±1 sum has at least
             two sources — a pairing involution AND a constraint on the L-polynomial; I named one and
             called it "the signature".
             **The structure is μ₃, not order 2.** `D = (x³+B)·M·(x−a)` (deg 7, squarefree, `M` cubic
             from interpolation, `a = x_{A₀}`) ⇒ `u²=D` genus 3, `W(R) = −s₁`. Measured `s₁ = 0` AND
             `s₂ = 0` at ALL `R`, `p=43` (30/30) and `p=67` (78/78) — 108 cases. By Newton + the
             functional equation this forces **`L(t) = t⁶ + a₃t³ + p³`**, a polynomial in `t³` =
             μ₃/CM-by-`Z[ω]` signature. `W(R)=0` is a COROLLARY; prove the μ₃, not the sum.
             μ₃ is exact and visible at `x_{A₀} = 0`: `D(βx) = βD(x)`, `(x,u)↦(βx,√β u)`, and
             `√β ∈ F_p` since `p ≡ 7 mod 12` ⇒ `(p−1)/3` even. For `a ≠ 0` it is NOT
             `x ↦ β(x−a)+a` (that moves the roots of `x³+B`) — find the right map.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-04 · Claude Code · N8 thread was DUPLICATION; CM explanation refuted; CLAIMS.md never consulted
STATUS:      CLOSED
CHANGED:     Withdrawal/supersession headers on `NOTE_n8_{pointwise_convolution,branch_confinement,
             twist_reduction,mu3_structure}_v1.md`; `ROADMAP_REDIRECT_v4.md` banner + §3.1 box (D-3
             withdrawn); `CLAIMS.md` — **MB closed** (`[OPEN]` → `[PROVED — PROVISIONAL]` ⟳ PROPOSED)
             and the N8 row annotated; `RESEARCH.md` entry `2026-09-04 (a)`. Ledger re-touched, green.
OWED:        User agreement on the MB grade move (CLAIMS.md rule 4 — it sits ⟳ PROPOSED).
             `citation-verifier` on P23 + MB. H1 (`p≡11 mod12`). `experiment-designer` (E3-chirality,
             LBE v2). Agents still unloaded. **`POSITIVE_FINDINGS_MASTER_v19` is NOT owed — withdrawn.**
DO NOT REDO: **RUN `python3 check_ledger.py` AT SESSION START. READ `CLAIMS.md` FIRST.** It says it is
             the only current document; everything else is a journal or a rotting snapshot. I skipped
             both and burned a session re-deriving `NOTE_n8_pencil_reduction_v1.md` (2026-09-01 21:57)
             — the `n`-odd hypothesis, the `Q₀=R/2` translation, the degree-7 x-line reduction, the
             genus-3 framing, the `R=O` case, the even-`n` control. The guard was RED the whole time.
             **N8 IS NOT OPEN.** P19 grades the identity `[PROVED — uniform]` (Galois descent on
             `E[2]`, reaches secp); M21 `[VERIFIED]→[PROVED]` via P19; the pencil note adds an
             outline + a passed falsifier.
             **The ζ₃ is GALOIS, NOT CM.** My `NOTE_n8_mu3_structure_v1` §4 says the `t³`-structure
             comes from μ₃/CM by `Z[ω]`. **REFUTED** — the lemma holds on non-`j=0` curves with no μ₃
             automorphism. Mechanism: `n` odd ⟺ `x³+Ax+B` irreducible ⟺ Frobenius 3-cycles `E[2]∖{O}`
             ⟹ `Jac(C)~E₁×E₂×E₃` cyclically permuted ⟹ trace 0.
             **Method rule (the real lesson): I computed `k=1,2` and named a mechanism. Those are
             exactly the two values where the CM story and the block story AGREE.** The discriminating
             test is `k=3` (nonzero over `F_{p³}`, divisible by 3) — already run in the pencil note.
             Stopping at the last point where two hypotheses agree is evidence for neither; before
             naming a mechanism, find the `k` where the rivals diverge and compute THAT.
             Also: `ROADMAP_REDIRECT_v4` D-3 is withdrawn — `CLAIMS.md` IS the consolidation, and its
             rule 1 forbids the `v19` I prescribed.
LEDGER:      UNCOMMITTED: repo not a git checkout at this path; artifacts on disk only.

---

## 2026-09-05 · Claude Code · NotebookLM resync + null-retest campaign opened
STATUS:      CLOSED
CHANGED:     `btc_puzzle_investigation/NULL_RETEST_MASTER_v1.md` (new, 242 rows / 18 batches);
             `.claude/agents/shortcut-tester.md` (new). NotebookLM "Mapping the Curve": +23 sources
             (41 → 64), the full set postdating `MASTER_v18`.
OWED:        `CLAIMS.md` P23 wording fix (proposed, awaiting user). `btc_puzzle_investigation/` still
             untracked in git — 1,973 files incl. `CLAIMS.md` itself; user decision pending.
             Unchanged: `citation-verifier` on P23 + MB; H1 (`p≡11 mod12`); user agreement on the MB
             grade move. **`shortcut-tester` cannot be spawned until a session restart** — agent
             definitions load at session start; this is the standing "agents unloaded" condition.
             Inlined the spec into `general-purpose` as the workaround.
IN FLIGHT:   none. Batch 1 arm C returned on both: **M25 UNFORCED** (planted lever of v1's size
             fires at z=+12.5 through the same matched control; "no residual" is a bound of ±5% yield;
             coverage gap found — v2's table covered 20/24 j0 primes, omitting the three highest-lever
             indices, re-run 2026-09-05, null holds). **N15 UNFORCED** (planted joint-only signal reaches
             the permutation floor at 0.92 bits while per-readout MIs stay at 5e-5–9e-5). Both tagged
             EXPLORATORY — they ran before the spec froze, so they carry no campaign rate.
             `experiment-designer` returned 8 blocking edits; all applied in `NULL_RETEST_MASTER_v2.md`.
             **Arms A/A2/B not started** — they need per-row type confirmation, the A2 script-rerun
             harness, and the redaction generator first.
DO NOT REDO: **Do not re-run `verify-jacobi-mlaw-code.py`'s conclusions as suspect — the code is
             correct.** It computes `J(χ₃,χ₄)` exactly in `Z[ζ₁₂]` over `F_{p²}` (`t²=−1`, valid at
             `p≡3 mod 4`), runs in 5.5s, and reproduces its table: 20/20, 20/20, 20/20 at
             `p≡7 mod 12`; 19/19, 19/19 at `p≡11 mod 12`. Independently confirmed.
             **Method error on record — the expensive kind.** I graded that run "not credible" on
             three planks, all wrong: (i) I wrote "brute-force summation over `F_p`" in my OWN prompt
             and then quoted it back as the notebook's claim; it never said it, and its code comment
             (line 156) says `F_p^2`. (ii) I read its later `F_{p²}` answer as a retrofit under
             questioning — the comment predates the question. (iii) I called the values fabricated;
             they are exact. **The generator: I was handed the artifact and wrote my own
             reimplementation instead of running it.** Running it costs 5.5 seconds. Run the artifact
             you were given, first, before constructing the frame that judges it.
             **The one real finding survives: 59 of the 98 reported passes are FORCED.** Given the
             source's own §1 reduction `S = χ₃(B)·J + χ̄₃(B)·J̄` with `J` real, `S = 2J` for `B` a
             cubic residue and `S = −J` otherwise. All 59 `S` rows reproduce from the 39 `J` values:
             **59/59, zero mismatches** (`scratchpad/forced.py`). The sweep carries 39 independent
             facts, not 98. Same defect `AUDIT_session_2026_09_01_honesty_flags_v1` already recorded
             in this claim's ancestry (`34/34` → 15 distinct, 19 forced). This is what motivated the
             `shortcut-tester` agent and check 1.
LEDGER:      **`426d47b`** — `btc_puzzle_investigation/` committed 2026-09-05 on user instruction:
             4105 files / 62 MB, `CLAIMS.md` tracked for the first time. ~200 MB of regenerable
             caches `.gitignore`d (15 files; `git add -f` to include). NOT pushed — no instruction.
             Corrected on the way: this folder's "largest untracked file is 1.6 MB, safe on size"
             flag was false (460 MB, 54 MB largest), and my own two predecessors' "repo not a git
             checkout at this path" was false — it is a checkout; files were never added.
