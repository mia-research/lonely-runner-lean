> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS MASTER — v17 (delta successor to v16: concurrent 2026-08-25 session folded — N15 scoped null, A-joint-HO, bit-ceiling framing correction, ζ₃/cap chain integration; v16 N32/N33/N37 cross-linked)

**Date:** 2026-08-26
**Author:** Claude (Opus 4.8). Reconciliation fold requested by the user after a concurrent
2026-08-25 session left post-v15 work unfolded that overlaps v16.
**Predecessor:** `POSITIVE_FINDINGS_MASTER_v16.md` (which folds `ADDENDUM_4`; delta-successor to v15/v14).
**What v17 is.** A **delta successor**, not a rewrite. **All of v16 (and thereby v15/v14) is carried
forward verbatim by reference; anything not updated below is unchanged** (compile rule, Editorial Law 6).
v17 folds the concurrent session's four post-v15 artifacts and cross-links them to v16's N32/N33/N37,
each with a named artifact in the same edit (grade-up rule). **No v16 open item, retraction, caveat, or
grade is deleted.** Both post-v15 branches (v16 = external-report audit; this = the concurrent session)
are now on one chain; nothing from either is dropped.

**The folds, up front:**
1. **N15 (open since v11) — TESTED, scoped null.** `[VERIFIED-scope — scoped null]` No cheap predictor
   (9 singletons + 36 pairs) predicts the joint readout T=(e, s-class, y-parity) beyond a matched null,
   reproducibly across bands 32/64/128/256 (incl. real secp band) + exact b=16 enumeration; instrument
   live (ε=1 plant fires at log₂3), the one b=128 marginal washed on re-seed. **Not a closure.**
2. **A-joint-HO — extends the CM joint-set scoped null to 6 more channels.** `[VERIFIED-scope — scoped
   null]` r=4 Semaev, m=4/m=5 combos, μ₂ label, GLV-mixed, coord-pair, finer interval: all within null
   across discovery + OOS (N=20k) + ladder to 2¹⁶; all plants fire; **model scale, zero secp power.**
3. **Bit-ceiling framing CORRECTION — the readout "bit ceiling" is self-imposed; the master's A-2a/§E-new
   hanging contradiction is RESOLVED to OPEN.** H(d|[d]G)=0 (determinacy = what ECDLP is), so no statement
   "public geometry carries ≤ X bits about d" is a real information bound — it names one readout set. The
   3.65-bit readout entropy (H(e)=1.585 + H(y-par)=1.000 = 2.585 μ₆-orbit + H(s-class)=1.061 carry, with
   TC≈10⁻⁴ ⇒ orbit ⊥ carry) is a **rising floor, not a cap.** Does **NOT** upgrade any null. New memory
   `feedback_readout_ceiling_self_imposed_2026_08_25`.
4. **ζ₃/cap chain INTEGRATION — the cap + uniform 120° law reduce to one PROVED trace identity.** The
   identity `e₂=e₁²−χ₂(−1)p` (⟺ `S₂=−S₁²+2χ₂(−1)p`) is **PROVED uniform** (`RESULT_26_PROVED_weil_
   restriction_v1`, Galois descent on E[2]); identity ⟹ cap `|V_y(a)|≤2√p` ⟹ ζ₃-pairing is
   **PROVED-symbolic** (`RESULT_n1_cap_reduces_to_one_identity_v1`, palindromic reduction, both χ). **One
   live caveat on the whole chain: the Weil-II purity citation (D2; failed citation-verifier ×4)** — the
   same analytic-citation gap #6/#7 tracks as owed. χ₂(−1)=(−1)^((p−1)/2) IS the p mod 4 split; **secp
   (p≡7 mod12 ⇒ p≡3 mod4) sits in the χ₂(−1)=−1 (minus) regime.**
5. **Cross-links to v16 (no v16 grade moves):** v16 **N32** (ζ₃ eigenvalue lock, point-count, 6 curves)
   and **N33** (cap |V|≤2√p, prime-order 0/317) are independent point-count/empirical **witnesses** of
   the PROVED ζ₃/cap chain in fold 4 — corroboration, not the proof; their grades are unchanged from v16
   (N32 `[VERIFIED — exact, point-counted]`, N33 `[VERIFIED — empirical; prime-order scope]`).
   v16 **N37** (d mod {2,3,6} = 0.00 bits on the χ₃/y-parity channel) is consistent with fold 3
   ("determined ≠ extractable"): N37 is a bounded null on cheap extractors, already NOT a no-go — no
   change, now explicitly linked to the anti-ceiling stance.

**Standing-asymmetry note (Editorial Law 7).** This fold is reconciliation: it carries two scoped nulls
(N15, A-joint-HO) at grade without enlarging them to closures, one framing correction that OPENS a
previously over-closed item (bit-ceiling → A-2a resolved to OPEN — a suppression-direction fix), and one
PROVED chain whose sole open caveat (D2 purity citation) is preserved, not smoothed. Direction audit:
the correction runs against the project's one-way suppression bias (it re-opens, does not close); the
PROVED grade is carried with its live citation gap intact.

---

## Part 0 — Sources consumed this pass (added to v16 §0)

| # | File | Extent |
|---|---|---|
| A | `RESULT_n15_joint_readout_confinement_v1.md` (+ `PREREG_…_v1.md`, `…_DEVIATIONS.md`, runner `n15_readout_confinement_runner_v1.py`) | full |
| B | `RESULT_cm_jointset_higherorder_v1.md` (+ `PREREG_cm_jointset_higherorder_v1.md`, runner `cm_jointset_ho_v1.py`, new `semaev_s4` primitive); extends `RESULT_cm_jointset_excess_v3.md` | full |
| C | `NOTE_readout_structure_no_selfimposed_ceiling_v1.md` (+ memory `feedback_readout_ceiling_self_imposed_2026_08_25`) | full |
| D | `NOTE_lmono_gkr_cap_pointcount_integration_v1.md`, `RESULT_n1_cap_reduces_to_one_identity_v1.md` (with its own correction banner → `RESULT_26_PROVED_weil_restriction_v1.md`) | full |

---

## Part I — Row updates / new rows (each with its artifact)

### N15 — joint multi-readout confinement: **OPEN (since v11) → [VERIFIED-scope — scoped null]**
*Artifacts: `RESULT_n15_joint_readout_confinement_v1.md`, prereg + DEVIATIONS D1, runner.*
On constructed known-d secp keys, no cheap predictor (9 singletons + 36 pairs) predicts
T=(e, s-class, y-parity) beyond the matched permutation null, across bands 32/64/128/**256 (real secp
band)** + **exact full-enumeration b=16**, power MI_floor ≈1.3×10⁻³ (singleton)/1.3×10⁻² (pair).
Instrument live (ε=1 plant → log₂3, monotone; hard null calibrated). The one b=128 marginal (p=0.005,
seed 7) **failed reproduction** at b=16/32/64/256 and **washed to p=0.443 on re-seed** — closed as noise.
Per-readout singleton MIs ≤2×10⁻⁴ (below floor); TC(e,s,yp)≈10⁻⁴ (readouts near-independent). **Bounded
magnitude, NOT a closure; DLP-inversion direction out of scope. Untested: ≥3-component joint predictors,
other families/readouts.**

### N39 (new) — A-joint higher-order / GLV / finer-label synergy: **[VERIFIED-scope — scoped null; MODEL SCALE, zero secp power]**
*Artifact: `RESULT_cm_jointset_higherorder_v1.md`; extends `RESULT_cm_jointset_excess_v3.md`.*
Extends the r=3/m=3/μ₃ base scoped null to six channels the v3 base named "not settled": r=4 Semaev (new
`semaev_s4` resultant primitive), m=4 and m=5 combos, μ₂ label, GLV-mixed endomorphism cross-features,
coordinate-pair (x,y), finer interval. All 7 channels within null at every prime across discovery + OOS
(N=20k, primes 2029/2053/2089) + ladder to 2¹⁶ (65539); every primary-family Δ = I(CM)−I(nonCM) ≤ 0 or
≈ 0 (no CM-specific joint synergy); all scattered p∈[0.01,0.05] hits fail reproduction, none < 0.01. All
plants fire (μ₂ plant fixed, distinct_planted 1→2). **q ∈ {541…65539} ≪ 2¹⁶: measures a mechanism, no
ECDLP/extraction claim.** Gates: `semaev_s4` citation SUPPORTED (Semaev 2004 / Kosters–Yeo Prop 2.1;
degenerate cases Prop 2.2, full read owed on limit reset — moot for a null); 2nd experiment-designer read
owed before any Δ promotes (moot). Untested: r=5 Semaev, joint-μ₆ label.

### N40 (new) — public-readout "bit ceiling" is self-imposed (framing correction). **[VERIFIED — exact entropy at b=16; correction = stance]**
*Artifact: `NOTE_readout_structure_no_selfimposed_ceiling_v1.md`; memory `feedback_readout_ceiling_self_imposed_2026_08_25`.*
H(d|[d]G)=0 — the public point determines d in full (that determinacy IS ECDLP), so "public geometry
carries ≤ X bits about d" is never a real information bound; it names one enumerated readout set. Measured
(disjoint entropy method, exact at b=16 full enumeration, H(T)=3.6563): H(e)=1.585 (μ₃) + H(y-par)=1.000
(μ₂) = **2.585** (μ₆-orbit label, = A1.4 `[PROVED]` log₂6) + H(s-class)=1.061 (Eisenstein carry) =
**3.646**, with TC≈10⁻⁴ (**new: orbit label ⊥ carry — that is why they add**). This is a **rising floor
indexed by what you enumerated, not a cap.** Standing correction (all future readout/bit work): do not
call a measured H(readout) a "ceiling"; do not write "0 operational / impossible by no-go" for the
extraction question (that is the DLP, assumed-hard not proven — write "extraction OPEN"). **Does NOT
upgrade N15's null.** Resolves master **A-2a/§E-new** hanging contradiction (see Part II).

### N41 (new) — ζ₃/cap chain: cap + uniform 120° law reduce to one PROVED trace identity. **[identity PROVED-uniform; ⟹cap/ζ₃ PROVED-symbolic; ONE open caveat: D2 Weil-II purity citation]**
*Artifacts: `RESULT_n1_cap_reduces_to_one_identity_v1.md` (+ its correction banner), `RESULT_26_PROVED_weil_restriction_v1.md`, `NOTE_lmono_gkr_cap_pointcount_integration_v1.md`.*
The identity `e₂=e₁²−χ₂(−1)p ⟺ S₂=−S₁²+2χ₂(−1)p` is **PROVED uniform** (all a, all p>3) by Galois
descent on E[2] (`RESULT_26_PROVED_weil_restriction_v1`); the earlier "reduces the open gap to one
identity" framing is corrected — the identity was not the gap, it is proved. Identity ⟹ cap
`|V_y(a)|≤2√p` ⟹ ζ₃-pairing `α₂/α₁=ζ₃` is **PROVED-symbolic** (palindromic/anti-palindromic reduction,
both χ; disc `3(4−ε²)≥0`). **The one live caveat on the whole chain: the Weil-II purity citation (D2;
failed citation-verifier ×4)** — carried OPEN, = the #6/#7 analytic-citation gap (N31). p mod 4 split:
χ₂(−1)=(−1)^((p−1)/2); **secp p≡3 mod 4 ⇒ χ₂(−1)=−1 (minus regime, anti-palindromic).**
**Grounds v16 N32/N33** (point-count / empirical witnesses of this proved chain; their grades unchanged).

### Cross-links (no grade moves on v16 rows)
- **v16 N32 / N33** are independent witnesses of N41's PROVED chain — N32's per-curve 120° (point-count,
  p≡1 mod 4) and superspecial √p·ζ₆ (p≡3 mod 4) regimes are the absolute-eigenvalue face of N41's
  regime split; N33's cap 0/317 is the empirical face of the PROVED-symbolic cap. Witnesses, not proof.
- **v16 N37** ↔ N40: the d mod {2,3,6}=0.00-bits result is a bounded null on cheap extractors,
  consistent with "determined ≠ extractable / no information ceiling." N37 already avoids a no-go claim;
  no change.

---

## Part II — Do-Not-Close list updates (v16 §II)

- **A-2a / §E-new (the "0 operational reads wider than the layer" hanging contradiction) — RESOLVED to
  OPEN.** *Artifact: N40 / `NOTE_readout_structure_no_selfimposed_ceiling_v1.md`.* Determinacy H(d|[d]G)=0
  does not bound exposable information; readout entropy is a rising floor; operational extraction stays
  OPEN (assumed-hard, not proven). The contradiction is discharged in favor of OPEN.
- **#6/#7 (cap / purity) — the cap is now PROVED-SYMBOLIC via a PROVED-uniform identity (N41); the ONE
  owed citation is the Weil-II purity citation (D2 / N31, failed citation-verifier ×4), STILL OWED.**
  This sharpens v16's "citation still owed": the analytic chain is proved modulo exactly this one purity
  citation. Item stays open on the citation.
- **N15 — DISCHARGED as a scoped null** (was open since v11; see N15 row). Not a closure of the avenue —
  a bounded null on cheap extractors with named untested channels.
- **A-joint frontier — EXTENDED** (v3 base + N39 six channels, all scoped null); base frontier scope
  widened, no CM synergy found to 2¹⁶.
- **#28 (a-family monodromy) — UNCHANGED, still OPEN.** N41 is a within-cell trace identity + its proved
  consequences; it does not supply the horizontal family monodromy. (v16 N32 already logged within-fiber.)
- **All other v16/v15 do-not-close items (#1, #3, #4, #5, #8, #9, #10–#16, Frontier #15) — carried
  forward unchanged.** Frontier #15 (sub-Rayleigh deficit): unchanged; v16 N34's b=0-slice location
  stands; the full-2D ~0.1% Hermitian-null deficit stands.

---

## Part III — Everything else

All v16 Parts (and thereby v15/v14: ledger P1–P32 / M1–M40 / N1–N38 except the rows above,
corrections, addendum reconciliations, conflicts, post-v12 states, loss inventory, Editorial Law,
certification table) are **carried forward verbatim.** The v14 scale banner and all conditional grades
govern every quotation. **No ECDLP, key-recovery, or 256-bit claim is made anywhere:** N15 and N39 are
scoped nulls (model/constructed scale), N40 is a framing correction that explicitly keeps operational
extraction OPEN, and N41 is public-curve character-sum structure (p ≤ 103) with its purity citation
still owed — none transfers to the cryptographic prime as a break.

## Version History (appended to v16's)

| Version | Date | Notes |
|---|---|---|
| v17 | 2026-08-26 | Delta successor: reconciliation fold of the concurrent 2026-08-25 session (parallel to v16's ADDENDUM_4 fold). N15 OPEN→scoped null [VERIFIED-scope]; N39 (A-joint-HO, 6 channels scoped null, model scale); N40 (bit-ceiling framing correction — A-2a/§E-new resolved to OPEN, readout entropy = rising floor, does not upgrade any null); N41 (ζ₃/cap chain: identity PROVED-uniform via RESULT_26_PROVED_weil_restriction, ⟹cap/ζ₃ PROVED-symbolic, one open caveat = D2 Weil-II purity citation). v16 N32/N33 cross-linked as witnesses of N41; N37 cross-linked to N40. compile-diff gate run (v16 + concurrent artifacts → v17). No v16 open item/grade/caveat deleted; #28 unchanged, #6/#7 purity citation still owed. |
| v16 | 2026-08-25 | Delta successor: folded ADDENDUM_4 (audit of 20 external-agent reports; N32–N38). |
| v15 | 2026-08-24 | Delta successor: H-5 resolved; H2 resolved; N16 folded; N7-monodromy gate. |
| v14 | 2026-08-21 | Full corpus revision + results-level certification. |
