> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS MASTER — v14 (Full Corpus Revision + Results-Level Certification)

**Date:** 2026-08-21
**Author:** ZCode (corpus revision executing the v13 §VII mandate, then a results-level certification pass)
**Predecessor:** `POSITIVE_FINDINGS_MASTER_v13.md` (audit-corrected ledger, provisional grades).
**What v14 is:** the first master compiled after **reading the entire v13 Part-0 gap table from
source** (pass 1), then — per the user's directive "we should do the job properly" — a **second pass
that read the primary RESULT/PREREG/AUDIT/NOTE artifacts behind the load-bearing rows**, so the
certifications below rest on test results, not on masters' restatements or audit syntheses
(Part IX). Every grade is certified against `COUNTERPRIOR_and_closure_grade_spec_v1.md` (a closure
is a graded claim: object, class, power, scope).

**The two findings of the certification pass, up front:**
1. **A new unresolved contradiction (H-5) against the programme's headline positive.** The final
   Semaev v4 RESULT (M25's H1 leg, "the strongest positive finding in the BTC investigation to
   date" per its own §10) reuses v3's |V|=4,5 arms byte-identically (its own C6), while a **same-day
   adversarial audit** (`AUDIT_semaev_v4_method_result_conclusion_v1`) examined the corrected
   #E-bracketed rebuild, found H1 **null** (T1 ≈ −0.01/+0.01, n=22), and identified a design-level
   artifact mechanism (one-sided nearest-#E matching of the edge-#E fixed j0 twist, with
   `quo ∝ 1/#E` supplying the leak). The final RESULT never mentions the audit; no later document
   (v10–v12, compendium, v5 prereg, v13) noticed the seam. Both verdicts are carried; the
   contradiction is unresolved (§IX, M25 note).
2. **A major PROVED result that no master ever folded: the #26 Galois-descent theorem chain
   (2026-08-01/03).** `e₂ = e₁² − χ₂(−1)p` is **proved uniformly** (all `a`, all `p>3`, every
   nonsingular cubic with `n` odd) — upgrading the identity behind M21 far beyond
   `[VERIFIED]`-at-tested-cells, answering N8's "why" at the identity level (Galois descent on
   `E[2]`, finite monodromy; the Stickelberger/ideal route retired for this purpose), and reducing
   the 2√p **cap** to "proved identity + purity," with the purity/Weil-II citation (4 failed
   verifier runs) the sole live input. Folded here as P32; M21/N8/do-not-close items updated.

---

## Part 0 — Completeness Statement and Gap Table

### 0.1 Sources consumed (by file, from source)

*Pass 1 (the v13 gap table):*

| # | File | Extent |
|---|---|---|
| 1 | `POSITIVE_FINDINGS_MASTER_v13.md` | full |
| 2 | `POSITIVE_FINDINGS_MASTER_v12.md` | full (all 1671 lines) |
| 3 | `POSITIVE_FINDINGS_MASTER_v9.md` | front matter, full ledger, Parts 0–IV; remainder via mechanical diff vs v12 |
| 4–6 | `POSITIVE_FINDINGS_ADDENDUM_1/2/3_v1.md` | all full |
| 7–8 | `COUNTERPRIOR_and_closure_grade_spec_v1.md`, `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md` | full |
| 9–17 | the 9 `CORRECTION_*` files | all full |
| 18–22 | the 5 `CONFIRMED_*` files | all full |
| 23–25 | `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v1.md` + `ERRATA_anew_step3_propagation_v1.md` | full |
| 26 | `PROJECT_SUMMARY_secp256k1_v2.md` | targeted rows only (see gap table) |
| 27 | `RESULT_e3_owed_measurement_v1.md` + the two E3 summary JSONs | full |
| 28–29 | `RESULT_cside_replication_v1.md`, `RESULT_mu3_diffset_control_repair_v1.md` | full |
| 30 | mechanical `diff` v9 ↔ v12 | full |

*Pass 2 (results-level certification; verdicts in Part IX):*

| # | File | Extent |
|---|---|---|
| 31–37 | `AUDIT_loadbearing_claims_v1`, `AUDIT_item2_overclaims_v1`, `AUDIT_session_conclusions_v1`, `AUDIT_semaev_v4_method_result_conclusion_v1`, `AUDIT_deflation_claim_chain_v1`, `AUDIT_narrative_conclusion_layer_v1/v2` | all full (v13's primaries, now first-hand) |
| 38–42 | `RESULT_e2_identity_extended_verification_v1`, `RESULT_subrayleigh_deficit_scaling_v1`, `RESULT_jacobi_sign_law_stickelberger_v1`, `RESULT_stickelberger_citation_verified_v1`, `RESULT_cside_pooled_tilt_settlement_v1` | all full |
| 43–44 | `RESULT_semaev_cm_relation_yield_v3.md`, `RESULT_semaev_cm_relation_yield_v4.md` | full (v4 incl. all per-prime tables and deviations D1–D5) |
| 45–46 | `RESULT_26_PROVED_weil_restriction_v1.md`, `RESULT_26_closure_symbolic_uniformity_v1.md` | full |
| 47 | `RESULT_n1_cap_reduces_to_one_identity_v1.md` (incl. its header correction) | full |
| 48–49 | `PREREG_e3_owed_measurement_v2.md`, `PREREG_grouplaw_e3_real82_v1.md` | arms + decision rules (§0–§2 each) |
| 50–52 | `NOTE_k3_analytic_reduction_v2.md`, `NOTE_core_gate_exact_carry_region_v1.md`, `NOTE_glv_orbit_carry_conservation_v1.md` | all full |
| 53 | `RESULT_anew_supersingularity_step3_gap_and_cartier_route_v2.md` | full (pass 1 had the head; tail now read) |

### 0.2 Gap table — still not read from source in this pass

| File(s) | Consequence |
|---|---|
| `POSITIVE_FINDINGS_MASTER_v1–v8`, `v10`, `v11` | covered by the carried compile-diff records + the clean v9↔v12 mechanical diff; not independently re-read. |
| `PROJECT_SUMMARY_secp256k1_v1/v2.md` (full text) | conflict-bearing rows + the audit's byte-diff findings (Axis A) read; the remaining Parts may hold unfolded items. |
| The remaining RESULT/PREREG primaries named in the ledger but not in §0.1 (e.g. `RESULT_mu6_cohomology_supersingular_v2` itself, `RESULT_n1_120deg_exact_v1`, `RESULT_twist_orbit_*`, `RESULT_N1_P1_gate…`, `RESULT_lambda3_*`, `RESULT_jacobi_closed_form_m_law_v4`, `harmonic_support_pattern` lineage, `masked_structure_findings_v1–v38`) | known through the addenda/corrections/masters at grade; not opened directly in either pass. |
| `PREREG_semaev_cm_lever_capability_v5.md` (updated 2026-08-21 — active thread), the v5 smoke results, `COMPENDIUM_mu6_lever_v1`, `ROADMAP_REDIRECT_v3` | referenced by read files; not read. |
| `RECOVERED_RESULTS_v1.md`, `LIVE_LEADS_MAP_v1.md` | known via v12 §C; not read. |
| Scripts, logs, `.jsonl` data, memory files, `archive_handovers/` | never; this pass read documents only. |

No completeness claim is made beyond §0.1. Everything unlisted is a gap, not a certificate.

### 0.3 What this revision found, in one paragraph

The v10–v12 consolidation seam is **mechanically clean** (zero content losses v9→v12). The real
losses were at the **addendum seam** (ADD1/2/3 never reconciled: 19 retractions, several proved
results, the N1 account, the E3 reject), in the **grade-tag layer** (four cross-document
conflicts, §IV), and — found by the certification pass — in the **primary layer itself**: one
proved theorem chain (#26) never folded, and one unresolved same-day audit against the headline
positive (M25) never surfaced. Two corrections on disk had never been applied to the master. The
E3 measurement owed by v12 §E.3 was discharged 2026-08-18/19 (after v12, unknown to v13).

---

## Part I — The Certified Ledger (P/M/N), v12 grades + v14 audit status

*Carried from v12 Part A with corrections applied. The scale banner, language rules, compile rule,
and anomaly-drill rule of v12 govern every row verbatim and are not restated.*

### I.1 Proved rows (P-family)

| # | statement (compressed) | v12 grade | v14 status |
|---|---|---|---|
| P1 | secp congruences `p≡3 mod 4, 1 mod 3, 7 mod 12` | `[PROVED]` | carried |
| P2 | `Σχ₂(y_P)=0` exactly at every `p≡3 mod 4`; converse false | `[PROVED]` | carried |
| P3 | `C: w⁴=x³+B` genus 3, `H¹(C)=H¹(E)⊕H¹_new` (2+4) | `[PROVED]` | carried |
| P4 | `ζ₄∈Aut(C)` any cubic ⇒ `Q(i)⊆End⁰(A_new)` | `[PROVED]` | carried |
| P5 | `x³+B` only: `Q(ζ₁₂)⊆End⁰(A_new)`, degree `4=2·dim` | `[PROVED]` | carried |
| P6a | additive bound `\|U\| ≤ 4√p+1` (WD=KS) | `[PROVED\|WD]` | carried; exhaustive FFT audit first-hand (worst ratio 0.960, p=61,67,211) |
| P6b | χ₂ rows via **Kummer** sheaf (`2√p`/`4√p`); **not KS** | `[PROVED\|WD]` | carried |
| P7 | secp `E` ordinary | `[PROVED]` | carried |
| P7′ | `ord_n(p)=(n−1)/6`, 254-bit | `[VERIFIED — 254-bit]` | carried |
| P8 | Claim S: μ₆ selection rule on the curve | `[PROVED]+[VERIFIED]` | carried (54/54 re-verified in the audit) |
| P9 | Claim F: field-level rule (6/3 sectors) | `[PROVED]+[VERIFIED]` | carried |
| P10 | missing ℤ/2 = sextic twist | `[PROVED]` | carried |
| P11 | Cap Law: flap ⟺ `\|u−v\|>½`; ¾:⅛:⅛ | `[PROVED — continuum]` | carried; 126/126…99666/99666 exact at 5 primes (ADD1 A3.1); Cap-Law steps 1+3 regraded `[PROVED — classical input]` at source (ADD2 B2.4) |
| P12 | CM spine law, ¾:⅛:⅛, ε μ₃-orbit invariant | `[PROVED — continuum]+[VERIFIED]` | carried |
| P13 | `Hom(E,A_new)=0` at secp via Tate | `[PROVED]` | **RE-CERTIFIED CONDITIONAL — §IV.1/IV.4**: rests on the reviewed Cartier derivation, 2 citation caveats. Correct tag: `[PROVED — conditional; 2 caveats]` |
| P14 | prime-order rigidity; `C_t` smooth genus-1 ∀t | `[PROVED]` | carried |
| P15 | concentration ⟺ character correlation (exact reduction) | `[PROVED]` | carried |
| P16 | twist-discriminator ≡ scalar census identity (exact symbolic) | `[PROVED — exact symbolic]` | carried; audit-re-derived in sympy |
| P17 | GLV-orbit carry-conservation law; label ⊥ carry; 18-class joint law | `[PROVED — exact]` | carried; primary NOTE read — closed form `c(X)=(0,⌊u−v+½⌋)∈{0,±ω}`, exact ¾:⅛:⅛ law, conservation identity, 20k orbits + 82 keys + 6 puzzles; **P145 the sole exposed puzzle with certified ε≠0 (c=−ω)** |
| P18 | slope² identity + un-normalized k=3×χ₂ channel | `[PROVED]` | carried; primary NOTE read — `W(0)=n²−O(n)` with `#{slope-0}=O(n)` rigorous, 0/18906 violations, W(0) exact at 3 primes; phase-normalized `\|mean_QR\|≥c` remains the named `\|T\|`-tail gap; the "GLV-eigenvalue-restricted" story is killed **analytically** (flat s=0 mode) |
| P19 | carry-ceiling work-invariance (compression × oracle = 1 identity) | `[PROVED — identity]` | carried |
| P20 | Aut₆ carry-exclusion ledger (73/82 keys; no exposed puzzle is an Aut₆-relative) | `[PROVED — exact, 82-key census]` | carried; primary NOTE read — 65/8/9 split, definitive `x_a≟β^k x_b` test, 3.65-bits-indexical ceiling with the no-go argument |

**Proved rows restored from the addenda and the primary layer (homeless in every master):**

| # | statement | grade | source |
|---|---|---|---|
| P21 | **Aut(E) orbit bit-ladder has constant ceiling `log₂6 ≈ 2.585` bits**; μ₂/μ₃/μ₆ bits chain additively; conversion convention recorded. Scope: Aut-quotient maps only. | `[PROVED]`+`[VERIFIED]` | ADD1 A1.4 |
| P22 | **`(n,k,D)` T=1 stratum = the Dirichlet reciprocal-floor lattice** `{base ± ⌊lo/q⌋}`; `√lo` the exact continent/island boundary. | `[PROVED + VERIFIED identical sets]` | ADD1 A1.5 |
| P23 | **A_new supersingular at every `p≡3 mod 4`, every separable cubic — incl. secp — via the Cartier route** (`𝒞\|V₁⊕V₃=0` forced twice ⇒ superspecial ⇒ supersingular), replacing the gapped μ₄/End⁰ argument. **Caveats (travel with every quotation):** (i) Oort Thm 2+Rmk 3 give `a=g⟺superspecial` over `F̄_p` only; (ii) Pries Prop 3.17 (`g=2` p-rank 0 ⟺ ss) is stated for *principally polarized* varieties — `A_new`'s induced polarization need not be principal; unresolved whether load-bearing. Owed: Xing / Maisner–Nart peer-reviewed primaries for `m=±1` (the SMZ preprint is the current weakest link); the verdict-neutral `b₁` sign-flip errata (`anew_cartier_audit_v2.sage:190`, confined to printed `b₁` on the `p≡1 mod 4` arm). | `[PROVED — one independent review (instrument self-validated); 2 citation caveats]` | RESULT_anew…_cartier_v1/v2 (both read in full), ERRATA |
| P24 | **secp is a Silverman–Stange amicable pair** (verified at the actual 256-bit primes; twist-discriminating control); enforcing structure named; framing narrowed (Pasta curves exist). Curve-side fact. | `[PROVED by verification — at scale]` | ADD1 A1.2, ADD2 R-B5.45 |
| P25 | **120°-law exact identities**: `V₂=V₁²±2p` exact in `ℤ[x]/Φ_n` (10 primes); `v=u²−¾` (357/357); `max_a v ≤ ¼` unconditional. | `[PROVED — exact]` | ADD2 B1.2 |
| P26 | **`S_y≤2` reduces to the sign of one L-coefficient**; the `v≤0` route dead (exact counterexamples) but the inequality not refuted. **Certification addendum:** the palindromic reduction (purity + identity ⟹ `\|ε\|≤2`, discriminant `3(4−ε²)≥0`) is `[PROVED — symbolic]` at source — the cap and this inequality share the identity+purity structure. | `[PROVED — algebra]` (reduction); inequality OPEN | ADD2 B1.3/B1.4; `RESULT_n1_cap_reduces…` §2 |
| P27 | **Jacobi sign law `J(χ₃,χ₄)=∓p`** both halves; Stickelberger citation discharged against Katre, **3 load-bearing caveats** (proof's hypothesis, not the printed one; digit-sum `f=2` form; ideal-not-value). Consequence: **`m=1` at secp** (`√p·{ω,ω²,ζ₆,ζ₆⁵}`, orders [3,3,6,6]) — the promotion the m-law file pre-committed. **Certification detail:** the primary RESULT still carries its `[PROVED — modulo (D2), citation UNVERIFIED]` tag — the in-file grade move was offered (2026-07-27) and never applied; the Katre verification supersedes with the caveats attached. Novelty doubted. | `[PROVED — 3 Katre caveats]` | ADD2 B1.5/B2.1; both primaries read |
| P28 | **Ideal-level CM route collapses to a rational symbol** (ℓ≥5); ℓ=3 escapes via μ₆ units. | `[PROVED — forced]` | ADD2 B1.6 |
| P29 | **Twist-orbit forced landscape**: `⟨f_a,f_b⟩=nI−J` exactly; Parseval `Σ\|V(a)\|²=n(n−1)`; 3-pt bispectrum ≡ 0 forced; `\|V(a)\|²` the one free 2nd-order object. | `[PROVED — forced, exact]` | ADD2 B1.7 |
| P30 | **Three exact conservations of `U`**: alignment = `l¹` norm; `Σ\|U\|²=p²(n−1)` basis-invariant (unitary-only; oblique untested); `Σ_a\|U(a,b,c)\|²=n(n−1)` — the constraint random nulls lack. | `[PROVED — exact]` | ADD1 A1.7 |
| P31 | **The E[2]-branch-locus correction**: the "exhaustive over F̄" symmetry negative was exhaustive over the wrong set (7 roots; the branch locus has 8 points incl. ∞); the true stabilizer has order 4 (the E[2]-translations). | `[PROVED]` | `CORRECTION_26_branch_locus_8point_v1` |
| P32 | **★ The #26 Galois-descent theorem (unfolded by every master).** For every nonsingular `E/F_p`, `p>3`, with `n` odd: `Σ_λ χ₂(G_R(λ))=0` exactly, equivalently **`e₂(a)=e₁(a)²−χ₂(−1)p` for every `a`, uniformly in `p`** — via Galois descent on `E[2]` (the lifts close into a Klein four-group; Frobenius 3-cycles the three 2-dim eigenspaces; `Jac(C)=Res_{F_{p³}/F_p}(E₁)`; trace 0). The one hedged link (Klein-four closure) is itself a symbolic identity over `ℚ(A,B)` (uniform), second-code-path-confirmed to `p=10⁶`, mechanism char-poly `T⁶−c₃T³+p³` machine-checked with a **firing even-`n` control** (117 cells, 0 pass). Hypothesis is `n` odd — **not** `j=0`, not `p≡7 mod 12`. **Owed:** one end-to-end isolated re-run of the four claims (the reviewer confirmed the load-bearing `D,F` frame by hand, then hit a session limit; the mechanical remainder was discharged by decidable artifact). Consequences folded below (M21, N8, cap). | `[PROVED — symbolic, uniform]` | `RESULT_26_PROVED_weil_restriction_v1` + `RESULT_26_closure_symbolic_uniformity_v1` (both full); acknowledged by `RESULT_n1_cap_reduces…`'s header correction |

### I.2 Measured rows (M-family)

M1–M24 carry from v12 verbatim (samples and caveats as there). Certification notes where v14 changes or adds:

- **M3/M4** (saturation; V real/imag): carried. N1 — the ½-saturation question — is **PARTIALLY
  ACCOUNTED** (§IV.3), not "no explanation offered" (the v9–v12 row text is stale).
- **M9**: carried with the v10 scope note.
- **M14**: carried with the forced-control caveat; ADD1 A2.3 adds that the non-separation holds in
  **both** norms (sup-norm control computed; ρ₂/ρ∞ char≈random in each).
- **M21** (census identity / 120° law): carried at `[VERIFIED]` **with the P32 upgrade attached**:
  the underlying identity `e₂=e₁²−χ₂(−1)p` is now **PROVED uniformly** (odd `n`, any cubic) by the
  #26 descent theorem — the exact-convolution certificate (7 primes/1182 frequencies in the
  primary; +823,1303 by the v8 audit) and the 22-prime `g=deg gcd` sweep become consistency
  checks, not the best evidence. The eigenvalue-level ζ₃-pairing reading additionally consumes the
  purity input (numerically verified at p=43,67,127 to 160-bit; on-disk WD derivation; the Weil II
  **citation itself failed the verifier 4×** — N31).
- **M25** (Semaev CM relation-yield lever): **status changed to DISPUTED — see the H-5
  certification in Part IX.** Reported facts of the frozen-schedule run (SHA f92cb4bb, 24 primes,
  |V|=4..8): T1(j0) 0.207→0.834, p<0.0001 per level, 21–22/24 positive, pooled 0.544/120;
  best AICc `0.90·ln\|V\|−1.04` ⇒ ratio ≈ `0.35\|V\|^0.9`; bootstrap stability 62.6% (j0), 10.6%
  (j1728, downgraded per D4); C1–C6 pass; deviations D1–D5 declared. **But the same-day audit**
  (`AUDIT_semaev_v4_method_result_conclusion_v1`, read in full) examined the corrected
  #E-bracketed rebuild, found H1 null (T1_j0 = −0.010/+0.012, n=22) with the mechanism
  (edge-#E fixed j0 twist + one-sided nearest-match + `quo∝1/#E`; B=1 isolation T1=−0.014; class-
  and trace-independent; C4 shows the #E-sensitivity channel), and the final v4 RESULT's |V|=4,5
  arms are **byte-identical to v3's** (its own C6) — i.e. the audited design. The |V|-growth shape
  is the live counter-consideration (a constant matching bias does not obviously grow with |V|),
  but **no document derives the |V|-signature of the hypothesized leak**, and the RESULT never
  mentions the audit. Net: **H1 leg unresolved; do not cite "the strongest positive in the
  programme" without H-5 attached. Owed: bracket-matched re-run at all 5 levels, or a derivation
  of the leak's |V|-dependence.** Power floor caveat unchanged (residual effects <0.092 log-units
  not excluded).
- **M26** (x-closure effect, bounded): carried, with the label correction attached (v4 control =
  3k independent elements vs k β-orbits; **β/CM specificity NOT isolated**; the order-3
  structure-matched control still owed). The audit agrees H2 is real and stable (R2≈1.6–2.2×).
- **M27–M30**: carried with their CONFIRMED/NOTE evidence (exact #135/#140 readouts; k=3 channel
  with the amplitude-hierarchy correction — CM≈non-CM≈0.30–0.31 flat at scale; μ₆ 6×/2×
  multiplication; character grading ~9σ + scoped fill-in null). The AUDIT_session_conclusions
  re-tests of the three v11 nulls are now first-hand (cubic-e 0/8 at n≈6000; χ²=0.837; fill-in at
  the 30th percentile).

**M-rows restored from the addenda:**

| # | statement | grade | source |
|---|---|---|---|
| M31 | `m=b₂/p` names all four A_new eigenvalues; measured law H1 (`p≡11 mod 12 ⇒ m=2`, 42/42) and H2 (`p≡7 mod 12`: `m=−2` iff B cubic residue, else `m=1`, 36/36), OOS, forced columns not counted. At secp (with P27): `m=1`. **Certification addendum (Cartier v2 §4):** all five `m∈{−2..2}` are realizable by abelian surfaces over `F_p` (Honda–Tate; SMZ Thm 12.1(2) weakest link for `m=±1` at `p≡7 mod 12`) — so the family's `m`-support is a fact about the family, not a triviality. | `[EMPIRICAL — OOS]` | ADD1 A2.1/A2.2; RESULT_anew…_v2 §4 |
| M32 | Joint-object symmetry map complete: exactly `{parity ℤ/2}×{GLV μ₆}`; 6-cell equipartition; magnitude generic in both norms. | `[VERIFIED — exact]` | ADD1 A2.3 |
| M33 | Per-harmonic profile **Rayleigh at π/4**; no active/starved split. | `[EMPIRICAL, 7 primes]` | ADD1 A2.4 |
| M34 | `E[u⁴]` consistent with full SU(2), excludes the 3/8 torus/CM reduction (12/12 OOS). Not a proof of SU(2). | `[EMPIRICAL — scoped]` | ADD2 B3.1 |
| M35 | μ₃-spectral-invariance is CM-specific (j=0: 100%; j≠0 ≈ ⅓). | `[VERIFIED]` | ADD2 B3.2 |
| M36 | **Row-budget layer exists**: pooled `Z=+70.50`, 10/10 sign; instrument over-dispersion ≈1.55×; layer not decomposed. | `[EMPIRICAL]` | ADD2 B3.3 |
| M37 | Flap χ₂-imbalance `S′=(3/2)h(−p)(1−χ₂(2))`; P1 a theorem; the single open step **(†)**. | P1 `[PROVED]`; (†) `[VERIFIED, NOT PROVED]` | ADD1 A1.3 |
| M38 | `(n,k,D)` validity domain = contractible Farey solid / 1-D coprimality net; connectivity arithmetic-structured; μ₆ not on this object. | `[PROVED — exact]` + `[VERIFIED — matched control]` | ADD1 A2.8 |
| M39 | Complexity filtration: max D-terms 2 through width 7·10⁵; T=1 stratum shatters; clustering sub-generic; mechanism = Dirichlet lattice (2-adic guess refuted). | `[PROVED — exact]` + `[VERIFIED]` | ADD1 A2.9 |
| M40 | **The forced μ₃-invariant subspace** (restored positive): `h_k[m·d]=h_k[d]` (4 primes, k=1,2) — the χ₂(y) sign sequence constant on μ₃-orbits, `≈(n−1)/3` free signs; j=0-specific, present on secp; exploitability untested ("just GLV" closes a different object). | `[MEASURED — forced symmetry]` | `CORRECTION_deflation_overreach_v1` §4.2 |

### I.3 Open rows (N-family)

N1–N19 carry from v12 with these certifications:

- **N1** — **RE-CERTIFIED, grade corrected** (§IV.3): *structurally accounted modulo uniformity*.
- **N2** — **RE-CERTIFIED, grade corrected** (§IV.1): discharged by P23 (conditional, caveats).
- **N3–N7**: carried (N7 sub-Rayleigh deficit: **certification sharpening** — the scaling primary
  gives 30/30 primes, pooled Stouffer **−71.80**, one-directional, PERSISTENT across [151,12043]
  (FADES falsified; const-vs-1/log p ABSTAIN by the pre-committed contradiction guard, curvature
  k2=+0.021 z=+12.4 opposing the const slope-verdict); v12's "−13.99" headline is the earlier
  7-prime discovery number. Model range only; mechanism open; row-budget shadow live).
- **N8** ("why does `e₂=e₁²−χ₂(−1)p` hold?") — **largely ANSWERED at the identity level by P32**:
  the mechanism is Galois descent on `E[2]` (finite monodromy: Klein four × the ℤ/3 Frobenius
  cycle; trace 0 on `H¹(C)`); the ideal-arithmetic route is retired for this purpose. **Residue:**
  N9's module-splitting `W⊕W⊗ξ` remains open — a scalar-identity proof does not split the module
  (P16); and the a-family monodromy (#28) is a distinct open object.
- **N9/N10**: carried (W-piece unidentified; degree-40 group unpinned).
- **N11/N12**: carried; **conditional on H-5** (the lever whose mechanism/bend these ask about is
  the disputed M25 H1 leg).
- **N13–N16**: carried (N15 joint readout OPEN — the load-bearing open cryptographic question;
  N16 `eps==ε_LBE` open, `|u−v|≤½ == build.eps` cross-check owed).
- **N17–N19**: carried (D2/mod-6 null at power; Dirichlet-island closure by counting; χ₃-marginal
  balance Aut-enforced at `p≡7 mod 9` ⇒ secp's label marginal exactly uniform).

**N-rows restored/added:**

| # | item | status |
|---|---|---|
| N20 | `W_N` 1-D intertwined-proxy extraction route closed three ways; scope: the 1-D collapse only. | `[VERIFIED — decidable artifact]` (ADD3 A) |
| N21 | μ₃/GLV frequency-support and phase-within-triple: scoped nulls — the deficit's organization is not in the μ₃-graded b-channel. | `[EMPIRICAL — scoped nulls]` (ADD3 B/C) |
| N22 | Semaev v3/v4 H1 — see M25/H-5 (no longer stateable as "v3 artifact, v4 clean"). | `[DISPUTED — unresolved seam]` |
| N23 | LBE battery family-wise null at floor `e_min=0.02`; diffuse arm ABSTAINED; grid symmetry-mismatched. | `[EMPIRICAL — scoped bounded null]` (ADD1 A3.1) |
| N24 | Island curve-image nulls at secp itself (energies; exact GLV-orbit detectors `G1=G2=0`, plants fire). | `[EMPIRICAL — scoped, at scale]` (ADD1 A3.2/A3.3) |
| N25 | Flap ε under the group law at secp: null below ~2⁻⁶–2⁻⁹ forced-equal pairs; flap density 130≡256-bit. | `[EMPIRICAL — powered null]` (ADD1 A3.4/A3.5) |
| N26 | No pre-committed d-free selector predicts `\|U\|` above the permutation floor. | `[EMPIRICAL — scoped]` (ADD1 A3.6) |
| N27 | Twist-orbit spectrum and magnitude: null OOS (12 primes, plants fire); joint/higher-moment/larger-p untested. | `[EMPIRICAL — scoped, OOS]` (ADD2 B4.1/B4.2) |
| N28 | `S_diff` on the real 82: real ≡ known-MT (p=0.59); power floor ε≈0.034–0.048; blind to exactly the μ₃-graded subspace. | `[MEASURED — scoped null]` (ADD2 B4.3) |
| N29 | **cside chain final state (certified from all four primaries):** the √2 under-dispersion correction (raw z −2.64 → ≈−1.87) was real but moot for the `inv` lead — the calibrated pooled settlement (36 primes, empirical null of the pooled statistic) gives **p=0.265**, v1's own primes flip sign (+0.24 mean in-range), the lead **closed as a candidate** there; the secondary **pow7** hit (Z=−2.73, Holm-significant) failed the OOS AND-gate, and the 30-fresh-prime 80%-powered replication **washed** it (p_fresh=0.178 > 0.159 boundary; residual ≤ ~⅓ claimed size would owe M≈118). Shortscalar arm at 2¹²⁸ gate-blocked, untouched. | `[EMPIRICAL — inv closed-as-candidate; pow7 WASH, pre-registered]` |
| N30 | μ₃ difference-set channel (group-law multiset, real-82): repaired powered bound **no cubic-class concentration above ε=0.0415** (80% power, secp's p; E3x=489 inside [84,12537]; cell B void). The v32 "generic, AP-control fires" clause was wrong twice over (one control forced to 0, one firing for an unrelated reason). | `[EMPIRICAL, powered, control fires]` |
| N31 | **The Weil II purity citation debt** — the one live input of the cap chain (P32 + palindromic reduction ⟹ `\|V\|≤2√p`): the Deligne/Weil-II purity statement the eigenvalue-level reading consumes has **failed citation-verifier 4×**; numerically verified (p=43,67,127, 160-bit) and partially derived on disk (`weil_deligne_character_bound_v1.md`), but by the project's own rule the citation must clear before any grade moves up on it. **Distinct from the (discharged) Stickelberger-(D2).** | `[CITED — TO VERIFY, ×4 failed]` |

---

## Part II — The 9 Corrections: Application Status (verified against targets)

| Correction | Target | Applied where | v14 action |
|---|---|---|---|
| `CORRECTION_120deg_census_certification_direction_v1` | `RESULT_n1_120deg_exact_v1` grade | applied at v8+ (M21 `[VERIFIED]`, exact-convolution certificate) | certified applied; **and superseded in substance by P32** (the identity is now proved uniformly; the one-sided-certification concern attached to the `g=2` cells is discharged for the identity, with the purity input N31 carrying the eigenvalue-level residue) |
| `CORRECTION_cside_v1_null_underdispersion_v1` | `RESULT_cside_nonalgebraic_correlation_v1` | **never applied in any master** | folded here as N29 (with the settlement + replication read from source) |
| `CORRECTION_deflation_overreach_v1` | `RESULT_jclass_B §4` | gate discharged at source; narrow form absorbed into the cross-curve control; **the §4.2 forced-subspace positive never folded into a master** | folded here as M40 |
| `CORRECTION_e3_cmvanishing_interaction_reading_v1` | E3 two-arm reading | scope-withdrawn at source; provenance concern answered by the generator-free null (2026-08-18) | certified applied; E3 disposition updated (Part V) |
| `CORRECTION_semaev_cm_yield_mechanism_literature_v1` | LFD citation misuse | applied in v12 §E.2; the counter-prior clause (no closure from a failed search) applied | certified applied |
| `CORRECTION_v10_lever_enumeration_v1` | v10 Framing | premise not restated in v12; replacement wording on disk | certified; the "not an enumeration of lever space" clause binds v14's own language |
| `CORRECTION_v32_mu3_diffset_controls_v1`/`_v2` | v32 control sentences + the master Appendix-A clause | **NOT applied in v12** (Appendix A still carries "AP control fires 13–36×") | struck here; replaced by N30's powered bound |
| `CORRECTION_26_branch_locus_8point_v1` | the exhaustive-negative | the superseding PROVED result existed on disk, referenced by no master ledger (v12 mentions "#26 theorem" only inside the A-2c memory-audit row) | restored as P31+**P32** (full chain read from source) |
| Stickelberger/(D2) discharge (`RESULT_stickelberger_citation_verified_v1`) | `(D2)` debts | partially applied: v12 still writes `[PROVED — modulo (D2)]`; the primary's own tag was never updated either (the offered in-file move was never executed) | resolved here: P27 carries the corrected grade with the 3 Katre caveats; both stale tags named |

---

## Part III — Addendum Reconciliation (every item restored or re-killed, with reason)

**On the audit tallies.** `AUDIT_narrative_conclusion_layer_v2`'s counts ("ADD1: 7 retractions
dropped, 1 re-claimed, 7 frontiers dropped; ADD2: 6 retractions, 13 frontiers, 4 de-sharpenings")
tally **dropped items**, not addenda contents — the actual contents are ADD1 = 12 retractions
(#27–38), 11 new frontiers (#15–25), 3 status changes; ADD2 = 7 retractions (#39–45), 5 new
frontiers (#26–30), 3 status changes, 2 framings narrowed. Both sets of numbers are correct for
what they count; the addenda were richer than the drop-tallies alone suggest. v14 restored
everything regardless of which bin it was in.

### III.1 ADD1 (2026-07-23)

| Item | Disposition in v14 |
|---|---|
| A1.1 A_new supersingular | restored with corrected grade (P23): `[PROVED]` at ADD1 → gapped 2026-08-02 (ordinary stratum not excluded; explicit ordinary witness `E×E^d`, 0/30) → re-closed on the reviewed Cartier route, 2 caveats; fact (i) discharged, (ii) retired-by-replacement |
| A1.2 amicable pair | restored (P24), framing narrowed |
| A1.3 flap = class number | restored (M37); (†) open |
| A1.4 bit-ladder ceiling | restored (P21) — was homeless |
| A1.5 reciprocal-floor lattice | restored (P22) |
| A1.6 gauge-free `W_cov` | restored (feeds the λ₃ dissolution and N30's machinery) |
| A1.7 three conservations of U | restored (P30) |
| A2.1/A2.2 m-law + Jacobi reduction | restored (M31, P27-chain) |
| A2.3 joint symmetry map | restored (M32) |
| A2.4 Rayleigh at π/4 | restored (M33) |
| A2.5 sub-Rayleigh deficit | already in master as N7 — no loss (certification sharpening in I.3) |
| A2.6 N1 parity refuted + tail localization | restored (into N1's corrected grade) |
| A2.7 λ₃ dissolution | restored as the **controlling retraction** (§IV.2) |
| A2.8/A2.9 Farey topology + T=1 fragmentation | restored (M38, M39) — d-side thread was ADD1-only |
| A3.1–A3.6 scoped nulls + positives | restored (N23–N26; Cap-Law 5-prime exact match into P11's status) |
| Retractions #27–38 | all 12 restored (standing retraction ledger continues from them) |
| Frontiers #15–25 | #15 resolved-by B1.5/B2.1; #16 (†) open; #17 superseded by M36; #18–25 carried to §VI |
| A6 method notes 1–10 | binding |

### III.2 ADD2 (2026-07-27)

| Item | Disposition |
|---|---|
| B1.1 120° exact identity | restored at the corrected grade — **and superseded by P32** (uniform proof) |
| B1.2/B1.3/B1.4 N1 mechanism identities + sub-Weil reduction + v≤0 refuted | restored (P25, P26) |
| B1.5 + B2.1 Jacobi sign law + Stickelberger/Katre | restored (P27); discharges v12's H-2 |
| B1.6 ideal-level collapse | restored (P28) |
| B1.7 twist-orbit forced landscape | restored (P29) |
| B2.2 non-abelian a≠0; ζ₃ geometric | restored — **re-scoped by P32**: the L-Stick retirement stands, and L-mono is no longer needed *for uniformity* (descent proves it); the a-family monodromy (#28) remains a distinct open object |
| B2.3 A_new channel framing; **½ = 2/4** | restored (the N1 account, §IV.3) — strengthened by P32 (the 120° ingredient is now proved, not just per-cell) |
| B2.4 literature sweep | restored (Cap-Law classical-input regrade; Lemma C not located; Pasta) |
| B3.1–B3.4 | restored (M34, M35, M36, E3→Part V) |
| B4.1–B4.3 | restored (N27, N28) |
| Retractions #39–45 | all 7 restored |
| Frontiers #26–30 + status changes | #26 (uniformity) **superseded by P32** — its residue is the purity citation (N31) and the a-family monodromy; #27–30 carried to §VI |
| B7 method notes 1–6 | binding |

### III.3 ADD3 (2026-08-10)

All items restored (N20, N21) plus the method note (a must-fire control can miss a variance
miscalibration unless it shares the signal's correlation structure; a √N-flat pooled Z is a
variance artifact). The deficit's organization is **not** in the μ₃-graded b-frequency channel;
named next probes open.

---

## Part IV — The Four Conflicts, Resolved From Source

### IV.1 A_new supersingular at secp — RESOLVED

Both stated sides were wrong. The "PROVED via Cartier, valid at 2²⁵⁶" reading overstates its own
source (the Cartier RESULT v1 says `[UNREVIEWED DERIVATION]… must not be cited as more`; v2's
review upgrades it but holds "Not flat `[PROVED]`" with the two caveats unresolved — Oort over
`F̄_p` only; Pries's principal-polarization hypothesis). The "24/24 small-p only, not proved at
dim 2" reading (v9/v12 N2) is doubly stale — it describes the v4-era `Q(i)`-inert criterion whose
*reason* was withdrawn 2026-07-23 (retraction #27), and ignores both the ADD1 proof and its
2026-08-02 re-audit. **Controlling grade (P23): `[PROVED — one independent review; 2 citation
caveats + peer-review-primary debt + b₁ sign-flip errata]`.** The summary layer's own v1→v2 drift
was conservative (the audits' byte-diff found every hunk a downgrade) — the distortion there was
staleness, not self-firming.

### IV.2 λ₃ eigenvector μ₃-covariance — RESOLVED: the retraction controls

ADD1 retraction #30 retracted the claim twice over (gauge instability at 8/8 powered primes, SEP
plant proving it isn't underpower; no covariant excess over the π-orthogonal matched null — the
6/6 "excess" was `(16/15)` rescaling arithmetic). v9 re-asserted the item at lines 890 (frontier
tail) and 1194 (Appendix A) — stale v4 carry-forwards, 19 days post-retraction, no new evidence;
v12 carries both verbatim and lists the contradiction as H-3 without resolving it. **v14: RETRACTED
(#30 controls); both stale sites struck; the λ₂ "~50%" item inherits the same gauge question
(not separately re-run — neither asserted nor retracted).**

### IV.3 N1 / half-saturation — RESOLVED: accounted modulo uniformity

The three grades and their homes: heading "RESOLVED to relative rigidity" (PROJECT_SUMMARY_v2
§B.5); ledger row "Major advance… **Open on uniformity** (frontier #26)" (same file); "no
explanation is offered here" (v9–v12 N1 row, stale v4 text). From source: the exact ingredients
are proved (P25; and now P32 makes the 120° ingredient uniform); the account is ADD2 B2.3's
rigidity budget (additive `bx+cy` 4 free eigenvalues; `χ₂(y)` 2 free × `{1,ζ₃}` ⇒ **½ = 2/4**);
ADD1 A2.6's older `[−1]`-involution candidate retains its live counterexample (`bx` at 0.909).
**Controlling grade: structurally accounted (candidate mechanism at hypothesis level on proved
ingredients); OPEN on the remaining axis** — which P32 has now narrowed from "uniformity of the
120° law" (done) to the eigenvalue-level/purity input and the a-family distribution questions.
The summary heading was firmer than its own row (synthesis-outruns-rows); the masters' "no
explanation" was stale. Neither extreme survives.

### IV.4 P13 — RESOLVED (follows IV.1)

`[PROVED — conditional on the reviewed Cartier derivation; 2 caveats]`. Route 2 inherits exactly
that conditionality. Do not quote P13 unconditionally.

---

## Part V — Post-v12 State Changes (unknown to v12 and v13)

1. **E3 (A-1d) owed measurement — DISCHARGED 2026-08-18** (`RESULT_e3_owed_measurement_v1.md`,
   frozen prereg v2 read: arms and decision conventions verified against the run). The reject is
   NOT a generator-pool artifact (generator-free structural null, 20k sets, forced symmetries
   shared: `E3=13125`, 98.24th pctile, `p=0.0354`); set-specific (band-matched MT sets at the 48.6th
   pctile, `q_MT=0.015`); instrument fires (β²-plant FPR 0.022, power 0.878 at Δ=100); **bounded**:
   family-wise non-significant (`p_FWER=0.083` Westfall–Young over {E2,E3,E6}; Bonferroni-7 0.248;
   N=82 ceiling); CM-mediated (absent on non-CM E′ at the same prime); μ₄ discriminator deferred
   with a structural scope reason. **The master's "neither signal nor noise" caveat is
   discharged: a bounded, set-specific, CM-mediated single-statistic reject at the power
   ceiling.**
2. **Group-law E3 — RAN 2026-08-19** (prereg read: frozen post-sign-off; the "fires harder"
   prediction framed as tested-not-assumed): `E3_gl=489` at the **13th percentile, p=0.26 —
   null**; GLV-closed control exactly 0 (consistent with the v32 forcing theorem); A4 FPR 0.012.
   The CM-native marginal channel does not reject. Live on this key set: triples (88,560),
   band-localized and orientation-odd subspaces (where E3 is blind by construction).
3. **The v5 Semaev capability prereg was updated 2026-08-21** (active thread; not read — gap).

---

## Part VI — The Do-Not-Close List (open frontiers; none may be closed by argument or mood)

1. **N15 / joint readout** — do `e ⊕ s-class ⊕ y-parity ⊕ interval` jointly constrain `d`?
   Untested; single readout carries full determined info (MI=1.585 bits) with no cheap filter (max
   0.033 bits / 8 predictors). The load-bearing open cryptographic question.
2. **The a-family monodromy (former frontier #26/#28)** — the distribution of the traces `V₁(a)`
   as `a` varies (`S_y≤2`/sub-Weil `\|V₁\|≤√3√p`; the sub-Rayleigh deficit's mechanism). NOTE the
   re-scope: **uniformity of the ζ₃-pairing/identity itself is now proved by descent (P32)** —
   what remains here is the distribution/monodromy object, plus the **purity citation (N31)** that
   the eigenvalue-level reading consumes.
3. **(†) `C′−C=3h(−p)`** — the single open step of the flap class-number law.
4. **Semaev H2 control** — β-orbits vs random order-3 orbits (decides the "CM" label on M26).
5. **Semaev H-5 resolution FIRST** — the capability triplet (§XI.20: cost-side, mechanism split,
   \|V\|=9/10 extrapolation) is conditional on the M25 H1 leg, which is disputed; the resolution
   owed is a bracket-matched re-run at all levels or a derivation of the hypothesized #E-leak's
   |V|-signature.
6. **The 2√p cap** — re-scoped by P32: the palindromic route (identity + purity ⟹ cap) is proved
   as an implication; the identity is proved uniform; the open input is the Weil II purity
   citation (N31) and any residue between the coefficient identity and the pointwise ceiling at
   eigenvalue level. (v13's "no verified progress toward the cap" is superseded — it predated the
   #26 chain.)
7. **Purity at every embedding (generic j)** — still the load-bearing open premise for reading
   the law at generic `j` at eigenvalue level (deflation audit D-1); note the coefficient
   identity itself is now proved for all odd `n` (P32).
8. **N7 sub-Rayleigh deficit mechanism** — row-budget shadow live (M36); ADD3's narrowing stands;
   c-axis, `c=±b`, higher phase invariants, p-scaling re-test each owe their own prereg.
9. **N16 `eps == ε_LBE`** + the owed `|u−v\|≤½ == build.eps` cross-check on the project script.
10. **N13 syzygy sweep** and the yield→cost translation (H8) — the latter conditional on H-5.
11. **cside residual**: sub-half-density orbit-level effect untested (owes M≈118); shortscalar
    arm at 2¹²⁸ gate-blocked, untouched.
12. **E3 blind subspaces** on the fixed 82-key set: triples, band-localized, orientation-odd.
13. **All restored ADD1/ADD2/ADD3 threads** (Part III): d-side Dirichlet-lattice extensions,
    LBE μ₆-matched pairs at `n>5·10⁴`, diffuse family-wise arm, eigenvector resolution at
    `n~10⁵–10⁶`, ε carry-trajectory, ≥3-key/amicable joint-SET, twist-orbit joint/higher-moment
    extensions, ADD3's named probes.
14. **P23's own debts** (2 caveats; Xing/Maisner–Nart primaries; Caveat-2 resolution) and
    **P32's owed isolated re-run**; **P27's in-file tag update**.
15. The five genuinely open items flagged by `AUDIT_session_conclusions` (joint readout; cleverer
    predictor incl. CM/Hecke route; `\|T\|`-near-0 equidistribution; j=1728 subgroup dip ~1.5σ;
    μ₃-graded syzygy module).
16. **Memory-layer corrections** (`secp_N2_supersingular_closed`, index I4) — still owed there;
    v14's grades supersede for any session reading this master first.

---

## Part VII — Version-Loss Inventory (merged: degradation audit + addendum seam + this pass)

### VII.1 The H3→Master compression (from `DEGRADATION_AUDIT_H3_TO_MASTER_v1`, read in full)

H3's five live frontiers → 4 deleted at H4, 0 left at Master v1. Repairs since: #1 restored as
§XI.1 (still open); #2 resolved-by KS; #3 restored as §XI.3 (Hom=0 scoped correctly); #4 held at
`[HEURISTIC+CITED]` via retraction #8; #5 restored as the standing SCALE BANNER. The H4 closure
frame (door map / costumes / "honestly open") is retired; the self-cert-word trigger is standing
law (Part VIII).

### VII.2 The addendum seam (2026-07-23 → 2026-08-18) — the dominant documented loss, now repaired

Because ADD1/2/3 were never reconciled into v5–v12 (referenced 0/1/0 times), the following were
invisible to every master until this document: 19 retractions, the proved results now P21–P30,
the N1 account, the λ₃ kill-record (allowing its stale re-assertion), the E3 pre-registered
reject (buried at the v9 seam back to a stale "at-the-floor" null), the d-side thread, and ADD3
entirely. **Not inflation** (0 grade-inflated across all three addenda, per the audit's own
check) — selective omission under a false completeness certificate. v12's "reconciled across
master + both addenda" certificate was false; this document is the reconcile. Per the narrative
audit's Phase-1 Axis A, the summary layer's own v1→v2 drift was conservative (every hunk a
downgrade) — the mechanism at both layers is **staleness + omission**, not self-firming.

### VII.3 The v9→v12 seam — CLEAN (mechanical, this pass)

`diff` v9 vs v12: 6 deletion lines, all non-lossy (5 title/lineage; 1 rewritten in place to carry
the v12 UPDATE annotation). 329 added lines. **Zero content losses at the v10–v12 seam.**

### VII.4 The primary-layer losses (found by the certification pass)

Two kinds, both previously invisible because no gate covers the primary→master seam:
- **An unfolded theorem chain**: `RESULT_26_PROVED` + `RESULT_26_closure_symbolic_uniformity`
  (2026-08-01/03) prove the e₂ identity uniformly; every master (v9–v12), the summary, and both
  addendas pre-date or omit it; v12 references a "#26 theorem" only inside a memory-audit row.
  Folded as P32 with its consequences (M21, N8, cap, frontier re-scoping).
- **An unresolved same-day audit against the headline positive** (H-5, §IX): the final Semaev v4
  RESULT and `AUDIT_semaev_v4…` flatly disagree on H1 at |V|=4,5 on the same frozen schedule; the
  RESULT reuses the audited design's arms verbatim (its own C6) and never mentions the audit; no
  later document noticed. Carried as DISPUTED; resolution owed (§VI.5).

### VII.5 Memory-layer over-closures (carried from v12 §A-2; corrections still owed there)

`secp_N2_supersingular_closed` and index I4 ("do NOT run another symmetry search" — which hid the
#26 theorem for five rounds) remain owed corrections in the memory layer.

---

## Part VIII — Editorial Law (binding on v14 and all successors)

1. **No sentence firmer than the weakest row beneath it.**
2. **Every completeness claim names its sources by file** (§0.1); anything unlisted is a gap (§0.2).
3. **Every negative verdict names its object, its class, its power, and its scope** (the closure-grade
   spec P1: a closure is a graded claim at the same bar as PROVED).
4. **"Honestly / genuine" are audit triggers** — audit whatever sentence contains them.
5. **Auditor false-negatives exist** (the 0.93-shadow near-miss, self-retracted in the audit
   itself): reproduce the exact stated metric before flagging a claim.
6. **Compile rule**: a successor may not delete an open item or retraction; carry forward verbatim
   or mark `resolved-by <artifact>` / `bounded-by <artifact>`. Grades move down freely; up
   requires a named artifact in the same edit.
7. **Standing asymmetry**: the measured distortion is dominated by staleness, omission, and
   negative bias — but both directions are audited (the cside settlement/replication and the E3
   FWER bound are downward-direction checks firing correctly; the #26 fold and the E3
   set-specificity are upward-direction recoveries).
8. **From the corrections and audits read at full depth, four additional standing rules**:
   (i) a null must share the signal's forced symmetries *and* its correlation structure (cside
   √2; ADD3's √N-flat-Z tell); (ii) a group action relating cells is not a within-cell forcing
   (ADD2 #39/#40 — committed twice); (iii) an inherited `[CITED]` tag is not verification
   (Semaev-literature correction); (iv) **a superseded/audited primary's verdict must be carried
   with its successor** (H-5's lesson: the final v4 RESULT and its same-day audit disagree, and
   neither the compile gates nor the narrative audits caught it because neither reads the primary
   layer).

---

## Part IX — Results-Level Certification Table (pass 2)

*Each load-bearing v14 item → primary read from source → verdict. This is the "test results, not
conclusions" pass the user directed.*

| Item | Primary read | Verdict |
|---|---|---|
| KS U-bound (P6a; v13 I.1) | `AUDIT_loadbearing_claims_v1` | **UPHELD**: exhaustive FFT, worst ratio 0.960 at p=61,67,211; FFT==direct to 1e-14. The auditor's own 0.93 false-negative is documented in-source and self-retracted. |
| 0.93 joint shadow (M14) | same | **UPHELD**: the stated metric `\|Corr(a₀)\|/‖F‖_∞` reproduces 0.927/0.920/0.950 with ratios 2.51–2.81 at p=163/211/433; the "not reproduced" flag was the auditor's metric error, not a defect. |
| 2√p cap mechanisms (v13 I.3) | `AUDIT_item2_overclaims_v1` | **UPHELD and SUPERSEDED IN PART**: M1 decidably false (minima 1.878/1.349/0.971/0.192), M2 refuted, M3-consistent, `D_β` generic + orthogonal, 73.9%→36.9% baseline correction — all verified. But "no verified progress toward proving the cap" (true 2026-07-24) is superseded by the #26 chain: the cap is now identity [PROVED, P32] + purity [N31, citation owed]. |
| "No keyspace reduction" correction (N15) | `AUDIT_session_conclusions_v1` | **UPHELD**: MI(e;d)=1.585 firing control; max 0.033 bits over 8 predictors at the n≈349 floor; joint readout untested. Three null re-tests hold with margin (0/8 at n≈6000; χ²=0.837; 30th pctile). Five open items confirmed. |
| Semaev H2 label / v3 artifact (M25/M26/N22) | `AUDIT_semaev_v4…` + `RESULT_semaev…_v3` + `_v4` (both full) | **CHANGED — new H-5**: see §IX.H-5 below. v13's I.6 (H2 label) upheld; v13's I.8 and v14-pass-1's "M25 survives on the v4 design" are **both wrong** — the final v4 reuses the audited design's V=4/5 arms verbatim. |
| Census identity (M21) | `RESULT_e2_identity_extended_verification_v1` + `RESULT_26_*` ×2 + `RESULT_n1_cap_reduces…` | **UPGRADED**: exact integer convolution 7 primes/1182 freqs/0 counterexamples (and the primary honestly corrects the record's "8–10 primes" to 3 for the brute V₂ route); **then P32 proves the identity uniformly** — the certification-direction concern is discharged for the identity; eigenvalue-level residue = N31 purity. The primary also independently refutes the commutative-commutation mechanism (non-abelian at p=43,67), matching B2.2. |
| Sub-Rayleigh deficit (N7) | `RESULT_subrayleigh_deficit_scaling_v1` | **UPHELD, SHARPENED**: 30/30 primes, Stouffer −71.80, PERSISTENT (2σ slope band excludes every decay law; FADES falsified), const-vs-1/log p ABSTAIN by the pre-committed contradiction guard; matched-null carries the forced Hermitian symmetry; model range only. v12's "−13.99" is the older 7-prime number. |
| Jacobi sign law (P27) | `RESULT_jacobi_sign_law_stickelberger_v1` + `RESULT_stickelberger_citation_verified_v1` | **UPHELD with a bookkeeping finding**: proof verified step-by-step ((D3) digit lemmas vs 4807 primes; 5 firing controls incl. FC5 killing the π² competitor; secp profile computed directly); information unit honestly 28 not 112. The Katre verification is real (3 caveats confirmed). **The primary's tag was never updated** — it still reads "modulo (D2), citation UNVERIFIED"; carry the correction explicitly. |
| #26 theorem (P32) | `RESULT_26_PROVED…` + `RESULT_26_closure…` | **NEW FOLD**: identity proved uniformly; the hedged closure link closed symbolically over ℚ(A,B); mechanism machine-checked with firing even-n control; group-theory step confirmed against Sage's library ((ℤ/2)³ uniquely gives 3 involutory lifts); one owed isolated re-run. Also explains the jclass 30/30-odd-n / 0/12-even-n pattern and retires the ideal route. |
| Cap reduction (P26) | `RESULT_n1_cap_reduces…` (incl. header correction) | **UPHELD**: palindromic/anti-palindromic reduction `[PROVED — symbolic]` both χ branches; the header correction correctly subordinates the file to P32 and names the one live input (Weil II purity citation, ×4 failed verifier) → N31. |
| cside chain (N29) | `RESULT_cside_pooled_tilt_settlement_v1` + `RESULT_cside_replication_v1` (+ the correction, pass 1) | **UPHELD, PRECISED**: `inv` lead closed at the settlement (calibrated p=0.265; v1's own primes flip sign; the −2.64 was the z-inflation artifact the correction flagged); pow7 secondary surfaced, OOS-gated FALSE, then washed at population level (p_fresh=0.178). Shortscalar arm untouched. |
| E3 field arm (Part V.1) | `PREREG_e3_owed_measurement_v2` + RESULT + JSON | **CERTIFIED PRE-REG-CLEAN**: arms, seeds (20260818), decision rules (integer order statistics, symmetric +1 ties, Westfall–Young min-p, q_MT primary) all frozen pre-data and matched by the run; the four owed items all delivered; numbers as reported. |
| E3 group-law arm (Part V.2) | `PREREG_grouplaw_e3_real82_v1` + JSON | **CERTIFIED**: frozen post-sign-off; the "fires harder" prediction explicitly framed as tested-not-assumed; outcome null (13th pctile); GLV-closed control exactly 0 (consistent with the v32 forcing theorem). |
| P17/P19/P20/N16 | `NOTE_glv_orbit_carry_conservation_v1`, `NOTE_core_gate_exact_carry_region_v1` | **UPHELD in full**: closed forms, exact laws, conservation, 3.65-bit ceiling, P145 (s=0.4035, c=−ω), 82-key census, demarcations — all as the masters carry them, with the proofs now read directly. |
| P18/M28 | `NOTE_k3_analytic_reduction_v2` | **UPHELD**: un-normalized channel PROVED with the rigorous `#{slope-0}=O(n)` bound; the "research-level wall" framing of v1 correctly corrected; phase-normalized gap = the `\|T\|`-tail estimate; the eigenvalue-restriction story killed analytically. |
| P23/P13 (§IV.1) | Cartier v1 (pass 1) + v2 tail (pass 2) + ERRATA | **UPHELD**: v2's grade table is exactly `[PROVED — one independent review; two citation caveats open]`, "Not flat [PROVED]"; downstream P13 "rests on a reviewed derivation carrying two named citation caveats"; §4 adds the m-support finding (all five m realizable; SMZ weakest link) and the b₁ sign-flip errata (verdict-neutral, printed-b₁ only). |

### §IX.H-5 — the Semaev seam, stated once, completely

**Object:** H1 (CM relation-yield on a random factor base, #E-matched), j0, m=3, the 24-prime
frozen schedule (SHA f92cb4bb).

- **The final RESULT** (`RESULT_semaev_cm_relation_yield_v4.md`, header-dated 2026-08-07, revised
  through 2026-08-15 per v12): H1 fires at all 5 levels (T1 0.207→0.834, p<0.0001, 21–22/24);
  V=4,5 **byte-identical to v3** (its own C6: "the same frozen schedule produces identical
  results"); verdict A1; deviations D1–D5 are decision-rule/documentation items only.
- **The same-day audit** (`AUDIT_semaev_v4…`, on the corrected rebuild's m=3 run — different log
  file, `semaev_v4_m3_run.log`): H1 **null** (T1_j0 = −0.010 (p=0.77) / +0.012 (p=0.30), n=22
  after bracket-dropping); the +0.21 mechanism identified (edge-#E fixed j0 twist; one-sided
  nearest-match; `quo∝1/#E`; C4 shows the #E-sensitivity channel at p=0.09–0.13); B=1 isolation
  null (T1=−0.014, n=5); class- and trace-independent; "the audit → rebuild → re-run caught a
  false-positive lever before it was graded."
- **The seam:** the final RESULT never mentions the audit or the rebuild; its C-controls (C2
  median-gap, C4 nonCM-vs-nonCM) do not test matching one-sidedness; no document between 2026-08-07
  and this pass (v10–v12, compendium, the v5 prereg updated today, v13) references either the
  audit or the rebuild.
- **The live counter-consideration:** the |V|-growth (0.207→0.834, monotone increments) is not
  obviously produced by a constant matching bias — but no document derives the |V|-signature of
  the hypothesized leak, and the audit's mechanism was never answered, only bypassed.
- **v14 disposition:** M25/N22 = **DISPUTED — carry both verdicts, unresolved.** Do not build on
  the H1 leg (N11/N12, the yield→cost translation, "strongest positive" framing) without H-5
  attached. **Owed (either discharges):** a bracket-matched re-run of H1 at all 5 levels, or a
  derivation showing the one-sided-#E leak cannot grow with |V| as observed.

---

## Version History

| Version | Date | Notes |
|---|---|---|
| v14 | 2026-08-21 | Pass 1 (corpus revision): v12 in full; addenda reconciled item-by-item; 9 corrections verified (2 never applied — folded); 4 conflicts resolved from source; v9→v12 seam verified clean; post-v12 E3 discharge folded; ledger extended P21–P31, M31–M40, N20–N30. Pass 2 (results-level certification, same day, user-directed): all 7 v13-primary audits + 16 RESULT/PREREG/NOTE primaries read from source; **new P32** (#26 Galois-descent theorem chain — unfolded by every master; upgrades M21, answers N8 at the identity level, reduces the cap to identity+purity with the purity citation owed as N31); **new H-5** (the Semaev v4 RESULT vs its same-day audit — M25's H1 leg now DISPUTED); N29 precised; E3 runs certified pre-reg-clean; Part IX added. |
| v13 | 2026-08-21 | Audit-corrected provisional ledger; the gap table this document closes. |
| v12 | 2026-08-18 | Last full master; false reconciliation certificate; addenda unreconciled. |
| v9 | 2026-08-11 | Last pre-consolidation master; source of most v12 grades. |

*No ECDLP, key-recovery, or security claim is made or implied anywhere in this document. The scale
banner of v12 governs every measured row. Grades marked conditional carry their conditions on every
quotation.*
