> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# POSITIVE FINDINGS MASTER — v16 (delta successor to v15: external-report audit folded — ζ₃ point-count witness + p mod 4 split, half-Weil cap scope-pinned, deficit b=0 source located, extraction-claim nulls)

**Date:** 2026-08-25
**Author:** Claude (Opus 4.8), auditing the 20 external-agent reports in `~/Downloads` (oldest→newest),
per user direction (test each method AND idea; keep the real, drop the language).
**Predecessor:** `POSITIVE_FINDINGS_MASTER_v15.md`.
**Source of record for this pass:** `POSITIVE_FINDINGS_ADDENDUM_4_v1.md` (2026-08-25) + scripts
`audit_external_reports_v1_scripts/` (21 files). Every number below is rerunnable from there.

**What v16 is.** A **delta successor**, not a rewrite. **All of v15 (and thereby v14) is carried
forward verbatim by reference; anything not updated below is unchanged** (compile rule, Editorial Law 6).
v16 folds one audit (`ADDENDUM_4`) and updates only the rows / do-not-close items it touches, each with a
named artifact in the same edit (grade-up rule). No v15 open item, retraction, or caveat is deleted.

**The folds, up front:**
1. **N32 (new) — the ζ₃/120° eigenvalue lock on A_new is confirmed by direct point-count** for non-CM
   p≡1 mod 4 (independent, finite-prime witness of the L-mono GKR result), AND a **new p mod 4 regime
   split** is recorded: ζ₃-pairing (ordinary, p≡1) vs √p·ζ₆ superspecial (p≡3). **This is a
   within-fiber witness — it does NOT address the horizontal a-family monodromy #28** (do-not-close #2
   stays open, object unchanged).
2. **N33 (new) — the half-Weil cap |V(a)|≤2√p is scope-pinned:** VERIFIED for prime-order non-CM curves
   (0/317, max 1.996), FAILS for composite-order (max 2.82). Attaches to the cap items (#6/#7);
   empirical, **citation N31 still owed** (not discharged).
3. **N34 (new) — the b=0 (y-only) sub-Rayleigh deficit magnitude is located as a wrong-null effect**
   (negation-parity realness); a matched ±-antisymmetry control leaves residual z<1.6 over 6 primes.
   **Frontier #15 is UNCHANGED** — this touches only the b=0 slice, not the full-2D ~0.1%
   Hermitian-null deficit of `RESULT_subrayleigh_deficit_scaling_v1`, which stands.
4. **N35 (new) — row-budget M₄ excess reproduced, universal (CM≈non-CM), scale-crossover;** linear-shear
   M₄ exactly invariant, nonlinear-shear breaks it with L² preserved.
5. **N36 (new) — two exact structural facts:** CM 3-orbit collapse to a cyclic **C₅** number field
   (disc a perfect square) and parity-protected Kummer descent splitting [1²³].
6. **N37 (new) — the external reports' key-extraction payoff is a set of scoped nulls:** d mod {2,3,6}
   from a public key measures **0.00 bits** on real secp keys; the "island-sieve" is an algebraic
   identity; secp E is ordinary with embedding degree ≈1.9×10⁷⁶ and A_new (the pairing-soft object) is
   the complement of E with no constructed transfer. **Graded EMPIRICAL/NULL with scope — not closures**
   (folder CLAUDE.md burden-of-proof-on-closure honored; each names the exact construction it bounds).
7. **N38 (new) — additional verified facts, carried explicitly so nothing graded is dropped:**
   formal-parameter exact linearity (z→βz all orders) `[EXACT]`; Weil pairing embedding-degree-2 at
   p=11 `[VERIFIED]`; Puzzle-140 public-substrate check `[EXACT]`; amicable-pair E3 null `[NULL]`.
8. **Reproductions (no row change):** Semaev β-orbit collinearity 100%/0% (= M26/#4, v15); Jacobi
   J=−p (= ADDENDUM_2 Frontier 15); Cartier vanishing p≡3 mod 4 (supports the A_new premise).

**Standing-asymmetry note (Editorial Law 7).** This pass is dominated by cross-checks of existing
frontiers (N32/N33 reinforce ζ₃-rigidity and the cap) plus scoped nulls on the external reports'
crypto claims (N37). Direction audit: the positives are recorded at grade, not shrunk; the nulls are
scoped to the exact constructions tested, not generalized to the avenue. **Two methodology
self-corrections are logged** (per `ADDENDUM_4`, provenance-preserving): (i) a prior in-session draft
compressed several positives with shrink-words ("trivial / forced / small / textbook"); each is
re-graded to object+power+scope in `ADDENDUM_4` (§A1, A3, B2, C1–C4) — a suppression-direction
correction, not a deletion. (ii) N34's residual, first quoted as a single-prime point estimate, is
superseded by the matched-control result (z<1.6 over 6 primes, consistent with 0); the point estimate
is not carried as a finding.

---

## Part 0 — Sources consumed this pass (added to v15 §0 / v14 §0.1)

| # | File | Extent |
|---|---|---|
| A | `POSITIVE_FINDINGS_ADDENDUM_4_v1.md` (this session's source of record) | full |
| B | 20 external-agent reports, `~/Downloads` batch (hypergeometric-formal-group, verify-d2-bisection, galois-tower-interferometry, cartier-manin-vanishing, weil-pairing-torsion-embedding [+dup], farey-coprimality-filament-p140-v2, dirichlet-island-sieve-verify, oblique-shear-splitting, verify-hecke-factorization-p1831, verify-hasse-davenport-reduction, y_deficit_scaling, row_budget_analysis, non_cm_row_budget_analysis, amicable_reference_beam_audit, amicable_y_deficit_report, amicable_m4_oscillations_report, oblique_shear_m4_invariance, nonlinear_shear_m4_report, verify-p1-spectral-cap) | read + tested |
| C | `audit_external_reports_v1_scripts/` (21 verification scripts) | code |

---

## Part I — Row updates / new rows (each with its artifact)

### N32 (new) — ζ₃/120° eigenvalue lock on A_new: point-count witness + p mod 4 regime split. `[VERIFIED — exact, point-counted]`
*Artifact: `ADDENDUM_4 §A1`; script `audit_phaselock.py`.*
Point-counted C: w⁴=x³+Ax+B over F_p, F_{p²}, F_{p³}; extracted A_new's 4 Frobenius eigenvalues.
- **non-CM, p≡1 mod 4** (p=13,29,37): the two conjugate eigenvalue-pairs are **120.0° apart** (ζ₃),
  on curves with no CM — cover-borne rigidity.
- **p≡3 mod 4** (p=11,23,43): eigenvalues on the **√p·ζ₆ / imaginary-axis lattice** (superspecial).
Independent finite-prime witness of the L-mono GKR analytic result (`RESULT_lmono_gkr_*`,
det(W_a)=ζ₆·p a-constant). **Scope discipline:** this is a **within-fiber** eigenvalue fact; it does
**NOT** touch the horizontal a-family monodromy (#28) — that object is the distribution of c₃(a) across
a, unaddressed here (see do-not-close #2). The external sources' "universal 120° law" over-generalized;
the p mod 4 split is the correction.

### N33 (new) — half-Weil cap |V(a)|≤2√p: scope-pinned. `[VERIFIED — empirical; prime-order scope]`
*Artifact: `ADDENDUM_4 §A2`; scripts `d20_capsweep.py`, `d20b_primeorder.py`, `d18_shears_cap.py`.*
V(a)=Σ_d χ₂(y_d)·e_n(ad). **Prime-order** non-CM curves (p≲180, all A,B): **0/317 violations, max
1.996.** **Composite-order** curves violate, up to **2.824** (p=193). The source's 13-curve prime-order
table reproduces exactly (p=113 → 1.9960). Consequence of N32's ζ₃ lock (half the 4√p A_new ceiling).
Attaches to do-not-close #6/#7 (cap/purity): **empirical reconfirmation + scope-pin; the analytic/cited
proof (N31) remains owed — not discharged.**

### N34 (new) — b=0 sub-Rayleigh deficit magnitude located: negation-parity realness (wrong-null). `[CHARACTERIZATION — matched-control]`
*Artifact: `ADDENDUM_4 §B1`; scripts `d12b_control.py`, `audit_deficit.py`.*
On the b=0 (y-only) line, U(1,0,c) is **exactly real** (max|Im|≈6×10⁻¹³) because y_{n−d}=−y_d. The
source's −9%…−18% "deficit" / +12%…+27% "low-tail excess" are measured against an **arbitrary-permutation**
null (COMPLEX sums) — real-vs-Rayleigh mismatch. Against a **±-antisymmetry-preserving** control the
low-tail excess vanishes (40.4% vs 40.7% @p=163) and the residual is **z∈[−0.76,+1.58] over 6 primes
(K=300), consistent with 0.**
**Reconciliation — Frontier #15 UNCHANGED:** this is the b=0 slice with a ±-antisymmetry null; it
re-confirms the wrong-null lesson (`RETROSPECTIVE_FINDING_01`) on the source's specific numbers. It does
**not** touch `RESULT_subrayleigh_deficit_scaling_v1` (full 2-D U(a,b,c), Hermitian-symmetric matched
null, ~0.1% surviving across 30 primes), which stands.

### N35 (new) — row-budget M₄: universal crossover; shear behavior. `[VERIFIED — matched-shuffle control]`
*Artifact: `ADDENDUM_4 §B2–B4`; scripts `d13c.py`, `d18_shears_cap.py`.*
Σₐ|U(a,b,c)|²=n(n−1) exact (P30, machine precision). M₄ excess vs coordinate-shuffle null: −0.79%
(p=43) → +0.23% (p=163), T≈+3.3 @163; **CM +0.23% vs non-CM +0.24%** (universal, parity-driven,
magnitude ~0.2%, statistically nonzero). Total M₄ exactly invariant under linear shear x→x+sy (reldiff
0.0); nonlinear shear x→x+sy² changes M₄ (+1.37/+1.82/+0.91%) with Σₐ|U|²=n(n−1) kept to 10⁻¹².
(Object is a whole-group sum; no per-key secret — characterization, not a channel.)

### N36 (new) — two exact structural facts. `[VERIFIED — exact]`
*Artifact: `ADDENDUM_4 §C2–C3`; scripts `d03_galois.py`, `d03b_gal.py`, `d09_splitting.py`.*
- CM 3-orbit collapse (p=43, x³+7): 15 squared twisted sums → 5 roots (mult 3); Q₅ =
  T⁵+155T⁴+6138T³+92070T²+555861T+1060975; disc = 56858430668800² (perfect square); Galois group **C₅**
  (galois_group + Chebotarev: only (1⁵),(5)).
- Parity-protected Kummer descent (E′:x³+x+3/F₄₃, n=47): odd-parity coordinate → complete splitting
  [1²³] at ℓ=281,283; mixed-parity shear → 1/23 at ℓ=281.

### N37 (new) — the external reports' key-extraction claims: scoped nulls. `[EMPIRICAL/NULL — construction-scoped]`
*Artifact: `ADDENDUM_4 §D1–D3`; scripts `idea_dmod6.py`, `idea_dmod6b.py`, `d02_bisection.py`, `d05_weil.py`.*
Per the folder's burden-of-proof-on-closure rule, each null names the exact construction it bounds and
does NOT claim the avenue is dead:
- **d mod {2,3,6} from public key = 0.00 bits.** χ₃(x_P)→d mod 3, y-parity→d mod 2, joint→d mod 6:
  mutual information at the permutation-null floor (z<1), full-range AND 2¹³⁴–2¹³⁵ (Puzzle-135), N=6000.
  The "2.585-bit reduction" would need MI≈2.585 bits; measured ≤0.006. **Bounds the χ₃/y-parity/Core-Gate
  channel as specified.**
- **"D2 island-sieve/bisection" = algebraic identity:** reconstruction returns d from d0 where d0 was
  defined as d·λʲ mod n; recovering d0 from the public point φʲ(P) is itself ECDLP.
- **secp is not the pairing-soft object:** E ordinary (trace≢0 mod p); embedding degree ord_n(p)
  ≈1.9×10⁷⁶. The supersingular embedding-degree-2 property is A_new's / the auxiliary E'/F_{p²}'s;
  A_new is the NEW part (complement of E in Jac(C), dim 2 vs 1); the "non-homomorphic transfer bridge"
  is named, not constructed.

### N38 (new) — additional verified facts folded from ADDENDUM_4 (§C1, C4, C5, B5). `[grades per item]`
*Artifacts: `ADDENDUM_4 §C1, C4, C5, B5`; scripts `d01_formalgroup.py`, `d01b_truelog.py`, `d05_weil.py`, `d07_farey.py`, `d17_amicable.py`.*
(Carried explicitly so no graded ADDENDUM_4 finding is dropped in the fold — the project's dominant
failure mode is selective omission under a false completeness certificate, v14 Part VII.2.)
- **C1-positive `[EXACT]`:** the GLV order-3 automorphism (x,y)→(βx,y) acts as z→βz at **all orders**
  on z=−x/y; L(βz)=βL(z) (β⁶=1); the series Σ Bʲ·C(3j,j)/(6j+1)·z^{6j+1} is the true formal-group log
  (coeffs 1, 3B/7, 15B²/13, …).
- **C4 `[VERIFIED — p=11]`:** Weil pairing on E′: y²=x³+1 / F_{11²} — order 144=(p+1)², e₁₂ a
  primitive 12th root, bilinear + alternating, embedding degree 2. This is the auxiliary supersingular
  object of N37/D3: the embedding-degree-2 property is A_new's / E'/F_{p²}'s, **not** E's.
- **C5 `[EXACT]`:** Puzzle-140 pubkey satisfies y²=x³+7 mod p; p = a²−ab+b² with the report's
  Eisenstein basis (public-substrate check; no per-key consequence).
- **B5 `[NULL — matched]`:** amicable-pair E3 cubic-character cross-match at the noise floor (33.17% vs
  33.33%); of the four amicable M₄ cells only CM E₂ is significant (+0.56%, T=+2.6), single curve per
  cell, contradicted as a "CM-accelerates" law by N35's universal crossover.

### Reproductions (no row change)
- **M26 / do-not-close #4** — Semaev β-orbit collinearity reproduced 100% (CM, F₆₇) / 0% (non-CM);
  consistent with v15's CM-affirming resolution. *(`ADDENDUM_4 §A3`.)*
- **ADDENDUM_2 Frontier 15** — Jacobi sign law J(χ₃,χ₄)=−p reproduced exactly (=−43); Φ₁₂ splits as
  recorded. *(`ADDENDUM_4 §A5`.)*
- **A_new premise** — Cartier–Manin block = 0 for all p≡3 mod 4 tested (12 primes × 3 curves).
  *(`ADDENDUM_4 §A4`.)*
- **Source error logged** — the hypergeometric report's inline series "3B z⁷ + 40B² z¹³" drops
  denominators; true coeffs 3B/7, 15B²/13 (the Σ-formula itself is correct). *(`ADDENDUM_4 §C1`.)*

---

## Part II — Do-Not-Close list updates (v15 §II / v14 §VI)

- **#2 (a-family monodromy #28) — UNCHANGED, still OPEN.** N32 is a *within-fiber* eigenvalue witness
  (per-curve ζ₃ pairing / superspecial split); the horizontal family monodromy — the distribution of
  c₃(a) across a — is untouched. The v15 statement of #28's object stands; correct next probe is still
  the pre-registered discrete-vs-Sato–Tate test of c₃(a).
- **#6/#7 (cap / purity) — cap EMPIRICALLY RECONFIRMED + SCOPE-PINNED (prime-order), citation STILL
  OWED.** N33 pins |V|≤2√p to prime-order (0/317) and records composite-order failure; it does not
  supply N31's owed citation. Item stays open on the citation.
- **#4 (Semaev H2) — reproduced, unchanged** (discharged v15; N-row reproduction only).
- **#1, #3, #5, #8, #9, #10–#16 — carried forward from v15 unchanged.**
- **Frontier #15 (sub-Rayleigh deficit) — UNCHANGED.** N34 locates the b=0-slice inflation as a
  wrong-null effect; the full-2D ~0.1% Hermitian-null deficit stands as recorded.

---

## Part III — Everything else

All v15 Parts (and thereby all v14 Parts: ledger P1–P32 / M1–M40 / N1–N31 except the rows/items above,
corrections, addendum reconciliations, conflicts, post-v12 states, loss inventory, Editorial Law,
certification table) are **carried forward verbatim.** The v14 scale banner and all conditional grades
govern every quotation. **No ECDLP, key-recovery, or 256-bit claim is made anywhere;** the new items are
model-scale structure (N32/N33/N36), a characterization (N34/N35), or construction-scoped nulls (N37)
that explicitly do not transfer to the cryptographic prime.

## Version History (appended to v15's)

| Version | Date | Notes |
|---|---|---|
| v16 | 2026-08-25 | Delta successor: folded `ADDENDUM_4` (audit of 20 external-agent reports). New rows N32 (ζ₃ point-count witness + p mod 4 split; within-fiber, #28 untouched), N33 (half-Weil cap prime-order 0/317, composite fails; citation still owed), N34 (b=0 deficit = wrong-null, Frontier #15 unchanged), N35 (M₄ universal crossover + shear behavior), N36 (C₅ collapse + parity splitting), N37 (extraction-claim scoped nulls: d mod 6 = 0.00 bits, sieve = identity, secp ordinary/embedding ≈1.9e76), N38 (formal-parameter linearity, Weil pairing p=11, Puzzle-140 substrate, amicable E3 null). Reproductions: Semaev (#4), Jacobi (F15), Cartier. compile-diff gate run (v15+ADDENDUM_4→v16); 6 flagged losses fixed (unsourced −3.7% removed, language-shrink note added, C1-positive/C4/C5/B5 carried as N38). All model-scale / null; no key-recovery claim. |
| v15 | 2026-08-24 | Delta successor: H-5 resolved (cofactor/sampling artifact; #E-leak refuted); H2 resolved (M26 CM-specific, GLV relation-triples); N16 folded; N7-monodromy gate (#28 sharpened, category error named). |
| v14 | 2026-08-21 | Full corpus revision + results-level certification (P32, H-5 seam opened). |
