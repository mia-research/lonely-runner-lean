# AUDIT — the ideation-agent "intersections/frontiers" map, grounded against the corpus + first-hand re-tests (v1)

**Date:** 2026-08-21. **Inputs:** the ideation agent's 9-claim map (session prompt), the full corpus
(graded per `POSITIVE_FINDINGS_MASTER_v14.md`, the controlling master), and a first-hand re-run of the
three cheap-to-test claims (`scratchpad/ideation_claims_firsthand_v1.py`, seed 20260821, exact ints in
the signal path, 3 s runtime; log `scratchpad/ideation_claims_firsthand_v1.log`).

**Headline:** no claim is wholly hallucinated — every one has a repo anchor — but **four of nine are
materially overclaimed or stale**, one repeats *verbatim* the "closing-by-declaration" error that
`CONFIRMED_core_gate_carry_epsilon_zero_v3.md` exists to correct, and the quoted reference file
("Mapping the Curve") **does not exist** in the corpus.

## Claim-by-claim verdict

| # | Ideation claim | Verdict | Grounding |
|---|---|---|---|
| 1 | Census identity `e₂=e₁²−χ₂(−1)p` "proven universally"; rep-theoretic proof "could close" Cap Law | **Stale.** Identity is `PROVED — symbolic, uniform` (P32: Galois descent on `E[2]`, all odd `n`, any cubic); N8 "largely ANSWERED". "Cap Law separation thesis" is not a repo phrase; Cap Law itself is separately `[PROVED — continuum]` (P11). Residues: module split `W⊕W⊗ζ₃` (N9), purity citation (N31) | v14 P32/N8; `cap_law_proofs_v1.md` |
| 2 | k=3 phase channel ∩ `V(a)` split are "the exact same `p mod 4` dichotomy" | **Half proved, half open — stated as fact.** Channel side PROVED (parity lemma: `χ₂(−1)` sets Re/Im component — re-verified first-hand today, incl. the flip at `p=61≡1 mod 4`); `V(a)` split `[VERIFIED]` (M4); "literally one statement" = the repo's OPEN probe | v11 L1259–61; `CONFIRMED_k3_phase_channel_weierstrass_v1.md` |
| 3 | Degree-20 tower ∩ `A_new`; SL₂ monodromy "may halve the 4-dim problem" | **Mixed/stale.** Degree-20 factorization VERIFIED; Galois group of the degree-40 closure UNPINNED (N10, needs Magma); the "2+2 split" is no longer "unidentified" — it is the accepted ½=2/4 account, `[PROVED — ingredients; OPEN on uniformity]` (IV.3). The ★4 monodromy→Newton-slopes lever has **reduced stakes**: N2 was settled by the Cartier route (P23) without it | v14 IV.3, N9/N10; `RESULT_anew_twisted_eigenvalues_nonabelian_v1.md` |
| 4 | Multiplicity-3 ∩ μ₃ through-line "may all originate from a single μ₃-equivariant sheaf" | **Correctly a conjecture — but the prior sheaf attempts are WRONG** (equivariant only at `a=0`; PROJECT_SUMMARY §608). Live positive residue: the forced μ₃-invariant subspace M40 (j=0-specific, on secp, exploitability untested) | v12 L1288–89; M40 |
| 5 | Joint (x,y) shadow at 0.93 = "highest-value lead" | **Stale by two deflations.** 0.93 is real but measures phase-only reconstruction quality of the coordinate geometry — indistinguishable from a random function of `d` (`RESULT_joint_shadow_decompose_v2`); the aligning-key extraction thesis REFUTED at tested scale (powered audit, no sub-cryptographic cost reduction). The honest open object is **N15 joint readout** (single readout carries 1.585 bits; no cheap filter in 8 predictors) | v14 N15; `RESULT_LBE_alignment_key_leakage_audit_v1.md` |
| 6 | D2 Lang-torsor twist bridge open; D1 failed | **Accurate.** D1 closed (non-affinity 0/666, 0/339); D2 open (does `√p·ζ` rigidity survive `L_{χ₂(y)}⊗L_{χ_a}`?); the one executed D2 realization (anti-Frobenius Lang) is a precise negative; next object = sheaf/crystalline | v11 L659–62; `RESULT_D2_lang_antifrobenius_v1.md` |
| 7 | `A_new` supersingular "verified at cryptographic scale"; k=3; non-homomorphic bridge open | **One detail wrong, one closure understated.** Not scale-verification — `PROVED` via Cartier for every `p≡3 mod 4` incl. secp (P23, 2 citation caveats); internal-DLP-easy is FORCED (generic, not secp-special); the transfer class **including non-homomorphic** constructions that recover `d` via dlog in `A_new(F_{p^j})` is CLOSED by the k-tradeoff (group-order gate); `Hom(E,A_new)=0` at secp `[PROVED|P23]` | P23/P13; `ANALYSIS_anew_bridge_n_visibility_v1.md` L158 |
| 8 | Silverman–Stange amicable anchor | **PROVED — and re-proved first-hand today** (Part A below). Repo scope caveat dropped by the ideation: **no ECDLP consequence**; ~1-in-4 CM event ("not miraculous", CLAIMS_LEDGER). "Closed dynamical system / predetermined CM position" is narrative inflation | P24; `RESULT_secp_amicable_pair_v1.md` |
| 9 | Core Gate: `s<3/16` ⇒ "carry transition state guaranteed zero, eliminates lattice rounding boundary noise" | **The exact v1/v2 error v3 retracts.** TRUE for the public coordinate-flap `eps(x)` (re-verified first-hand). FALSE for the scalar carry: the powered pre-registered run had 21–93 gate violations per cell; today's re-run: **1616/3384 gated draws carry `ε=1`** (independence confirmed). `eps==ε_LBE` remains OPEN (N16) but the gate specifically does not supply the carry; the XVI.D route does not de-circularize the arsenal | v3 doc; `RESULT_eps_to_d_constraint_v1/v2` |
| 10 | Reference file "Mapping the Curve" used "verbatim" | **Phantom.** No such document exists; closest is `secp256k1_atlas_findings_v1.md` (feature atlas, 2026-07-09) | — |

## First-hand re-tests (this session, exact arithmetic)

**Part A — amicable pair (Claim 8).** `[n]P=O` over `F_p` (5/5 random points) and `[p]P=O` over `F_n`
(5/5); both claimed orders lie in their Hasse windows; `2·order` excluded from each window by exact
integer comparison (`(2m−field−1)²>4·field`) ⇒ `#E(F_p)=n` and `#E(F_n)=p` **exactly** (order divides
`#E`, prime order of a random point, unique multiple in window). Trace of `E/F_n`: `t=n+1−p=−4324…327`,
`|t|²≤4n` ✓. Verdict: P24 reproduced; it is a proof, not a statistic.

**Part B — the gate's PROVED half (Claim 9).** Torus geometry (N=200,000 exact-integer points):
`Pr[eps=0]=0.7507` (0.75), `Pr[s<3/16]=0.68145` (π√3/8), **0 violations**, max `s` on the
`eps=0` locus 0.24915 (≤¼). Real secp x-coordinates of `[d]G` (N=2000): **0 violations**. Minor
observation (not load-bearing): `Pr[s<3/16]=0.6495` on real x's, ~2.9σ under uniform-equidistribution
at N=2000 — **[RESOLVED 2026-08-21 session (h): my lift-convention bias, not arithmetic — in the
canonical convention the curve-vs-uniform delta at secp is 0.05σ;
see `NOTE_eis_nonequidist_resolved_v1.md`]**.

**Part C — the gate's REFUTED half (Claim 9).** `y²=x³+7` over `F_547` (`#E=547` ✓), GLV eigenvalue
`λ=40 mod 547`. N=5000 two-key draws `(d1,d2,j)`, carry `ε=[d1+d2λ^j≥m]`, sum point x lifted exactly:
gated 3384, **flap violations 0** (theorem holds on the same x's), **carry violations 1616** (48% of
gated — consistent with the repo's independence finding; the repo's 21–93 "per cell" used structured
cells, mine pools draws). Examples on disk in the log. The ideation's "ε=0 guaranteed" is refuted
first-hand at this scope. (Variant note: I used `R=d1+d2λ^j`; the prereg used `d1λ^j+d2λ^j` — by
uniformity of `d1` the distributions match; refutation is variant-independent.)

**Part D — phase channel + `p mod 4` (Claim 2).** `R` reproduced to the digit: CM p=547 → 0.2886
(doc 0.289); CM p=43 → 0.4413 (0.441); non-CM p=43 → 0.3360 (0.336). Parity residual
`max|T(−b)−conj T(b)| ≤ 5e−14` (float noise). The dichotomy flips exactly per the parity lemma:
p≡3 mod 4 → `mean_all` real, χ₂-channel purely imaginary; p=61≡1 mod 4 (CM, prime order) →
`mean_QR` real to machine zero, channel purely real (`0.4449+0i`). The channel half of the claimed
"unification" is proved structure; whether `V(a)`'s M4 split is the *same* statement remains the open probe.

## The ideation's closing question, answered

"Explore the 2+2 eigenvalue-splitting machinery required to build the geometric gate that bypasses the
0.93 shadow" — **blocked three ways, each independently documented in the corpus**: (a) 0.93 is generic
reconstruction quality, not a d-specific leak; (b) the only gate in hand (`s<3/16`) provably does not
touch the d-carry (Part C today); (c) the `A_new` transfer class incl. non-homomorphic dlog bridges is
closed by the k-tradeoff. The 2+2 split itself is real but already structurally accounted (½=2/4) —
its live residue is uniformity/purity (N31) and the a-family monodromy, neither of which is a "gate."

## What is actually live (per v14 §VI do-not-close + this audit)

N15 joint readout (the load-bearing open cryptographic question) · D2 twist bridge (Claim 6, accurate) ·
N7 sub-Rayleigh mechanism (row-budget shadow M36) · N9 `W`-piece · N10 Galois group (Magma) ·
N16 `eps==ε_LBE` + the `build.eps` cross-check · E3 blind subspaces (triples, band-localized,
orientation-odd) · N31 purity citation · P32's owed isolated re-run · flap class-number step (†).
