# AUDIT — two "closed/null" results re-graded (joint-readout null; two-key/KS backstop)

**Date:** 2026-08-14. **Trigger:** distrust-the-nulls pass under the one-way suppression bias
(`feedback_suppression_bias_asymmetric`). Traced items, not summary tags. Neither audit found a leak;
both found "closed/proved" carrying more weight than the work under it (closure-direction overclaim).
Scripts are decidable artifacts, all exact-int signal path; MI is a monotone stat vs permutation/G-test null.

---

## Finding 1 — `RESULT_t2c_joint_readout_dmod3_BLINDED_v1.md`: null not properly earned; buried positive = fluke

**Method gap (object-level):**
- Joint MI on secp used |F|=324 cells over N=82 → Miller-Madow-crushed to ≈ −2.8 bits; the C1 **plant does
  not fire on secp (z=0.62)**. A powerless global test returning "not detected" is *no measurement*, not a null.
- The **single-feature** MIs — the only powered quantities at N=82 — were reported as bare numbers with
  **no null** (protocol §8). Information left on the table by construction.

**The omitted null, run** (`AUDIT_secp_singlefeature_null_v1.py`, permutation R=50000, all 6×4 feature/target):
one positive **survives Holm over all 24 tests**:
```
χ2(y) → d mod 5 :  MI = 0.171 bits,  perm-p = 0.0010,  z = +5.16   (Holm-24 survivor)
```
χ2(y) = QR-bit of the y-coordinate — the one y-dependent feature, structurally outside the "public
function of x is redundant with Q" argument the whole null rested on.

**Matched high-power control kills it** (`AUDIT_chi2y_dmod5_bothsets_v2.py`, constructed known-generator
set = same select-bitlen→curve pipeline, range-structured keys):
```
CONSTRUCTED N=20,000 :  χ2(y)→d mod 5:  MI=1.8e-4,  p=0.30   (null)
CONSTRUCTED N=100,000:  χ2(y)→d mod 5:  MI=1.5e-5,  p=0.73   (null; contingency flat 0.198–0.202)
```
**Verdict:** the secp-82 hit is a small-sample artifact of those 82 historical keys; Holm-24 survival at
N=82 did not protect against it. The **properly-earned** null is the matched 100k one (POWER: resolves
MI≳1e-4; SCOPE: χ2(y), d mod 5, range-structured keys). The original "null across the board on secp" was
not earned (powerless joint + un-null'd singles); it happens to hold, re-established here correctly.

---

## Finding 2 — `RESULT_joint_carry_twokey_mi_v1.md` / `bilinear_closure_proof_v1.md`: not the theorem it was filed as

**Object-level (decidable):** Theorem B / Cor B1 / Cor B2 require readouts `A = e_p(f)`, `f` a
nonconstant **rational function on E of bounded degree** — the sole class for which the cited KS bound
`max_k|Â(k)| = O(√p·polylog)` is asserted. The two-key test's features were `A,B = b_eps(x)`, and in
`int1_frame_operator_v1.py`:
```
c1 = rdiv(X·R2[1], DET)          # rdiv = round(): Babai / CVP nearest-lattice step
eis(X) = X − (c1·R1 + c2·R2)     # piecewise-constant lattice residual — NOT e_p(rational f)
eps(X) = threshold of eis(X), eis(βX) against the reduced basis  ∈ {0,1,2}
```
`eps` is a lattice-reduction step function; the rounding is non-algebraic. **Cor B2 does not cover the
features the two-key null used.** The result also mis-cited B1 (coord–coord) for the B2 (coord–carry) object.

**Thesis tested separately (`AUDIT_ks_covers_eps_fourier_v1.py`), and it survives:**
```
 p    max|ε̂|/√p (eps)   max|Â|/√p (harmonic e_p(x+y))
547        1.39                2.36
907        1.35                2.88
1303       1.17                2.96
1669       1.16                3.28
2089       1.31                2.55
 fitted exponent α:  eps 0.405   harmonic 0.618   (KS bound ⇒ 0.5; read the BOUNDED RATIO, not the 5-pt α)
```
eps empirically obeys the √p square-root-cancellation (ratio bounded ~1.2–1.4, non-growing) — *tighter*
than the genuine harmonic. So the eps two-point correlations really are O(p^−1/2); **the null is not wrong.**

**Re-grade:**
- Claimed: `[VERIFIED-scope NULL]`, bounded by Cor B1 `[PROVED given KS]`, coupling ≤ 2⁻¹²⁸.
- Actual: **`[EMPIRICAL scope NULL]`.** MI_min ≈ 2⁻¹⁰ on powered constructed arms (2⁻³ on real-82). The
  extension to the 2⁻¹²⁸ floor rests on an **unproven** (empirically-supported, α≈0.4) equidistribution
  bound for the Babai-lift readout — which the cited theorem does **not** supply. The `[2⁻¹⁰, 2⁻¹²⁸]` band
  is empirically-consistent-with-null but **not proved-null** for these features.
- Secondary (CORRECTED 2026-08-14): KS-for-`e_p(rational f)` **is source-verified** — the earlier
  "never verified" was a conflation with the failed *Lemmermeyer* citation-verifier run. See
  `secp_ks_bound_verified_2026_07_17` (memory) + the 2026-08-14 `citation-verifier` pass below:
  `|Â(k)| ≤ 4√p+1`, uniform, no polylog. The owed gate is NOT "verify KS"; it is the lift-step theorem
  for `eps` (below).

The bilinear-closure doc's purpose ("replace the empirical nulls with a theorem") **was not achieved for
the eps-flap features** — the theorem does not reach them; for those readouts it remains an empirical null.

---

## Owed / open
- **`citation-verifier` on KS/Lange–Shparlinski — DONE 2026-08-14, from primary sources on disk**
  (`kohel_shparlinski_ants4_2000.pdf` SHA-256 `645d9022…d8d2a`; `lange_shparlinski_jmc_2007.pdf`
  SHA-256 `f29c524a…c6edec`; hashes independently re-verified). Verdicts:
  - **e_p(rational f) readouts: SUPPORTS** — KS 2000 Thm 1 + bound (3) give `|Â(k)| ≤ 2·deg(f)·√p`
    (single-pole: `(1+deg f)√p`), uniform in `k` and in the coefficients of `f`; `Â(k)=S(ω_k,e_p,f)`
    identically for prime-order `⟨G⟩`. **Stronger than the doc claims — the `(log p)^{O(1)}` is
    spurious** (it belongs to KS's *interval-distribution* Thm 2, not the raw sum). Direction safe (M is
    an upper bound). Pole-order-≤3 for `bx+cy` correct.
  - **non-rational (Babai/CVP/step) readouts — e.g. `eps`: DOES-NOT-SUPPORT.** Both theorems require
    `A=e_p(rational f)` (proof runs through Artin–Schreier / L-function / RH-for-function-fields). A CVP
    step function is outside the hypothesis. Confirms Finding 2's object-level result **independently.**
  - Also flagged: Theorem B/B1/B3 are correctly *typed* to `e_p(rational f)`, but the doc's **summary
    prose** ("every such readout", "no such handle exists", `:48`,`:78-81`) over-generalizes to arbitrary
    bounded/CVP readouts — a prose-level hypothesis-drop. Narrow it, or add "…factors with Wiener norm
    `O(polylog)`" (as Cor B2 in fact does for the carry).
- **Named path to genuinely close the eps channel** (now literature-named, NOT a wall): either (i) express
  `eps` as an **interval-of-value indicator of a rational function** ⇒ KS Thm 2 / LS Thm 4.2 (Erdős–Turán +
  the character bound) close it with an extra `log p`; or (ii) bound `eps`'s **Wiener/ℓ¹ norm** directly.
  Until one is done the two-key null stays `[EMPIRICAL]` for eps features (empirically α≈0.4, so the bound
  is expected to hold — this is a proof gap, not a suspected leak).
- The other buried single-feature tables (`eps_to_d` 31-map, single-key fiber) not yet re-null'd feature-wise.
