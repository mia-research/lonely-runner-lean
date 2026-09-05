# New Insights Review — BTC / secp256k1 thread

**Date:** 2026-07-30
**Scope:** New findings since the consolidated master compendium (`PROJECT_SUMMARY_secp256k1_v1.md`, 2026-07-28; and the `POSITIVE_FINDINGS_MASTER_v4` → `ADDENDUM_1` → `ADDENDUM_2` lineage). This is a *findings* review — the structural reading it motivates is written up separately in `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md`.
**Register:** Purist number-theoretic. Lens-driven (thermodynamic / variational) observations are confined to one clearly-labelled conjectural aside, never imposed on the math.
**State in one sentence:** the cap-via-relative-rigidity programme has been reduced to a single structural gap; the same week produced one real number-theoretic consolidation, a run of positive-looking empirical cells that all died out-of-sample, one important control correction (retracting *power*, not signal), and a chronic citation/gate debt that is now load-bearing.

---

## 1. The headline new result: the characteristic-polynomial collapse

`ANALYSIS_n1_charpoly_collapse_v1.md` (Jul 30), with the `V₂` derivations in `RESULT_theta_structure_v1.md` and `RESULT_semicircle_null_and_verification_v1.md`.

The twisted L-polynomial of `A_new` has four roots $\{\alpha,\ \alpha\zeta_3,\ -\bar\alpha,\ -\bar\alpha\bar\zeta_3\}$ (with $|\alpha|=\sqrt{p}$). Three items previously recorded as *separate* collapse to **one polynomial identity**:

$$e_2(a)=e_1(a)^2+p \quad\Longleftrightarrow\quad V_2=V_1^2+2p \quad\Longleftrightarrow\quad \alpha_2/\alpha_1=\zeta_3\ (\text{the 120° law}).$$

- The closure $\alpha\mapsto -\bar\alpha$ is **forced** ($|\alpha|^2=p \Rightarrow \bar\alpha=p/\alpha$), which forces $e_3=\chi_2(-1)\,p\,e_1$ and $e_4=p^2$. So the twisted char poly has **exactly two free coefficients**, $e_1$ and $e_2$.
- The sign of $V_2=V_1^2\pm 2p$ is **resolved to $+2p$** (across 30+ orders of magnitude at 160-bit; residuals $\sim 10^{-43}$).
- **The cap chain now has one open link, not two:** $e_2=e_1^2+p \Rightarrow V_2=V_1^2+2p \Rightarrow S_y\le 2 \Rightarrow |V|\le 2\sqrt{p}$.
- Methodological corollary: the record's proposed "decisive ideal test" (measure $(\alpha_1),(\alpha_2)$ as ideals) is **un-runnable** — $120° \Rightarrow \alpha_2/\alpha_1=\zeta_3 \Rightarrow$ a unit $\Rightarrow (\alpha_1)=(\alpha_2)$ identically; the outcome is fixed before the test runs.

**Grade / caveats.** `[DERIVED + VERIFIED — exact, every frequency, p=43,67,127]`. The *derivation* is general (assumes only the proved closure); the *verification* is exact-integer at three small primes and confirms 120° at the eigenvalue level by a route independent of the existing $g=\deg\gcd$ route. It does **not** prove the cap, and the file states that "no finite sweep can" prove uniformity. The remaining target is the single identity $e_2(a)=e_1(a)^2+p$ for all $a$, all $p\equiv 7\bmod 12$ — a sharper, smaller object than "the ratio of eigenvalue pairs is a cube root of unity," and exactly the object the Kronecker/Stickelberger route factorizes. This regrades open frontier #26 (uniform $u=\zeta_3$ via geometric monodromy): still the sole gap, now expressed as a coefficient identity.

---

## 2. The N1 saturation anomaly: mechanism accounted, numeric residual not reportable

`RESULT_n1_saturation_residual_v1.md` splits the one "measured anomaly with no account" (saturation $\max_a|V(a)|/(4\sqrt{p})\approx 0.470$ vs $0.876$ for the same-dimension additive channel):

- **Mechanism half — accounted, `[PROVED-exact]`.** $\tfrac12=\tfrac24$. The 120° lock gives $|1+\zeta_3|=1$ exactly $\Rightarrow$ only 2 of 4 eigenvalues carry independent weight $\Rightarrow$ ceiling $2\sqrt{p}$ = $\tfrac12$ of $4\sqrt{p}$. The 1.86× gap is precisely $0.876/0.470$.
- **Numeric half ($0.470\to\tfrac12$ shortfall) — claimed finite-size artifact, flagged weak.** With $u=V/(2i\sqrt{p})$, $\max|u|$ is the max of $L=(n-1)/6$ draws from the semicircle marginal; predicted edge $1-\max|u|\sim c\,L^{-2/3}$. Null slope $-0.663$ vs prediction $-0.667$ (good), but the **data** slope $-0.807$ is explicitly "not robust" (min-type statistic, large scatter), and the 34-prime set **contains** the 17 discovery primes. The pooled-$z$ residual $+2.20$ is explicitly **not reportable** (re-uses the discovery sample).

Net: the *ceiling* is explained; the *shortfall-to-ceiling* remains open with no clean number yet. (This makes `MASTER_v4`'s "N1 OPEN" status stale — it predates this answer.)

---

## 3. Positive-looking empirical cells — all killed by control or out-of-sample

The most important *negative* pattern of the batch: several cells looked signal-bearing and **did not survive**. Tally of "chance patterns killed by the pre-committed OOS rule":

| Cell | Looked positive | Outcome | File |
|---|---|---|---|
| $S_3^{\max}$ tail statistic | 14/17 primes, pooled $+2.06$ | **Dead** OOS on 15 fresh primes ($+0.30$) | `RESULT_semicircle_null_and_verification_v1.md` |
| Chirp cell $k=t$ @ $p=2731$ | 98.8th pctile | **Dead** OOS on 12 primes (0 above 95th) | `RESULT_chirp_hologram_plane_v1.md` |
| Multiplicativity @ $p=2731$ | hit | **Dead twice** (OOS min perm-p $0.082$; fails to reproduce at its *own* prime, perm-p $0.295$) | `RESULT_theta_structure_v1.md` |
| Phase families (Q/C/I/M) | — | All **NULL** at $p=823,1303$ | `RESULT_phase_family_and_tail_v1.md` |
| Arrangement corr. $a^{-1},a^3$ | pooled $+1.48,+0.06$ | **NULL**, nothing $|z|\ge 2$ over 9 primes | `RESULT_large_p_and_arrangement_v1.md` |

Two **positive characterizations** survive, but are explicitly *re-presentations of known theorems, not new laws*:

- **The $k=0$ dark fringe.** The $k=0$ line (the record's entire twist-orbit programme, since $H(0,a)=V(-a)$) is the **darkest line in the chirp plane at every prime** (0.00 pctile). It is the proved cap "made visible as a dark fringe." Persists up to $p=8191$.
- **The spectral-decomp SVD** (`RESULT_spectral_decomp_v1.md` — the *only* file in this batch that ran a frozen `experiment-designer` prereg): $E3=\tfrac14|\mathbf{1}^\top C\mathbf{1}|^2$ is exactly the all-ones projection of the $82\times 82$ cubic-character matrix. **Destructive-interference hypothesis not supported** at this resolution; the diffset avenue on this surface is bounded at the spectral level.

---

## 4. The $\mu_3$ difference-set correction — what was wrong, what stands

The most consequential *integrity* event of the batch (`CORRECTION_v32_mu3_diffset_controls_v2.md`, supersedes `_v1`, Jul 30). Be precise about the object distinction — the correction turns on it:

- **Field-difference set** $\{x_i-x_j\}$, statistic $E3$ (`RESULT_diffset_cubic_cmvanishing_v1.md`): **stands.** secp $E3=13125$ (98.4th pctile, $p\approx 0.033$), but on the non-CM curve $E'$ it drops to $3711$ (67th pctile, $p\approx 0.660$). Characterization: a **CM/j=0 fingerprint via the endomorphism $(x,y)\mapsto(\omega x,y)$, not a $d$-fingerprint.** Not Bonferroni-significant at family level; not a security verdict.
- **Group-law difference multiset** $\{P_i-P_j\}$, statistic $M3$ (the v32 cell): **the controls were invalid.**
  - C1 ("GLV-triple control correctly does NOT fire") was **false**: the GLV-triple set is $\hat\lambda$-closed $\Rightarrow$ the difference multiset is $\hat\lambda$-closed $\Rightarrow \chi_3(\beta)$ primitive $\Rightarrow M3=(0,0)$ **exactly** for *every* $\hat\lambda$-closed set (exact `Counter` equality, support 1770/1770). The residual $0.17$ reading in v32 came from pair subsampling breaking orbit completeness. The control was algebraically forced to zero — an instrument assertion, not a control.
  - C2 ("AP control fires hard — detector validated") was **misattributed**: the AP firing is fully accounted for by point *multiplicity* (weight multiset $w_j=160-j$), confirmed by a multiplicity-preserving surrogate (rank $0.364$, INSIDE).
  - C4: the $x$ and $xy$ cells were **never independent** — on $y^2=x^3+7$, $\chi_3(xy)$ is a function of $x$ alone (verified 144/144).

**Net consequence:** the $\mu_3$ diffset cell of v32 had **zero working controls** — one forced to 0, one firing for an unrelated reason. **Crucially, no *signal* claim is retracted and no *number* is retracted — only the *power* attached to them.** The real-82 and constructed-36k sets are not $\hat\lambda$-closed, so their own $M3$ values were legitimate measurements; the channel is **un-probed, not null.**

**The repair** (`RESULT_mu3_diffset_control_repair_v1.md`): Cell A (real-82) now carries a powered, bounded result — **no cubic-class concentration above $\varepsilon=0.0415$** at 80% power, firing control firing 1.00. **Not a closure** (joint/triangle structure, $\mu_6$ $(1,1)$ component, band-localized concentration, sub-$\varepsilon_{80}$ effects all listed as blind subspaces). Cell B (constructed-160) is **void** — the run script reused the *same* `drawB` function on the *same* RNG stream for both the null and the studied set, so the studied draw is a sample from its own null; no hypothesis, no conclusion.

Same-day register: `CORRECTION_v10_lever_enumeration_v1.md` corrects **only the Framing paragraph** of v10 (an unproven exhaustive enumeration stated as a premise; a moved quantifier turning "we found two bounded levers" into "all levers are bounded"). **v10's measured results stand.**

---

## 5. The Jacobi $m$-law reduction — adversarially confirmed, still conditional

`RESULT_star_adversarial_review_v1.md` is an **isolated** review (subagent given only the statement $(\star)$, two helper facts, three file regions — no session narrative). Verdict:

$$S=\chi_3(B)\,J(\chi_3,\chi_4)+\bar\chi_3(B)\,J(\bar\chi_3,\chi_4)$$

is **correct**, re-derived from scratch, confirmed exactly at **598 $(p,B)$ pairs with zero failures** (528 in-sample + 70 out-of-sample over 15 primes). Three constructive wins: $\operatorname{Im}(S)=0$ is *algebraically forced* (so the "S is an exact rational integer" bullet carries no confirmatory info and is removed from the evidence column); the single-$J$ column equality is now *derived*, not observed; A3 (norm-lift) is shown non-load-bearing for $(\star)$.

**$m=1$ at secp: `[PROVED — modulo (D2), 3 Katre caveats; + one line owed on the $A_{new}$ identification]`.** Not unconditional. The one line owed: tying the $\chi_4$-isotypic factor of $\operatorname{Jac}(w^4=f)$ to "the new part complementary to $E$" — the two descriptions coincide, stated not proved.

---

## 6. The 120° anchor from the $m$-law — delivered at true scope, narrative overreach withdrawn

`RESULT_120deg_anchor_from_mlaw_v1.md` (Jul 30). Exact $\mathbb{Z}/24$ arithmetic, roots of unity as exponents, membership *derived* in $\mathbb{Z}[x]/\Phi_{24}$:

- **Steps 2–3 hold `[PROVED-exact]`** (with one misstatement corrected: the $\pm$ pairs have ratio $-1$, not $\zeta_3$; the $\zeta_3$ ratios sit *within* each same-order pair).
- **Step 1 is load-bearing** (corrected): at $p\equiv 7\bmod 12$, $m=-2$ if $B$ is a cubic residue, else $m=1$; secp has $B=7$ a cubic non-residue (computed directly) $\Rightarrow m=1\Rightarrow g=2$. **So the cubic-residue symbol decides whether the 120° lock exists at all.**
- **Step 4 does NOT follow**, three independent reasons: object mismatch ($m=1$ governs the $a=0$ untwisted anchor, outside the 120° census by construction); the absolute-rigidity property does **not** survive the twist (angle becomes free, Sato–Tate) — measured, not assumed; and $m$ is a CM number on Frobenius eigenvalues that extracts no bit of any scalar (recorded non-additivity $0/48$ raw).
- **What it does deliver:** for every $p\equiv 7\bmod 12$ with $B$ a cubic non-residue (incl. secp), the $a=0$ fibre satisfies $\alpha_2/\alpha_1=\zeta_3$ exactly, conditional on the $J$-sign law. **Zero power over any $a\neq 0$ cell** — a necessary consistency condition on any uniform mechanism, not a step toward uniformity. The phrasing "$a=0$ is no longer the weak end" is withdrawn; the weak end was always $a\neq 0$ and still is.

---

## 7. $\chi_k$ / $d\bmod k$ leakage — clean scoped null

`RESULT_chik_dmodk_leakage_v1.md`: does $\chi_k(x([d]G))$ leak $d\bmod k$ for $k\in\{2,3,6\}$? **NULL** on both unseen random-style sets, all $k$, with the positive control firing (so power existed; extraction ceiling $\approx 1/20$). `[EMPIRICAL — SCOPED]`. This is a per-point *marginal* bound — a Farey-generic distribution marginal, expected null; **not a closure** (higher-order/joint/set-level readouts untested). The in-sample $\chi_3$ $p=0.043$ on the real 82 flattens to $p\approx 0.39/0.65$ at $N=10^4$ — small-$N$ noise, properly closed on unseen data.

---

## 8. GLV chirality lock — retired before run (a self-caught tautology)

`PREREG_glv_lock_chirality_v1.md`: retired because $\eta(a)=\alpha_2/\alpha_1$ at $a$ and at $\lambda a$ are read from the **same** Frobenius eigenvalue multiset ($L^*(a)=L^*(\lambda a)$ is an exact family identity) $\Rightarrow \chi(\lambda a)=\chi(a)$ is **forced** $\Rightarrow$ the only branch the test can return is the tautological one. Verified two independent ways (object-level + trace-level witness $V_k(a)=V_k(\lambda a)$). **Power identically zero at every $n$.** Redirect: identify the $\mu_3$ in the geometric/arithmetic monodromy of $L_{\chi_2(y)}\otimes L_{\chi_a}$ — the live object, needs its own spec.

---

## 9. CM laws scaled to secp — exact, but only the $\pi$-only tier

`RESULT_scale_cm_laws_ladder_v1.md`: the **CM/$\pi$-only laws hold exactly at secp's own $p$** `[VERIFIED — exact, at secp]` (norm, trace, CM discriminant $4p=t^2+3f^2$, rhombus theorem, amicability $N(\pi-1)=\#E$, sextant angle). Firing control: derived secp constants equal the on-file Part I values exactly. **N6 no longer governs this subset.**

But the tier boundaries are themselves findings: the $V(a)$/twisted-sum laws (120°, $\tfrac12$-saturation, joint readout) are **structurally banner-locked by the DLP** — their defining object encodes the discrete log, so they cannot reach secp even in principle (evaluating $V(a)$ at secp *is* an ECDLP-scale enumeration). N6 is re-scoped to the statistical/twisted-sum rows and **stands**. Not a leakage claim.

---

## 10. Cross-cutting: two instrument defects, and a chronic gate/citation debt

**Instrument defects (self-caught, not denied):**

1. **Even-index probes annihilate identically against the odd readout.** $u(-a)=-u(a)$, and any even index map ($a\mapsto a^2$, quadratic chirp, multiplicative chirp) pairs $a$ with $-a$ to give exactly $0$. This silently mis-specified **three** probes this session ($a^2$ returned $-0.00000$ with null sd $0.00000$ at every prime). Standing rule now issued: check probe parity against $u$'s oddness before running.
2. **The upper tail of $|V|$ never had a valid null** until the semicircle null was built: the signal-domain null violates the proved cap; the frequency-domain null preserves $|V|$ exactly $\Rightarrow$ zero power. The semicircle/Sato–Tate marginal null (cap-respecting by construction) is the fix, and it killed $S_3^{\max}$ OOS.

**The shortscalar arm has never run** (`PREREG_incomplete_shortscalar_v2.md`, `RESULT_shortscalar_gate_debts_v1.md`): the mandatory pre-data `experiment-designer` gate failed **three times, three distinct causes** (org access disabled; weekly limit; watchdog stall at 600s reaching §8). `[PROVISIONAL — gate UNAVAILABLE]`; per `CLAUDE.md §2a condition 4`, **no grade promotion** on any run against this spec. Two mechanical debts discharged clean — FWER calibration `[VERIFIED 2×10^4 reps]` (Holm at $0.05 = 0.0482$), and an exactness scan that found the lift/point core clean with three required repairs (`n**.5` $\to$ `math.isqrt`; float surrogate counts; float self-test) owed before any run. Frame layers (§1, §3, §6, §7, §9) remain unaudited — and §1 is the retraction-24 tautology trap (disjoint construction).

**Citation debt is now load-bearing.** The $V_2$/cap chain and the destructive-interference refutation both lean on a **KS/Weil citation chain with an unverified link** (`(D2)` — three failed `citation-verifier` runs). The Katre primary-text check (`RESULT_D2_katre_primary_text_v1.md`) is explicitly `[PROVISIONAL — gate UNAVAILABLE]`: the *mechanical* layer (what the text says, $84\equiv 0\bmod 12$) is covered with a quote artifact, but the *frame* layer (the judgment that Prop 3′ + Prop 1(f) may substitute for Prop 4(ii)) was made with knowledge of the desired answer, not isolated, and no second source checked (Ireland–Rosen, Berndt–Evans–Williams, Gross–Koblitz, Lang, Washington all unchecked). **Fourth citation-verifier failure on the project. No promotion.**

---

## 11. Governance: the closure-grade spec and the rules audit

Two new governance artifacts shape how all of the above is to be read:

- `COUNTERPRIOR_and_closure_grade_spec_v1.md` (Jul 28): a dismissal is a *graded claim* — to be valid it must name object + class + power + scope. An empirical null is **not** a closure. Two structural findings: the corpus polices overclaim *upward* but is near-blind *downward* (no grade tag for a dismissal); and the stance "only a rigorous analytical proof closes" *trusts* analytical closures, which is the subtlest false-closure vector (both 2026-07-28 errors were analytical, via a moved quantifier/object).
- `RULES_AUDIT_dogma_vs_guidance_v1.md` (Jul 30): distinguishes a *failed-search* negative (correctly a scoped null) from an *exhibited-counterexample* negative (a positive result wearing a negative sentence, correctly `[PROVED]`). The authority rule "the model does not close findings — the user does" stands but is scoped to findings/adjudications, not mathematical refutations. It also flags that several project memories carry *legitimate instructions with illegitimate justifications bolted on* (e.g. the no-PRNG boundary is a legitimate scope choice, but "says nothing about the curve" is a retracted closure).

---

## 12. Bottom line + next moves (findings layer)

- **One genuine consolidation:** the char-poly collapse turns the cap programme's two open links into one ($e_2=e_1^2+p$), reframing frontier #26 as a coefficient identity. This is the thing to push.
- **The empirical front went clean:** every positive-looking cell died OOS; the surviving "positives" (dark fringe, $E3$ CM-fingerprint) are characterizations of known theorems, not new laws.
- **One real control correction:** the v32 $\mu_3$ diffset cell had zero working controls — *power* retracted, *signal/numbers* not; re-run as a powered bounded result ($\varepsilon<0.0415$, not a closure).
- **Two process debts are now on the critical path:** the `experiment-designer`/`citation-verifier` gate unavailability (shortscalar never ran; `(D2)` Katre unverified, no promotion), and the two self-caught instrument defects (even-index annihilation; the $|V|$-tail null gap — now fixed).

The single highest-value next move remains frontier #1 (a cheap *partial* of the joint $(x,y)$ shadow) on the leakage side, and **proving $e_2(a)=e_1(a)^2+p$ uniformly** on the structural side — with the citation chain (`(D2)`) discharged as a prerequisite to any grade promotion on the cap.

---

## 13. Source-file citation block

| File | Object | Grade |
|---|---|---|
| `ANALYSIS_n1_charpoly_collapse_v1.md` | char-poly collapse: 2 free coeffs, $e_2=e_1^2+p\Leftrightarrow$ 120° | `[DERIVED+VERIFIED, exact, p=43,67,127]` |
| `RESULT_theta_structure_v1.md` | 4-line forcing of $V_2=V_1^2+2p$; folded angle; angle-increment/mult. autocorr NULL | `[EXPLORATORY, OOS retested]` + `[VERIFIED, exact, 3 primes]` |
| `RESULT_semicircle_null_and_verification_v1.md` | cap-respecting semicircle/Sato–Tate marginal null; $S_3^{\max}$ killed OOS; $V_2$ identity | `[EXPLORATORY, OOS retested]`; §3 `[VERIFIED, exact]` |
| `RESULT_n1_saturation_residual_v1.md` | N1 mechanism $\tfrac12=\tfrac24$; numeric shortfall flagged weak/non-reportable | `[EMPIRICAL, 34 primes]` |
| `RESULT_spectral_decomp_v1.md` | SVD of cubic-character matrix; $E3$ as all-ones projection; destruct-interf. not supported | characterization (frozen prereg) |
| `RESULT_chirp_hologram_plane_v1.md` | chirp plane; $k=0$ dark fringe (cap re-presented); $k=t$@2731 killed OOS | `[EXPLORATORY, scoped]` |
| `RESULT_phase_family_and_tail_v1.md` | phase families Q/C/I/M NULL; odd-phase+bijection selection rule | `[EXPLORATORY, scoped]` |
| `RESULT_large_p_and_arrangement_v1.md` | inverse-phase NULL to $p=8191$; arrangement corr. NULL; even-index annihilation | `[EXPLORATORY, scoped]` |
| `ANALYSIS_destructive_interference_frame_v1.md` | three-walls triage; Parseval budget accounted (conditional on `(D2)`) | analysis only, no grade |
| `RESULT_diffset_cubic_cmvanishing_v1.md` | field-diff $E3$ stands; CM-fingerprint characterization | `[EMPIRICAL]` characterization |
| `CORRECTION_v32_mu3_diffset_controls_v2.md` | v32 group-law $M3$ controls invalid (C1 forced-zero, C2 mult., C4 non-indep.) | `[PROVED]` forcing; `[NO VALIDATED POWER]` |
| `RESULT_mu3_diffset_control_repair_v1.md` | repair: cell A bounded $\varepsilon<0.0415$, not closure; cell B void | `[EMPIRICAL, powered, control fires]` |
| `CORRECTION_v10_lever_enumeration_v1.md` | v10 framing-only correction; v10 results stand | correction |
| `RESULT_star_adversarial_review_v1.md` | Jacobi $m$-law $(\star)$ confirmed, 598 pairs 0 failures | `[PROVED]`; $m=1$ at secp `[PROVED mod (D2)+caveats]` |
| `RESULT_120deg_anchor_from_mlaw_v1.md` | 120° at $a=0$ anchor; steps 2–3 proved, step 4 not | `[PROVED-exact]` at $a=0$; 0 power over $a\neq 0$ |
| `RESULT_chik_dmodk_leakage_v1.md` | $\chi_k$ vs $d\bmod k$ NULL on unseen sets | `[EMPIRICAL-SCOPED]` |
| `PREREG_glv_lock_chirality_v1.md` | GLV chirality retired before run (tautology) | retired, nothing run |
| `RESULT_scale_cm_laws_ladder_v1.md` | CM/$\pi$-only laws exact at secp; N6 re-scoped | `[VERIFIED, exact, at secp]` |
| `RESULT_D2_katre_primary_text_v1.md` | Katre text verified mechanically; frame layer not isolated | `[PROVISIONAL — gate UNAVAILABLE]` |
| `PREREG_incomplete_shortscalar_v2.md` + `RESULT_shortscalar_gate_debts_v1.md` + `AUDIT_..._SELFAUDIT_v1.md` | shortscalar arm, never run; 2 debts discharged | `[PROVISIONAL — gate UNAVAILABLE]` |
| `COUNTERPRIOR_and_closure_grade_spec_v1.md` | closure-grade spec; F1/F2 false-closure vectors | governance |
| `RULES_AUDIT_dogma_vs_guidance_v1.md` | failed-search vs exhibited-counterexample; scoped authority rule | governance |
