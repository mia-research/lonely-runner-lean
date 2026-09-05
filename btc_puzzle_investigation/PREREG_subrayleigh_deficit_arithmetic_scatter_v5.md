# PREREG v5 — is the sub-Rayleigh deficit's scatter arithmetic BEYOND the smooth δ(p,n) surface?

**File:** `PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md`  **Date:** 2026-08-06
**Supersedes v4** after a FOURTH (confirming) isolated `experiment-designer` pass: v3's three control
defects were all confirmed discharged, but v4's refinement-a introduced ONE new localized defect — the
sextic-class(7) invariant was mislabeled "misspecification-protected" (verified: η²(u₀²|sextic-class)=
**0.180**, vs 0.081 / 0.014 for `a_p mod 3` / `a_p mod 4`), and §4/§9-A8 contradicted each other on that
channel. v5 fixes exactly that. Change log §10.
**Status: PRE-RUN.** No confirmatory statistic computed. The 30-prime table of
`RESULT_subrayleigh_deficit_scaling_v1.md` is TRAINING (fixes signs/priors only); it may not enter a
confirmation number.

**Design lineage (five versions, each pass found something real).** v1→v2: six mechanical/power defects.
v2→v3: the *conceptual* obstruction — at fixed p, group order `n` and Frobenius trace `a_p=p+1−n` are the
**same axis**; v2's control B was ill-posed. v3→v4: surface-residual reframing well-posed; three control
fixes. v4→v5: the sextic-class channel is a **partial `u`-proxy** (structural: the sextic class of 7
selects the twist-slot, hence `|a₀|`, hence `u₀²`), so it is NOT orthogonal-protected like a pure residue.

**The two numbers that bind v5 (both independently verified):** `R²_smooth(deg-2 in ln p)=0.0048` (the
smooth-p surface explains ~none of the scatter ⇒ gate the within-`u` slope, not overall-R²);
`η²(u₀² | sextic-class(7))=0.180` (sextic-class is smooth-confoundable; `a_p mod 3/4` at 0.081/0.014 are
clean).

---

## §0 SCOPE BANNER (inherited by every number)

Enumerable model curves over `F_p`, `p ≡ 1 (mod 3)`, full group enumeration, cyclic part only.
`p = 2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers to it**. No ECDLP, extraction,
key-recovery, or security claim is made or derivable. This studies the structure of a spectral statistic.

---

## §1 OBJECT AND THE WELL-POSED QUESTION

Frozen instrument `subrayleigh_deficit_scaling_v1.py` (`run_prime`): for cyclic `E/F_p` order `n`,
`δ=(mu−M_char)/mu`, `SE_δ=sdM/(mu√K)`; δ deterministic; `√(n−1)` scale cancels (verified,
`mu/√(n−1)=√(π/4)` to 0.03%), so δ is a pure L1/L2 **shape** ratio.

**δ is a function of two independent variables `(p,n)`; `a_p=p+1−n` is their affine combination, not a
third channel.** Along the base-curve trajectory `p↦(p, n₀(p))`, `n₀(p)=#E(y²=x³+7/F_p)`, δ scatters far
beyond any smooth `p`-model (`R²_smooth=0.0048`, verified). Well-posed successor question:

> **After removing the smooth `δ(p,n)` surface, does the base-curve trajectory's residual depend on an
> arithmetic RESIDUE invariant a smooth surface cannot mimic — or is the scatter fully accounted for by
> δ's `n`-dependence?**

The sextic twists supply the off-trajectory `(p,n,δ)` samples that fix the surface `n`-slope.

---

## §2 HYPOTHESES (signs/priors from TRAINING only)

`u=(n−p−1)/√p=−a_p/√p` (`|u|≤2`). Surface `f̂(p,n)=g₀(p)+g₁(p)·u` (§3), fit from OFF-trajectory `k≠0`
twists; base `k=0` HELD OUT. Residual `r(p)=δ₀(p)−f̂(p,n₀(p))`.

- **H1 — trajectory residual carries arithmetic structure.** THREE protection tiers (v5 correction):
  - **H1a (CLEAN PRIMARY — orthogonal-protected residues).** `r(p)` associates with `a_p mod 3` or
    `a_p mod 4`. Verified nearly orthogonal to the smooth regressor `u₀²` (η²=0.081 / 0.014), so a hit
    here **cannot** be a surface-underfit artifact. **This is the load-bearing primary.** Holm-FWER-0.05
    over the two.
  - **H1a′ (REFIT-PROTECTED — sextic-class(7), a partial `u`-proxy).** `r(p)` associates with the sextic
    class of 7 (∈ Z/6). Because η²(u₀²|sextic-class)=0.180 (structural: sextic-class selects the
    twist-slot ⇒ `|a₀|` ⇒ `u₀²`), a raw hit could be a `u²` artifact. **H1a′ fires ONLY if the
    association survives a refit with a richer `u`-basis (`u²`, `u³`, higher `ln p` regressed out of `r`
    first) — UNCONDITIONALLY, regardless of the §4 SM state.** Own Holm slot; keeps the more-powerful
    Z/6 test while guarding the confound.
  - **H1b (SMOOTH-CONFOUNDABLE SECONDARY).** `r(p)` vs `M` (`4p=L²+27M²`); lag-1 rank autocorr. These
    confound with out-of-class smooth misspecification; **gated on (H1a or H1a′) firing AND a clean §4 SM
    control.** Reported, non-primary.
- **H2 (ENABLING — within-p `n`-slope, correctly scoped).** `g₁(p)=∂δ/∂n|_p` nonzero, consistent sign
  across primes (training prior `g₁<0`). Establishes "**δ depends on the group order `n` at fixed p**" —
  no finite-size-vs-geometry claim. **H2 is also the surface-adequacy gate for H1** (§4).
- **H3 (SECONDARY, `M>1` only — trace-universality).** At fixed `(p,n,a_p)`, does δ depend on the
  j-invariant beyond the trace? Ensemble-compared vs non-CM `E'` with `#E'=n` (audit NEW-1/3).
- **H0 (a valid pre-committed positive).** `(H1a and H1a′) null (powered) ∧ H2 fires`: the scatter is
  **fully** δ's smooth dependence on group order `n` (which scatters via `a_p`); no arithmetic-residue
  structure beyond the surface at this scope. Scoped characterization, not a closure, not a mechanism.

**"H1 fires" ≡ (H1a Holm-significant) OR (H1a′ Holm-significant AND richer-`u` refit-survived).** Both
disjuncts are misspecification-protected; the §4 SM state does NOT gate them (it gates only H1b).

---

## §3 STATISTICS

**Surface fit `f̂(p,n)=g₀(p)+g₁(p)·u`**, `g₀,g₁` degree ≤2 in `ln p` (frozen), fit from `k≠0` twists
only, exact-rational weighted LS (weights `1/SE_δ²`). Base `k=0` held out.

| id | statistic (verdict-bearing) | null |
|---|---|---|
| **H1a** | exact-permutation **Mann–Whitney / rank-biserial** of `r(p)` split by `a_p mod 3` and by `a_p mod 4` (binary 2-group splits — NOT continuous Spearman, audit c). Primary = **Holm-FWER-0.05 over the two**. | exact permutation of `r(p)` labels (integer counts) |
| **H1a′** | exact-permutation **Kruskal–Wallis** of `r(p)` by sextic-class(7) ∈ Z/6, THEN the SAME KW on the residual of `r(p)` after regressing out `{u², u³, higher ln p}` (the richer-`u` refit). **Fires only if BOTH are Holm-significant** (own slot). | exact permutation of labels; refit residual permutation |
| **H1b** | `r(p)` vs `M`: one-sided Spearman; lag-1 rank autocorr of `r(p)`. Separate Holm slot; **gated on (H1a or H1a′) ∧ clean §4 SM**. | exact permutation of `r(p)` labels |
| **H2** | per prime: exact permutation one-sided p-value `π_p` of δ-vs-`n` rank slope over `m_p` resolved cyclic twists (all `m_p!` orderings); Fisher `X=−2Σln π_p`; threshold from the **EXACT combined null** (convolve discrete `π_p` supports), not χ²/N(0,1). | discrete exact combined null |
| **H3** | at each `M>1` matched `(p,n)`: `δ_twist − δ_{B1}` vs the **B1 ensemble scatter** over ≥K_B curves (audit NEW-3). | B1 ensemble |

**Frozen invariant lists (ONLY these; no post-hoc additions):** CLEAN-RESIDUE `{a_p mod 3, a_p mod 4}`
(H1a); REFIT-PROTECTED `{sextic-class(7)}` (H1a′); SMOOTH-CONFOUNDABLE `{M, lag-1 autocorr}` (H1b).
Directions fixed here from TRAINING. Note (audit c): sextic-class(7) and `a_p mod 3` both carry the
cubic/sextic character ⇒ dependent; they now live in **separate tiers**, so no shared-Holm-slot double
count. `a_p mod 3`/`a_p mod 4` are binary imbalanced (19:11, 14:16 — verified) ⇒ ceilinged effect,
imbalance-aware power (§7).

---

## §4 CONTROLS

- **Off-trajectory fit.** `f̂` from `k≠0` only; tested `k=0` residuals out-of-fit.
- **Surface-adequacy gate (v4 respecification, PASSED).** NOT overall CV-R² (≈`R²_smooth=0.0048`,
  vacuous). It is the **within-prime partial-R² of the `u`-term** ≡ **H2's Fisher significance**.
  Pre-committed floor: H1 proceeds only if H2 fires (exact combined-null p<0.01) AND pooled within-prime
  partial-R²(u) ≥ **0.25**. Non-achievement ⇒ "surface underdetermined; uninformative" (routes to A5).
- **SM — smooth-misspecification control (v5 role clarified).** `r(p)` vs `u₀²=a_p²/p` **should be null**.
  A dirty SM (nonzero) means the linear surface under-fits a `u²` term leaking into `r`. **Effect of a
  dirty SM, by tier:** (i) **H1b is VOID** (its M/autocorr channels are exactly the smooth-confoundable
  ones); (ii) **H1a is UNAFFECTED** (η²≤0.08 to `u₀²` — orthogonal); (iii) **H1a′ is UNAFFECTED because
  it already requires the richer-`u` refit unconditionally** — the refit removes the `u²` leak whether or
  not SM is dirty. A dirty SM is therefore a **data state that is handled**, NOT a no-verdict condition
  (this resolves the v4 §4/A8 contradiction). SM's own firing (a real `u²` present) is expected whenever
  a genuine sextic-class signal exists (η²=0.18), which is exactly why H1a′'s refit is unconditional.
- **H3 ensemble (audit NEW-3).** compare to the B1 **ensemble scatter**, never a single realization.
- **Multiplicity/disjointness.** Frozen lists (§3), Holm within each tier; residue invariants are exact
  integer point-count residues; the (r↔invariant) pairing is across different curves.
- **Scatter ≫ estimation.** trajectory δ-spread ≥10·SE_δ (ratio ~400 at p=12043), asserted in code.

---

## §5 PLANTED / NEGATIVE CONTROLS — all must behave

| id | plant | in | pass |
|---|---|---|---|
| **P1** | inject `r'(p)=c·[a_p mod 3]+noise` onto real labels | H1a | recovered Holm-significant |
| **P2** | shuffle (curve↔invariant) on same `r` (negative — SILENT) | H1a,H1a′,H1b | null at nominal rate |
| **P3** | inject a known `g₁` slope into synthetic twist δ | H2 | recovered; exact combined-null threshold calibrated |
| **P4** | `#E`/`a_p`/`M`/sextic-class by two independent exact methods; six `a_p` sum to 0 | invariants | integer-identical (**audit-verified** structure) |
| **P5** | re-measure δ at 3 training primes, independent seeds | instrument | stable ≤2·SE_δ |
| **P6** | plant an **OUT-of-model-class** smooth surface (`u²/u³`/higher ln p, e.g. one whose sextic-class projection is large) with **zero arithmetic residual**; fit in-class `f̂` | H1, SM | **H1a silent; H1a′ silent AFTER its richer-`u` refit; H1b silent; SM control FIRES** (catches the `u²` leak). Confirms the refit actually neutralizes a `u²` masquerading as sextic-class. |

Any misbehavior ⇒ that arm uninformative; no verdict. (Dirty SM is NOT "misbehavior" — see §4.)

---

## §6 SCOPE & SCHEDULE

- **Training (FROZEN, direction/priors only):** the 30 primes of `RESULT_subrayleigh_deficit_scaling_v1`.
- **Cheap integer cyclicity screen (no FFT):** ~160 candidate primes `p≡1 mod 3`, `p∈[3000,12000]`
  (large-p for δ-resolvability, §8), disjoint from training; compute all six twists' `#E`, cyclicity, `M`,
  sextic-class exactly.
- **FFT δ-measurement schedule:** ALL cyclic twists at a frozen `P_surf ≥ 50` screened primes (~150
  measurements; fit `f̂`, give H2); base curve `k=0` at ≥30 frozen **trajectory primes** (held out) for
  the H1 residual sequence; `M>1` matched-`(p,n)` B1 ensembles at ~10 primes (H3).
- **`_SCHEDULE.txt` (SHA-256'd with this spec, binding):** exact prime lists (surface / trajectory / H3),
  `g` per prime, per-prime cyclic count, per-twist `M` and sextic-class, dropped primes + reason. Nothing
  enters a fit or combine unless frozen here.
- **Cost.** Screen: minutes. FFT: one `p×p` complex128 (~1.8 GB at p≈12000) per (object,K-draw);
  ~150 surface + ~30 trajectory + H3 — hours to ~a day. complex128 only.

---

## §7 POWER

- **H1a (clean-residue primary):** two binary Mann–Whitney tests, Holm-over-2, imbalanced (19:11, 14:16).
  Achievable rank-biserial is ceilinged; floor = the Mann–Whitney detectable shift at that imbalance
  (≈0.9·residual-sd for 0.8 power at 30 primes). A null H1a is `[UNDERPOWERED]` below that. (Thinner than
  a continuous test — the honest cost of dropping sextic-class from the clean tier.)
- **H1a′ (sextic-class Z/6):** KW at 30 primes detects a between-class shift ≥ ~1·(residual sd) at ≈0.8,
  but the mandatory richer-`u` refit reduces d.o.f.; report the post-refit power. A null is
  `[UNDERPOWERED]` below the post-refit floor.
- **H2 (`n`-slope):** exact small-`m` power (audit check5): `P_surf≈50`, `m_p≈3–4` ⇒ ≥0.8 at `ρ_p≈0.5`.
  Adequacy floor as in §4.
- **H3:** `K_B` sized so ensemble SE ≤ (target j-effect)/3.
- A1 requires "H1 fires" (H1a or refit-survived H1a′) at Holm level with H2 fired and the §4 partial-R²
  floor met. Verdicts state individual floors.

---

## §8 EXACTNESS

- **Exact int:** EC arithmetic, `#E`, `a_p`, `M` (integer solve of `4p=L²+27M²`), sextic-class(7) (exact
  power-residue), `a_p mod ℓ`, twist `g^k`, six-`a_p`-sum-zero, all rank/permutation counts & p-values,
  the surface-fit weighted LS in exact `Fraction`, invariant ranks by integer cross-multiplication.
- **δ-rank resolvability (v2 D5):** `p≥3000`; per-prime `K` sized so `SE_δ≤gap/5`; resolved-pair
  `|δ_i−δ_j|>5·SE_δ`; drop `<3` resolved pairs (sign-neutral magnitude filter).
- **Sanctioned float carve-out (analytic magnitude only):** the `p×p` FFT `|U|`, `e_n(·)`; error
  `≤1e−12≪δ`. complex128 only. No verdict decided by float precision. The richer-`u` refit (H1a′) is a
  monotone statistic ranked against the permutation null — never a float threshold on the data.
- `check_no_float.sh` passes on the invariant/statistic module before any verdict.

---

## §9 PRE-COMMITTED OUTCOME TABLE — MECE over {H1-fires, H2∈(fire, underpowered, null-flat), H3}

"H1 fires" = H1a Holm-significant OR (H1a′ Holm-significant AND richer-`u` refit-survived). The §4 SM
state is NOT an axis of this table — it only voids H1b (noted in the report), never blocks a verdict.

| # | Condition | Conclusion |
|---|---|---|
| **A1** | H1 fires ∧ H2 fires | **Arithmetic-residue structure BEYOND the smooth δ(p,n) surface.** Name the surviving invariant(s) and tier (H1a clean, or H1a′ refit-survived); the trajectory deficit is not fully explained by δ tracking `n`. Report `f̂`, within-`u` partial-R², `r(p)`, surviving p-values, the SM state (and, if dirty, that H1b is void but A1 stands on H1a/H1a′), any H1b support. Deepest positive; next probe = the mechanism, its own prereg. |
| **A2** | H1 null (powered) ∧ H2 fires | **H0: the scatter is δ's smooth dependence on group order `n` (which scatters via `a_p`); no residue structure beyond the surface.** The correctly-derived answer, WITHOUT the ill-posed finite-size/geometry label. Report surface, within-`u` partial-R², flat residual, power floor. |
| **A3** | H1 fires ∧ H2 underpowered | residue structure without a powered surface slope ⇒ `f̂` underdetermined; report H1 **provisional**, requiring powered H2 (more twist primes) before A1. |
| **A4** | H1 null (powered) ∧ H2 underpowered | inconclusive on both; report bounds + §7/§4 floors; extend the twist schedule. NOT a refutation. |
| **A5** | H2 null-flat (`g₁≈0` resolved, powered) — ANY H1 state | **δ has no resolved `n`-dependence in the sampled band ⇒ the scatter is NOT the group order.** Positive: excludes the leading hypothesis; re-open the source (finer curve data or a p-direct effect). If H1 nonetheless fires, report the residue structure as the new object (not `n`-mediated). |
| **A6** | H1 or H2 `[UNDERPOWERED]` below §7 floor | bounded result + floor; route to A2/A4 only when the floor is met. NOT a refutation. |
| **A7** | H3 fires (independent) | δ depends on `j` beyond the trace (j=0-family-specific); its own follow-up. H3-null ⇒ "trace-universal at this scope." Never folded into A1. |
| **A8** | any **P1–P6 misbehaves** (an instrument/plant/negative control failing) | affected arm uninformative; no verdict. **NB: a dirty §4 SM is NOT a P-control failure** — it voids H1b only and is handled by §4; it does not reach this row. |

**Unprojected-covariate clause (mandatory).** If H1 null and H2 fires/flat: report (i) the confirmed real
trajectory spread (≥10·SE_δ); (ii) within-`u` partial-R² and residual variance as numbers; (iii) the
explicit untested list (higher-order surface terms, `a_p mod ℓ` for ℓ∉{3,4}, class/conductor data,
`v₂(n)`), as next candidates — not absences.

**Output type:** a characterization + power + §0 scope. Never ECDLP/extraction/security; never a
mechanism claim.

---

## §10 CHANGE LOG v4→v5 (one confirming-pass defect)
1. **Sextic-class(7) reclassified** (§2, §3): moved from the "clean orthogonal-protected H1a primary" to
   its own **H1a′ tier** requiring an **unconditional richer-`u` refit** (η²(u₀²|sextic-class)=0.180,
   verified — it is a partial `u`-proxy, not orthogonal). `a_p mod 3/4` remain the clean H1a primary.
2. **§4 SM role clarified / §9 A8 contradiction resolved:** a dirty SM voids **H1b only**; H1a is
   orthogonal-unaffected and H1a′ is refit-protected, so neither is blocked. A8 now explicitly excludes
   "dirty SM" from the no-verdict condition (P-control failure ≠ data state). This gives the expected
   real-sextic-class path (SM dirty ∧ refit-survived) a valid home: **A1**.
3. **P6** updated to require H1a′ silent *after* its refit on an out-of-class `u²` plant whose
   sextic-class projection is large — directly exercising the reclassified confound.
4. **§7** power split by tier (H1a two binary MW; H1a′ Z/6 KW post-refit) with imbalance-aware floors.
- **Carried from v4 (PASSED the confirming pass):** surface-adequacy within-`u` gate, out-of-class P6,
  MECE H2 three-state grid; and from earlier: obstruction retirement, off-trajectory fit, exact small-`m`
  Fisher/H2, δ-resolvability, cheap cyclicity screen, direction-fixing cleanliness, frozen SHA'd schedule.
