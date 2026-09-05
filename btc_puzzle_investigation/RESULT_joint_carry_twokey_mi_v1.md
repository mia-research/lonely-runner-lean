# RESULT — Two-key joint-carry synergy `Î(ε;A|B)`: scoped NULL on all arms (instrument valid, bounded by bilinear Cor B1)

**Date:** 2026-08-13. **Executes:** `PREREG_joint_carry_twokey_mi_v1.md` (frozen, verbatim).
**Artifact:** `scratchpad/joint_carry_twokey_mi_v1.py` + stdout (below). Exact integer signal path;
float guard `check_no_float.sh` **exits 0** (all carve-out lines `# noqa: float`-exempted; a safety
pass verified none of the exempted lines sit inside a signal-path function — so the clean exit now
genuinely certifies `b_eps`/`eps_carry`/`point_add_affine`/`mu6_canon`/`build_records` are float-free).

## What was tested (the one genuinely-distinct object)

The pre-registration first ruled on three feature choices for the tool-7 two-key carry
`ε = [r₁+r₂≥n] = [(d₁+d₂)·λ mod n < r₁]` (r₁=⌊n/2⌋ via a fixed KNOWN d₁, branch j=1):
- **F0 = `b_eps(x_{P_sum})`** → **REDUCES EXACTLY to v1** (`d↦d_sum`), not run.
- **F1 = `b_eps(x_{P₂})`** → **v1-class replay** (fixed-shift target reparam.), not run.
- **F2 = the pair `(A,B)` with the sum-marginal `B` conditioned out** → **genuinely distinct** (registered):
  the conditional/synergy MI `Î(ε ; A | B)`, `A=b_eps(x_{P₂})`, `B=b_eps(x_{P_sum})`. Distinct because
  `x_{P₂}=x(P_sum−P₁)` is NOT a function of `x_{P_sum}` alone (group-law subtraction of the fixed `P₁`
  uses `y_{P_sum}`; `P_sum` and `−P_sum` share x but differ in `x_{P₂}`). With both marginals already
  null (v1 + the F0 reduction), any signal in `Î(ε;A|B)` is **pure cross-point synergy** — the
  coordinate shadow of the addition `P₂+P₁=P_sum` where the tool-7 scalar carry physically sits.

**Frame correction inherited from the pre-reg:** "feature not a function of `d_sum` alone" is
unachievable with `d₁` fixed (everything is a deterministic function of the one unknown `d₂`) — that
determinism is the v1 DLP-tautology, defused by the decisional-bit framing (1-bit target, 2-bit
feature ≪ log₂N, plant fires), not by independence. The correct criterion is "not a function of
`x_{P_sum}` alone," which F2 clears.

## Controls (all fired) and the result

- **Correctness gate:** the explicit group-law addition `P_sum = P₂+P₁` (Jacobian `_add`, exact int
  mod p) equals `scalar_mul((d₁+d₂) mod n)` for every real key (asserted `verify=True`).
- **Firing control (strong plant `A⊕Bern(0.25)`, injected into the CONDITIONED-IN channel A — NOT B,
  which would leave CMI≈0 and silently fail):** fires on ALL arms — real-82 `Îhat=0.163, p=3.5e-4`;
  constructed `p=1e-4`. Floor plant (q=0.30, ≈MI_min): fires on the N=10⁴ arms (p=1e-4), borderline at
  N=82 (`Îhat=0.056, p=0.062`) — consistent with MI_min=0.122 being right at the N=82 detection edge.
- **Matched null:** μ₆-canonicalize + orbit-dedup on `d₂`, then GLOBAL permutation of `ε` labels with
  `(A,B)` fixed, Monte-Carlo. Dedup dropped 0 (real, full) / 879 (matched bit-bands) — machinery live.

**PRIMARY `Î(ε ; A | B)` (conditional MI, df=2, verdict-driving):**

| arm | N (post-dedup) | Pr[ε=1] | Îₚᵣᵢₘ (bits) | perm-p | MI_min(df=2) | grade |
|---|---|---|---|---|---|---|
| real-82 (d₂=puzzle keys) | 82 | 0.488 | 0.01703 | 0.433 | 0.122 | scope NULL |
| constructed-full (uniform d₂) | 10000 | 0.499 | 0.00005 | 0.705 | 0.0010 | scope NULL |
| constructed-matched (puzzle bands) | 9121 | 0.504 | 0.00002 | 0.896 | 0.0011 | scope NULL |

The real-82 `Îₚᵣᵢₘ=0.017` bits is exactly the df=2 plug-in bias at N=82 (`2/(2·82·ln2)≈0.0176`),
sitting at the null center (perm-p=0.43) — pure estimator bias, no signal. **SECONDARY `Î(ε;(A,B))`
(2×4, df=3, not verdict-driving):** null on all arms (perm-p 0.46 / 0.61 / 0.18).

## Grade, power, scope (per PREREG §9)

**`[VERIFIED-scope NULL]`.** **Object:** cross-point synergy of the summand-flap `A=b_eps(x_{P₂})` and
the sum-flap `B=b_eps(x_{P_sum})` with the two-key GLV coupling-carry bit `ε(d_sum)`. **Class:** the
conditional mutual information `ε ⊥̸ A | B` (decisional bit). **Power:** strong plant fires (MI≈0.19
detectable); `MI_min` = 0.122 bits (N=82) → 1.0×10⁻³ bits (N=10⁴). **Scope:** secp256k1; `eps` per
`RESULT_linchpin_s_gate_v2.md`; `ε` via canonical `λ`, r₁=⌊n/2⌋, branch j=1; both key sets.

**NOT A CLOSURE.** `MI_min` reaches `1.0×10⁻³ ≈ 2^−10`; the KS floor is `2^−128` — a synergy anywhere
in the `[2^−128, 2^−10]` band (~2¹¹⁸ of dynamic range) is invisible here. Verdict: **no gross
summand-flap → carry synergy beyond the sum-flap at `MI ≥ MI_min(N)`.**

**Consistent with and bounded by theory.** `Îₚᵣᵢₘ` is a two-point / addition-coupled coordinate
correlation, so the null is exactly what `bilinear_closure_proof_v1.md` Corollary B1 predicts
(true coupling `≤ O(p^−1/2)=O(2^−128) ≪ MI_min`, `[PROVED given KS]`). A positive at `MI ≥ 0.12` bits
would have CONTRADICTED B1 by ~127 orders and been graded `EMPIRICAL (pending bug-hunt)` — an
instrumentation defect until independently reproduced. It did not occur.

## Where this leaves the "joint fiber" line

Both non-tautological realizations of "a pair of transverse public invariants that separates the GLV
lifts" have now been tested and returned scoped nulls, with the instrument validated each time:
- **single-key cross-channel** (`RESULT_joint_fiber_carry_mi_v1.md`): flap `b_eps` vs single-key carry — null.
- **two-key synergy** (this file): summand-flap vs sum-flap conditional on the carry — null.

The empirical picture is now aligned with the analytical one: the bilinear-closure theorem
(PROVED given KS) bounds exactly this class of two-point coordinate coupling to the KS floor, and the
decisional MI at feasible N sees nothing above `MI_min`. **This does not retire the GLV/CM avenue** —
the `[2^−128, 2^−10]` band is untested, and the aligned single-index readout (= the DLP) is a separate
object untouched by any of this. **Named next probes** that are NOT this class of two-point coupling:
(i) the `s<3/16` core-exclusion as a *deterministic* constraint (pin ε=0 for the core fraction and ask
whether the pinned subset admits a Babai/GLV-lattice range cut on `d₂` — a search-space question, not
an MI question); (ii) the µ₆ solving-degree lever for the j=0 Semaev system (`ANALYSIS_semaev_cm_yield_mechanism_v1.md` P2),
which lives outside the KS-bounded correlation frame entirely.

**Owed gates:** `citation-verifier` on the Cap-Law `¾:⅛:⅛`/`eps=0⟺core` inputs and on the KS input to
Cor B1 before any grade moves up on them; `compile-diff` if folded into a master. Moves no grade up on a citation.

## stdout (reproduced)

```
===== ARM: real-82 (d2=puzzle keys) =====
  N(raw)=82 mu6-drop=0 N(kept)=82
  A(flap P2): 0=65 1=17 | B(flap Psum): 0=67 1=15 | eps: 0=42 1=40 (Pr[eps=1]=0.4878)
  MI_min(80%pow,df=2)=0.12195 bits
  PLANTS(into A) strong q=.25: Ihat=0.1626 p=3.50e-04 [FIRES]   floor q=.30: Ihat=0.0557 p=6.16e-02
  PRIMARY  Ihat(eps;A|B)=0.01703 bits  perm-p=0.43258 (8651/20000)  -> below power/null
  SECOND.  Ihat(eps;(A,B))=0.02520 bits  perm-p=0.46433 [not verdict-driving]
===== ARM: constructed-full (uniform d2, N=10000) =====
  N(raw)=10000 mu6-drop=0 N(kept)=10000
  A(flap P2): 0=7444 1=2556 | B(flap Psum): 0=7505 1=2495 | eps: 0=5013 1=4987 (Pr[eps=1]=0.4987)
  MI_min(80%pow,df=2)=0.00100 bits
  PLANTS(into A) strong q=.25: Ihat=0.1831 p=1.00e-04 [FIRES]   floor q=.30: Ihat=0.1299 p=1.00e-04
  PRIMARY  Ihat(eps;A|B)=0.00005 bits  perm-p=0.70503 (7050/10000)  -> below power/null
  SECOND.  Ihat(eps;(A,B))=0.00013 bits  perm-p=0.60824 [not verdict-driving]
===== ARM: constructed-matched (puzzle bit-bands, N=10000) =====
  N(raw)=10000 mu6-drop=879 N(kept)=9121
  A(flap P2): 0=6822 1=2299 | B(flap Psum): 0=6793 1=2328 | eps: 0=4521 1=4600 (Pr[eps=1]=0.5043)
  MI_min(80%pow,df=2)=0.00110 bits
  PLANTS(into A) strong q=.25: Ihat=0.1838 p=1.00e-04 [FIRES]   floor q=.30: Ihat=0.1171 p=1.00e-04
  PRIMARY  Ihat(eps;A|B)=0.00002 bits  perm-p=0.89601 (8960/10000)  -> below power/null
  SECOND.  Ihat(eps;(A,B))=0.00039 bits  perm-p=0.18438 [not verdict-driving]
```
