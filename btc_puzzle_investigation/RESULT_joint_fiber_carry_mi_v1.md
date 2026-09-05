# RESULT — Joint-fiber → GLV carry-bit leakage drill: original statistic ILL-POSED; repaired cross-channel test = scoped NULL (instrument valid)

**Date:** 2026-08-13. **Executes:** `PREREG_joint_fiber_carry_mi_v1.md` (frozen, verbatim).
**Artifact:** `scratchpad/joint_fiber_carry_mi_v1.py` + stdout (reproduced below). Exact integer
signal path (float carve-out = MI log2 + p reporting only, PREREG §8); float guard `check_no_float.sh`
exits 0 with all flags in the statistic/plant/reporting layer, none in a key-derived map.

## What was proposed vs. what was run

The proposal: intersect two public invariants — `I₁ = F(P) = χ₃(x_P)·y_P` (GLV orbit index `j`) and
`I₂ = s(x) = N(eis(X))/p` (Eisenstein lift norm) — and measure `I( c ; (I₁,I₂) )` against the integer
lift / carry `c = ⌊dλ^j/n⌋` to cross the non-affine boundary.

**The single-point statistic `I(c;(I₁,I₂))` is graded `[ILL-POSED]` (not run)** — two independent
reasons, confirmed by experiment-designer pre-registration:
1. **Power saturation.** `c` carries ~256 bits; any feasible-N plug-in MI estimator saturates at
   `log₂N` and is invariant under the matched shuffle ⇒ `z≈0` by construction (zero power).
2. **DLP-tautology.** `(I₁,I₂)=g(P)` is a deterministic public function of `P=[d]G`; `P` determines
   `d` only *up to the DLP*. Any nonzero MI is the saturation artifact or information locked behind
   the DLP — the statistic cannot separate sub-DLP leak from tautological determinism. (Same family
   as the `r=v−w` residue-vs-component tautology, `z=+5000`, that the shuffle control does not expose.)
   `I₂'=e₂=e₁²−χ₂(−1)p` separately excluded: it is a curve-global zeta invariant, zero per-point variance.

**Repaired test (run):** cross-channel decisional-bit predictivity — does the **coordinate-channel**
flap `b_eps = [eps(x_P)≠0]` (exact fn of `x_P` alone) predict the **scalar-channel** coupling-carry
`ε = [ (d·λ mod n) ≥ ⌈n/2⌉ ]` (exact fn of `d` in `Z/n` via `λ`)? Disjoint rings; a correlation would
be a genuine cross-ring leak, its absence a scoped null.

## Controls (fired) and the result

- **Correctness gate:** `scalar_mul(d)` reproduces the on-chain `(X,Y)` for sampled puzzle keys (asserted).
- **Firing control (strong plant, `b=ε⊕Bern(0.25)`, MUST fire):** fires on ALL arms — real-82
  `Îhat=0.161, p=5.3e-5`; constructed-full `p≈0`; constructed-matched `p≈0`. **Instrument alive.**
- **Matched null:** μ₆-canonicalize + orbit-dedup, then permute `ε` labels with `b_eps` fixed.
  For the 2×2 primary + plants this is computed as the **exact** fixed-margin hypergeometric p-value
  (the `≥10⁴`-permutation limit, no sampling). Dedup dropped 0 (real, full) / 879 (matched bit-bands) —
  machinery verified live.

**PRIMARY `Îhat(ε ; b_eps)` (df=1, verdict-driving):**

| arm | N (post-dedup) | Pr[flap] | Pr[ε=1] | Îhat (bits) | exact perm-p | MI_min(80%,df=1) | grade |
|---|---|---|---|---|---|---|---|
| real-82 (on-chain pubkeys) | 82 | 0.207 | 0.488 | 0.00131 | 0.788 | 0.1028 | scope NULL |
| constructed-full (uniform d) | 10000 | 0.256 | 0.499 | 0.00002 | 0.582 | 0.00084 | scope NULL |
| constructed-matched (puzzle bands) | 9121 | 0.252 | 0.504 | 0.00001 | 0.700 | 0.00092 | scope NULL |

**SECONDARY `Îhat(ε ; (j,s_neg,eps))` (18-cell, df=17, NOT verdict-driving):** all null — real
`Îhat=0.074, p=0.870` (below the df=17 plug-in bias ⇒ no positive); constructed `p=0.84 / 0.77`.

## Grade, power, scope (per PREREG §9 slot 3)

**`[VERIFIED-scope NULL]`.** **Object:** cross-channel dependence between the public coordinate flap
`b_eps(x([d]G))` and the single-key GLV coupling-carry bit `ε(d)`. **Class of observable:** their
mutual information (single-key decisional bit). **Power:** strong plant fires (MI≈0.19 detectable);
`MI_min` ranges 0.103 bits (N=82) → 8.4×10⁻⁴ bits (N=10⁴). **Scope:** secp256k1; `eps`/`s` per
`RESULT_linchpin_s_gate_v2.md`; `ε` via canonical `λ`, threshold `⌈n/2⌉`; both key sets.

**NOT A CLOSURE.** The Kohel–Shparlinski floor is `2^−128`; the best `MI_min` reached here is
`8.4×10⁻⁴ ≈ 2^−10.2` — a leak anywhere in the `[2^−128, 2^−10]` band (~2¹¹⁸ of unexamined dynamic
range) is invisible to this test. The verdict is: **no GROSS single-key flap→carry coupling at
`MI ≥ MI_min(N)`**; the sub-`MI_min` regime is untouched. Per the closure-burden rule, this scopes one
feature/target pair; it does not retire the GLV/CM joint-fiber avenue.

## What survives / the named next probe (drill ends in a probe, not a closure)

- **What the intersection idea correctly identified and what it hit:** both `F(P)` and `s(x)` ARE
  independently public-computable (the s-gate verified `s` to 2²⁵⁶). But two public functions of the
  **same single point** jointly form another public function of that point — a finer public partition,
  DLP-equivalent — so a *single-point* joint fiber cannot separate the lift. This drill confirms the
  decisional shadow of that fact: the finest public single-point flap bit is decoupled from the
  single-key carry bit at the gross level.
- **The one non-tautological realization of "joint fiber that separates lifts" — the named next probe
  (pre-register separately):** the **two-key / joint-carry** object `c_sum = c₁ + c₂ + ε` with a KNOWN
  `d₁` and UNKNOWN `d₂` (ARSENAL tool 7 / `OPEN_d2`). There the coupling carry `ε` is a function of the
  **sum** of two distinct points, NOT of either point alone, so it escapes the "public function of one
  `P`" redundancy that makes the single-key statistic empty. This is `T2a′` from
  `RESULT_linchpin_s_gate_v2.md`, still open; the unresolved input is whether the public Cap-Law
  `eps(x)` equals / constrains the LBE carry `ε` that tool 7 consumes (XVI.C: measuring the LBE carry
  from one point's public coords is circular).

**Owed gates:** `citation-verifier` on the Cap-Law `¾:⅛:⅛` / `eps=0⟺core` inputs before any grade
moves up on them; `compile-diff` if folded into a master. This result moves no grade up on a citation.

## stdout (reproduced)

```
===== ARM: real-82 (on-chain pubkeys) =====
  N(raw)=82  mu6-dropped=0  N(kept)=82
  b_eps: core=65 flap=17 (Pr[flap]=0.2073) | eps_carry: 0=42 1=40 (Pr[1]=0.4878)
  MI_min(80%pow,df=1)=0.10280 bits
  PLANTS  strong q=.25: Ihat=0.1607 p=5.29e-05 [FIRES]   floor q=.41: Ihat=0.0037 p=6.58e-01
  PRIMARY Ihat(carry;b_eps)=0.00131 bits  EXACT perm-p=0.78838  -> below power/null
  SECOND. Ihat(carry;(j,s,eps))=0.07357 bits  perm-p=0.86962 (43481/50000) [not verdict-driving]
===== ARM: constructed-full (uniform d, N=10000) =====
  N(raw)=10000  mu6-dropped=0  N(kept)=10000
  b_eps: core=7444 flap=2556 (Pr[flap]=0.2556) | eps_carry: 0=5013 1=4987 (Pr[1]=0.4987)
  MI_min(80%pow,df=1)=0.00084 bits
  PLANTS  strong q=.25: Ihat=0.1829 p=0.00e+00 [FIRES]   floor q=.41: Ihat=0.0290 p=3.19e-89
  PRIMARY Ihat(carry;b_eps)=0.00002 bits  EXACT perm-p=0.58219  -> below power/null
  SECOND. Ihat(carry;(j,s,eps))=0.00046 bits  perm-p=0.84039 (2521/3000)
===== ARM: constructed-matched (puzzle bit-bands, N=10000) =====
  N(raw)=10000  mu6-dropped=879  N(kept)=9121
  b_eps: core=6822 flap=2299 (Pr[flap]=0.2521) | eps_carry: 0=4521 1=4600 (Pr[1]=0.5043)
  MI_min(80%pow,df=1)=0.00092 bits
  PLANTS  strong q=.25: Ihat=0.1836 p=0.00e+00 [FIRES]   floor q=.41: Ihat=0.0236 p=9.26e-67
  PRIMARY Ihat(carry;b_eps)=0.00001 bits  EXACT perm-p=0.69960  -> below power/null
  SECOND. Ihat(carry;(j,s,eps))=0.00058 bits  perm-p=0.77041 (2311/3000)
```
