# Findings v15 — phase alignment is the ONLY axis (Wiener norm was a red herring)

**Date:** 2026-07-16 · `aligned_scaling_and_gap_v1.py`, `flap_sign_parity_v1.py`.
Follows v14 (the leak = a phase-aligned readout; barrier is computability, not information).

---

## ★ CORRECTION to v14's "next step #3" — the ‖F‖_A gap is NOT the door

v14 said: *"the `‖F‖_A ≳ √p` gap in the closure theorem — now identifiably the only analytic
door left open."* **That framing is wrong.**

**[PROVED]** For any F, Cauchy–Schwarz + Parseval give `‖F‖_A ≤ √p·‖F‖_∞`, with equality iff
`|F̂(b)|` is constant (flat spectrum). So the "gap" is not an unpatched hole — it is the
**extremal case**. Fine. But the measurement kills the framing:

| readout | ‖F‖_A/‖F‖_∞ | % of √p ceiling | leaks? |
|---|---|---|---|
| **χ₂(x)** | 32.405 | **100.0 %** | **NO** (mixed char-sum bound; hybrid sum ≈2√p) |
| random ±1 | 28.616 | 88.3 % | no |
| **ALIGNED** | 11.607 | **35.8 %** | **YES (28× noise, v14)** |
| ε flap indicator | 6.448 | 19.9 % | no (closure-covered) |
| 1[x<p/2] | 3.195 | 9.9 % | no |

**χ₂ saturates the ceiling exactly (Gauss sums ⇒ `|χ̂₂(b)|=1/√p` ∀b) and provably does NOT
leak. The aligned readout is at 36 % of the ceiling and DOES leak.** So high Wiener norm is
**neither necessary nor sufficient** for leakage. (The aligned readout misses the ceiling by
exactly `√(log p)`: its sup-norm is `√(p log p)`, not `√p`.)

> **Conclusion: ‖F‖_A is a red herring.** It only ever supplied a *lossy sufficient* condition
> for the closure bound to bite. **The sole axis that determines leakage is PHASE ALIGNMENT
> with `T(a,b)`.** This sharpens v14; it does not extend it.

---

## [PROVED + VERIFIED, exact] The complete known symmetry group of the phase pattern

At p=1051, n=1093 (max |diff| ≈ 5e-14 = roundoff):

| symmetry | origin |
|---|---|
| `T(−a,b) = T(a,b)` | `x_d` is EVEN in d |
| `T(a,−b) = conj T(a,b)` | conjugation |
| `T(a,b) = T(aλ, bβ)` | GLV μ₃ (`d↦λd` bijection, `x_d↦βx_d`) |

This is the **entire computable phase structure we know**. λ=151, β=870.

## [EMPIRICAL] Hunt beyond the group — principled candidates, all null

CM/Frobenius-derived (not ad-hoc `a·b` guesses), uniform null ≈ 0.00093:

| candidate | \|mean e^{i(argT − 2πg/k)}\| |
|---|---|
| χ₂(b) | 0.00014 |
| χ₃(b) phase | 0.00000 |
| ε(b) flap | 0.00026 |
| lift-norm(b) | 0.00069 |
| a mod 3 | 0.00125 |
| λ-orbit index of a | 0.00028 |

All at the null ⇒ **no phase pattern beyond the symmetry group**. Scope: 6 candidates, one
prime — a real improvement on v14's 3 ad-hoc guesses, still **does not close** the question.

## [PARTIAL — NOT confirmed] Scaling of the aligned leak

`ratio·√(ln p)` over p=211…577: 0.849, 0.879, 0.824, 0.833, 0.747, **0.726** — mean 0.810,
sd 0.055, but **drifting monotonically downward**, not flat. `log p` moves only 19 % across
this range. So the `1/√log p` model is *consistent but unconfirmed*, and the true decay may be
somewhat faster. **The "only logarithmic decay at secp (~c/13)" claim from v14 remains an
ESTIMATE.** (The script's "CONFIRMED" print was too generous — corrected here.)

## [From `flap_sign_parity_v1.py`] The two intertwining Z/2's — classified, not exploitable

User's reframe (± flaps vs x-even/y-odd, with Frobenius/slippage as *reference*, not
expansion point) — verified exactly:
- `σ(−x) = −σ(x)`: the flap sign flips under **FIELD** negation (a lift symmetry, `eis(−x)=−eis(x)`).
- `x([−d]G)=x([d]G)` even, `y([−d]G)=−y([d]G)` odd: **CURVE** negation.
- ⇒ σ is EVEN in d, `s_y` is ODD in d — **two Z/2's under DIFFERENT involutions**; product odd.
- **± flap counts are EXACTLY equal** (0.0995/0.0995 at p=211) — forced by `σ(−x)=−σ(x)` and
  F_p\{0} being negation-closed. The "one positive, one negative" is an exact symmetry.
- Basis-orientation gotcha: the cap is `|u−v|>½` at p=211 (matches ε 210/210) but `|u+v|>½` at
  p=1009 — **the reduced-basis orientation flips per prime**; detect it against ε, don't assume.

**What the reference point buys (this is the payoff):** it *classifies* both parts without
experiment. σ is a lattice-region indicator of x ⇒ low Wiener norm (Lemma W) ⇒ **closure
covers it ⇒ provably cannot leak**. `s_y` is the **known free parity bit** (d vs n−d, readable
off any compressed pubkey, ~1 bit, already in the ledger). The only genuinely new object is the
**mix σ·s_y** — odd, CM-derived, outside closure's stated scope (closure covers `F(x([d]G))`;
`s_y` is not a function of x). It tests **misaligned** (0.093 vs noise-floor baseline 0.231).

---

## Where this leaves it

- The leak = phase alignment with `T`. **Nothing else is the axis.** (v15 correction.)
- Known computable phase structure: exactly the 3-element symmetry group. Not enough.
- 9 principled candidates across v14+v15: all null. Scoped — the space of computable
  functions is vast; this closes nothing.
- **The live, un-bounded corner** (exposed by the user's reframe): a **y-twisted `T`**,
  `Σ_d e_p(b x_d)·s_y(d)·e_n(ad)`. Closure covers x-readouts precisely because `T(a,b)` is an
  x-object; the y-parity sits outside it and I know of **no bound** for the twisted sum. That
  is the next object.
