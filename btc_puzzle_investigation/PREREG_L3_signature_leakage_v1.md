# PREREG — does the arithmetic signature of C_a leak the parameter `a`?

Pre-registered BEFORE seeing the counts. Gate run inline (experiment-designer
unavailable this turn — owed; conditions §2a: tagged, self-audit below, no grade
promotion off this alone).

## Question
The idea under test: the μ₃ / `L^(3)`-perfect-square structure of `C_a : w^4=x^3+a`
is a *lever* — its arithmetic reveals the parameter `a`. Reframed as leakage:
**how many bits of `a` are recoverable from the full Frobenius signature of `C_a`?**

## Feature / target (disjoint-recovery framing)
- **Target** = `a ∈ F_p^*` (the "secret" parameter).
- **Feature** = the full genus-3 Frobenius polynomial `L_a(T)` of `C_a` (6 integer
  coefficients) — the maximal arithmetic observable, superset of the μ₃/L^(3) data.
- Map is `a ↦ L_a`; the leakage question is whether it is many-to-one (no lever)
  or effectively invertible (lever). Recoverable info = `H(a) − H(a | L_a)`.

## Statistic
`N_sig(p)` = number of DISTINCT signatures `L_a` as `a` ranges over `F_p^*`.
Recoverable bits `≤ log2(N_sig)`. Fraction of secret pinned = `log2(N_sig)/log2(p−1)`.
Also report max class size and `H(a | L_a)` (bits).

## Controls that MUST fire (else harness is broken)
- **Positive (leak must show):** feature = `a` itself. Expect `N_sig = p−1`,
  fraction = 1.0. If not, the counter cannot see a leak → abort.
- **Negative (bounded must show bounded):** feature = `a mod 12`. Expect
  `N_sig ≤ 12`, fraction → 0 as `p` grows. If not, the counter inflates → abort.

## Power / scaling (the decisive axis)
Sweep `p ≡ 7 mod 12` across ~2 orders of magnitude (7 … ~2000). The two hypotheses
give DIFFERENT scaling and the sweep discriminates them:
- **H0 (no lever):** `N_sig` bounded by a small constant (predicted `≤ 12`, tied to
  `F_p^*/(F_p^*)^12`), flat in `p` ⇒ recoverable bits = O(1) ⇒ at 256 bits, a
  vanishing fraction, and those bits are the forward-computable residue symbols of `a`.
- **H1 (lever):** `N_sig` grows with `p` (∝ `p`, `√p`, or `log`-many bits that scale)
  ⇒ signature constrains `a` at scale.

## Pre-committed prediction (mine, before running)
H0. `N_sig` flat ≈ small constant (I expect exactly the number of `(cubic,quartic)`
residue classes, ~12), fraction → 0. **Falsifier: `N_sig` rises with `p`** on the sweep
(log-log slope distinguishable from 0). If it rises, the idea survives as a lever and
I was wrong.

## Scope (what this does NOT test)
Only information in the Frobenius signature of the *family* `C_a` about the *parameter*
`a`. It does not test the fixed-curve secp ECDLP (a different object: `Q=kG`, one curve),
nor non-arithmetic side channels. A null here bounds this channel only — conditional on
method + this observable.
