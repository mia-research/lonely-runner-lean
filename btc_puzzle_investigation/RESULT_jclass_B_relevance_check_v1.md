# RESULT — queue item B: the relevance check answers it, and B should be RETIRED in the form proposed

**Date:** 2026-08-01. **Item:** B of `NEXT_SESSION_PROMPT_2026-08-01_v2.md`, which directs:
*"Decide whether a cross-`j` contrast still discriminates against the surviving mechanism before
spending on it — if it does not, retire B explicitly rather than leaving it dangling."*
**Route:** the reduction in `RESULT_120deg_certificate_regrade_v1.md` §5.
**Scripts:** `jclass_e2_relation_probe_v1.py` / `_v2.py` (+ logs, JSONs). Both pass `check_no_float.py`.

---

## 1. Verdict

> **Retire B in the form proposed.** The `ζ₃` lock is **present on curves whose `Aut` lacks `μ₃`**.
> A cross-`j` Aut-contrast therefore cannot discriminate: its necessary condition is satisfied by the
> arm that was supposed to fail.

B was built to test a necessary condition — *if the mechanism routes the `ζ₃` through the curve's
automorphism/CM structure, the lock must vanish when `μ₃ ⊄ Aut`.* Measured directly, it does not
vanish. **30/30** curves with `j ∉ {0, 1728}` (so `Aut(E_{F̄}) = μ₂`, no `μ₃`) satisfy the relation
exactly, across both `χ₂(−1)` branches.

## 2. What was measured

Per §5 of the regrade, the Aut question reduces from the `deg gcd` census (which needs cells,
`ℓ`-selection, prime order) to **one integer per curve**:

- **R1 (definitional):** is `f[d] = h₂[d] − (h₁∗h₁)[d]` **constant off `d = 0`**? If yes the object
  B needs exists on that curve — `V₂(a) − V₁(a)²` is a single integer independent of `a`.
- **R2 (mechanism):** does that integer equal `−2·χ₂(−1)·p`?

| arm | `Aut` | curves | R1 | R2 |
|---|---|---|---|---|
| `j = 0`, odd `n` — **positive control** | `μ₆ ⊃ μ₃` | 6 | 6/6 | 6/6 |
| generic `j`, odd `n`, `p ≡ 3 mod 4` | `μ₂` | 18 | **18/18** | **18/18** |
| generic `j`, odd `n`, `p ≡ 1 mod 4` | `μ₂` | 12 | **12/12** | **12/12** |
| generic `j`, **even** `n` | `μ₂` | 12 | **0/12** | 0/12 |
| `j = 1728`, even `n` (forced) | `μ₄` | 6 | **0/6** | 0/6 |

**The positive control is load-bearing and ordered first:** this is new code, generalized to
`y² = x³+Ax+B`, and it reproduces the established `j=0` result exactly (`f` constant, `f[0]−c =
−2χ₂(−1)p`) before any other arm runs. The run halts if it fails.

**The firing control is the even-`n` arm:** 0/18 across `j=1728` and generic `j`. The statistic *can*
fail and does — R1/R2 are not passing on everything. Without this the 30/30 would be uninterpretable.

## 3. The confounder, and why v1's result did not mean what it looked like

v1 read R1 6/6 at `j=0`, 0/6 at `j=1728`, 2/6 at generic `j` — which looks like an Aut effect. It is
not. **Every R1 failure had even `n`; every R1 success had odd `n`.** `j` and parity of `n` were
perfectly confounded, because `j=1728` has rational 2-torsion at `(0,0)` and so **always** has even
`n`, while the sampled `j=0` curves happened all to be odd.

v2 broke the confound by sampling generic-`j` curves at both parities. R1 tracks **parity of `n`**,
with no residual `j` effect: generic-`j` odd-`n` passes 30/30, generic-`j` even-`n` fails 12/12.

**The one cell that would discriminate the other way — `j=0`, even `n`, cyclic — is empty by a
theorem, not by sampling.** At `p ≡ 1 mod 3`, `μ₃ ⊂ F_p`, so `x³+B` has 0 or 3 roots; even `n` forces
a root, hence all three, hence `E[2] ⊂ E(F_p)`, hence `ℤ/2×ℤ/2` — never cyclic. Verified: **0 of 228**
even-`n` `j=0` curves over the six primes are cyclic. So H_j cannot be rescued from that cell; it is
refuted on the generic-`j` odd-`n` cell alone, where it predicted failure and got 30/30.

## 4. ⚠ The larger implication — flagged, NOT graded

R2 holding at `Aut = μ₂` says more than "B is retired". It says the relation
`V₂ − V₁² = −2χ₂(−1)p` — which by
`ANALYSIS_120deg_exact_factorization_certificate_v1.md` §1 is **equivalent to the 120° pairing** —
may be a **general fact about odd-order cyclic elliptic curves**, carrying no information specific to
`j = 0`, to `μ₃`, or to secp256k1.

**This is the deflationary reading and it must be tested as hard as a positive would be.**
Stated at the closure-grade bar (object / class / power / scope) as far as the evidence goes:

- **Object:** `f[d] = h₂[d] − (h₁∗h₁)[d]` and the derived `V₂ − V₁²`, on `y²=x³+Ax+B` over `F_p`
  with `E(F_p)` cyclic of odd order.
- **Observed:** `f` constant off `0` and `V₂−V₁² = −2χ₂(−1)p` exactly, 30/30, `j ∉ {0,1728}`.
- **Power:** exact and deterministic — a failure shows as `distinct > 1` or a wrong integer; the
  even-`n` arm demonstrates both failure modes fire.
- **Scope:** 12 primes, `p ≤ 211`, **all `p ≡ 1 mod 3`**; `n` odd and cyclic; 2 curves per prime.
  Not tested: `p ≢ 1 mod 3`, large `p`, non-cyclic `n`.

**GRADE: `[PROVISIONAL — experiment-designer pre-registration OWED]`.** Per `CLAUDE.md` §2 a
mechanism sweep requires the gate *before* running. This run was designed and pre-committed as a
**definitional/confounder check on R1** — R2 was declared descriptive-only in the script docstring
before execution — and R2 came along with it. Per §2a: the tag is in the grade slot; the uncovered
frame layers are **object/disjointness adequacy** and **scope** (I chose the curve sample myself,
`A=1` in most cells, first-fit rather than randomized); the gate is recorded as owed as of
2026-08-01; **no grade promotion until it clears.**

**What is NOT established.** That the *whole* 120° law is generic. §1's factorization needs
`e₃ = χ₂(−1)p·e₁` and `e₄ = p²` alongside the `e₂` relation, and those are **not** re-measured here at
generic `j` (they need `V₃, V₄`, i.e. `O(p³)/O(p⁴)`). Their derivation from `|α|²=p` plus the closure
contains no `j=0` hypothesis on its face — but "on its face" is not a check. **Until that is settled
the deflation is a strong lead, not a result**, and the `j=0` results it would deflate stand.

## 5. Consequences for the record

- **Item B: RETIRED** in the cross-`j` Aut-contrast form. Its revival plan (cofactor availability,
  `χ₂(−A)` cyclic branch, measuring `b₁` at `p ≡ 1 mod 4`) is moot — that engineering existed to
  build arms for a contrast whose premise is now measured false. The v2 defect list (F-EMPTY
  ordering etc.) does not need to be worked through.
- **`prime order` was never the requirement.** The operative condition is **odd cyclic `n`**. Curves
  with `n = 87, 69, 123, 111, 171, 155, 175, 201, 189, 121, 85, 55` — all composite — satisfy R1 and
  R2. The prompt's "drop the prime-order requirement" instinct was right, for a sharper reason than
  it gave.
- **`j = 1728` is structurally untestable** by this statistic, not merely inconvenient: rational
  2-torsion forces even `n`, and even `n` fails R1. No sampling effort fixes this.
- The next question is not another arm. It is **why odd `n` is the hinge** — the even-`n` failure is
  a characterization (R1's `distinct` count grows with `p`: 11→28), not a null.
