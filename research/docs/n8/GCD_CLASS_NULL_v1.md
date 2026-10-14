# The Dual φ(n) Law does not transfer to `u(E)` — and the primitivity filter is unsound

2026-09-11. Script `experiments/n8/ok_gcd_class_v1.py`. Pre-registered before the run as
`PREREG_GCD_CLASS_INVARIANCE_v1` (spec by `experiment-designer`, context-isolated). Exact
`Fraction`; all controls fired.

Provenance: GECT v5.0 §"The Dual φ(n) Relation" states `τ_collapse = r/(nδ)` for
`gcd(r,n) ≠ 1`, runners collapsing onto `n/gcd(r,n)` positions, graded there **"Empirically
validated for n=12, requires extended testing."** The n=8 extension is the transfer tested
here.

---

## 0. A targeting error, corrected before the run  `[quoted]`

The test was first aimed at `u(E_non)`, following `CASE_TREE_AUDIT_v1.md` §6:

> "**Bound `u(E_non)` for an arbitrary set of `≤ 6` non-divisible speeds.** Shape-free,
> subsumes all 27 shapes and both open leaves."

That target was already dead. `U_REFORMULATION_v2.md` §2, written **twelve minutes later**
the same morning (07:22 → 07:34), grades it `[PROVED — counterexample]`:

> "The split `u(E_non) + |⋃B_m| < 1` is lossy at **every** `|E_div|`, not just the hard leaf.
> Separating the divisible runners from the rest is the error; §1 keeps them together."

So the test was retargeted onto `u(E)` for the **full** tuple, which `U_REFORMULATION_v2` §1
proves is the whole of n=8 outside Case 1. Recorded because reading the earlier document and
not the later one is the error, not the hypothesis.

## 1. The hypotheses

- **R0 (the GECT transfer).** `u(E)` depends only on the multiset `{gcd(e,8) : e ∈ E}`.
- **R1 (the rung that would have mattered).** `u(E)` depends only on `{e mod 8 : e ∈ E}`.

R1 was pre-registered as the valuable one: it has **finitely many classes for unbounded
speeds**, so a finite table would bound `u(E) < 1` outright.

## 2. Controls — all fired  `[VERIFIED — exact]`

| control | result |
|---|---|
| **P1** planted: the three published argmaxes of `U_REFORMULATION_v2` §2 | `u(1,4,12,20) = 1/3`, `u(1,3,4,5,7) = 9/14`, `u(1,4,5,6,7,11) = 125/154` — all exact |
| **C3** independent bitmask implementation vs the `ok_umax_v1` oracle | 1470 sets, **0** mismatches |
| **C2** odd dilation `λ ∈ {3,5,7,9}` | **0/480** mismatches — invariant |
| **C8** even dilation `λ ∈ {2,4,6}` | **317/360** mismatches — **not** invariant |

## 3. Both hypotheses are false  `[PROVED — counterexample]`

A counterexample is a proof, not a statistic: one unequal pair inside a class refutes a
∀-statement. Census over `[1..20]`, no primitivity filter.

| `k` | rung | classes | live | with ≥2 distinct `u` | minimal witness |
|---|---|---|---|---|---|
| 3 | **R0** | 19 | 13 | 4 | `u(1,4,12) = 0` vs `u(1,4,20) = 1/5`, class `(1,4,4)` |
| 3 | **R1** | 116 | 45 | 10 | `u(4,6,14) = 0` vs `u(6,14,20) = 13/70`, class `(4,6,6)` |
| 4 | R0 | 30 | 27 | 13 | `u(1,3,4,12) = 0` vs `u(1,3,4,20) = 1/5` |
| 4 | R1 | 294 | 211 | 105 | `u(1,3,9,17) = 0` vs `u(1,9,17,19) = 10/323` |
| 5 | R0 | 42 | 42 | 27 | `u(1,3,4,5,12) = 0` vs `u(1,3,4,5,20) = 1/5` |
| 5 | R1 | 616 | 613 | 422 | `u(4,6,8,14,16) = 3/8` vs `u(6,8,14,16,20) = 15/28` |

**R0 is rejected**, so the Dual φ(n) Law's "structure is determined by `gcd(r,n)`" does not
transfer to `u`. **R1 is rejected**, so there is no finite bound table on residues mod 8
either — `u(E)` genuinely depends on the speeds and not only on their classes mod 8. The
failing axiom is stateable: `X(x)` reads `e` through the pair `(e mod 8, ⌊ex⌋ mod 8)`, and
the second coordinate depends on `e` itself, not on any residue of it.

**Scope.** Rejection is unconditional — the witnesses are exact and exhibited. No claim is
made that some *other* coarsening fails; rungs above R1 (relation multiset, mod 16, odd
dilation classes) are untested.

## 4. A defect in our own code  `[PROVED — counterexample]`

`experiments/n8/ok_umax_v1.py`, docstring:

> "`u` is a DILATION INVARIANT (`u(lambda E) = u(E)`), so only primitive `E_non` matter."

and acting on it, lines 62 and 73: `if reduce(gcd,E)!=1: continue`.

**The justification is false for even `λ`.** The invariance argument needs `λr mod 8` to
exhaust `ℤ/8`, which holds iff `λ` is odd. Witness: `u(1,6,10) = 0` but `u(2,12,20) = 2/15`.
C8 above: 317 of 360 even dilates change `u`.

**Consequence, measured.** Maxima over `E_non ⊆ [1..20]`, `8 ∤ e`:

| `k` | primitive max (quoted) | **imprimitive max** | overall max |
|---|---|---|---|
| 4 | `1/3` at `(1,4,12,20)` | **`16/35`** at `(2,6,10,14)` | `16/35` |
| 5 | `9/14` at `(1,3,4,5,7)` | **`24/35`** at `(2,4,6,10,14)` | `24/35` |
| 6 | `125/154` at `(1,4,5,6,7,11)` | `4/5` at `(2,4,6,10,12,14)` | `125/154` |

**Impact, stated narrowly.** `U_REFORMULATION_v2.md` §2 labels its table "Exact maxima over
**primitive** `E_non`", so **that document is correctly scoped and its numbers reproduce
exactly** (P1). What is wrong is the *reason* the code gives for the restriction, and hence
any future use of `ok_umax_v1` as a maximiser over all `E_non`. §2's conclusion is
unaffected and in fact reinforced: the true maxima are larger, so the split fails harder.

## 5. What survives

The transfer fails for a stateable reason (§3), which is the useful output. Nothing about
GECT's Dual φ(n) Law at `n = 12` is touched — that is a statement about collapse positions
for AP speeds, and `u(E)` is a measure of a covering set for integer speeds. **The two are
not the same object**, and this is a null on the transfer, not on the law.

Separately, `QUARTER_DICHOTOMY_v1.md` §1 remains a `[PROVED]` n=8 statement whose strata are
indexed by `gcd(e,8) ∈ {1,2,4,8}` — so the gcd stratification *is* the right frame for the
collapse geometry. It is `u`, a measure, that is not a function of it.

## 6. Ledger

`[PROVED — counterexample]` §3, both R0 and R1 rejected, witnesses exhibited exactly.
`[PROVED — counterexample]` §4, the even-dilation defect and its measured consequence.
`[VERIFIED — exact]` §2, all four controls; §4's maxima table.
`[CORRECTED]` §0, the target: `CASE_TREE_AUDIT_v1` §6's recommendation was superseded by
`U_REFORMULATION_v2` §2 the same morning.
`[UNTESTED]` rungs above R1.

`n = 8` is **not proved**, and nothing here moves any grade.
