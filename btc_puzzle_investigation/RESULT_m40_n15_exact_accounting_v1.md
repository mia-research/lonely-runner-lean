# RESULT — M40 sharpened to μ₆ and its marginal/pairwise exploitability accounted exactly; N15's joint-tuple budget computed exactly (8 primes + secp)

**Date 2026-08-21. Grade: `[VERIFIED — exact, total enumeration]`** for every number below (counts exact;
floats only to display entropies). Deterministic first pass per `ROADMAP_REDIRECT_v3` (no leakage claim).
Scripts: `m40_n15_exact_accounting_v1.py` (+ `.log`), `m40_n15_addendum_decomp_secp_v1.py` (+ `.log`).
These are the **first statistics on record projecting onto M40's forced subspace** (its source:
"No statistic in the record projects onto it. It is not retired.").

## A — M40 (the forced μ₃-invariant sign sequence), three exact findings

Object: `h[d] = χ₂(y_{[d]G})`, `d ∈ [0,n)`, `y²=x³+7`, `n` prime; primes 43, 67, 79, 127, 163, 211
(p≡7 mod 12), 349, 61-anomalous (p≡1 mod 12).

**A1 — SHARPENED: the free-sign count is (n−1)/6, not (n−1)/3.** Beyond the measured μ₃-constancy
`h[λd]=h[d]` (re-verified 8/8), the sequence obeys the **sign symmetry** `h[−d] = χ₂(−1)·h[d]` (verified
8/8, both arms). Hence `h` is determined by one sign per **μ₆-orbit** {±d, ±λd, ±λ²d}: anti-monochromatic
at p≡3 mod 4, monochromatic at p≡1 mod 4 — either way **exactly (n−1)/6 free signs** (counted exactly,
8/8, both arms). The forced reduction in the quadratic-character sequence along the group is **6×**, not
M40's stated 3× — and the mechanism is named: the same χ₂(−1) that governs M4/closure/k=3-channel parity.

**A2 — Marginal exploitability: exactly 1 bit, provably.** At p≡3 mod 4 the antisymmetry pairs every `d`
with `−d` at opposite signs ⇒ the two sign classes are **exactly balanced** (verified: 15/15, 39/39,
33/33, 63/63, 69/69, 99/99) ⇒ `H(f) = 1.0000` exactly and the posterior worth of observing `f(D)` is
exactly **1 bit** — no more than any balanced public bit. The 6× reduction constrains the *labeling's*
complexity, not `D`'s posterior. (p≡1 mod 4: mild imbalance — 0.84/0.74 bits.) The "√3-worth" reading
(conflating the sequence collapse with a search-space collapse) is now refuted by exact accounting, at
the information level, at these scopes.

**A3 — Pairwise group-law coupling: entirely the forced anti-diagonal.** The exact pairwise mutual
information `MI(f(d₁+d₂); (f(d₁), f(d₂)))` over ALL pairs is nonzero but O(1/n) (0.036 @ n=31 → 0.0033 @
n=313). Decomposition: **off the anti-diagonal `d₁+d₂≡0` it is 0.0000–0.0017 bits at every prime (flat,
20× below 1/n)**. The whole signal is the trivial forcing: at `d₁+d₂≡0`, `f₂=−f₁` exactly (p≡3 mod 4)
and the sum's sign class is deterministic. **Scoped closure:** on the tested scopes (8 primes ≤ 349,
total enumeration, zero sampling error), the forced subspace carries **no pairwise group-law coupling
beyond the named forcing**. Open residue: higher-order (triple) couplings — the E3-family multiset nulls
(N30) already bound one neighboring class.

## B — N15's joint-tuple budget, exact

The public readout tuple of `Q=[d]G` — `e` (Eisenstein flap class {0,+,−}), sextant (6), `s`-band (3),
`y`-parity = `f` — is a deterministic function of `d`, so `MI(d; tuple) = H(tuple)` exactly:

| prime | H(tuple) | synergy vs ΣH(parts) | max-cell pruning |
|---|---|---|---|
| 43–211 (6 primes, ≡7 arm) | 3.50–4.59 bits | **negative everywhere** (−0.11…−1.32) | 2.6–3.3 bits |
| 349, 61 (≡1 arm) | 4.08 / 3.61 bits | −1.04 / −0.97 | 2.8 / 2.3 bits |
| **secp (N=20 000 exact-feature sample)** | **4.41 bits** | **−1.11 (redundant)** | — |

**Reading (scoped):** the joint tuple's entire determined content is an **O(1) ≈ 4.4-bit** pruning budget
at secp — sub-additive at every scope tested (features overlap; no joint-beyond-sum structure; no cell
explosion: 38 occupied cells of 108). Combined with the record's 0.033-bit cheap-filter bound, the
deterministic content of THIS readout class is now exactly accounted: ~4.4 free bits, no synergy, no
cheap arithmetic alignment. **N15's open residue is unchanged and narrower:** other readout classes
(non-tuple-style), and any filter aligning cells with d-arithmetic — this run claims nothing about those.

## Flagged observation — RESOLVED same day (see `NOTE_eis_nonequidist_resolved_v1.md`)

Real `x([d]G)` coordinates at secp measured ~3–5% off the continuum rates under MY lift convention
(core 0.771 vs ¾, band-0 0.659 vs 0.680). **Resolution: my `±2` min-max square-centering is a
nonstandard centering with a p-dependent bias (~2.5pt); in the canonical convention
(`lift_uv`+`strip_pred` ⟺ `build.eps`) the curve-vs-uniform delta at secp is −0.0002 = 0.05σ — zero.**
The real small-p support-conditioning effect decays Weil-like (~p^{−1/2}) and does not reach secp.
No secp-scale arithmetic signature; the M40/N15 conclusions above are convention-robust (tuple budget
shifts ≲0.06 bits).

## Burden-on-closure statement (per CLAUDE.md)

Closed here, with power and scope: (i) M40's *marginal* exploitability at the information level — exact,
8 primes, both arms, mechanism proved (antisymmetry balance); (ii) M40's *pairwise* group-law coupling
beyond the named anti-diagonal forcing — exact total enumeration, 8 primes ≤ 349, decaying below 1/n.
NOT closed: M40 at higher order; N15 for readout classes beyond this tuple; any computational (as opposed
to informational) exploitation; anything at secp beyond the sampled budget rates.
