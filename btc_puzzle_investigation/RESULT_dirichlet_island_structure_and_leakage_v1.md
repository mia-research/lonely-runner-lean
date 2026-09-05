# RESULT — Dirichlet islands, re-thought: the real object (three-distance return set) + correct-target leakage test

**Grade: Part A `[VERIFIED — exact, real secp params]`; Part B `[EMPIRICAL — NULL at power, scale-resolved]`.**
Date 2026-08-17. Supersedes the *island* portion of the earlier work: `RESULT_public_feature_dmodq_battery_v1`
tested public-feature → `d mod q`, which is the wrong object for an island (a residue, not a
rational-approximation/position property). This file tests the correct island objects. It does NOT edit any
master; it accumulates toward a future v13. Reproduction: `scratchpad/islands_rethink.py`,
`islands_leak.py`, `islands_leak_control.py`, `islands_scale.py`. Signal path exact `int`; MI ranked only
against a matched permutation null (no-float rule).

## Re-framing (the think-again)
A "Dirichlet island" `d_q = 2^(b−1)(1 ± 1/q)` is a **good rational approximation** of `d` — a
position/magnitude property, not a residue class. Three distinct in-scope objects, none = `d mod q`:
- **(A) return-time island:** `{d ∈ I : λd mod n ∈ I}` — scalars whose GLV-image `φ(P)=[λ]P` lands back in
  the interval. A **three-distance / Bohr set** whose gaps are fixed by `CF(λ/n)`.
- **(B) best-approximation island:** `min_{q≤Q}|qd mod n|` small — `d` close to a small-denominator rational.
- **(C) lift/carry rounding resonances** (untested here; lives in the existing carry object).

## Part A — the REAL secp island structure (exact, novel characterization)
`λ` = primitive cube root of unity mod `n` (verified `λ²+λ+1≡0`). `CF(λ/n) = [0,1,2,14,3,2,1,7,1,2,8,…]`.
The return-time island set for the puzzle interval `I=[2^(b−1),2^b)`:

| puzzle | `|I|` | `n/|I|` | E[#islands in I] | structure |
|---|---|---|---|---|
| 135 | 2^134 | ~2^121 | **2^12** | three-distance set, ≤3 gap sizes from `CF(λ/n)` |
| 140 | 2^139 | ~2^116 | **2^22** | " |
| 145 | 2^144 | ~2^111 | **2^32** | " |

- The island set is **publicly computable** (λ, n, I all public) — an explicit, structured, small subset of `I`.
- **But membership of the SECRET `d`** in it is `λd mod n ∈ I` = the discrete log of the public point `φ(P)`
  lying in `I` — a **DLP question**. No reduction unless `P` leaks island-membership. That is Part B.

## Part B — does `P` leak island-membership? (correct targets, firing control, scale resolution)
- **(A) return-time target `λd mod n ∈ [0,|I|)`: clean NULL** — 0/4 curves fire any of 9 public features of
  `P`/`φ(P)` (matched-perm p<0.02); firing control (35%-noised island vs island) FIRES p=0.001.
- **(B) best-approximation target: apparent signal → resolved to a finite-size artifact.**
  - Low-card φ-features fired on ~2/6 curves with real p≈0.003 while the **cardinality-matched scramble did
    NOT fire** (p≈0.5–0.8) — i.e. the firing instances were *real x-relations*, not MI-bias. Not dismissable
    as cardinality noise; demanded a scale test.
  - **Mechanism:** `good-approx(d)` with denominator `q` ⟺ `[q]P ≈ [small]G` (P a small-rational multiple),
    a measure ~`Q²/n` subset that is **publicly checkable by baby-steps and RECOVERS `d` when it hits** —
    but covers negligibly many keys at scale. At small `n` a loose threshold (`n/40`) makes that subset ~30%
    of keys, so its special coordinates couple to cheap features.
  - **Decisive scale test (constant-15% marginal target, n=379→6163):** the correlation **VANISHES** — real
    p for `x_phi%6` = 0.43,0.43,0.33,0.52,0.38,0.30,0.16 (no trend to 0; real not below scramble). Holding the
    marginal fixed removes the threshold coupling and the signal is gone. **Finite-size, confirmed.**

## Grade & scope
- **Part A:** exact structural characterization of the real secp island object — a three-distance return set.
  NOT a leak; a publicly-computable set whose secret-membership is DLP-hard.
- **Part B:** **NULL at power** that any tested public feature of `P`/`φ(P)` leaks island-membership (return
  or best-approx), scale-resolved (the one lead washed out under a constant-marginal target). Firing control
  fires throughout. Scope: 9 features, prime-order CM curves `n≤6163`, `Q≤12`.
- **Held to scope, not enlarged:** the general "any cheap public function" absence is DLP-adjacent and
  unprovable by sampling (unchanged).

## The genuinely OPEN direction this surfaced (NOT closed, NOT tested here)
The **interval-DLP-with-endomorphism** lever: the ×λ return set has real three-distance structure from
`CF(λ/n)`. The audit dismissed it ("orbit-mates leave the interval"), but Galbraith–Ruprai-type interval-DLP
speedups use the automorphism **symmetry**, not orbit-mates-in-interval (negation already gives √2 for
symmetric intervals). Whether the order-3 `λ` geometry permits an interval **folding**/√3-type speedup for
the puzzle interval is **unresolved** — a real cryptanalytic question, flagged as the next probe, not an
avenue to close by assertion.
