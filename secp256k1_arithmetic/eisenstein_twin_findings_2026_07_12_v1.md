# Eisenstein twin primes — density is Bateman–Horn (Threads 1–3, v1, 2026-07-12)

**Scope.** Answers the "NEW THREADS" agenda's Thread 1 (Eisenstein twin prime
density), Thread 3 (is `27M²` special to `b=7`), and situates Thread 2/4 against
existing findings. Exact-integer arithmetic throughout; floats appear only in the
heuristic density value and reported ratios, never in a primality decision.
Scripts: `eisenstein_twin_density_v1.py`, `twin_thread3_27_universality_v1.py`.

**Epistemic tags:** [found] = supported by the stated computation;
[known] = restates a documented fact; [inference] = interpretation.

---

## 0. What the object actually is  [found + known]

A "primary Eisenstein twin prime" (primary `π=a+bω` with `N(π)` and `N(π−1)`
both prime) is **exactly the amicable / prime-order condition already in
KNOWN_FACTS §4**: because `π_n = π_p − 1`, "`N(π)` and `N(π−1)` both prime" is
"`p` and `n` both prime" = a prime-order `j=0` curve. The forms are
`F(a,b)=a²−ab+b²=p` and `G(a,b)=(a−1)²−(a−1)b+b²=n`, both binary quadratics of
discriminant `−3`. So the thread's terminology is new; the object is documented.

## 1. The density is fully Bateman–Horn — not an anomalous rarity  [found]

Over the box `a,b ∈ [−500,500]` (10⁶ lattice points), exact sieve to norm 750001:
- `#{F prime}` = 143 514; `#{F & G both prime}` = 12 840.
- Bateman–Horn prediction `E = 𝔖 · Σ_{F,G≥2} 1/(ln F·ln G)`, with singular series
  `𝔖 = ∏_q (1−ν(q)/q²)/(1−1/q)²`, `ν(q)=#{(a,b) mod q: F·G≡0}`.
  Analytic `ν`: `ν(2)=2, ν(3)=6, ν(q)=4q−4` for `q≡1 mod 3`, `ν(q)=2` for
  `q≡2 mod 3` (verified against brute force for all primes `<60`).
- `𝔖 = 1.6693`, `E = 12 872`. **observed/predicted = 0.9975** (0.25%).

⇒ [found] The joint primality of `p` and `n` is a positive-density event
described to sub-percent accuracy by Bateman–Horn. There is **no rarity beyond
"n prime given p prime."**

**Conditional constant.** `κ = P(n prime | p prime)·ln(N)` is scale-stable across
3–6 digit norms (0.946, 0.959, 0.973, 1.060; mean **κ ≈ 0.98**). So
`P(n prime | p prime) ≈ 0.98/ln(n)` — the *ordinary* prime density, no anomalous
suppression or enhancement. Extrapolated to secp256k1 (`ln n = 177.4`):
`P ≈ 0.0056`, i.e. **~1 in 180** primes `p≡1 mod 3` give a prime-order `j=0` twin.
That is exactly the standard cost of a prime-order-curve search.

**De-inflation [inference].** The pasted agenda's "enormous rarity" / "shadow of a
number-theoretic rarity" framing overstates it. secp256k1's twin-prime-ness is as
special as *any* prime-order curve: a curve designer fixes `j=0` (CM by ℤ[ω]),
scans the Solinas prime family for `p` prime, and keeps the first where `n` is
also prime — an ~1-in-180 event at this size, precisely as Bateman–Horn predicts.
There is a genuine Hardy–Littlewood-type constant here (`κ≈0.98`, `𝔖≈1.67`); it is
`O(1)`, which is the whole point — the event is generic, not suppressed.

## 2. Thread 3: `27M²` is universal to `j=0`, not special to `b=7`  [found]

- `4p = t² + 27M²` solved for **all 37** primes `p≡1 mod 3` in `[7,400]`. It is the
  CM-by-ℤ[ω] norm form (`4p = (2a−b)² + 3b²`, `M=b/3`), so universal to every such
  `p`. Not a `D=7` effect.
- For `p=103`, the six curves `y²=x³+D` realize six orders
  `{84,91,97,111,117,124}` — all six sharing the **same** `M=3`. The choice of `b`
  moves only `t` (which twist); `M` is a `p`-invariant.
- secp256k1: `4p−t²` is divisible by 27 with `M = 1011381…253057`, matching
  KNOWN_FACTS. So `b=7` selects the unique prime-order sextic twist; the `27` is
  the discriminant-`−3` shadow common to all `j=0` curves.

## 3. Threads 2 and 4: already answered / underdetermined  [known]

- **Thread 2 (Hecke image size / survival density).** `session_findings_2026_07_12_v1
  §1` established the finite character has **order 6**, reproduced on **494/494**
  split primes. Image size 6 ⇒ survival-set density `χ(π_p)=1` is **1/6** by
  equidistribution of a nontrivial Hecke Grössencharacter. No recomputation needed.
- **Thread 4 (p-adic Γ, fractional arguments).** `session_findings §6` marks the
  single-prime mod-`p²` test **[no-evidence] / underdetermined** — a
  permutation-and-sign search at `p=13` produced many matching formulas, so one
  prime cannot identify the formula; Morita's `Γ_p` verified at integer arguments
  only. A real attempt needs a multi-prime pre-registered design, not done here.

## 3b. Implications of the equivalence (grounded, not just "generic")

Filing the twin condition as "known = prime-order j=0" is correct but skips content:

- **[found] n itself splits in ℚ(√−3), forced.** `n == N((a−1)+bω)` exactly, so
  `n ≡ 1 mod 3` (verified) and n factors in ℤ[ω]. This is the *mechanism* of the
  amicable pair: n splitting in the CM field is what makes `#E₇(F_n)=p` well-posed.
  The amicable pair is a **corollary** of the twin condition (and symmetric:
  `π_n+1=π_p` sends n back to p), not a separate special fact. Generic
  (non-CM) prime-order curves have no such property.
- **[inference] Existence/density is a Hardy–Littlewood conjecture, unconditionally
  open.** `𝔖=1.67>0` ⇒ no local obstruction ⇒ *conjecturally* infinitely many
  Eisenstein twin primes / prime-order j=0 curves at every size. The obs/pred=0.9975
  match **confirms the heuristic empirically but does not prove existence** — that
  sits in the twin-prime difficulty class. So §1's "~1 in 180" is the *conjectural*
  rate, numerically verified, not a theorem. (Correction to §1's confidence level.)
- **[found] The ℤ-shadow is a √p-gap prime pair, not adjacent primes.** `n−p = 1−t`
  with `|t|≈2^129≈√p`. The distance-1 twin in ℤ[ω] projects to a prime pair at gap
  ≈√p in ℤ. `𝔖` governs that √p-gap correlation, a different object from the classical
  ℤ twin-prime constant — do not conflate.
- **[found] The twin is maximal (no triplet).** `Q(c)=c²−tc+p` prime only at
  `c∈{0,1}` (`Q(−1),Q(2),Q(3)` composite). `disc(Q)=−27M²` gives ~`(1+χ₋₃)` roots
  mod ℓ, so consecutive prime-norm runs are generically short; `{0,1}` is the ceiling.
- **No ECDLP/key consequence.** "n splits in ℚ(√−3)" is CM-universal to all
  prime-order j=0 curves ⇒ no secp256k1-specific leverage. Does not resurrect the
  retracted "977 = smallest offset" claim (KNOWN_FACTS §2).

## 3c. Norm-ordered reconciliation + no twist-enrichment  [found]

A separate norm-ordered count (primes `p≡1 mod 3`, `p<10⁶`, 39 231 of them; the
`b=3M` representation) pins the *single-twist* conditional and settles a factor-2
ambiguity between the (a,b)-box count and any norm-ordered count that ranges over
unit associates:
- **Fixed twist** (is *this* curve's `n=N(π−1)` prime — the crypto object):
  3203 twins, `P(n|p)=0.0816`, **κ=1.13**. Agrees with §1's box κ≈1.0–1.1.
  ⇒ ~1 in 180 at 2²⁵⁶.
- **Any of 6 sextic twists prime-order**: 16 820, `frac=0.4287`, κ=5.9 — but this
  is just six ~independent chances: `1−(1−0.082)⁶=0.40 ≈ 0.4287`. So the
  **primary/amicable twist is NOT prime-enriched** (rate 0.0816 = the single-twist
  average). Had it been ~2× a generic twist, that would be structure; it is not.

**Caveat on a competing writeup.** A norm-ordered analysis that reports the count
"converging to the Hardy–Littlewood prediction" (ratio → 1, C_fit → theoretical
~2.06) and then concludes secp256k1 is "genuinely rare / not generic /
astronomically small" is **self-contradictory**: convergence to the HL heuristic
*is* genericity. It conflates "sparse among all integers (~1/ln²X, true of every
prime constellation)" with "anomalously suppressed vs HL" (false — ratio→1). The
conditional rate is ~1/180, the ordinary cost of a prime-order search, not
astronomical.

**Constant reconciliation — RETRACTED claims + verified replacement
(`eisenstein_twin_reproduce_v1.py`).** An earlier draft here asserted
`C_Eis/2 = κ∞ = 1.031 → 1 in 172` and `6064 ≈ 2·3203 (conjugate double-count)`.
**Both are withdrawn — neither was verified and both are wrong:**
- My *independent* Bateman–Horn Euler product (same formula as `𝔖`) converges to
  **1.6717** (`q≤5·10⁵`), NOT the competing writeup's `C_Eis=2.06277`. They are
  different constants under different count normalizations; the map was never
  derived. Dividing 2.06 by 2 to compare to a directly-measured κ was invalid.
- The competing count convention is **b>0, 3∣b, both norms prime** (identified by
  reproducing its sequence — **161, 551, 962, 3532 reproduced exactly**; its 10⁶
  value 6064 could NOT be reproduced, I get **6359**, cause unknown, not a
  sieve-cap artifact). So the count is unrelated to the `3203`/conjugate story.

**Verified, convention-free result [found].** Computed directly as `twins/Fprime`
(no constant): `κ = P(n|p)·ln X ≈ 1.11`, stable across `X∈[10⁴,10⁶]` and across
the 'all'/'b3'/'b3pos' conventions (1.17→1.11). ⇒ `P(n prime|p prime) ≈ 1.11/ln(n)`
= **~1 in 160** at 2²⁵⁶ (κ drifts slightly down with X, so extrapolation carries
real uncertainty, ~1 in 160–200). κ is `O(1)` — a mild ~11% singular-series
enhancement over a random prime, NOT suppression. This is the "generic" conclusion,
now resting on a measured quantity, not an asserted constant.

**The two "specialness" numbers a competing writeup reports** both read the
**unconditional joint** rate as a **conditional** one:
- `1/ln²(p) = 1/31487 ≈ "1 in 30,000"` is the joint rate (both p AND n prime over
  all π) — correct, but NOT "the rate among primary primes." Conditional on p
  prime it is `~1.11/ln(n) ≈ 1 in 160`. `1/ln²` is just two independent ~`1/ln`
  primality events (any prime pair), not a specialness signal.

**The "27" origin [found].** The general CM form is `4p = t² + 3b²` (the `3` =
`|disc ℚ(√−3)|`). The `27` appears ONLY because secp's twist has `3|b` (b=3M,
verified), giving `3b² = 27M²`; so `27 = 3·9 = |disc|·3²`, the `3²` being the `3|b`
normalization at the ramified prime 3 — the same ramification the Hecke conductor
records as its `(√−3)²=(−3)` factor. Exactly one of the six twists carries the 27
(the one whose imaginary part ≡ 0 mod 3; for secp `{a,b,a−b} mod 3 = {2,0,2}`). So
"27 = shadow of the conductor's (√−3)²" is right in spirit (both are the D=−3
ramification at 3) but imprecise: the 27 is `|disc|·3²` and selects one twist, it
is not literally the conductor factor.

## 4. Bottom line

The "central paradox" framing dissolves under measurement: every listed layer —
CM by ℚ(√−3), `χ(π_p)=1`, the `27M²` form, the amicable `(p,n)`, and the twin-prime
condition — is a **generic consequence of choosing a prime-order `j=0` curve**, each
occurring at its Bateman–Horn / equidistribution density (twin: ~1/180; survival:
1/6; `27M²`: probability 1). secp256k1 is a typical member of that family, not a
number-theoretic outlier. This matches, and quantifies, KNOWN_FACTS §14's standing
verdict that the curve's structure is "structurally generic given its 3 defining
features." No cryptographic consequence: none of these densities touch ECDLP.
