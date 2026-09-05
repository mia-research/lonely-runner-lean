# Flap ↔ N1: a forced parity obstruction, and one channel bounded (with power)

**Date:** 2026-07-25 · Scripts: `n1_flap_bridge_v1.py` (superseded statistic), `n1_flap_bridge_v2.py`
(the run), power check inline. **`[EXPLORATORY]` — no `experiment-designer` pre-registration.**
Nothing here is confirmatory; anything worth keeping needs its own frozen spec and an OOS retest.

**Provenance:** written because the user pushed back on a prior armchair dismissal
(*"shared substrate, not a link… adds nothing"*). That dismissal used the exact words
`feedback_negative_bias_enlarge_nulls_2026_07_17` flags (**generic**, **adds nothing**) and violated
`CLAUDE.md`'s stance (*don't open a thread with a futility verdict; build the object first*).
**The two findings below did not exist until the object was built.** Recorded as evidence that the
dismissal was the error, not the caution.

---

## 1. The setup — why these two objects are comparable at all

Two functions on the **same** group `E(F_p) ≅ ℤ/n`, for `y² = x³+7` (secp's own equation):

```
f(d)     = χ₂( y_[d]G )        the N1 weight.  V₁(a) = Σ_d f(d) ζ_n^{ad} is its Fourier transform,
                               and  v ≤ 0  ⟺  |V₁(a)| ≤ √3·√p .
σ(d)     = flap sign of x_[d]G  the cap-law classifier, ε(X)=1 iff 2|cent(s)−cent(ρs)|>p, ρ=β+1.
```

This is not a generic analogy: the record already couples them — **the flap's `χ₂`-imbalance is
`h(−p)`**, which is a statement about `f` summed over the flap, i.e. about **one frequency**. The
natural next question is what happens at *every* frequency, and specifically at the exceptional ones.

## 2. ★ Finding 1 — the zero-frequency bridge is PARITY-FORBIDDEN on the whole SIN stratum

Measured `Σ_d f(d)σ(d)` = **0 exactly** at `p = 127, 163, 211, 547`, nonzero only at `p = 349, 433`.
The split is exactly `p mod 4`, and it is **forced, not empirical**:

> `f(−d) = χ₂(−y) = χ₂(−1)·f(d)`, so `f` is **odd** under point negation when `p ≡ 3 mod 4`.
> But `σ` reads only the **x-coordinate**, and `−P = (x,−y)` has the **same** `x`, so `σ` is **even**.
> Odd × even summed over a symmetric index set vanishes identically.

⇒ **`Σ f σ = 0` is forced for every `p ≡ 3 mod 4`, and carries zero information.** Any flap↔`χ₂`
bridge on the SIN stratum must either live at **nonzero frequency** (which is precisely what `V₁(a)`,
`a ≠ 0`, is) or use a **y-aware** flap. This is a design constraint on the bridge, obtained for free,
and it is the reason the spectral route below is the right repair rather than an escalation.

⚠ Note the cap law's own `σ(−x) = −σ(x)` refers to negating the **lattice point / field element**, not
the **curve point**. Those are different negations. Conflating them is what makes the naive pairing
look promising.

## 3. Finding 2 — one channel bounded, with the control shown to have power

**Statistic (repaired).** v1 used `|V_flap|/|V₁|`, which is unbounded and blew up where `|V₁| ≈ 0`
(means of `2.1–2.8` for a quantity called a "share"). Replaced by (a) the Spearman rank correlation
between the two power spectra `|V₁(a)|²` and `|FT σ(a)|²` over `a ≠ 0`, and (b) the normalised
`|FT σ|²` restricted to the exceptional frequencies.

**Instrument checks, all PASS at all 7 primes:**

| | |
|---|---|
| **I1** `σ` constant on GLV orbits `d ↦ λd` | **PASS** — independently reproduces **cap-law Theorem B** (`σ(βx)=σ(x)`) in a fresh implementation |
| **I2** `V₁ = V_flap + V_core` exact | **PASS** |
| **I3** exceptional-frequency count = 6× the μ₆-class count | **PASS** (6,6,18,18,12,18,24 vs 1,1,3,3,2,3,4) |

**Control.** Matched null permutes `σ` **across GLV orbits**, preserving orbit structure and the value
multiset — so "a μ₃-invariant subset of this density" cannot by itself produce a hit.

**Result — null:**

| `p` | 127 | 163 | 211 | 349 | 397 | 433 | 547 |
|---|---|---|---|---|---|---|---|
| spectra rank-corr `ρ` | `−0.056` | `−0.162` | `−0.061` | `+0.040` | `+0.042` | `−0.016` | `+0.022` |
| two-sided `p` | 0.82 | 0.46 | 0.75 | 0.80 | 0.74 | 0.89 | 0.85 |
| exc-freq `\|FT σ\|²` (norm.) | 1.38 | 0.98 | 1.42 | 0.24 | 0.48 | 0.44 | 0.16 |
| one-sided `p` | 0.26 | 0.35 | 0.20 | 0.97 | 0.75 | 0.85 | 0.995 |

**★ The control has power — the null is therefore informative.** A planted `σ` tied to the exceptional
set (GLV-symmetrised `sign cos(2πa*d/n)` at an exceptional `a*`) fires at the permutation floor:

| `p` | 127 | 211 | 349 | 547 |
|---|---|---|---|---|
| exc-power, **planted** | 13.27 | 7.09 | 10.27 | 15.02 |
| `p`(planted) | **0.0025** | **0.0025** | **0.0025** | **0.0025** |
| exc-power, **real** | 1.38 | 1.42 | 0.24 | 0.16 |

A real coupling of the planted size would have been seen `7–15×` over. It is not there.

## 4. Scope — what is bounded and what is untouched

**Bounded (a SCOPED null, not a closure):** the *marginal spectral* channel between the flap sign and
the N1 exceptional set, at 7 primes `p ≤ 547`, for the **x-coordinate flap classifier at multiplier
`a = 1`**, against a GLV-orbit-preserving null with demonstrated power.

**Explicitly NOT tested, and each a distinct channel:**
- the flap classifier's **free multiplier `a`** — the record has an entire prereg on `a`-invariance;
  I used `a = 1` throughout;
- a **y-aware** flap, which is what §2 says a SIN-stratum bridge would need;
- the record's flap as a subset of the **fundamental domain** under uniform measure — my object is a
  density over **curve points**, a different measure (which is why v1's comparison against the cap
  law's `1/4` was invalid and convicted nothing);
- **joint / higher-order** statistics — two marginal spectra and one targeted mean were tested;
- `p > 547`; the geometric flap `{|u−v|>½}` rather than the as-implemented absolute-value classifier.

**What the geometry does say, and it is not nothing:** the N1 half-trace pair is a 120° pair of
modulus `2√p` — exactly the flap rhombus of `L = π_p·ℤ[ω]` scaled by **2** — and the N1 threshold
`√3·√p` is exactly that rhombus's **long diagonal**, with Weil's `2√p` its doubled **short** diagonal.
That is a shared substrate, established; whether it is more than shared CM structure is what §3 tested
in one channel and did not find.

## 5b. Both ends in one language — and an honest unforced-hit audit

Reframing the N1 pair as a `μ₃` **triple** puts both ends in the flap's own language. The two
half-traces sit at `t±60°`; the third sibling is at `t+180°`, i.e. `s₃ = −u`. Then:

- the three half-traces are the roots of **`4z³ − 3z + cos 3t = 0`** (Chebyshev triplication), and
  `cos 3t = 4u³ − 3u` is the **`μ₃`-invariant** of the configuration;
- the triple is a point of the **`A₂` plane** (= the hexagonal/Eisenstein lattice's own plane) on the
  circle of squared radius `3/2`, with `μ₃` acting by cyclic permutation — **the same `ω`** that acts
  on `L = π_p·ℤ[ω]` in Cap Law Thm A/B;
- **`v > 0` ⟺ `s₃` is the dominant coordinate**, i.e. the exceptional classes are exactly those where
  the *observable* coordinate `−V₁/(2√p)` wins. Measured dominance: `s₁ 0.445`, `s₂ 0.507`,
  **`s₃ 0.048`** against `1/3` each under exchangeability.

**★ UNFORCED-HIT AUDIT — the reframing yields NO new information, and saying otherwise would be
narrative overreach.** Counted per the drill rule:

| apparent finding | status |
|---|---|
| `Σ sᵢ = 0` ("traceless") | **FORCED — definitional.** `s₃` was *defined* as `−(s₁+s₂)`. Zero information. |
| `Σ sᵢ² = 3/2` ("constant norm") | **RESTATEMENT.** Equivalent to `s₁²+s₁s₂+s₂² = 3/4`, i.e. to `v = u²−3/4`, already established. Not a second conservation. |
| at most one `\|sᵢ\| > √3/2` | **FORCED** given the line above. |
| `s₁` vs `s₂` dominance `0.445/0.507` | **FORCED** by the symmetry of the `u`-distribution (`t↦−t` swaps them); `159/340 = 0.468`, consistent with `1/2`. |
| `s₃` dominance `0.048` vs `1/3` | **RESTATEMENT** of "`\|u\| > √3/2` is rare". |

> **Net new information from the reframing: zero.** It is a change of coordinates on one fact.
> Recorded because it is *illuminating* and connects the two ends precisely — not because it is a
> finding. The story here owes no payoff.

**★ What it does buy, and this part is load-bearing — a dimension count.**
`cos 3t = 4u³ − 3u` is a function of `u` alone, so:

| | degrees of freedom |
|---|---|
| **N1 side** | **1** — `u = V₁/(2√p)`; `v`, `s₁`, `s₂`, `s₃`, `cos3t` are all functions of it |
| **flap side** | **2** — a point of the fundamental domain `P` |

> **Any flap → N1 bridge must factor through a 2D → 1D reduction.** That is a concrete structural
> reason the marginal spectral test of §3 could not have seen a link even had one existed in the
> discarded dimension — and unlike the armchair verdict this replaces, it is checkable.
> **It also names the repair:** test the flap against `u` *after* projecting `P` along the direction
> the N1 side keeps, rather than against `σ`, which has already collapsed `P` to a sign.

## 5. What this does not license

No ECDLP, leakage, key-recovery or security claim. No statement about `p = 2²⁵⁶−2³²−977`.
**§3 does not close the flap↔N1 question** — it bounds one channel at one scale with one classifier.
Per the drill protocol, a bounded magnitude with a firing control is a positive characterization, and
the next probe is named in §4 (the `a`-multiplier and the y-aware flap, in that order).
