# Masked-Structure — Findings v5: the corner we never looked at

**Date:** 2026-07-16 · extends v3/v4. Prompted by *"did we miss any opportunity to
discover masked structure?"* + *"do your own context review, don't rely on the last one."*
Scripts: `scalar_mult_char_sum_v1.py`. Primary source re-read: `glv_closure_theorem_v2.md`.

---

## 0. The meta-move that found it: read the primary source, don't trust the tag

Re-reading the closure theorem myself (not its inherited "PROVED given KS" summary)
surfaced an **overclaim I had absorbed**:

> **§5 C1 says `χ_k` has additive Wiener norm `‖·‖_A = O(1)`.**  FALSE.

`χ_k` is a multiplicative character, so its *additive* Wiener norm (the one Lemma R uses)
is a sum of Gauss sums: `‖χ_k‖_A = (p−1)/√p ≈ √p`. The level-set indicator `1_{χ_k=ζ^j}`
is a multiplicative coset ⇒ also `‖·‖_A ≈ √p` ⇒ hypothesis **(H3) fails** ⇒ the MI
corollary (§4) does **not** apply to `χ_k`. What actually covers `χ_k`-vs-additive is the
**hybrid sum** built in v3 (empirical, small p) — *not* C1. The inherited map said "C1
handles it"; the source says C1 can't. **This is exactly the kind of inherited error the
meta-instruction was aimed at**, and correcting it is what exposed the real gap below.

### The corrected coverage map (what Lemma R actually proves)

Lemma R (the one complete proof): `|Cov(F(x_d), g(d))| ≤ (max|T|/n)·‖F‖_A·‖g‖_A`, both
norms **additive**, `T` the **additive×additive** twisted sum. Non-vacuous only when
**both** `‖F‖_A` and `‖g‖_A` are small (`p^{o(1)}`).

| corner | `‖F‖_A` | `‖g‖_A` | covered? |
|---|---|---|---|
| additive/geometric readout vs additive scalar | small (Lemma W) | small | **yes** (given KS + Lemma W) |
| `χ_k` readout vs additive scalar | `≈√p` | small | **no via Lemma R** → hybrid sum (v3, empirical) |
| **any readout vs MULTIPLICATIVE scalar `ψ(d)`** | any | **`≈√n`** | **NO — untested until now** |

---

## 1. THE MISSED CORNER — multiplicative characters of the scalar

A multiplicative character `ψ(d)` (e.g. the quadratic symbol `(d|n)`) has additive Wiener
norm `‖ψ‖_A ≈ √n`. So for **every** readout `F` — including the geometric ones
(`ε`, sextant, norm-band) that we *did* close on the additive side:

```
    |Cov(F(x_d), ψ(d))|  ≤  (max|T|/n)·‖F‖_A·‖ψ‖_A  ≈  (√p/n)·‖F‖_A·√n  ≈  ‖F‖_A     (VACUOUS)
```

**The multiplicative structure of the scalar breaks the closure bound universally.** This
is the symmetric dual of the readout-side blind spot we spent v3 closing — and it is
*broader*, because `ψ` kills the bound for all `F`, not just for `χ_k`. It is also exactly
the original masking prompt's deepest candidate: *"d smooth / multiplicatively simple even
though additively complex."* A smooth or subgroup-constrained `d` is what a multiplicative
character detects — and none of our machinery (closure, hybrid sum, Cap Law) reaches it.

**We never tested it.** That is the missed opportunity.

### 1a. Structural constraint found on the way: x-readouts are EVEN in d

`x([m−d]G) = x(−[d]G) = x([d]G)` ⇒ every x-coordinate readout is **even in d** ⇒ only the
**even part** of `ψ` can correlate. Consequences (exact, not statistical):
- quadratic `ψ` is even iff `m ≡ 1 mod 4`; for `m ≡ 3 mod 4` the sum is **identically 0**
  by the `d ↔ m−d` pairing — structural, not cancellation.
- cubic `ψ` is **always even** (`−1` is a cube mod `m` for `m ≡ 1 mod 6`) → the clean probe.
- **the entire ODD spectrum of scalar structure is invisible to x** — it lives in the
  y-coordinate (which flips sign under `d ↔ −d`). See §2.2.

### 1b. Built and tested — `scalar_mult_char_sum_v1.py`  [VERIFIED small p, generic]

`S(ψ,F) = Σ_{d=1}^{m−1} ψ(d)·F(x([d]G))` over the **whole prime-order ⟨G⟩**, full
enumeration, exact signal path (`±1` and Eisenstein-integer sums; `|S|²` via the exact
`ℤ[ω]` norm — no float in the signal path). `ψ ∈ {`quadratic, cubic`}`,
`F ∈ {χ_2, χ_3, χ_6, ε}`. Verdict = `|S|/√m`: generic ⇒ O(1) & flat; leak ⇒ ~√m.

**Scaling (√m over ~10×):**

| p | m | √m | max signal `|S|/√m` | `q self` /√m (fires) |
|---|---|---|---|---|
| 577 | 613 | 24.8 | 3.76 | 24.7 |
| 1831 | 1753 | 41.9 | 2.08 | 41.8 |
| 6091 | 5953 | 77.2 | 3.58 | 77.1 |
| 13669 | 13873 | 117.8 | 3.09 | 117.8 |
| 27361 | 27361 | 165.4 | 3.57 | 165.4 |
| 54163 | 54469 | 233.4 | 3.00 | 233.4 |

**max signal stays 2–3.8 while √m grows 10×** ⇒ `|S| = O(√m)`, **generic square-root
cancellation.** Controls behave: `q self` tracks `√m` (detector fires); the pure
coordinate sum (`triv×χ2`) sits at the Weil `√p` scale; random control O(1).

**Grade:** the scalar-multiplicative corner is **generic (VERIFIED, exact, m ≤ 54,469,
√m spanning 10×, proper scaling)** — for `χ_k` and geometric readouts, for quadratic and
cubic scalar characters. **Not a gate. But it was a real, untested gap**, and it is the
broader half of the closure blind spot. A general-p statement would need a
multiplicative(scalar-index)×multiplicative(coordinate) character-sum bound — a
Konyagin–Shparlinski-type estimate, **not** the additive×additive KS the closure theorem
cites. That extension is unproved here → named, not claimed.

---

## 2. The other genuinely-missed opportunities, ranked (honest priors)

### 2.1 Bilinear / two-point — STILL the deepest, still unbuilt  [OPEN]

Closure's own §7 names it: Lemma R bounds a **single** sum over one `d`. The **difference
set** `{x([d_i−d_j]G)}` and two-point/addition objects are outside KS as stated, and the
stance principle ("only a joint SET property survives the ECDLP scramble") is exactly this
complement. Flagged every version, **built in none.** Prior: this is where a real leak, if
any, must live — a single-point readout that recovered `d` *would be* a break, so the
marginals are expected-null by construction; only the joint set can carry it. **Highest
structural value. Design note (from v2 R3): use a per-point / per-pair distribution
statistic, never a set mean — 82 keys give `82·81/2 = 3321` pairs, and a set mean has ~no
power.**

### 2.2 The y-coordinate — the ODD half we structurally never saw  [OPEN, partly reducible]

Every readout we have *ever* used factors through `x`, which is even in `d` (§1a). So the
**entire odd spectrum** — odd scalar characters, the odd part of any feature — has never
been probed. The `y`-coordinate flips sign under `d ↔ −d` and carries exactly it. Honest
analysis of how much is genuinely new: `y = ±√(x³+7)`, so a `y`-readout = an `x`-readout
**plus the sign bit**, and `sign(y([d]G))` is the `d`-vs-`n−d` (≈ "which half") indicator.
For the puzzle keys (small `d ≪ n/2`) that bit is **pinned** — it reduces to the known
smallness, not new leverage. Curve-generically the odd character sum `Σ_d ψ_odd(d)·sign
(y([d]G))` is the natural object and is **untested**. Prior: likely generic, but it is a
structurally distinct half we can now *name why* we missed (x-projection), so it should be
built, not assumed.

### 2.3 Joint 2-D `(u,v)` distribution at secp's p / over key sets  [OPEN]

v4 R5 reduced all shape observables to the map `x ↦ (u,v)` and measured its
equidistribution defect on the **curve-point set at small p** (generic, `O(p^{−1/2})`).
Untested: the **joint 2-D** distribution (only 1-D projections done — `z³`, the shape
constants), the defect at secp's **actual** `p`, and the defect over **orbits / key sets /
difference sets** (which is 2.1 again).

### 2.4 Higher-degree (Weyl) scalar phases `e_n(a d²), …`  [OPEN, motivation-adjacent]

The hybrid sum (v3) covers **linear** additive features exhaustively. Quadratic-phase sums
`Σ_d F(x([d]G)) e_n(ad²)` are a legitimate curve object and untested; their *motivation*
(does a construction show a frequency comb) edges toward generation, so lower priority.

---

## 3. Net answer to "did we miss anything?"

**Yes — one real corner (scalar-multiplicative, §1), now built and generic at small p; one
structural half (the odd / y-coordinate spectrum, §2.2) we can now say precisely why we
never saw; and the bilinear frontier (§2.1) we have flagged four times and still not
built.** The find was only visible after re-reading the closure theorem from source and
catching that its C1 line overclaims `χ_k`'s Wiener norm — which is the concrete payoff of
"do your own context review."

None of these overturns the picture; all sharpen *where a leak could still be*, which is
the point of the exercise (fence → gate), and each is stated with a grade and a scope
rather than a verdict.

## 4. Grade discipline (the session's actual lesson, restated as a rule)

Every positive in the knowledge base carries a grade: **PROVED / VERIFIED(scope) / CITED /
EMPIRICAL / NAMED-GAP**. "Generic null" is a *scoped* VERIFIED, not a closure — it names
the set, the observable, the scale, and the power. The handover documents are the
positive-knowledge base **and** the bias-defense; those are not in tension only if each
entry is graded, because an ungraded positive inflates exactly as four of this session's
did.
