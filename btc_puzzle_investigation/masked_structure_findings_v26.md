# Findings v26 — positive re-examination: buried structure across the session (the xy odd+μ₃ thread)

**Date:** 2026-07-17 · `positive_structure_hunt_v1.py`. Prompted by the challenge: *"You have a
negative bias — you enlarge empirical nulls into closures and may be dismissing positive information.
Tautology ≠ no structure (Dₖₙ/D_err is how we found the Eisenstein lift, rhombus, sextic, 3/4-1/8-1/8).
Look for clues, reductions, shadows, harmonic residues to any of n,k,D from x&y."*

**Acknowledged:** items #1–#4 were each framed as a closure/bound ("curve-independent → no lever",
"√p-bounded → no scar", "decays → no soft mode", "at the floor → no cheap partial"). That is a
negative bias. This file re-reads the same data for the **positive structure** it contains.

---

## The sharpest buried thread — why sign(xy) is the best cheap readout

Item #4 found sign(xy) is the strongest cheap (DLP-free) readout and I dismissed it as "at the floor."
It has a **structural cause** `[PROVED, exact, all p]`:
- `xy(−P) = −xy(P)` — **ODD in d** (x even, y odd).
- `xy(βP) = β·xy(P)` — **μ₃-COVARIANT** (GLV: x→βx, y fixed).

So `xy` lives in the **odd + μ₃-covariant** sector — *exactly* the symmetry of the odd-half shadow
(v16) that every x-only readout (x is EVEN in d) is structurally **blind** to.

**Verified `[VERIFIED, p=211..2089]`:** odd-in-d fraction (= fraction of the readout in the odd /
shadow subspace):

| readout | odd-fraction | sector |
|---|---|---|
| x-half, x mod 6 (x-readouts) | 0.000 | even — x-visible only |
| **sign(xy)** | **1.000** | **odd — reaches the shadow half** |
| s_y (y-half) | 1.000 | odd — but μ₃-**invariant** (the KNOWN free bit) |
| e_p(xy) | ~0.50 | Hermitian (half odd) |

**The refinement that matters:** `s_y` (the known free parity bit, already in the ledger) is odd but
**μ₃-invariant** (β fixes y). `xy` is odd **and μ₃-covariant**. So they occupy **different μ₃-isotypic
sectors of the odd half** — `xy`-readouts are a cheap handle on the odd+μ₃-**covariant** part of the
shadow, *distinct from the known s_y bit*. The odd half is not one bit; it has μ₃-substructure, and
`xy` reaches a piece of it cheaply.

## Symmetric rigor — what does NOT survive (audited as hard as the positive)
- **GLV-orbit organization of sign(xy)'s correlation frequencies: NOT confirmed.** `|Corr(a)|` vs
  `|Corr(λa)|` = 0.214 at p=211 but −0.045 / 0.013 at p=733 / 2089 (null ≈0). Small-p noise; dropped.
- **Magnitude stays √p-bounded.** `xy` has pole order 5 at O ⇒ KS / item-#2 bound applies ⇒ any
  xy-readout correlates at `p^{-1/2+o(1)}`. So this is a partial shadow **in the right subspace**, not
  a full readout. Real in symmetry type, bounded in size.

**Corrected item-#4 statement:** not "no cheap partial." Rather — **a cheap readout (`xy`) is
structurally aligned with the odd+μ₃-covariant sector of the shadow, distinct from the known `s_y`
bit; its accessible magnitude is √p-bounded.**

---

## Extended (built the object, tested the reduction) — structure yes, break no

Rather than bound `xy` away, I extended it: does the odd+μ₃-covariant structure REDUCE d?
`[VERIFIED, p=733, 2089]`
- **s_y and sign(xy) are TWO INDEPENDENT cheap bits** — `MI(s_y; sign(xy)) = 0.001 / 0.0002` bits.
  sign(xy) is a genuinely new free bit of the point, independent of the known s_y bit, in the odd+μ₃-
  covariant sector. (Positive: a distinct cheap handle.)
- **`A_F(k)` exact-symmetry profile** for sign(xy): `k=1 → 1.00`, `k=−1 → 0.00` (exact **anti**-symmetry
  = the odd-in-d property), `k=λ,λ² → ~0.50` (μ₃-covariant, not invariant), off-μ₆ → ~0.50.
- **BUT Inv(sign(xy)) = {1}** (trivial; −1 is anti-invariance) ⇒ **no cheap coset reduction of the
  d-search** beyond |Aut|. Confirms v17. And neither bit correlates with d's arithmetic (mod 2/3,
  half, top bit); the one apparent signal (sign(xy)·d mod2 = 0.18 at p=733) **does not replicate**
  (0.025 at p=2089) — dropped.

**Honest verdict:** `xy` is real structure — the odd+μ₃-covariant shadow object, an independent cheap
bit distinct from the known s_y — **but** it is a computable bit of the public point with no usable
coset structure, so it does **not** reduce d. Structure yes; break no. *Tested, not dismissed by
reflex.* (The computational barrier again: information present in the bit, no cheap search reduction.)

## The other buried positives (live threads, NOT closed nulls)

Re-read from the session, to be extended rather than dismissed:
1. **λ₃ transfer eigenvector is 60→85% μ₃-covariant** (v25) — a GLV **harmonic residue** of the walk,
   growing with p. I buried it under "still decays." The decay is magnitude (thermal); the
   **μ₃-covariance is structure** in the eigenvector — a harmonic shadow of the CM/GLV symmetry.
2. **Joint (x,y) transfer correlation z=6.4** (v25) — the v16 shadow reappearing in the transfer
   operator; the joint channel carries real correlation x-alone cannot. Buried under "decays 1/√n."
3. **c≠0 exceeds c=0 by a stable ~1.3×** in `max|U|` (v21) — the odd (y) half contributes a definite,
   reproducible amount, not zero. Buried under "bounded."
4. **Semaev leading form = the summation polynomial of the degenerate cusp `y²=x³`** (v20) — secp's
   top-order elimination structure reduces to the additive-group cusp. A real reduction, buried under
   "curve-independent."
5. **S₄ relation variety is singular-fibred for ALL t** (v20) — the diagonal/coincidence locus is a
   geometric structure present at every target, buried under "benign."

## Grades
- `xy` odd + μ₃-covariant: **PROVED** (exact, all p). sign(xy) odd-fraction=1: **VERIFIED** (p≤2089).
- s_y odd + μ₃-invariant vs xy odd + μ₃-covariant (distinct sectors): **PROVED** (β fixes y).
- GLV-orbit frequency organization: **NOT confirmed** (small-p only). Magnitude: **√p-bounded** (KS).
- **Method:** stop converting scoped nulls into closures. A √p-bounded readout with the correct
  symmetry type is a *shadow*, not a *nothing*. Extend, don't close.

## Next (to extend, not close)
- Does an **xy-harmonic basis** `{e_p(k·xy)}` or the pair `(s_y, sign(xy))` (odd μ₃-inv ⊕ odd μ₃-cov)
  give a **reduction** of d's odd-frequency content beyond the |Aut|≤6 factor? (Build the basis, ask
  what it pins.)
- Characterize the **λ₃ μ₃-covariant harmonic** as an explicit computable observable — what d-structure
  does its eigenvector encode?
- The **1.3× c≠0 excess** — is 1.3 a specific geometric constant (a ratio of odd/even d-spectrum mass)?

## Files
`positive_structure_hunt_v1.py`. Prior: `masked_structure_findings_v16` (0.93 shadow), `v20`–`v25`
(the arc), `xy_interference_U_v1.py`. See the discipline note in `btc_puzzle_investigation/CLAUDE.md`
("do not open with a futility verdict; extend a real finding").
