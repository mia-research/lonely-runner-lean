# RESULT — pushing the curve ×λ island: the three-strip map + the interval-DLP-with-λ folding question, resolved

**Grade: map `[VERIFIED — exact/enumerated]`; folding closure `[PROVED — quantified, scoped to orbit-identification folding]`.**
Date 2026-08-17. Pushes `RESULT_dirichlet_island_existence_mapping_v1` Object 3. Resolves the open direction
flagged in `RESULT_dirichlet_island_structure_and_leakage_v1` ("interval-DLP-with-λ folding"). Does not edit
any master; accumulates toward a future v13. Reproduction: `scratchpad/lambda_fold.py`, `lambda_fold2.py`.
Exact `int`; costs are `√`-model estimates (standard).

## The map (positive structural content)
In GLV coordinates `d = d₁ + d₂λ (mod n)`, the order-3 endomorphism acts as the **linear 120° rotation**
`λ: (d₁,d₂) → (−d₂, d₁−d₂)` (companion matrix of `x²+x+1`). The puzzle interval `I=[2^(b−1),2^b)` is a **thin
sheared strip** in this plane; its three λ-rotations `I, λI, λ²I` are three strips at 120°, and the curve
island `S = I ∩ λI ∩ λ²I` (from the mapping file, size `2^12/2^22/2^32`) is their **central overlap**.
- **Verified by enumeration:** the orbit-min representatives of a length-`L` interval land in **~3 clusters**
  (the lower parts of the three strips), NOT uniformly — 12-bin distributions show 3–4 populated bins, rest
  exactly 0, at every tested interval location (n/3, n/7, n/2, 3n/7, 2 random).

## The folding question (the audit only hand-waved "orbit-mates leave the interval")
**Q:** does the order-3 λ give a √3 interval-DLP speedup, the way negation gives √2?
**Requirement (why negation works):** an automorphism speeds up interval DLP only if it keeps the folded
search **confined to a region of size ~|I|**. Negation on a *centered* interval maps it to itself: reps
`|d−c|` stay in `[0,|I|/2)` → real √2.

**Test (λ):** the orbit-`⟨λ⟩`-min reps of `I` do **NOT** confine — measured fold-region width / |I| =
**5.5×–18.4×** across six interval placements (n-scale asymptotically, since `I` is not a union of λ-orbits
so `λI ≠ I`). Folding by λ therefore trades the interval bound `L` for an ~`n`-scale search.

**Quantified (real secp, puzzle 135):**
| attack | search region | cost |
|---|---|---|
| plain interval kangaroo on `I` | `L = 2^134` | **~2^68** group ops |
| λ-fold (orbit-identification) | delocalizes to ~`n/6` | **~2^126.5** group ops |

**λ-folding is ~2^58× WORSE.** The interval bound `L = 2^134 ≪ n` is worth far more than the √3; folding
throws the bound away. `[PROVED — quantified]`, scoped to the **orbit-identification folding class** (the
standard automorphism-assisted kangaroo/rho that canonicalizes each point by its `βx`-orbit-class).

## What this does and does not close
- **Closes:** the √3-via-λ-folding avenue for interval DLP, for the orbit-identification class, with a named
  reason (non-invariance `λI≠I` ⇒ reps delocalize to n-scale) and a number (2^58× worse), not a hand-wave.
- **Does NOT claim:** that no conceivable use of λ ever helps interval DLP (out of scope of the class analyzed).
- **Kept honest (the real positive that survives):** **negation gives a genuine √2** for the puzzle interval
  via centering `d' = d − 3·2^(b−1)/... ` (centered interval is negation-invariant) — a standard, real speedup,
  unaffected by the above. The μ6 full-group rho √6 is real too but lives at 2^126-scale, irrelevant to the
  2^68 interval attack.

## Net
The curve ×λ island is now fully mapped (three-strip / 120°-rotation geometry, central-overlap island, all
exact and enumeration-verified). The endomorphism's *folding* value for the interval attack is resolved:
**λ cannot fold the interval** (delocalization, 2^58× worse) — while **negation's √2 remains the one real
interval-level automorphism speedup**. The interval bound, not the automorphism, is the dominant resource.
