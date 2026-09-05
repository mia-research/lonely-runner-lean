# RESULT — `S_diff` applied to the real 82 (v1)

**Grade:** `[MEASURED-EXACT — scoped null for the frozen-orientation projection, n=82, secp P]`.
Applied 2026-07-26 against [PREREG_diffset_sdiff_v1.md] (frozen before data). Integer-exact path.

---

## Result
```
S_diff(real) = −35      (S_diff² = 1225, odd ✓)
frozen reject region:   S_diff < −115  or  > +111
decision:               −35 is INSIDE  →  NO REJECT
position:               −0.57σ,  30th percentile of the matched known-MT control null
two-sided rank p:       0.59
jitter band:            clear (well short of 111–115)
```

## Verification (trust-but-verify)
- Frozen null order-statistics reproduce the region exactly: 250th-smallest = −115,
  9751st-smallest = +111.
- **Independent regeneration** (different seed 999, 1,500 resamples): mean −2.2, σ 58.9,
  `[2.5%, 97.5%] = [−123, +117]` — consistent with the frozen artifact within its ±2 seed jitter.
- Signal path integer-only (exact `pow` Legendre); no float touched the decision.

## Characterization (not a verdict)
The real 82 keys' frozen-orientation difference-set character sum is **−35, indistinguishable from
the known-MT construction** (30th percentile of its own matched null) — the recurring `real ≡
known-MT` pattern, now measured on a **joint** object, not a marginal. This is a more
informative null than the flat sextant tally: it actively probed pairwise structure and bounds it in
this one direction.

## Power + scope of the bound
Rules out a frozen-orientation per-pair QR-bias above **ε ≈ 0.034** (50% power) / **ε ≈ 0.048** (80%
power). The planted control fired (0.046 → 0.83 at ε=0.05), so an effect of that size *would* have
shown. Scoped to: these 82 puzzles, bit-lengths `{1–70, 75–130}`, secp256k1 P, ascending-bit
ordering.

## What stays open (the orthogonal subspace)
By `χ₂(−1) = −1`, orientation-**symmetric** difference-set structure is identically 0 in `S_diff` —
**invisible, not bounded**. A single-projection null is a scoped fact about this probe, **not**
evidence the avenue is closed (repo stance: a cheap null bounds the probe, not the geometry).

**Next probes (each a distinct joint object, each its own pre-registration):**
1. **μ₃-graded / cubic difference character** — `χ₃(x_j − x_k)` over F_P. Verified `χ₃(−1) = 1` at
   secp (P ≡ 1 mod 6), so it is **orientation-symmetric** → probes exactly the subspace `S_diff` is
   blind to, and it is secp's actual CM/Eisenstein direction. **Pre-registration in progress.**
2. **σ-weighted difference sum** — the on-curve analogue of the v34 `C = Σ σ(x)χ₂(x³+7)` object,
   evaluated over the key set.
3. **Triple / multilinear** difference-set objects (the "three difference-set/multilinear objects"
   already in the project history).
