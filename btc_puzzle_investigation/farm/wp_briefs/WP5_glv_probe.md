# WP5 — GLV / endomorphism residue probe  (STRUCTURE PROBE · minor)

**Farm to:** Haiku subagent.  **Runtime budget:** ~15 min.  **Priority:** low —
run only if WP1/2 leave spare capacity.

## Scope
The source doc raises the GLV decomposition ~5 times (Inv 2, 2.3, 2.7, 5.4, 9.1).
Two distinct claims hide in there; separate them:

1. **Attack form — already covered by WP2.** "Does `(βX,Y)` leak n?" is a
   public-only map property; WP2 includes GLV-image features. Do NOT re-run;
   just confirm in the writeup that GLV features added nothing over raw `(X,Y)`
   in WP2 (cite WP2's importance ranking).

2. **Structure probe — the only new bit.** Compute the GLV decomposition
   `d = d₁ + d₂·λ (mod N_ord)` from the *known* `d` (dataset), with `d₁,d₂ ≈ √N`.
   Test whether `(d₁ mod n, d₂ mod n)` clusters, i.e. whether the small-`n`
   rational structure imprints the GLV coordinates. This uses `d` → it is a
   **diagnostic**, never an attack (you cannot get `d₁,d₂` from `P` alone without
   solving the split, which needs `d`).

## Procedure
- Implement the GLV split (balanced representation via the lattice basis of
  `{(a,b): a+bλ ≡ 0 mod N}`; standard two-short-vector method with `λ=lib_data.LAMBDA`).
- Verify `d₁·G + d₂·φ(G) == P` on a sample (correctness gate).
- χ² / MI test of `(d₁ mod n)` and `(d₂ mod n)` vs `n` across the dataset, with a
  `matched_null` comparison.

## Report → `../RESULTS/WP5_glv_probe.json`
`{split_verified: n/n, d1modn_MI, d2modn_MI, vs_matched_null, attack_valid: false}`.

**Done-check:** split verified on the sample; MI reported vs matched null;
explicitly labeled a structure probe (not an attack).
