# Nested (n,k,D) recursion — the ~11-term model — (X,Y) deep-level test (2026-07-10)

**Key correction (user):** 246 bits should give ~10-11 recursive terms; my earlier
recursion (validated = dataset `D_terms`) gives only 4-5. Resolved: those are
DIFFERENT recursions.

## Which recursion gives ~11 terms (term-count probe, N=246, 400 keys)
- (S) simple/CSV unit-fraction expansion: mean **4.1** {4,5} — the dataset's D_terms.
- (N256) nested best-approx of residual each scale, denom≤256: mean **15.5**.
- (N2048) nested, denom≤2048: mean **11.6** {11,12}. ← matches the user's 10-11.

⇒ The user's "recursive error" = the **nested (n,k,D)** decomposition: recursively
best-rational-approximate the residual at each scale (each level = another φ(n_i)
position), denominator bound ≈ 2048. Structurally richer and more φ(n)-native than
the CSV unit-fraction expansion. (Exact denom bound is inferred — user to confirm.)

## Deep-level leak test (the user's hypothesis: signal hides in deep terms)
Generated M=8000 keys d→P=d·G (exact ECC) at N=246, nested-decomposed (mean 11.6
levels, max 13). Tested (X,Y) features {X mod ℓ, X·Y mod ℓ, v_ℓ} vs the residual
r_level mod ℓ at levels 1,3,6,9,10,11,12, ℓ∈{7,13}. REAL controls (target-leaking
full + 40% corrupted) fire at the permutation floor p=0.007 at EVERY level.

**Result: NULL at every level, shallow to deep.** All |z| ≤ 2.3, all min-residuals
≥ −2.8, nothing flagged. The deep levels (9–12), where signal was hypothesised, are
as null as the shallow ones — with the detector proven to catch planted signal at
each level.

## Verdict
The user's actual recursion (nested, ~11 terms) is now identified, built, and tested
at full bit-length (246): **(X,Y) leaks no level of it, deep or shallow.** Combined
with the frozen/full-range direct-d nulls, this closes the high-N + deep-recursion
hypothesis with validated detectors. Remaining open: the EXACT denominator bound /
recursion definition if it differs from denom≤2048 — send it and the identical
harness re-runs. This is a bounded null on the correct object, not a dismissal.
