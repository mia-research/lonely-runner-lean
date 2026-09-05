# Assumptions: CLAIM-LRC-000056-EXT-001

1. Source integrity verified by SHA-256
   `99b30d585e6378f834d3357efef71ec14852fee04e01ecbb52e86a5d52c00139`.
   All three laws are conditioned on this specific file and are falsifiable by recomputation.

2. Scope is restricted to rows where `family = arithmetic` (55,000 of 220,110 total rows).
   Non-arithmetic families (geometric, perturbed, random) are outside the scope of Laws 1–3:
   these families have `isolation_count = 0` for all rows and `first_isolation` is empty.
   No claim is made about Laws 1–3 for non-arithmetic families.

3. `n` ranges over {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} only (11 distinct values).
   Law 3 is tested at all 11 values; 8 conform, 3 are exceptions. Results are NOT claimed
   to generalise beyond n=15 without additional testing.

4. The `delta` column reflects the arithmetic step of the speed sequence
   (sequence: `a_k = base + k·delta`). Law 1 (`fi = 1/(n·delta)`) is an empirical observation
   across all tested `(n, base, delta, alpha, seed)` combinations in the corpus. Its
   mathematical derivation from LRC axioms is NOT established in this claim — the formula
   is empirically exact to machine precision but is stated as an observation, not a theorem.

5. Law 2 (`iso ≥ phi_n`) is an empirical lower bound, not a proven theorem.
   It holds universally across all 55,000 arithmetic rows in this corpus. Universality is
   not asserted beyond this dataset. The tightness of the bound (rows where iso = phi_n
   exactly) is not characterized in this claim and is recommended for follow-up.

6. Law 3 (`mode(iso | n) = 3·phi_n`) is a modal pattern — it describes the most
   frequently occurring value of `isolation_count` for each n, not a fixed per-row formula.
   Known exceptions: n=11 (mode=32 vs 3·phi=30), n=13 (mode=40 vs 3·phi=36),
   n=14 (mode=20 vs 3·phi=18). In all three exceptions, mode > 3·phi_n (not below).
   These deviations do not falsify Law 3 for the 8 conforming n values.

7. No row filtering beyond `family = arithmetic` was applied. All 55,000 arithmetic rows
   were included in all three law verifications; no rows were dropped for missing values,
   outlier status, or other criteria.

8. The 000056 corpus uses a continuous-time simulation regime. The boundary count law
   `bc = 5000·n(n-1)` from CLAIM-LRC-000044 (discrete 5000-step simulation) does NOT
   transfer to this dataset. Claims here are independent of CLAIM-LRC-000044 findings.

9. These three laws are logically independent of each other and of the phi_match claim
   in CLAIM-LRC-000056. Law 1 concerns timing, Law 2 a count lower bound, Law 3 a
   modal pattern. They are bundled for adjudication convenience; they may be split
   into separate claims at the quorum committee's discretion.
