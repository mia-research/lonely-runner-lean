# Assumptions: CLAIM-LRC-000043

1. Source integrity verified by SHA-256
   `23ffbf7966ffd15a56878b162206af8bb457e490b6fe26b2b7574a8cb33efe55`.
   The source file `lrc_efficiency_runtime_validation (1).csv` is byte-for-byte identical
   to `lrc_efficiency_runtime_validation.csv`; the "(1)" suffix is a browser download
   artifact. All claims are conditioned on this single source.

2. The corpus covers 4 families (arithmetic, geometric, harmonic, quadratic),
   16 n values {5,7,8,10,11,12,13,15,16,17,19,20,23,25,29,30}, and 6 seeds per (family, n),
   for a total of 384 rows. No rows are excluded from any statement.

3. `efficiency = isolation_count / boundary_count` is the operational definition used
   throughout. This is not claimed to equal a specific analytic formula; it is the
   empirical ratio as stored in the CSV.

4. Statement 1 (per-n efficiency): values are read directly from the CSV and not
   recomputed. Falsification requires recomputing efficiency from isolation_count and
   boundary_count and comparing to stored values.

5. Statement 2 (seed invariance): "seed-invariant" is an informal description. The formal
   claim is that within-n efficiency range ≤ 0.000355 across 6 seeds. No claim is made
   about whether this invariance would hold for additional seeds beyond {0..5}.

6. Statement 3 (phi_over_n precision): phi_over_n is treated as a derived column
   (φ(n)/n truncated to 6 significant decimal places). The precision characterization
   is about the stored value in the CSV, not about the mathematical ratio itself.
   The "medium float risk" label in the dossier is explained by n=30 phi_over_n having
   rel_err=1.25e-6, marginally above the 1e-6 sensitive threshold. The `efficiency`
   and other computed columns are NOT affected by this 6-decimal truncation.

7. This claim is designated P3_context_or_auxiliary. It provides per-n granularity
   and precision diagnostics that contextualize CLAIM-LRC-000044's family-level findings.
   It does not duplicate CLAIM-LRC-000044; the two claims are complementary.

8. No extrapolation is made to n values outside {5,7,8,10,11,12,13,15,16,17,19,20,23,25,29,30}
   or to seeds beyond {0..5}.
