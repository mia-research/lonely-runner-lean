# Assumptions: CLAIM-LRC-000057

1. CSV rows are valid and schema-consistent; source integrity verified by SHA-256
   `230183bfcc95b2ae90ecbfc70a6e0e645b7fb01f1599f2819c3d164292916aa7`.
2. `Agreement` (true/false) is the ground-truth correctness indicator for this dataset.
3. `Boundary Isolated` and `Brute Isolated` are counts of isolated LRC phases produced
   by the respective methods on the same input case.
4. `Speedup = Brute Time / Boundary Time` as recorded; timing values reflect
   wall-clock or CPU time under consistent hardware conditions.
5. This is a dataset claim over 100 test cases; it is not asserted to generalise to
   all possible LRC inputs, parameter ranges, or hardware environments.
6. No row filtering or case selection bias is assumed beyond the 100 cases present.
7. Timing measurements carry floating-point representation noise (float32 artifact
   visible in values such as 13.200000017881393); this does not affect correctness
   of the Agreement or isolation count columns.
