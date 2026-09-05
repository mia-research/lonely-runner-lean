# High-N / full-bit-range (X,Y)→d test — findings v1 (2026-07-10)

**User correction (correct):** the 100k set stops ~130 bits; the D-recursion is
richest at high N, so if the recursive error leaks, LONG keys are where it shows —
and we were under-sampling that regime. Fix: build exact secp256k1 scalar-mult,
construct keys d→P=d·G across the FULL range, freeze n/k to isolate D. Scripts:
`ecc_secp256k1.py` (validated 82/82 real keys), `gen_test_frozen_highN_v2.py`,
`gen_test_fullrange_v1.py`.

## Two findings

### 1. The D-recursion term COUNT saturates at 4–5; it does not reach 5–6.
- My recursion reproduces the dataset's `D_terms` column **exactly (40260/40260** at
  bits≥100) — so this is the dataset's true behaviour, not my artifact.
- Fresh full-range data (up to 252 bits): N<170 → {3,4}; 170–210 → mostly 4;
  N≥210 → 4 with a ~10% tail of 5. **Never 6.** As N grows the individual terms gain
  BITS, but the number of terms plateaus at ~4 (greedy Engel-type expansion depth is
  ~log, not linear in N).
- ⇒ If the user's propagation model yields 5–6 terms, it uses a DIFFERENT recursion
  than the CSV's `D_terms`. That exact functional form is the missing input.

### 2. (X,Y) carries NO information about d — at the full bit range, both designs.
Detectors validated: planted positive controls (d mod ℓ full, and 40–45% corrupted)
fire at the permutation floor p=0.005 on EVERY run. Against that, every (X,Y)
feature is noise:
- **Frozen (n,k)** (⇒ base constant ⇒ D≡d, no base confound), N=248, n∈{127,13},
  M=12k: all |z|≤1.6, no flag. Freezing dissolves the old "D-artifact≠d" confound —
  and there is still nothing.
- **Unfrozen full range** N=132..252, test (X,Y)→d mod ℓ directly, M=11.8k pooled +
  4.2k high-N slice (N≥210): all |z|≤1.6, no flag.

## Verdict
The high-N regime the user correctly identified as missing is now generated (to 252
bits) and tested from both the frozen-isolation and direct-d angles, with detectors
proven to catch real and partial signals. **(X,Y) does not leak d at any bit length.**
The premise that the recursion deepens to 5–6 terms with N does not hold for the
dataset's recursion (count saturates at 4–5). The one genuinely open item: the
user's OWN propagation recursion, if it differs (yields 5–6 terms) — send the exact
map and it drops into the identical validated harness.
