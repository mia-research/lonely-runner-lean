# Gap-2 Generalization Probe Summary (v1)

Date: 2026-03-03  
Purpose: support-check the new generalization sections (§17.25–§17.26) beyond the tracked prime family.

## Scope
- Prime probe:
  - `n in {7,11,13}`
  - `|E_div| in {2,3}`
  - randomized `E_fix` subsets (size `n-2-d`)
  - divisible factors sampled from `1..8`
  - admissible `M` values with `gcd(M,nL0)=1`
- Composite unit-scope probe:
  - `n in {8,9,10,12}`
  - same `d` range and sampling style
  - unit-speed hypothesis enforced: all `e in E_fix` and `M` coprime to `n`

## Results
- `prime_templates_tested = 2100`
- `prime_affine_exact_pass = 2100`
- `prime_slope_positive = 2050`
- `prime_slope_zero = 50`
- `prime_slope_nonint = 0`

Zero-slope witness (prime scope):
- `n=7`, `E_fix=[3,4,5]`, divisible factors `[5,6]`
- `S(M)` sample values: `(1,2), (11,2), (13,2), (17,2), (19,2)`

Composite unit-scope local-no-bad check:
- `composite_unit_templates_tested = 260`
- `composite_unit_local_no_bad_pass = 260`
- `composite_unit_local_no_bad_fail = 0`

## Interpretation (support-only)
- Exact affine `S(F,M)` behavior appears stable across broader prime templates.
- A genuine prime zero-slope subclass exists, so global all-prime closure cannot rely only on `s1_F>0`.
- The local component-band no-bad mechanism extends cleanly to tested composite unit-scope templates.

This probe is support only and is not used as a proof step.
