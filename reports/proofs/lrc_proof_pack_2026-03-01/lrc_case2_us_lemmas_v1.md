# Case-2 First U_s Lemmas (v1)

## Goal
Build classwise bounds `N_s^bad <= U_s` from CRT compatibility / coverage constraints, then test

`sum_s U_s F_s <= n(B_div-(n-1))`.

Here signature class `s` is on admissible fibers `b in B_div`, with class size `N_s` and class weight
`F_s = I_s - P_s + T_s`.

---

## U_s Lemmas
### Lemma U1 (capacity obstruction)
For signature `s`, each non-divisible speed contributes at most `(1+delta_e)g_e` covered `a` points,
`g_e=gcd(e,n)`, `delta_e in {0,1}`.
So bad coverage (`cover_s=n`) requires

`sum_e (1+delta_e) g_e >= n`.

Define bound:

`U_s^cap = N_s` if capacity condition holds, else `0`.

This has **no false negatives** on tested grids (necessary condition), but many false positives.

### Lemma U2 (solvable-branch capacity)
Refine U1 by counting only solvable branches per speed (`s_e in {0,g_e,2g_e}` from residue divisibility).
Bad coverage requires

`sum_e s_e >= n`.

Define bound:

`U_s^solv = N_s` if solvable-capacity condition holds, else `0`.

Also no false negatives on tested grids; fewer false positives than U1 in some n.

### Lemma U3 (exact coverage obstruction)
For fixed signature, the q-profile over `a in Z_n` is deterministic. Therefore coverage size `cover_s`
is deterministic and

`N_s^bad = N_s * 1_{cover_s=n}`.

Define exact classwise bound:

`U_s^cov = N_s` if `cover_s=n`, else `0`.

This is exact (not just necessary).

---

## Symbolic checker results (bounded exhaustive Case-2 grids)
Using `sum_s U_s F_s <= n(B_div-(n-1))`:

- `U_s^cap` proves a substantial subset but not all tuples.
- `U_s^solv` improves over `U_s^cap` at n=4,6 but still not universal.
- `U_s^cov` proves all tested tuples (exactly matches actual bad-class occupancy).

So first U_s lemmas are established; remaining universal work is to turn exact class occupancy into a
closed-form bound without per-signature brute evaluation.

Artifacts:
- `lrc_case2_signature_us_checker_v2.py`
- `lrc_case2_signature_us_summary_v2.md`
- `lrc_case2_universal_crt_attempt_v2.md`
