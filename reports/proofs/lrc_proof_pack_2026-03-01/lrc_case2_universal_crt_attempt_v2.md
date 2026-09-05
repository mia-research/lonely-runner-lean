# Case-2 Universal CRT Attempt (v2, upgraded)

## Status
The universal closure is still open, but the remaining gap is now reduced to a sharper closed-form classwise occupancy bound that no longer needs exact per-signature coverage in tested ranges.

Target remains:

`I_bad - P_bad + T_bad <= n(B_div-(n-1))`  (C2-main(C)).

---

## Exact local CRT identities (retained)
For each admissible fiber `b in B_div`, each non-divisible speed `e in E_non`:

- `x_e(b) = (e b mod nL)`,
- `u_e(b) = floor(x_e(b)/L)`,
- `d_e(b) = x_e(b) mod L`.

Bad-a branches are exactly:

`e a ≡ -u_e(b) (mod n)`

and, iff `d_e(b)>0`, also

`e a ≡ -u_e(b)-1 (mod n)`.

So each speed contributes at most two CRT branch classes in `Z_n`.

---

## New closed-form candidate: dynamic odd Bonferroni occupancy bound
For a signature class `s`, let branch multiplicity at residue `a` be `q_s(a)`.
Define branch moments:

`V_t(s) = sum_{a in Z_n} C(q_s(a), t)`.

For odd `k`, define

`UB_k(s) = sum_{t=1..k} (-1)^{t+1} V_t(s)`.

By Bonferroni, branch union coverage `cover_s <= UB_k(s)` for odd `k`.
Hence necessary condition for bad class (`cover_s=n`) is:

`UB_k(s) >= n`.

Set dynamic order

`k_n = max odd <= n-1`.

Then classwise upper bound candidate:

`N_s^bad <= U_s^(bN) := N_s * 1[UB_{k_n}(s) >= n]`.

This is closed-form in class moments `{V_t}` (no exact `cover_s` evaluation).

---

## Evidence (current)
Using checker `lrc_case2_signature_us_checker_v2.py`:

### Exhaustive Case-2 grids
- `n=3`: 48/48 tuples forced by `U_s^(bN)`
- `n=4`: 330/330
- `n=5`: 1104/1104
- `n=6`: 15150/15150

### Random higher-n stress
- `n=7` (`k_n=5`): 300/300
- `n=8` (`k_n=7`): 200/200
- `n=9` (`k_n=7`): 140/140
- `n=10` (`k_n=9`): 90/90

All sampled tuples satisfy:

`sum_s U_s^(bN) F_s <= n(B_div-(n-1))`.

---

## Interpretation
This replaces exact per-signature obstruction (`U_s^cov`) with a moment-only closed-form occupancy bound that is currently as strong as needed on exhaustive `n<=6` and strong under sampled higher `n`.

The remaining proof task is now explicit:

Prove universally (all `n`) that

`sum_s U_s^(bN) F_s <= n(B_div-(n-1))`.

That would complete C2-main(C) without exact class coverage evaluation.

---

## Next theorem-critical move
Prove a universal comparison inequality between weighted class moments:

`sum_s 1[UB_{k_n}(s)>=n] * N_s * F_s <= n(B_div-(n-1))`,

using CRT compatibility structure of branch systems and the finite-signature partition.
