# Case-2 Universal CRT Attempt (v1)

## Objective
Prove universally (all `n`, all Case-2 tuples):

`I_bad - P_bad + T_bad <= n(B_div-(n-1))`  (C2-main(C))

which implies `|B_safe|>=n-1` and hence `x0>=phi(n)`.

---

## Fiber-level residue-class expansion
Fix tuple `E`, `n`, `L=lcm(E)`, `N=nL`, and admissible fiber `b in B_div`.
For each non-divisible speed `e in E_non`, define:

- `x_e(b) = (e b mod N)`
- `u_e(b) = floor(x_e(b)/L) in {0,...,n-1}`
- `d_e(b) = x_e(b) mod L`.

For `a in Z_n`:

`e(aL+b) mod N = (L*(e a + u_e(b)) + d_e(b)) mod nL`.

So the bad condition (`<L` or `>(n-1)L`) is equivalent to at most two linear congruences:

1. `e a ≡ -u_e(b) (mod n)`
2. if `d_e(b)>0`, also `e a ≡ -u_e(b)-1 (mod n)`.

Hence each speed contributes a bad-a set that is the union of at most two congruence classes in `Z_n`.

---

## CRT branch-intersection counts
For any speed subset `J` and branch choices `sigma in {0,1}^{|J|}` (allowed by `d_e(b)`), define residues

`c_e^{(sigma_e)}(b) = -u_e(b) - sigma_e (mod n)`.

Define branch intersection count:

`M_{J,sigma}(b) = #{a in Z_n : e a ≡ c_e^{(sigma_e)}(b) (mod n) for all e in J}`.

By generalized CRT, `M_{J,sigma}(b)` is exactly:
- `0` if compatibility fails,
- otherwise `n / lcm_{e in J}(n/g_e)`, where `g_e=gcd(e,n)`.

(Equivalent size form when compatible: `M_{J,sigma}(b)=gcd(n, {e}_{e in J})`.)

So, fiber moments are exact finite sums:

`I_b = sum_{|J|=1} sum_sigma M_{J,sigma}(b)`

`P_b = sum_{|J|=2} sum_sigma M_{J,sigma}(b)`

`T_b = sum_{|J|=3} sum_sigma M_{J,sigma}(b)`.

Thus

`I_b - P_b + T_b = sum_{t=1}^3 (-1)^{t+1} sum_{|J|=t} sum_sigma M_{J,sigma}(b)`.

This is the requested residue-class/CRT expansion.

---

## Global bad-fiber inequality in CRT form
With bad-fiber indicator `1_bad(b)`:

`I_bad - P_bad + T_bad`

`= sum_{b in B_div} 1_bad(b) * [sum_{t=1}^3 (-1)^{t+1} sum_{|J|=t} sum_sigma M_{J,sigma}(b)]`.

So C2-main(C) becomes a purely finite CRT-count inequality:

`sum_{b in B_div} 1_bad(b) * F_b <= n(B_div-(n-1))`,

where `F_b` is the bracketed CRT branch sum.

---

## What is now proved vs open
### Proved in this attempt
1. Exact per-speed bad-set decomposition into <=2 congruence branches.
2. Exact pair/triple branch intersection counting by CRT.
3. Exact reconstruction of `I_b,P_b,T_b` from branch CRT sums.

### Computational validation
- Exhaustive: `n=3,4,5` Case-2 grids.
- Random: `n=6,7,8` (thousands of tuples, sampled admissible fibers).
- All checks passed for the identities.

### Remaining universal step
Control the weighted sum over **bad fibers only**:

`sum_{b in B_div} 1_bad(b) F_b`.

This is where the global theorem still needs a closed-form upper bound.

---

## Suggested next theorem move
Prove a uniform upper bound on average branch contribution over bad fibers:

`(1/C_bad) * sum_{bad b} F_b <= n * (B_div-(n-1))/C_bad`.

Natural route: classify `b` by finite residue signatures of `(u_e(b), 1_{d_e(b)>0})_{e in E_non}` and aggregate each class with CRT counts.

Artifacts:
- `lrc_case2_residue_crt_identity_checker_v1.py`
- `lrc_case2_residue_crt_identity_summary_v1.md`
- `lrc_case2_c23_c24_checker_v2.py`
- `lrc_case2_c23_c24_summary_v2.md`
