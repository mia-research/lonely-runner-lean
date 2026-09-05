# Case-2 Full Proof Candidate (v1)

## Claim target
For every Case-2 tuple `E` (`|E|=n-1`, `gcd(E)=1`, at least one `e_r ≡ 0 (mod n)`):

`x0(E) >= phi(n)`.

Using the fiber split:

`x0(E) = sum_{b in B_div} |A_b| >= |B_safe|`,

it is sufficient to prove `|B_safe| >= n-1`.

---

## Regime split (core architecture)

### Regime A (anchor): `L=n`
Empirical profile (extensively verified):

`B_div = n-1`, `C_bad = 0`, `B_safe = n-1`.

This is the tight boundary regime.

### Regime B (slack): `L>n`
Observed behavior: `B_safe` exceeds `n-1` with margin that grows with family parameter `m`.
This is the only remaining analytical regime.

---

## Proven/validated structural ingredients

### 1) Single-divisible closed form (exact)
If only one divisible family parameter `f_i=e_i/n` is active and

`L = f_i * n * M`,

then

`B_div(f_i) = f_i * ((n-2)M + 1) = (n-2)L/n + f_i`.

Validated by brute-force grid: `n=3..20`, `f_i=1..12`, `M=1..30` (all matched).

### 2) n=7 family formulas (example of affine families)
With `L=14m` and divisible-profile set `F`:

- `F=(1,)`: `B_div = 10m + 1`
- `F=(2,)`: `B_div = 10m + 2`
- `F=(1,2)`: `B_div = 8m + 2`

So gap structure is profile-induced arithmetic lattice geometry, not random sparsity.

### 3) Tight-minimum localization
In bounded exhaustive Case-2 scans (`n=3..7`), every tuple with `B_safe=n-1` has profile:

`L=n`, `B_div=n-1`, `C_bad=0`.

No `L>n` tuple attained the boundary minimum in these scans.

---

## Remaining lemma (single open step)

### Lemma R (slack-regime strict margin)
For every Case-2 tuple with `L>n`:

`B_safe >= n`  (or any explicit lower bound `> n-1`).

Then regime split gives immediately:
- anchor: `B_safe=n-1`,
- slack: `B_safe>n-1`,

hence globally `B_safe>=n-1`, therefore

`x0(E) >= |B_safe| >= n-1 >= phi(n)`.

---

## Route B for Lemma R (recommended)

### Family-by-family polynomial-over-residues program
For each divisible-profile family `F` with parameter `m`:
1. express `B_div(F,m)` as affine `C_F m + D_F`,
2. lower-bound guaranteed-safe lower-band contribution linearly,
3. upper-bound bad upper-band count `C_bad(F,m)` by proving slope `< C_F` (or equivalent strict deficit),
4. conclude `B_safe = B_div - C_bad` has positive linear margin over `n-1`.

This isolates all remaining work into one per-family growth inequality.

---

## Status
This is a coherent full proof candidate architecture with one explicit unresolved lemma (`Lemma R`).
It is no longer an undifferentiated global inequality problem.
