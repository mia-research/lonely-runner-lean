# Case-2 Structural Necessity Chain (v1)

## Objective
Provide a theorem chain that treats Case-2 closure as a structural necessity problem,
not a numerical bound-search problem.

Target statement:

`x0(E) >= phi(n)` for every Case-2 tuple `E` (`|E|=n-1`, gcd-1, at least one `e` divisible by `n`).

We use the stronger candidate target `x0(E) >= n-1`.

---

## Setup
Fix a Case-2 tuple `E` at size `n`.
Let
- `B_div` be divisible-feasible fibers,
- for each `b in B_div`, `A_b subseteq Z_n` the set of safe `a` values,
- `cover(b) = n - |A_b|`,
- `delta_b = |A_b| = n - cover(b)`.

Then exactly:

`x0(E) = sum_{b in B_div} delta_b`.

For each non-divisible speed `e`, define branch-bad residues in `a`:
- `B_e(b) subseteq Z_n` (size 0, 1, or 2 depending on solvability and boundary flag).

A residue `a` is unsafe at fiber `b` iff `a in union_e B_e(b)`.

---

## Lemma S1 (Structural Obstruction Equivalence) — PROVED
For `b in B_div`, the following are equivalent:

1. fiber `b` is bad (`A_b=emptyset`),
2. `cover(b)=n`,
3. `union_e B_e(b) = Z_n`,
4. `delta_b=0`.

### Proof
Directly from definitions:
`A_b = Z_n \ union_e B_e(b)`, so emptiness of `A_b` is exactly full union coverage.
Also `delta_b=|A_b|` and `cover(b)=n-|A_b|`. ∎

---

## Lemma S2 (Feasible-Signature Path Lemma) — PROVED
The realized signature sequence as `b` runs through `B_div` is a one-parameter event path,
not an arbitrary product assignment.

### Formal statement
For each non-divisible speed `e`, define
- `t_e(b)=floor(e b / L)`,
- `d_e(b)=1[(e b mod L)>0]`.

Then the full signature `sigma(b)=((t_e(b),d_e(b)))_{e in E_non}` changes only at event indices

`Xi = union_{e in E_non} { ceil(mL/e) : m=1,...,e-1 }`.

Hence `B_div` decomposes into finitely many event intervals on which `sigma` is constant.
Equivalently, realized signatures are exactly the image of a 1D walk through event cells.

### Consequence
Any universal bound may use only realized signature classes; abstract independent signature counts
are irrelevant overestimates.

---

## Lemma S3 (Obstruction-Hit Counting Lemma) — OPEN (the final structural gap)
Let event cells be indexed by `j`, each with occupancy `N_j` and fixed signature `sigma_j`.
Define obstruction indicator

`I_j = 1[ union_e B_e(sigma_j) = Z_n ]`.

Then

`C_bad = sum_j N_j * I_j`,
`x0 = sum_j N_j * (n - cover_j)`.

### Required universal claim
Prove

`sum_j N_j * (1 - I_j) >= n-1`.

Equivalent forms:
- `C_bad <= B_div-(n-1)`,
- `sum_{b in B_div} delta_b >= n-1`,
- `x0 >= n-1`.

This is exactly the global structural obstruction count: full-coverage cells cannot occupy too much
of the feasible path.

---

## Theorem S4 (Aggregate Deficit Closure) — CONDITIONAL ON S3
If Lemma S3 holds for all Case-2 tuples, then:

`x0(E) >= n-1 >= phi(n)`.

### Proof
By S1, non-obstructed fibers are precisely fibers with `delta_b>0`.
S3 gives at least `n-1` worth of non-obstruction mass; equivalently
`sum_b delta_b >= n-1`.
Then `x0=sum_b delta_b >= n-1 >= phi(n)`. ∎

---

## Evidence Status (current)
- S1: proved (definition-level equivalence).
- S2: proved (event decomposition).
- S3: **PROVED for prime n** (2026-03-02). See `lrc_s3_proof_prime_n_v1.md`.
  Composite n residual still open (z_e property fails when gcd(e,n) = d and d|j).
- S4: **PROVED for prime n** (conditional on S3, now unconditional for prime n).

Empirical support for S3 target:
- exhaustive `n=3..7` Case-2 scans: zero violations of `x0>=n-1`;
- random `n=8..12` bounded-`L` stress: zero violations of `x0>=n-1`.

Anchor-only and lower-band-only subarguments are insufficient in general (explicit counterexamples exist),
so S3 must be proved as a global path/occupancy statement.

---

## Immediate Proof Program for S3
1. **Cell criterion:** characterize `I_j=1` using exact CRT branch-cover condition.
2. **Transition control:** bound how obstruction state can persist across adjacent event cells.
3. **Cycle deficit:** show every full traversal in `b` forces at least `n-1` non-obstructed mass.
4. **Conclude S3:** weighted non-obstruction count `>= n-1`.

This is the structural-necessity route to unconditional Case-2 closure.
