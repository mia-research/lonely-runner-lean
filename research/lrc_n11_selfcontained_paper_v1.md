# The Lonely Runner Conjecture for `n = 11`: Self-Contained Rewrite Draft

**Author:** Trent Palelei  
**Date:** 2026-03-30  
**Status:** Exact self-contained rewrite draft. This document internalizes the stable `n = 11` setup, the no-divisible branch, and the exact actual-state reduction for the hard exactly-one-divisible branch. It does **not** yet close the final weighted occupancy theorem for that hard branch, and it does **not** claim a completed standalone proof of the full theorem.

---

## Abstract

We rewrite the `n = 11` project into a single standalone line that is explicit
about what is already exact and what remains open in the present workspace.
The paper has three aims:

1. give a self-contained discrete setup for the classical `n = 11` problem;
2. prove the no-divisible branch directly;
3. replace the old template-normalization shorthand in the actual exactly-one-divisible
   branch by an exact finite local-state certificate pack on actual tuples.

The hard branch now has a genuinely finite exact local formulation. Its local
bad geometry compresses to `1268` multiplicity profiles, of which exactly `45`
are fully covered and exactly `38` are actual bad profiles. The remaining
global theorem is a weighted bad-occupancy inequality along `B_div`:

```text
sum_j N_j <= B_div - 10.
```

That exact finite reduction is self-contained in this draft and in the frozen
artifact pack under
`reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/`.

---

## 1. Setup and Normalization

Let

```text
E = (e_1, ..., e_10)
```

be a gcd-`1` tuple of distinct positive integers. Set

- `L = lcm(E)`,
- `N = 11L`.

Define the safe-point count

```text
x_0(E) = #{ k in {1,...,N-1} : (e_i k mod N) in [L,10L] for all i }.
```

Then `x_0(E) > 0` is equivalent to the classical Lonely Runner Conjecture for
the tuple `E`.

We split the tuple by divisibility by `11`:

- `E_div = { e in E : 11 | e }`,
- `E_non = E minus E_div`.

The intended main theorem for a finished standalone paper is:

> **Main Theorem.** For every gcd-`1` tuple `E` of `10` distinct positive
> integers, one has `x_0(E) > 0`.

This draft does not yet prove the Main Theorem in full. It proves the
no-divisible branch and gives an exact finite reduction for the hard actual
exactly-one-divisible branch.

---

## 2. Branch Decomposition by Divisibility by `11`

There are three mutually exclusive cases:

1. `|E_div| = 0`,
2. `|E_div| = 1`,
3. `|E_div| >= 2`.

The original plan for this rewrite was:

- analytic proofs for Cases `0` and `>= 2`,
- an exact finite certificate for Case `1`.

The current corpus supports the first item only for Case `0` in a fully
self-contained way. For Case `>= 2`, older analytic exports exist, but the
workspace does not currently contain a clean standalone rebuild that avoids
importing unresolved or superseded dependencies. For Case `1`, the local exact
certificate layer is now precise and frozen, but the final weighted occupancy
theorem is not yet proved.

So the honest content of the present draft is:

- Case `0`: proved here.
- Case `1`: reduced here to one explicit finite certificate target.
- Case `>= 2`: recorded here as an export target, not yet internalized to the
  same standard as Cases `0` and `1`.

---

## 3. No-Divisible Branch

> **Proposition 3.1.** If `E_div = emptyset`, then `x_0(E) >= 10`.

**Proof.** Consider the `10` times

```text
k_j = jL,   j = 1,...,10.
```

For any `e in E`,

```text
e k_j mod 11L = L * (e j mod 11).
```

Because `11` is prime and `11` does not divide `e`, the residue `e j mod 11`
is nonzero, hence belongs to `{1,...,10}`. Therefore

```text
e k_j mod 11L in [L,10L]
```

for every runner `e` and every `j = 1,...,10`. So each `k_j` is safe, and
`x_0(E) >= 10`. `square`

---

## 4. Multiple-Divisible Branch

This section records the exact status of the standalone rebuild for the branch
`|E_div| >= 2`.

### 4.1 What is stable

The following mechanism is stable across the existing notes:

- write each divisible speed as `11K_i`,
- regular divisible runners are transparent on the lower band,
- the remaining obstruction comes from extreme divisible runners,
- the correct combinatorial object is a lower-band fibre count.

### 4.2 What is not yet rebuilt here

The workspace does not currently contain a standalone rebuild of the full
multiple-divisible branch that is both:

- independent of the omnibus prime-branch export machinery, and
- free of the older unresolved H1b-style bookkeeping issues.

Accordingly, this draft does **not** claim a self-contained proof of the
multiple-divisible branch. The branch remains an explicit export target for a
future revision of this document.

---

## 5. Exactly-One-Divisible Branch: Easy Exact Structure

We now turn to the hard branch `|E_div| = 1`.

Write the unique divisible speed as

```text
d = 11q,
```

and write

- `E = {d} union E_non`,
- `L = lcm(E)`,
- `M = L / 11`.

### 5.1 Actual-divisible fibres

Define

```text
B_div = { b in {0,...,L-1} : L <= d b mod 11L <= 10L }.
```

This is the set of fibres on which the divisible runner is already safe.

### 5.2 Anchor / pure-pair reduction

Write each fibre as

```text
b = 11c + r,   0 <= r <= 10.
```

For each `e in E_non`, set `m_e = L / e = 11 h_e`; this is divisible by `11`
because `e` is coprime to `11` and `L` contains exactly one factor `11`
coming from `d`.

> **Lemma 5.2 (Pure-pair strip lemma).** If `1 <= r <= 10`, then every
> non-divisible runner is on a 2-point branch at `b = 11c + r`, and the full
> local profile is constant across the whole strip
> `11c + 1, ..., 11c + 10`.

**Proof.** A non-divisible runner `e` is singleton exactly when `m_e | b`,
equivalently when `e b / L` is an integer. Since `m_e` is divisible by `11`,
this can happen only when `r = 0`. So for `1 <= r <= 10`, every non-divisible
runner is a pair runner.

Moreover,

```text
floor(e b / L) = floor((11c + r) / (11 h_e)) = floor(c / h_e),
```

because `0 < r < 11 <= 11 h_e`. Thus the bad set of `e` depends only on `c`,
not on `r`, and the full local profile is constant on the strip. `square`

> **Corollary 5.3.** Every non-anchor fibre has total branch mass `T = 18`.

### 5.3 Anchor fibres

At an anchor fibre `b = 11c`, a non-divisible runner `e` is singleton iff
`h_e | c`; otherwise it remains a pair runner.

> **Lemma 5.4 (Anchor characterization).** If a fibre has at least one
> singleton runner, then it is an anchor fibre `b = 0 (mod 11)`. Equivalently,
> every non-anchor fibre is pure-pair with `T = 18`.

This is immediate from the discussion above.

### 5.4 Anchor monotonicity

> **Lemma 5.5 (Anchor monotonicity).** Let `b = 11c` be an anchor in `B_div`.
> Then
>
> ```text
> Cover(b) subseteq Cover(b-1),   Cover(b) subseteq Cover(b+1),
> ```
>
> whenever the neighbouring fibres lie in `B_div`.

**Proof sketch.** If a runner is singleton at `b`, then moving to `b +/- 1`
keeps the old singleton residue and adds one new residue. If a runner is pair
at `b`, then the step from `b` to `b +/- 1` is too small to cross an integer
boundary in the floor term, so the same pair persists. Thus no residue covered
at `b` can disappear immediately at `b-1` or `b+1`. `square`

> **Corollary 5.6.** A bad anchor can occur only between bad pure-pair
> neighbours.

So the persistent bad occupancy lives on the pure-pair strip sequence; the
anchor fibres are subordinate transition points.

---

## 6. Actual-Signature Reduction for the Hard Branch

The local exact object at a fibre `b in B_div` is the branch multiplicity
profile

```text
q = (q(a))_{a in Z_11},
```

where `q(a)` counts how many singleton/pair branch hits land at residue `a`.
After sorting, only

```text
q^down = (q_1,...,q_11)
```

matters for the local coverage statistics used below.

### 6.1 Exact finite local kernel

Each of the `9` non-divisible runners contributes either a singleton or a
2-point subset of `Z_11`. So the exact local state space is the set of sorted
profiles reachable from `9` successive singleton/pair insertions.

The frozen pack proves:

- total reachable local profiles: `1268`,
- fully covered local profiles: `45`.

These are written in
`reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_local_profile_rows_2026-03-30.csv`.

### 6.2 Local Bonferroni data

For a local profile `q^down`, define

```text
UB5(q) = sum_i q_i - sum_i C(q_i,2) + sum_i C(q_i,3) - sum_i C(q_i,4) + sum_i C(q_i,5),
```

and

```text
UB9(q) = sum_{t=1}^9 (-1)^{t+1} sum_i C(q_i,t).
```

Because `11` is prime and every non-divisible runner is coprime to `11`, the
capacity and solvability terms coincide locally with the total branch mass

```text
T(q) = sum_i q_i.
```

So the frozen local lower bound used in the pack is

```text
local_lb(q) = max(0, 11 - min(11, T(q), UB9(q))).
```

This is a local exact lower bound on the number of safe residues at a fibre.

### 6.3 Exact actual bad-state theorem

Let `q^down` be a fully covered local profile and write `T = sum_i q_i`.
Since each of the `9` non-divisible runners contributes either one or two hits,
the singleton-runner count is

```text
s = 18 - T.
```

All singleton runners collapse to one common residue, so every actual bad
profile must satisfy

```text
q_1 >= s = 18 - T.
```

The frozen pack verifies that among the `45` fully covered local profiles:

- exactly `38` satisfy this criterion and have explicit witness tuples,
- exactly `7` fail it and are impossible as actual bad profiles.

This yields:

> **Theorem 6.7 (Exact actual bad-state theorem).** A fully covered local
> profile `q^down` in the actual exactly-one-divisible `n = 11` branch is
> actual if and only if
>
> ```text
> q_1 >= 18 - sum_i q_i.
> ```

The `38` witnessed actual bad profiles are frozen in
`reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_actual_bad_state_witnesses_2026-03-30.csv`.

---

## 7. Exact Finite Certificate Theorem

This section states exactly what the frozen artifact pack certifies today.

> **Theorem 7.1 (Frozen exact local certificate).** The artifact pack under
> `reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/` certifies,
> using exact integer combinatorics only, the following facts for the actual
> exactly-one-divisible `n = 11` branch:
>
> 1. the local multiplicity-profile kernel has exactly `1268` reachable states;
> 2. exactly `45` of those states are fully covered;
> 3. exactly `38` fully covered states are actual bad states;
> 4. exactly `7` fully covered states are impossible by singleton collapse.

**Proof.** The builder script

```text
tools/build_lrc_n11_selfcontained_certificate_pack.py
```

enumerates the local kernel by repeated insertion of singleton or 2-point
contributors on `Z_11`; no floating-point arithmetic or randomization is used.
It computes coverage, `UB5`, `UB9`, the exact singleton-collapse classifier,
and writes the frozen rows together with a manifest of hashes. Running the
builder reproduces the counts above and emits the manifest

```text
lrc_n11_selfcontained_certificate_manifest_2026-03-30.json.
```

`square`

### 7.2 What the pack does not certify

The pack closes the local-state layer. It does **not** yet certify the global
weighted occupancy inequality on the bad event-path decomposition along
`B_div`.

The remaining theorem target is:

> **Occupancy Theorem O11.** For every actual exactly-one-divisible `n = 11`
> tuple,
>
> ```text
> sum_j N_j <= B_div - 10.
> ```
>
> Equivalently, `x_0(E) >= 10`.

This is now the single live global theorem for the hard branch in the present
workspace.

---

## 8. Completion of the Main Theorem

At the time of writing, the current workspace supports the following clean
implication chain:

1. Case `|E_div| = 0` is closed by Proposition 3.1.
2. The actual exactly-one-divisible branch has an exact local finite
   certificate reduction, culminating in Theorem 7.1 and the explicit target
   O11.
3. The multiple-divisible branch remains an export/internalization task for a
   later draft.

So the finished standalone theorem would follow from two remaining items:

- a self-contained proof of the multiple-divisible branch,
- the weighted occupancy theorem O11 for the actual exactly-one-divisible
  branch.

This draft therefore stops at the exact finite frontier rather than claiming a
completed proof.

---

## 9. Appendices for Certificate Specification, Reproducibility, and Non-Dependencies

### Appendix A. Artifact Pack

The self-contained certificate artifacts for the hard branch are:

- `reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_local_profile_rows_2026-03-30.csv`
- `reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_local_bad_profile_rows_2026-03-30.csv`
- `reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_actual_bad_state_witnesses_2026-03-30.csv`
- `reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_impossible_bad_profile_rows_2026-03-30.csv`
- `reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_selfcontained_certificate_appendix_2026-03-30.md`
- `reports/proofs/lrc_n11_selfcontained_certificate_2026-03-30/lrc_n11_selfcontained_certificate_manifest_2026-03-30.json`

### Appendix B. Reproducibility

The pack is regenerated by:

```bash
python3 tools/build_lrc_n11_selfcontained_certificate_pack.py
```

The script is deterministic and uses only the Python standard library.

### Appendix C. Non-Dependencies

The proof path in this draft does **not** use:

- the old template normalization `E = F union {M} union {11}`,
- the false actual-anchor covering theorem,
- PSCC / FSCCC / SCT chamber programs,
- random stress evidence as proof,
- the old open compactness / Route-3 program.

Those objects may be mentioned historically elsewhere in the repository, but
they are not part of the proof path of the exact reduction recorded here.
