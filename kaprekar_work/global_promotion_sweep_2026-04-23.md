# Global Promotion Sweep
## Full-corpus support for the last two endgame claims — 2026-04-23

---

## Purpose

The symbolic endgame had narrowed to two remaining claims:

1. every base-10 fixed point has lead/tail pair in
   `{(5,5),(6,2),(8,2),(9,1)}`
2. every `(9,1)` fixed point satisfies the shell inequalities, hence enters `E`
   once the shell-reduction note is applied.

This note records the full available-corpus check for exactly those two
statements.

---

## Runner

- `scripts/kaprekar_global_promotion_sweep.py`

Machine output:

- `analysis/base10/global_promotion_sweep_2026-04-23.json`

The sweep streams the full current base-10 fixed-point corpus:

- `kaprekar_d3-100_verified.csv`
- `kaprekar_d101-150.csv`
- `kaprekar_d101-1000_multiset.csv`

with the standard duplicate suppression at the `150/151` boundary, for a total
of:

- `9,910,464` fixed-point rows through `d<=1000`.

For each row it:

1. computes the exact lead/tail pair `(g_1,g_m)` by block shell-pairing from
   the digit counts alone,
2. checks whether that pair lies in the allowed set
   `{(5,5),(6,2),(8,2),(9,1)}`,
3. on the `(9,1)` branch, checks:
   - the shell inequalities
     - `A>=q`
     - `B>=q`
     - `C>=q`
     - `D>q`
   - the final `E`-fit itself.

---

## Result

### 1. Lead/tail pair theorem support

Observed pair counts on the full available corpus:

- `(5,5)`: `50`
- `(6,2)`: `499`
- `(8,2)`: `4,440`
- `(9,1)`: `9,905,475`

Everything else:

- bad pair count: `0`

So on every currently available fixed-point row through `d<=1000`,

> the lead/tail pair already lies in
> `{(5,5),(6,2),(8,2),(9,1)}`.

### 2. `(9,1)` shell-inequality support

Rows on the `(9,1)` branch:

- `9,905,475`

Among them:

- shell-inequality failures: `0`
- `E`-fit failures: `0`

So on the full available high-dimensional corpus,

> every checked `(9,1)` fixed point already satisfies the shell inequalities
> and lies in `E`.

---

## Interpretation

This is no longer just local theorem-window evidence.

The remaining gap is now **purely symbolic**:

- no extra lead/tail branch appears anywhere in the full available corpus
- no `(9,1)` counterexample to the shell inequalities appears anywhere in the
  full available corpus

So the theorem endgame has become:

1. prove the four lead/tail pairs symbolically
2. prove the `(9,1)` shell inequalities symbolically

There is no longer any positive computational evidence for a hidden fifth
branch or a hidden non-`E` `(9,1)` family.

---

## Relation to the existing theorem stack

This note does not replace the symbolic notes.

It strengthens them:

- [inner_asymmetry_lemma_2026-04-23.md](/Users/trentpalelei/Desktop/Kaprekar/analysis/base10/inner_asymmetry_lemma_2026-04-23.md)
  reduces the endgame to the `(9,1)` branch plus the four-pair theorem.
- [e_branch_shell_reduction_2026-04-23.md](/Users/trentpalelei/Desktop/Kaprekar/analysis/base10/e_branch_shell_reduction_2026-04-23.md)
  reduces `(9,1) -> E` to the shell inequalities.

This sweep says both reductions are aligned with the full currently available
base-10 corpus through `d<=1000`.
