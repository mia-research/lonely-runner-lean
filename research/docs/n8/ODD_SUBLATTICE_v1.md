# The parity route: why the proposed closure fails, and the repair that works

The proposed argument was: the order-6 clear window contains two consecutive candidate indices;
consecutive integers alternate in parity; so one is odd and `b = 2` is satisfied. The shape is
right and the repair below comes straight out of it — but as stated it cannot work, for a reason
that is decisive rather than quantitative.

Lean: `experiments/n8/OddSublattice_v1.lean` (6 theorems, axiom-clean; five need only
`[propext, Quot.sound]`). Scripts: `window_length_v1.py`, `odd_sublattice_v1.py`.

---

## 1. Step 3's premise is unsatisfiable exactly when `b = 2` occurs

Clearing at `b = 2` is `q` odd. So **the clear set *is* the odd integers**, and it contains no two
consecutive members — by definition, not by accident.

Step 3 needs an interval holding two consecutive indices that are *both* clear. When `b = 2` is a
modulus, no such interval exists. **[VERIFIED]** with `b = 2` present, the longest run of
consecutive clear indices is **1**: median 1, max 1, and `≥ 2` consecutive in **0.0%** of 827
profiles. For comparison, `b_min = 3` gives median 2, `b_min ≥ 10` gives median 10.

So the step is not hard to establish; it is false in the one case it was introduced to handle.

## 2. Step 2 also mis-measures the window

The `1/6` of `intLRC_six` is a **circle-distance margin**, not a length in scale space. Perturbing
`t` by `δ` moves `dist(t/b, ℤ)` by `δ/b`, so holding the `1/8` threshold allows `δ ≤ b/24`: the
window's length in index units is **`b_min/12`**, governed by the *smallest* modulus, not by `m`.

Two consecutive integers therefore need `b_min ≥ 24` — which sits inside the `b ≥ 10` case already
closed by `DivisorOrder6`, so it wins no new ground. The claimed count of `m/6` grid points
overstates by a factor of order `m`.

## 3. The repair: force the parity, do not recover it

Substitute `q = 2u + 1`. Then the acute case dissolves, and two more with it:

| modulus | odd-index residues | window | status on the odd sublattice |
|---|---|---|---|
| `b = 2` | `{1}` | `{1}` | **vacuous** (`two_vacuous`) |
| `b = 4` | `{1,3}` | `{1,2,3}` | **vacuous** (`four_vacuous`) |
| `b = 6` | `{1,3,5}` | `{1,…,5}` | **vacuous** (`six_vacuous`) |
| `b = 3` | — | `{1,2}` | `u ≢ 1 (mod 3)` (`three_iff`) |
| `b = 8` | `{1,3,5,7}` | `{1,…,6}` | `u ≢ 3 (mod 4)` (`eight_iff`) |
| `b = 9` | — | `{1,…,7}` | `u ≢ 4` and `u ≢ 8 (mod 9)` (`nine_iff`) |

**[PROVED]** all six. Forcing the parity makes `b = 2`, `4` and `6` disappear outright, and the
`b = 8` condition **halves** its modulus from `8` to `4`.

**[VERIFIED]** with `b = 2` present, the longest run of consecutive admissible `u` is median 3,
max 33, `≥ 2` consecutive in 97.3%, and **never 0** across 1,500 profiles — the obstruction of §1
is gone.

### A correction Lean forced

`nine_iff` was first written as `u ≢ 8 (mod 9)`, by analogy with `b = 3` and `b = 8`. That is
false: at `b = 9` the window is `[1,7]`, so **two** residues are blocked, and unlike the other two
cases an odd index can still land on `0` mod `9` — at `u ≡ 4`. The `FourResidues` list names only
`8` because there the band already excludes `0`; stated without the band, both are needed. The
analogy was the error, and the proof assistant caught it.

## 4. Where this leaves the open step

`FourResidues` reduced it to four exclusions at `b ∈ {2,3,8,9}`. On the odd sublattice it is
**three**, at `b ∈ {3,8,9}`, with the acute one removed:

> **`[OPEN]`** For every commensurable profile there is a generating reading whose order-6 band
> contains an odd candidate `q = 2u+1` with `u ≢ 1 (mod 3)`, `u ≢ 3 (mod 4)`, and `u ≢ 4, 8
> (mod 9)`, for whichever of those moduli occur.

What is **not** yet established is that the order-6 margin argument transfers to the `u`-problem:
its windows have different widths (`2/3` at `b = 3`, `6/8` at `b = 8`, `7/9` at `b = 9`) and are
not centred as the `q`-windows are. The `97.3%` above is a measurement, not a theorem, and the
remaining `2.7%` is real.

Existence at order 8 remains open.
