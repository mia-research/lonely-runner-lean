# Independent verification — n=8 Parity Lemma and the [3/5, 5/7) safe-window claim

Date: 2026-09-07. Verifier: independent agent, working only from the definitions supplied
in the task statement (treated as axioms). No manuscript file was read.

Scripts (all written and actually run for this report):

- `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/verify_parity_lemma_v1.py`
- `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/verify_cells_v1.py`
- `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/verify_window_bads_v1.py`
- `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/verify_tuples_v1.py`
- `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/sweep_ediv_v1.py`
- `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/verify_second_window_and_cert_v1.py`
- `/Users/trentpalelei/Desktop/Math Ex/experiments/n8/addendum_rho6_v1.py`

All arithmetic is exact: `fractions.Fraction` for the `x = b/L` geometry, plain `int` for
everything modular. No floating point is used in any decision.

---

## Verdict summary

| # | Item | Result |
|---|---|---|
| 1 | Parity Lemma, unit half | **Correct** |
| 1 | Parity Lemma, non-unit half | **Correct** (one omission of a true sub-case, harmless — see 1c) |
| 2 | Floors and bad sets on `[3/5, 5/7)` | **Correct**, exact rational endpoints check out |
| 3 | "Exactly two mixed-parity cells" | **Correct as to windows; the word "cells" is wrong.** There are **four** mixed-parity cells, forming **two** maximal windows. Terminological, not mathematical. |
| 4 | Integer exists in `[3L/5, 5L/7)` | **Correct**; the stated bound is not tight (`L >= 9` suffices), worst admissible case `L = 24` gives 3 integers |
| 5 | Explicit tuples: `b` safe, and `x_0(E) > 0` | **Both hold in every one of 36 brute-forced tuples**; 828 tuples checked for safety. No counterexample. |
| 6 | Hypotheses vacuous? | **Not vacuous.** Explicit tuple + explicit witness `k` given below. |
| — | **SAFE ⟹ x_0 > 0** | **GAP.** SAFE as defined is not sufficient. See §7 — this is the one finding that affects correctness of the argument as a route to LRC. |

---

## 1. The Parity Lemma

Re-derived from scratch, then checked exhaustively over `t = 0..63` (period in `t` is 8, so
this is exhaustive) — `verify_parity_lemma_v1.py`.

**(a) Every unit is its own inverse mod 8.** `1²=1, 3²=9=1, 5²=25=1, 7²=49=1`. Verified.
Hence `Sol(e, j, 8) = {e·j}` for a unit `e`, and

    bad(e,t,8) = {-t·e, -(t+1)·e}  mod 8.

**(b) Two elements, opposite parity.** The difference is `-e`, odd, so the two elements
have opposite parity; in particular they are distinct, so `|bad| = 2` always. Script
output: `units: bad=={-te,-(t+1)e}, |bad|==2, exactly one odd+one even, all t in 0..63: True`.

**(c) Non-units.** For `e ∈ {2,4,6}`, `g = gcd(e,8) ∈ {2,4}`, kernel of multiplication-by-`e`:

    e=2: H = {0,4}   e=4: H = {0,2,4,6}   e=6: H = {0,4}

Both `H_2` and `H_4` consist of even residues, so every coset `r + H_g` lies inside a single
parity class. This is the correct reason and the manuscript states it correctly.

`bad(e,t,8) = Sol(e,-t,8) ∪ Sol(e,-(t+1),8)`, and `Sol(e,j,8) ≠ ∅` iff `g | j`. Since `-t`
and `-(t+1)` have opposite parity and `g` is even, **at most one** of the two `Sol` sets is
non-empty. So `bad(e,t,8)` is a single coset of `H_g`, or empty. Verified for all `t`.

Attained sizes: `e=2` and `e=6` give `|bad| = 2` always; `e=4` gives `|bad| ∈ {0,4}`
(empty when `t ≢ 0, 3 mod 4`).

**Minor omission, not a defect.** The claim writes "(or is empty)" only for the coset, and
does not say that emptiness occurs *only* for `g = 4`; for `g = 2` exactly one of the two
`Sol` sets always fires, so `bad` is never empty. This strengthens rather than weakens the
lemma. The operative consequence — *a non-unit runner never blocks both an odd and an even
residue* — is verified exhaustively (`[d] ... True`).

**Parity Lemma: correct as stated.**

## 2. Floors and bad sets on x ∈ [3/5, 5/7)

Exact endpoint arithmetic (`verify_window_bads_v1.py`), no decimals:

| e | `e·(3/5)` | `e·(5/7)` | floor at left | floor just below right | conclusion |
|---|---|---|---|---|---|
| 1 | `3/5` | `5/7` | 0 | 0 | `t_1 = 0` throughout |
| 3 | `9/5` | `15/7` | 1 | 2 | `t_3 ∈ {1,2}`, splits at `x = 2/3` |
| 5 | `3` | `25/7` | 3 | 3 | `t_5 = 3` throughout |
| 7 | `21/5` | `5` | 4 | 4 | `t_7 = 4` throughout |

The two boundary cases are the ones worth stating exactly:

- `t_5 = 3`: `5·(3/5) = 3` **exactly** (left endpoint is included, so `t_5 = 3` not 2), and
  `5·(5/7) = 25/7 < 28/7 = 4`. So `[3/5, 5/7)` sits strictly inside `[3/5, 4/5)`, the
  `t_5 = 3` region. Confirmed.
- `t_7 = 4`: `7·(3/5) = 21/5 > 20/5 = 4`, and `7·(5/7) = 5` **exactly** — which is why the
  right endpoint must be **excluded**. `[3/5, 5/7)` sits inside `[4/7, 5/7)`, the `t_7 = 4`
  region. Confirmed. The half-open form of the window is load-bearing here and the claim
  states it correctly.

Bad sets, recomputed from the definition:

    bad(1,0) = {0,7}    bad(3,1) = {2,5}    bad(3,2) = {2,7}
    bad(5,3) = {1,4}    bad(7,4) = {4,5}

    union (t_3 = 1) = {0,1,2,4,5,7}   uncovered {3,6}
    union (t_3 = 2) = {0,1,2,4,5,7}   uncovered {3,6}

All five bad sets and both unions match the claim exactly. Residues 3 (odd) and 6 (even)
are uncovered by the units in both sub-cases, and by §1 a single non-unit runner cannot
block both. **Every `b` with `3L/5 ≤ b < 5L/7` is a SAFE fibre: confirmed.**

Also `[3/5, 5/7) ⊂ [1/8, 7/8]` (`3/5 > 1/8`, `5/7 < 7/8`), so these `b` do lie in `B_div`,
as the definition of SAFE requires.

**Strengthening available (free).** The non-unit's bad set is also constant on the window
(`addendum_rho6_v1.py`), so the surviving residue is explicit rather than merely existent:

| ρ | `t_ρ` on `[3/5,5/7)` | `bad(ρ,t_ρ)` | uncovered after ρ |
|---|---|---|---|
| 2 | 1 | `{3,7}` | `{6}` |
| 4 | 2 | `∅` | `{3,6}` |
| 6 | 3 then 4 | `{2,6}` both | `{3}` |

Note for ρ=6 the *floor* `t_6` is not constant (it jumps at `x = 2/3`), but
`bad(6,3) = bad(6,4) = {2,6}`, so the conclusion is unaffected. If the manuscript ever
asserts that all `E_non` floor states are constant on this window, that assertion is false
for ρ=6; the parity argument does not need it.

## 3. The 13 cells and the "exactly two" claim

`verify_cells_v1.py`. Breakpoints on `[1/8, 7/8]` from `j/m`, `m ∈ {1,3,5,7}`, plus the two
endpoints:

    1/8, 1/7, 1/5, 2/7, 1/3, 2/5, 3/7, 4/7, 3/5, 2/3, 5/7, 4/5, 6/7, 7/8

14 points, **13 cells** — the stated count is right. Full table (floors of the four unit
runners; "uncovered" = complement of the union of the four unit bad sets):

| cell | `t_1 t_3 t_5 t_7` | uncovered | parity | mixed |
|---|---|---|---|---|
| `[1/8,1/7)` | 0 0 0 0 | `{2,4,6}` | even | no |
| `[1/7,1/5)` | 0 0 0 1 | `{4,6}` | even | no |
| `[1/5,2/7)` | 0 0 1 1 | `{4}` | even | no |
| `[2/7,1/3)` | 0 0 1 2 | `{1,4}` | mixed | **YES** |
| `[1/3,2/5)` | 0 1 1 2 | `{1,4}` | mixed | **YES** |
| `[2/5,3/7)` | 0 1 2 2 | `{4}` | even | no |
| `[3/7,4/7)` | 0 1 2 3 | `∅` | — | no |
| `[4/7,3/5)` | 0 1 2 4 | `{3}` | odd | no |
| `[3/5,2/3)` | 0 1 3 4 | `{3,6}` | mixed | **YES** |
| `[2/3,5/7)` | 0 2 3 4 | `{3,6}` | mixed | **YES** |
| `[5/7,4/5)` | 0 2 3 5 | `{3}` | odd | no |
| `[4/5,6/7)` | 0 2 4 5 | `{1,3}` | odd | no |
| `[6/7,7/8)` | 0 2 4 6 | `{1,3,5}` | odd | no |

The floor value of each unit runner was verified constant across each cell by comparing the
floor at the left endpoint, at the exact rational midpoint, and in the limit from the left
at the right endpoint (`assert` in the script; it did not fire).

**Finding (terminological).** The claim as quoted reads:

> "the claim that these two are the only cells (among the 13 cells cut on [1/8,7/8] by the
> points j/1, j/3, j/5, j/7) whose uncovered set contains both an odd and an even residue"

There are **four** such cells, not two: `[2/7,1/3)`, `[1/3,2/5)`, `[3/5,2/3)`, `[2/3,5/7)`.
They merge into exactly **two maximal contiguous windows with a constant uncovered set**:

    [2/7, 2/5)  uncovered {1,4}   length 4/35
    [3/5, 5/7)  uncovered {3,6}   length 4/35

So the *substance* of the claim — two windows, uncovered sets `{1,4}` and `{3,6}` — is
**correct**, and the merge is legitimate precisely because the uncovered set is unchanged
across the internal boundary (`x = 1/3` and `x = 2/3`, where only `t_3` moves, and
`bad(3,0)` vs `bad(3,1)`, resp. `bad(3,1)` vs `bad(3,2)`, contribute the same union).
The word **"cells" should read "windows"** (or "the only two maximal intervals"). As
written the sentence is false by a factor of two on its own stated granularity.

The second window checks out independently (`verify_second_window_and_cert_v1.py`): on
`[2/7,2/5)`, `t_1=0, t_5=1, t_7=2`, `t_3 ∈ {0,1}`, union `{0,2,3,5,6,7}`, uncovered `{1,4}`
in both sub-cases; and the non-unit blocks at most one of them (`ρ=2 → {0,4}` kills 4 and
leaves 1; `ρ=6 → {1,5}` kills 1 and leaves 4; `ρ=4 → ∅` leaves both).

Incidental: cell `[3/7,4/7)` has **empty** uncovered set — the four unit runners alone cover
all of `Z/8` there. Worth knowing if any argument elsewhere assumes a survivor always exists.

## 4. Integer existence in [3L/5, 5L/7)

Window length is exactly `5L/7 - 3L/5 = (25L - 21L)/35 = 4L/35`. A half-open interval of
length `≥ 1` always contains an integer, so it suffices that `4L/35 ≥ 1`, i.e. **`L ≥ 9`**.

The hypotheses give `8 | L` and `L > 2n = 16`, hence `L ≥ 24`, hence length `≥ 96/35 =
2.742...`. The stated bound is therefore correct but far from tight.

**Exact worst case.** `L = 24`: the window is `[72/5, 120/7) = [14.4, 17.142857...)`,
containing the three integers 15, 16, 17. Brute-force over every admissible
`L = 24, 32, ..., 95992` (`verify_window_bads_v1.py`): the minimum integer count is **3**,
first attained at `L = 24`. The count never drops to 0 or 1 or 2. **Step correct.**

## 5. Explicit tuples — direct computation

`verify_tuples_v1.py`. 36 tuples `E = {1,3,5,7,ρ} ∪ {8m₁, 8m₂}`, `ρ ∈ {2,4,6}`, twelve
`E_div` choices. Each was screened against every hypothesis mechanically (7 distinct
positive speeds, `gcd = 1`, `E_div ≠ ∅`, all `E_non` in `{1,...,7}` so `q_e = 0`, exactly two
missing residue classes both non-units, `8 | L`, `L > 16`). All 36 pass.

For each, every integer `b` in `[3L/5, 5L/7)` was tested for SAFE-ness, and `x_0(E)` was
computed by **direct brute force over all `k ∈ {1,...,N-1}`** against the original
definition, with exact integers.

Result:

- **SAFE holds for every `b` in the window, in all 36 tuples** (e.g. 192/192 for `L=1680`,
  96/96 for `L=840`, 384/384 for `L=3360`).
- **`x_0(E) > 0` in all 36 tuples.** Range of `x_0`: 96 to 1972.
- The residual uncovered set (after including the non-unit ρ) is `{6}` for ρ=2, `{3,6}` for
  ρ=4, `{3}` for ρ=6 — exactly as predicted in §2.

A wider sweep (`sweep_ediv_v1.py`, 828 admissible tuples with `E_div = {8m₁, 8m₂}`,
`m ≤ 24`) confirms: `SAFE holds for EVERY b in the window in all of them: True`.

**No tuple was found where the hypotheses hold and the conclusion fails.**

## 6. Vacuity

The hypotheses are **not vacuous**. 828 admissible tuples were exhibited by the sweep.
Explicit certificate (`verify_second_window_and_cert_v1.py`):

    E = {1, 2, 3, 5, 7, 8, 16}
      7 distinct positive speeds, gcd = 1
      E_div = {8, 16} (non-empty -> Case 2)
      E_non = {1, 2, 3, 5, 7}, all < 8 -> representative speeds (q_e = 0)
      R_non = {1,2,3,5,7}; missing from {1..7}: {4, 6}, both non-units -> Unit-Complete
      L = lcm(E) = 1680, 8 | L, L > 16
      N = 8L = 13440

    window [3L/5, 5L/7) = [1008, 1200)
    fibre b = 1008 (= 3L/5 exactly), uncovered residue r = 6
    witness k = L*r + b = 1680*6 + 1008 = 11088

    e:    1     2     3     5     7     8    16
    e*k mod N / L:  33/5  26/5  19/5   1   31/5  24/5   8/5     all in [1,7]  -> OK

    x_0(E) = 702 > 0.

Also note `L = 24` (the worst case of §4) is **not** attainable under these hypotheses:
`E_non ⊇ {1,3,5,7}` forces `105 | L`, so `L` is a multiple of `lcm(105,8) = 840`. The
`L ≥ 24` bound used in the claim is sound but very loose; the true minimum is `L = 840`.

## 7. The one gap that affects correctness

**SAFE, as defined, does not imply `x_0(E) > 0`.**

The correspondence between fibres and witnesses is (verified exactly in `sweep_ediv_v1.py`,
`[identity] ... True`): writing `k = L·r + b` with `r ∈ {0,...,n-1}`, `b ∈ {0,...,L-1}` — a
bijection onto `{0,...,N-1}` — and `t_e = ⌊eb/L⌋`, `u_e = eb mod L`,

    e·k mod N  =  L · (((e·r) + t_e) mod n)  +  u_e .

For `e ∈ E_non` the obstruction in `r` is exactly `bad(e, t_e, n)`, which is what SAFE
controls. But for `e ∈ E_div` we have `n | e`, hence `e·r ≡ 0 mod n`, hence the whole
expression is **independent of `r`**: those runners impose a condition on `b` alone, namely
`e·b mod N ∈ [L, (n-1)L]`.

The definition `B_div := {b : L/n ≤ b ≤ (n-1)L/n}` encodes **exactly** that condition for
`e = n` and for no other member of `E_div`. For `e = n·m` with `m > 1` the condition is
`b mod (L/m) ∈ [L/(nm), (n-1)L/(nm)]`, which `B_div` does not imply. Under the stated
hypotheses `|E_non| = 5` and `|E| = n-1 = 7`, so `|E_div| = 2` — at most one of the two can
be `e = n`, and the other is a proper multiple of `n`. So this is not a corner case; it is
the generic situation.

Measured consequence (`verify_tuples_v1.py`, columns `wit` and `divOK`, which agree in every
row — confirming the analysis above):

| E | `L` | integers in window | SAFE | actually usable |
|---|---|---|---|---|
| `{1,2,3,5,7,8,16}` | 1680 | 192 | 192 | 192 |
| `{1,2,3,5,7,8,24}` | 840 | 96 | 96 | **27** |
| `{1,2,3,5,7,16,24}` | 1680 | 192 | 192 | **53** |
| `{1,2,3,5,7,24,40}` | 840 | 96 | 96 | **6** |

So up to 94% of the SAFE fibres in the window carry no witness at all. In the 828-tuple
sweep the count of usable `b` never reached zero, so no counterexample to the *conclusion*
was produced — but the *argument* as quoted stops one step short:

> "Therefore every integer b with 3L/5 <= b < 5L/7 is a SAFE fibre. Such an integer exists
> because the window has length 4L/35 and L >= 24."

That sentence is **true and verified**. What it does not establish is that some such `b`
also clears the `E_div` runners other than `e = n`. Either the manuscript supplies that
step elsewhere (a covering/density argument on `b mod L/m` inside a window of length
`4L/35`), or the deduction to `x_0(E) > 0` has a hole. A verifier reading only the quoted
passage cannot close it.

Sketch of what would close it, for what it is worth: each `e = nm ∈ E_div` forbids a
fraction `2/n = 1/4` of a period of length `L/m`; for `m ≥ 9` the window `4L/35` exceeds a
full period so a good `b` always exists, and for `m ≤ 8` a two-runner union bound gives at
most `1/2` of the window forbidden. That is a genuine argument but it is not in the quoted
text, and the `m ≤ 8` half needs the endpoints handled exactly rather than by density.

---

## Defects, listed

1. **Wording, §3.** "these two are the only **cells** ... among the 13 cells" — false as
   stated; there are four such cells. Substance correct once "cells" is read as "maximal
   windows". Fix: say "the only two maximal intervals on which the uncovered set is constant
   and mixed-parity", or list the four cells and note they merge in pairs.
2. **Gap, §7.** SAFE (as defined, `E_non` only, plus `b ∈ B_div`) is necessary but not
   sufficient for a witness; the `E_div` runners other than `e = n` are unconstrained by
   `B_div`, and they eliminate up to 94% of the window's SAFE fibres in tested tuples. The
   step from "a SAFE fibre exists" to "`x_0(E) > 0`" is not carried by the quoted argument.
3. **Loose but sound, §4/§6.** `L ≥ 24` is correct but the hypotheses actually force
   `840 | L`; and the integer-existence step only needs `L ≥ 9`. No error.
4. **Non-defect worth recording, §2.** `t_6` is *not* constant on either window (it jumps at
   `x = 2/3`, resp. `x = 1/3`). `bad(6, ·)` is constant across the jump, so nothing breaks —
   but any statement that all `E_non` floors are constant on the window would be false.

Everything else re-derived independently and matched.
