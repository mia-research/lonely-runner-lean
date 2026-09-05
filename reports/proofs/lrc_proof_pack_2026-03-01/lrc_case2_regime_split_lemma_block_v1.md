# Case-2 Regime Split Lemma Block (v1)

## Goal
Refactor Case-2 closure into two regimes:

1. **Anchor regime** `L=n` (tight boundary),
2. **Slack regime** `L>n` (excess-safe mass).

This isolates the hard edge from the bulk and matches observed extremal structure.

---

## Definitions
For Case-2 tuple `E` (`gcd(E)=1`, at least one `e_r ≡ 0 (mod n)`), with `L=lcm(E), N=nL`, and split
`E = E_div ⊔ E_non`, define:

- `B_div = { b in [0,L-1] : divisible-speed constraints pass }`
- `A_b = { a in [0,n-1] : non-divisible constraints pass on k=aL+b }`
- `B_safe = { b in B_div : |A_b|>0 }`
- `C_bad = |B_div \ B_safe|`.

Identity:

`x0(E) = sum_{b in B_div} |A_b| >= |B_safe|`.

So `|B_safe| >= n-1` is sufficient for Case-2 closure.

---

## Lemma RS.1 (Anchor profile in L=n regime)
If `L=n`, then every divisible speed must equal `n`, hence `E_div={n,...,n}`.
Therefore:

`B_div = {1,2,...,n-1}`, so `|B_div|=n-1`.

Empirical strengthening (now heavily supported):

`C_bad=0` and `B_safe=n-1` throughout tested `L=n` tuples.

This gives the tight boundary behavior exactly.

### Evidence
- Exhaustive bounded Case-2 grids `n=3..7`: all tight tuples satisfy profile
  `(L=n, B_div=n-1, C_bad=0, B_safe=n-1)`.
- Random `L=n` stress for `n=8,9,10,11,12,14,15,16,18,20`: 0 violations in all tested samples.

---

## Lemma RS.2 (Slack signature for L>n regime)
In tested grids, `L>n` tuples satisfy strict slack:

`B_safe > n-1`.

Observed minima in exhaustive bounded scans:

- `n=3`: min `B_safe(L>n)=3`
- `n=4`: min `=4`
- `n=5`: min `=7`
- `n=6`: min `=9`
- `n=7`: min `=11`

So non-anchor tuples are not edge-tight in these regimes.

This is the natural location for a separate excess-mass lemma.

---

## Theorem RS-main (conditional split closure)
If the following two statements are proved:

1. (Anchor) For `L=n`: `B_safe=n-1`.
2. (Slack) For `L>n`: `B_safe>=n` (or any explicit lower bound `>n-1`),

then for all Case-2 tuples:

`B_safe >= n-1`.

Hence

`x0(E) >= |B_safe| >= n-1 >= phi(n)`.

So Case-2 closes.

---

## Why this split helps
- Anchor regime captures exactly the tight frontier (extremal behavior).
- Slack regime only needs a strict-gap lemma, not equality analysis.
- This avoids forcing one global inequality to do two different jobs.

---

## Artifacts
- `lrc_case2_regime_split_scan_v1.py`
- `lrc_case2_regime_split_summary_v1.md`
- `lrc_case2_regime_split_rows_v1.csv`
