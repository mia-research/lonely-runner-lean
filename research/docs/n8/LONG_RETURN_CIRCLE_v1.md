# The Long-Return circle cannot close — and why the measurement that said so was a tautology

Date: 2026-09-18. Artefact: `experiments/n8/long_return_circle_v1/`.
Supersedes the §4 readings in commits `0a064df`, `64b5902`.

## 0. Three successive statements of mine, two of them wrong

| | claim | status |
|---|---|---|
| v1 | the only floor that helps is `c_* = 1/4`, excluded by `0 < δ < 1/4` | **wrong** — arithmetic slip |
| v2 | the threshold is `c_* > 1/4 − 3/(4k)` = `1/7` at `k=7`, attainable in principle, but the measured floor is `0.001` so the route fails quantitatively | threshold correct; **conclusion wrong** — see §1 |
| v3 | the composed constant is forced `≥ 1` identically; the route cannot close on any correct inputs | **this document** |

## 1. The forcing

Let `c_*` be any **true** lower bound on the depths and `C_lap` any **true** upper bound
on `Σ(1/s_j)/log G`. Then

1. `log G = Σ_j log(1 + (2−8δ_j)/s_j) ≤ Σ_j (2−8δ_j)/s_j`    (`log(1+x) ≤ x`)
2. `δ_j ≥ c_*`  ⟹  `Σ_j (2−8δ_j)/s_j ≤ (2−8c_*)·Σ_j 1/s_j`
3. hence `log G ≤ (2−8c_*)·Σ_j 1/s_j`
4. `Σ_j 1/s_j ≤ C_lap · log G`
5. compose, divide by `log G > 0`:  **`(2−8c_*) · C_lap ≥ 1`**

§4 of the memo seeks `(2−8c_*)·C_lap < 1`. That is the exact negation of line 5. The route
asks for a contradiction to emerge from two premises that are both true and both point the
same way.

**Step 2 is termwise.** It never needs a uniform `c_*`. So no refinement of the depth bound
can help — including our own `depth_floor` (`δ_j ≥ 1/(8b_j)`, `Flanks.lean`). Any upper
bound whatever on `Σ(2−8δ_j)/s_j` sits above `log G` by line 1.

## 2. Why: (i) is a Riemann sum bounding its own integral

For a runner of speed `d` moving from `t` to `t' = (N + 1/8)/d`, with `s = 8dt` and
`δ = dt − N + 1/8`:

    s' = 8dt' = 8N + 1 = (8dt) − 8δ + 2 = s + (2 − 8δ)        [exact]

So `s` increases by `2 − 8δ ∈ (0,2)` per move of that runner — **linearly in move count,
not geometrically.** Then `log λ = log(s'/s)`, which telescopes, and

    Σ_j (2−8δ_j)/s_j   is a left-endpoint Riemann sum for   ∫ ds/s = log(s_end/s_start).

Inequality (i) is therefore nothing but *"a left Riemann sum overestimates the integral of a
decreasing function."* It carries no arithmetic content. And (iii) is the same count read the
other way: `s ≈ s_0 + 2j` gives `Σ1/s ≈ ½ log j` and `log G ≈ log j`, so their ratio is a
constant by construction, near `1/2`.

**Both sides of the circle count the same thing — the number of moves.** That is why no
contradiction can come out of it, and why sharpening either side is pointless.

## 3. What the measurement actually shows (`forced.out`, 1,560 arriving cascades, ds ⊂ [1,100])

| quantity | min | 1% | median | max |
|---|---|---|---|---|
| `1/s`-weighted mean depth `c_eff` | 0.0237 | 0.0312 | 0.0743 | 0.1495 |
| min depth over the cascade | 0.0013 | 0.0016 | 0.0192 | 0.1094 |
| lap ratio `Σ(1/s)/log G` | 0.5969 | 0.6221 | 0.7640 | 1.2769 |
| **true (i) ratio `Σ((2−8δ)/s)/log G`** | **1.0080** | 1.0115 | 1.0798 | 1.1236 |

Three corrections fall out.

- **The true (i) ratio never drops below 1** — 0 of 1,560, as line 1 forces. The earlier
  "composed constant below 1 in zero of 1,527 cascades" was measuring a theorem.
- **Step 1 is nearly exact**: it loses between 0.8% and 12%. There is no slack to mine there
  either — the discretisation error of the Riemann sum is the entire gap.
- **`min δ` was the wrong statistic.** Depth enters (i) *per term*, weighted by `1/s_j`, so
  the operative quantity is the `1/s`-weighted mean, median **0.0743** — about 4× the
  median min-depth `0.0192`, and 50× the extremal `0.0013` I quoted. Quoting a
  min-over-cascade-over-40,000-samples as "the actual floor" compared an extreme-value
  statistic against a mean-like threshold.
- Separately: **(iii) as stated is not always true** — `Σ(1/s) ≤ (k/6)log G` is violated in
  5 of 1,560 cascades (0.32%, max ratio 1.277 against `k/6 = 1.167`). The lap bound needs
  weakening, not strengthening.

## 4. The `2k < n` signature is exact, not approximate

The v2 threshold `c_* > 1/4 − 3/(4k)` is non-positive — no floor needed — exactly when
`1/4 ≤ 3/(4k)`, i.e. `k ≤ 3`. At `n = 8`, `2k < n` is `k ≤ 3`. **The same line.**

So this route is free precisely where `2k < n` already closes the problem, and demands a
positive floor precisely where `2k ≥ n`. It is not an independent obstacle; it is the
`2k < n` wall with the coefficient written differently. Consistent with every other route
tried (potential `Ψ`, move counting, union bound, Prop 6.11's criterion), all of which
degrade at the same place.

## 5. What is left

Closed, with reasons:

- sharpening the depth floor — closed by the termwise forcing in §1
- sharpening the lap bound — closed by the same forcing, and (iii) is already false 0.32% of the time
- mining the slack in `log(1+x) ≤ x` — closed by measurement, 0.8% at minimum
- any quantity that counts moves — closed by §2; both sides of the circle are that count

Live, because they are not counts of moves:

- **arithmetic/residue.** `clear_at_opening_of_band` / `band_of_clear_at_opening` is an
  **iff**, not an inequality: clearance at flank `e`'s `k`-th opening holds iff
  `∃M, nM+1 ≤ (d/e)(nk+1) ≤ nM+n−1`. Growth arguments discard exactly this.
- **finiteness from periodicity.** `lonely_periodic_of_int_flank` / `lonely_iff_bounded_search`
  collapse the search to `k < e` — a finite bound obtained from residues, not magnitudes.
- **integrality.** `depth_floor` came from `depth_eq_int_div`: the numerator is an integer.
  Discreteness is the one thing a growth argument erases and cannot recover.
