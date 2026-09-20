# The transit closed form — and why it does not reach the n = 8 object

2026-09-12. Supersedes `TRANSIT_DENSITY_CLOSED_FORM_v1`. **`n = |V| = 8`** throughout
([[feedback_count_the_runners_given_2026_09_12]]: translation, never adjoining).

v1 derived exact densities for a one-runner transit and read a conclusion off them. The
derivation is unchanged and still exact. **The conclusion was wrong**, and the way it was
wrong is the point of this note.

---

## 1. Scope, stated first

The n = 8 analytic object is `E` = **seven distinct positive integers**, gcd 1, `L = lcm(E)`,
`x = b/L`, all breakpoints at integer `b`, counts `= L ×` measure exactly
(`STATUS_n8_ANALYTIC_v1`, and the framework in
[[project-n8-unitcomplete-theorem-2026-09-07]]).

§2's closed form is derived at **irrational** speed, which is **not a member of that family**.
It is the limit the family approaches, and the approach is never attained: at `r = 7 + 1/q`
the exact density is `q = 53 → 0.130128988`, `211 → 0.130208920`, `401 → 0.130208525`,
against `25/192 = 0.130208333`, equal at no finite `q`. The n = 8 difficulty sits at **small**
denominators, which is exactly where equidistribution says nothing.

## 2. The closed form  `[PROVED | Weyl]` `[PROVED — exact]`

Move one runner of the AP to `r`, others at `J`. With `y = t`, `x = rt`, the moved runner's
constraints are `‖x − jy‖ ≥ 1/8`. The differences `r − j` are pairwise separated by the fixed
integers `j − k`, so the system has **two** degrees of freedom for every `r`. For irrational
`r`, Weyl gives density = area of `A_J = {(x,y) ∈ T² : ‖x − jy‖ ≥ 1/8, j ∈ J}`.

| moved runner | density | value |
|---|---|---|
| 7 (endpoint) | `25/192` | 0.1302083 |
| 1 (interior) | `853/6720` | 0.1269345 |
| 3 (interior) | `941/6720` | 0.1400298 |

Exact `Fraction` over the derived breakpoint grid (`‖(j−k)y‖ = 1/4`), per-cell linearity check.
Stable at `N = 240, 480, 720`; **the control fires** — at `N = 24` it reports 6 nonlinear cells
and a wrong area (`41/288`). Non-moved runners factorise exactly: density `= (3/4)·|G_fixed|`,
since six constraints depend on `y` alone and one on `x` alone. Profile for the endpoint
transit: `21/320, 7/64, 1/4, 11/32, 1/4, 7/64, 21/320`, moved runner `25/192`.

`25/192` answers `AP_GRID_SUMMARY_v1` §8's open item: the generic measure has a closed form.

## 3. Retraction — the reading of that profile  `[RETRACTED]`

v1 §3 said:

> "**The ends of the pack are five times more exposed than the centre**, which is the
> measure-side statement of `OBSERVATIONS` item 23."

Both halves are wrong.

**It is not the measure-side statement of item 23.** Item 23 is about **count**, and it points
the other way: moving a runner toward the centre costs more. The two statements were aligned by
assertion, not by measurement.

**"Exposed" inverts on the object that matters.** On integer speeds, density and count disagree
about where the pack is dangerous:

| rank (0 = slowest) | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| mean **count** | 23.4 | 19.4 | 16.8 | **14.7** | **14.8** | 16.5 | 19.6 | 23.4 |
| mean **density** | 0.1225 | 0.1282 | 0.1367 | **0.1409** | **0.1425** | 0.1355 | 0.1290 | 0.1222 |

Density is centre-peaked, agreeing with §2. Count is centre-**minimal**. Both are true and
consistent — the centre runner holds more measure in **fewer, larger** components — but the
quantity with a floor is count, and it says the centre is where the danger is, not the ends.

## 4. Density does not localise the floor  `[VERIFIED — scoped null]`

Sharper than the means. Over the same configurations, where does each statistic put its
minimum?

| argmin at rank | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|---|
| **count** | 21 | 85 | 220 | **412** | **305** | 121 | 28 | 8 |
| **density** | 142 | 127 | 143 | 174 | 142 | 162 | 151 | 159 |
| uniform-random control | 149 | 157 | 140 | 152 | 152 | 142 | 158 | 155 |

**Density's argmin is indistinguishable from a coin flip over rank**, at a sample size where
count's argmin is detected decisively.

- **Object**: which runner of a configuration carries the minimum, by rank in the sorted pack.
- **Class of observable**: the argmin-rank distribution.
- **Power**: the same 1,200 configurations resolve count's argmin at ~20× uniform in the modal
  cell; a uniform-random control is reported alongside and matches density's profile.
- **Scope**: integer speeds sampled uniformly from `[0,40)`, 1,200 configurations, seed 5.
  Not tested at larger spans, near-AP adversaries, or non-uniform sampling.

Artifact: `experiments/n8/ok_rank_profile_v1.py`.

This does **not** say measure arguments are useless at n = 8, and it is not a closure. It says
one specific thing: on this statistic, at this scope, the density profile carries no
information about where the count floor sits. A measure route that hopes to **localise** the
hard runner needs something the density does not contain.

## 5. Status

`[PROVED | Weyl]` §2's reduction to a `T²` area.
`[PROVED — exact]` §2's three areas, the factorisation, the eight-runner profile.
`[VERIFIED — q ≤ 401]` §1's convergence.
`[VERIFIED — scoped null]` §4, scope as stated.
`[RETRACTED]` v1 §3's reading, in full; and `AP_GRID_SUMMARY_v1:53`'s explanation of the
`(3/4)⁷` deficit (unchanged from v1 — the deficit belongs to the transit family, not to eight
speeds; 60 generic difference sets average 0.13347).
`[OPEN]` The jump magnitude at `p/q` as a function of `q`.

**n = 8 is not proved, and §2 bears on it only as a limit the integer family never reaches.**
