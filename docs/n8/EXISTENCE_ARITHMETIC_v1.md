# §6.7's arithmetic line: the reduction, the gate that licenses it, and where it actually stands

2026-09-17. Taking up §6.7's *"What failure would require"* at the owner's instruction, with
`PROVENANCE_MAP_v1.md`'s gate filled in rather than assumed. **This is an opening, not a result.**
Existence at order 8 is open and nothing here closes it.

Artefacts: `experiments/n8/framework_cases_v1.py` / `.out` (the named cases),
`r_bounded_seeded_v1.py` / `.out` (step-factor structure), `scale_recursion_check_v1.py` / `.out`.

---

## 1. The gate, filled in

| | §6.7's line |
|---|---|
| **G1 object** | openings `t = a/(8d)`, differences `e`, `d`, `d_min`, integers `a`, `w`, scales `D`, readings `s`. All §1–§2.1, §6.1–§6.2 |
| **G2 tool/target** | the target is §6.7 verbatim. Residue and pigeonhole arguments are tools, admissible under the 2026-09-15 ruling |
| **G3 reduction** | the only bound is `|e·a − 8w·d| < d`, with `c = d`, a difference. Not a lap boundary, not a window. **Passes** — this is the gate the cap failed |
| **G4 strength** | the target **is** Existence. Equivalent by construction, not merely sufficient |
| **G5 premise** | no assumption that the nearest never sets, no window, no cap. The named cases (nearest sets at step 24 and step 19) are inside scope, not excluded |
| **G6 calibration** | every claim below is run against `framework_cases_v1.py`, 4 of 4 reproducing published values |
| **G7 determination** | scales in, instant out. No path is searched; §6.2's recursion is evaluated forward |

## 2. The reduction  `[PROVED — §6.2 identity; VERIFIED exactly]`

Three facts already owned, composed:

- §6.2, scale coordinate: `D_0 = d_min`, `D_{j+1} = D_j·λ_j⁻¹`, `instant = 1/(8·D_final)`.
- §6.2, reading coordinate: a step multiplies **every** reading by the same `λ_j = (8N_j+1)/s_{x_j}`,
  where the setter's reading `s_{x_j} ∈ (8N_j−1, 8N_j+1)`; the setter lands exactly on `8N_j+1`.
- `exists_fixed_of_capped` (§8.2): a cascade whose instants are capped stops.

Hence, with `R = d_min/D_final`,

> **`R = ∏_j λ_j`,  with  `1 < λ_j ≤ (8N_j+1)/(8N_j−1) ≤ 9/7`,**

and **Existence for the runner ⟺ `R < ∞`**. Verified exactly: the product equals `R` on both named
climbs (`10.3125` over 23 steps; `10.2607` over 28), and the largest single factor observed is `1.2805`
against the bound `9/7 = 1.2857`.

**This is the statement to attack, and it is not `R < n − 1`.** The cap demanded `∏λ_j < 7`; Existence
demands only that the product not diverge. The difference is the whole of Lemma C's difficulty:
`RETURN_CORRECTION_v2` showed `∏λ_j < 7` is false at order 8 — the named cases reach `10.3` — while
`∏λ_j < ∞` is untouched by that refutation.

## 3. What a bound has to survive  `[EMPIRICAL — calibrated]`

Step-factor structure of the largest case found (`d = 30, 74, 96, 127, 159, 175, 224`, `S = 7.467`,
`R = 165/16`, 23 steps):

| `N_j` | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| steps | 7 | 5 | 4 | 3 | 3 | 1 |

Since `λ ≤ (8N+1)/(8N−1)`, only small `N` contributes materially — `N = 1` gives `≤ 9/7`, `N = 6` gives
`≤ 49/47`. So **a bound on `R` is a bound on how many small-`N` steps a cascade can take**, which is
where §8.2's existing machinery points (`no_four_alternation`, `no_return_after_few_faster`,
`nearest_reading_recurrence`).

Calibration, stated plainly: my own hill climb from random starts reached only `4.92` and would have
supported a false ceiling. Seeded from the named cases it reproduces `10.31` and improves on it not at
all, while §6.7 records `≈ 11.96` at `S ≈ 7.44` — so **my search is still weaker than the manuscript's**
and no ceiling claim is made here.

## 4. The honest scope of this line

Carried to completion, §6.7's line **is** LRC(8) for the runner — §9 says so: *"If Existence held for
every runner, the conjecture at eight runners would follow."* It is not a shortcut to the conjecture; it
is the conjecture, in the framework's objects. What the framework contributes is that the object is
**determinate and arithmetic**: one path per arrangement, each step a residue condition
`(e·a mod 8d) ∈ [0,d) ∪ (7d, 8d)`, and failure requiring that condition at every step for ever.

That is worth saying because the previous route looked easier only by being about something else.

## 5. Next, in order

1. **Bound the `N = 1` steps.** `λ ≤ 9/7` only at `N = 1`; everything else is closer to 1. A bound on
   their count, with the rest absorbed, bounds `R`. Check `no_four_alternation` and
   `no_return_after_few_faster` for what they already give here — read them before inventing.
2. **Strengthen the search to the manuscript's `11.96`** before any ceiling is claimed. The gap between
   `10.31` and `11.96` is my search, not the mathematics.
3. **Does `∏λ_j` diverge for any arrangement?** The native form of the open question. A divergent
   product needs infinitely many steps with `λ` bounded away from 1, hence infinitely many small-`N`
   steps — which is what item 1 would forbid.
