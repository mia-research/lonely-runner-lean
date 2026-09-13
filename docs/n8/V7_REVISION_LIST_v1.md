# v7 revision list — running, for later review

Started 2026-09-14. **Append only. The manuscript is frozen; nothing here is applied.**
Each item says what to change, where, and why, with the evidence that settles it.

---

## 1. §7.1 — the procedure carries a window the framework does not require  `[SETTLED]`

**Change:** drop the window condition `d ≤ a·m ≤ 7d` and the restriction of `d` to the
runner's own differences. The candidates are `t = a/(8D)`, `a ≡ 1 (mod 8)`, `D` a free
positive integer — the resolution at which the seed is framed.

**Why:** verified counterexample, `WHY_THE_LAST_MILE_RESISTS_v1.md` §1. Speeds
`(1, 31, 75, 97, 128, 160, 176, 225)`, the runner at speed 1: nothing clears in its first
window, and it is lonely at `t = 9/40 = 9/(8·5)` — resolution `D = 5`, lap 6.

**Owner:** *"I never thought the first window/cycle was a requirement and think it keeps
getting introduced from context loss and revert to training data."* Provenance confirmed:
§1.3 introduces it and flags it as a choice; §7.1 bakes it in; §7.4 makes it the claim.

## 2. §7.4 — the Claim is false as written  `[SETTLED]`

**Change:** restate over the relaxed form — a runner is cleared at **some** resolution, with
no bound on the lap. The instant stays exactly named.

**Why:** same counterexample. `[PROVED — exact, exhibited]`

## 3. §1.3 — its justification for the window does not survive checking  `[SETTLED]`

§1.3 keeps the first-window form because the relaxed form *"would leave the lap `k`
unsupplied"*. In the `(a, D)` form it is not unsupplied: `t = a/(8D)` names the instant
outright and the lap is `⌊d_min·t⌋`. Checked: `d_min = 30`, `t = 9/40` → lap 6;
`d_min = 1974`, `t = 3/64` → lap 92. **The closed expression survives the relaxation.** Only
a bound on the lap is lost, and the framework never claimed one.

## 4. §7.2 — Proposition 7.1 is scoped to the window  `[OPEN — needs restating]`

The proposition (*the candidates are exactly the openings*) is **true and machine-checked**
as `exists_clear_candidate`, but it is stated about one window. Under item 1 it should be
restated per resolution: within any lap, the clear set is closed, so its components have
least elements, and those are openings. The Lean core is resolution-agnostic already and
should carry over unchanged.

## 5. §7.3 — soundness, phrasing  `[OPEN]`

Still correct: a returned instant is correct. Should be phrased on `(a, D)` rather than on a
window. Matches the deferred Lean item below.

## 6. Lean — `procedure_sound` naming  `[OPEN, deferred at owner's direction]`

True as stated, but phrased on the window and named for "the procedure". Restate on `(a, D)`
and rename. Not a reproof.

## 7. §8 — no row for the cascade family  `[OPEN]`

The cascade's clearing test **is** `coord_iff`, so it is machine-checked, but §8's table does
not say so.

## 8. §9 — the `2σ` containment threshold  `[OPEN]`

`two_sigma_zone_inside` needs `3 < n`; at `n = 3` the two ends coincide. §9 lists the other
thresholds (`n > 4` for the exclusion, `n > 2` for the clear interval) and should list this.

## 9. Restorations still outstanding from `LOST_FUNCTIONS_v1`  `[OPEN]`

Not yet in any manuscript version: **H1** (same-side runners within `1/4` of a lap line), the
**wrap gap / global start / gap migration**, the **relay anatomy** (231,294 blocked instances,
0 chains reaching the window's end), and **Part II's perturbation mechanisms**. §6.2 still
refutes the relay without stating the rule the relay runs on.
