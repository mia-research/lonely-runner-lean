# The Long-Return Depth Lemma — final adjudication

2026-09-18. **This file is the record.** It supersedes the running account in commits
`c7b425a`, `9d680df`, `d11cede`, `7f5b97d`, `9c5f5f6`, `64b5902`, `0a064df`, `e999672`, each of
which corrected the one before it. Nothing here is expected to move again; §6 says why, and §5
lists every earlier statement of mine that was wrong, so the drift is visible rather than quiet.

Provenance: the memo came from a separate proprietary project and its language is partly
obfuscated. Not queried, by instruction. Everything below is adjudicated on the mathematics as
written.

---

## 1. What the memo claimed

**Parametrisation.** For `g ≥ 4`, let `R_g` be the `n = 8` cascade configurations in which a
setter returns after exactly `g` intervening setter moves. Write the returning setter's reading as
`s_R = 8N_R − 1 + 8δ(R)` with `0 < δ(R) < 1/4`.

**Proposition 1.** There is a universal `c_* > 0` with `δ(R) ≥ c_*` for all `g ≥ 4` and all
`R ∈ R_g`.

**Proposition 2.** The extremal return length is `g = 4`: `c_* = inf over R_4 = inf over all g ≥ 4`.

**§4.** Use the floor to cap the cascade, via `λ_j ≤ 1 + (2 − 8c_*)/s_j`.

---

## 2. Verdicts

| | claim | verdict | grade | witness |
|---|---|---|---|---|
| 2.1 | the memo's model is our cascade | **confirmed** | `[VERIFIED]` | `λ_j = (8N_j+1)/s_j` reproduces actual growth exactly on 2,753 moves, exact arithmetic |
| 2.2 | which `s` is meant | **position, `s = 8·d·t`** | `[SETTLED]` | reading (B) `s = d/d_min` exists for only 208 of 332 returns; the lemma says to write *every* `R` in the form, so (A) is intended |
| 2.3 | Prop 1 over **real** speeds | **false** | `[REFUTED]` | `δ` reaches `6.1e-13` on an arriving cascade with ordinary speeds |
| 2.4 | Prop 1 over **whole-number** speeds | **true, but not universal** | `[PROVED]` | `Flanks.depth_floor`, axiom-clean; `δ ≥ 1/(n·b)`, `b` = previous setter |
| 2.5 | Prop 2, extremality at `g = 4` | **vacuous** | `[REFUTED]` | over reals `inf δ = 0` at every `g ∈ 1..6`; over integers `g=3` **ties** `g=4` at `1/784`, `g=2` reaches `1/584` |
| 2.6 | §4 closes the cap | **cannot close** | `[PROVED]` | the composed constant is forced `≥ 1`; §4 below |

### 2.4 in detail — the one true theorem the memo contains

The cascade's instant is always the previous setter's opening `t = (N′ + 1/8)/b`, so
`δ = d·t − N + 1/8` is a rational with denominator dividing `n·b`, and a nonzero such rational is
at least `1/(n·b)`. **Tight**: minimum ratio `δ/bound = 1.000` exactly over 13,603 moves, and the
observed minima are exactly `1/(8b)` at the extremal `b` (`1/480` over speeds `[1,60]`, `1/1160`
over `[1,200]`).

So the lemma's instinct was right and its form was wrong. There is a floor. It is set by the
previous setter, not by the return length, and it vanishes as speeds grow — the real-speed
counterexamples are the `b → ∞` limit. `[PROVED]` as `Flanks.depth_floor`.

---

## 3. Proposition 2 was sampling noise, and the noise ran the other way

The apparent `g = 4` extremality came from bins of 39, 95, 173, 76 and 21 with minima all within
one order of magnitude; `g = 4` held the lowest draw. Refined: `inf δ` is driven to machine epsilon
at **every** `g` — `5.33e-15, 1.33e-15, 2.22e-16, 1.33e-15, 5.77e-15, 2.00e-15` for `g = 1..6`. So
`inf over g≥4 = inf over g=4` reads `0 = 0`.

**Worth keeping**: a first attempt used 150 random restarts per `g` against a base rate near 0.4%,
expecting under one hit, and reported "none found" for five of six values. That is a null
manufactured by an underpowered search. The corrected run harvests seeds first (69,341
arrangements, 25 per `g`). Same defect as the day's other underpowered searches, **opposite sign**:
those manufactured nulls, this one manufactured a positive.

---

## 4. §4 cannot close — the composed constant is forced ≥ 1

For any **true** depth floor `c_*` and any **true** lap bound `C_lap` on `Σ(1/s_j)/log G`:

1. `log G = Σ_j log(1 + (2−8δ_j)/s_j) ≤ Σ_j (2−8δ_j)/s_j`   (`log(1+x) ≤ x`)
2. `δ_j ≥ c_*` ⟹ `Σ_j (2−8δ_j)/s_j ≤ (2−8c_*)·Σ_j 1/s_j`
3. `log G ≤ (2−8c_*)·Σ_j 1/s_j`
4. `Σ_j 1/s_j ≤ C_lap·log G`
5. divide by `log G > 0`: **`(2−8c_*)·C_lap ≥ 1`**

§4 wants `< 1`. It asks for a contradiction from two true premises pointing the same way.

**Step 2 is termwise**, so no sharpening of the depth bound helps — `depth_floor` included. Any
upper bound on `Σ(2−8δ_j)/s_j` already sits above `log G` by step 1.

**Why.** For a runner moving `t → (N + 1/8)/d`, with `s = 8dt`:

    s' = 8N + 1 = s + (2 − 8δ)        [exact]

`s` grows **linearly in move count**, so `Σ(2−8δ_j)/s_j` is a left-endpoint Riemann sum for
`∫ds/s = log(s_end/s_start)`. Inequality (1) is *"a left Riemann sum overestimates the integral of
a decreasing function"* and carries no arithmetic content. Measured overestimate: **0.8% to 12%**
over 1,560 cascades — there is no slack to mine. And (4) is the same count read backwards
(`s ≈ s₀+2j` gives `Σ1/s ≈ ½log j`, `log G ≈ log j`). **Both sides of the circle count the number
of moves.**

Full detail and artefacts: `LONG_RETURN_CIRCLE_v1.md`, `experiments/n8/long_return_circle_v1/`.

---

## 5. Every earlier statement of mine that was wrong

Listed so the drift is auditable rather than quiet.

| # | I said | correct | cause |
|---|---|---|---|
| 1 | `c_* > 0` refuted outright | refuted over reals; **true and proved** over whole numbers | tested one reading of "admissible" before checking the word had no framework definition |
| 2 | `g = 4` extremality is a real structural fact | bin-size noise | underpowered search, positive-manufacturing |
| 3 | a floor on `δ` bounds the move **below** | `δ → 0` is the **near** edge and forces the **maximal** move | direction stated backwards |
| 4 | the counterexample contradicts `SmallOrders.return_lemma` | it does not — `hret` requires the returner in the way at the next setter's opening, so `return_lemma` governs **immediate** returns (`g = 0`) | read 3 of its 4 hypotheses |
| 5 | §4 needs `c_* = 1/4`, excluded | threshold is `1/4 − 3/(4k)` = `1/7` at `k=7` | arithmetic slip |
| 6 | §4 fails **quantitatively** (floor `0.001` vs needed `0.143`) | fails **structurally**; and `min δ` was the wrong statistic — depth enters per term weighted by `1/s_j`, operative median `0.0743`, not `0.0013` | compared an extreme-value statistic to a mean-like threshold, then measured a tautology |

---

## 6. Why this will not move again

§2.1–2.5 rest on exact-arithmetic measurements with their scripts deposited, and §2.4 is a Lean
theorem with `#print axioms` = `[propext, Classical.choice, Quot.sound]`. §4 is an algebraic
forcing argument in five lines, not a measurement — that is the difference from every earlier
version of this file's conclusion, each of which was a measurement and each of which moved.

**Still unread, and it cannot be resolved from here**: the memo's constant is corrupted in the
source — `c_* = c_4 = inf … « 0. »`. Had that been a specific decimal it would identify the class
the author fixed. A floor of `1/(8b)` is `0.125` at `b=1`, `0.0625` at `b=2`, `0.0125` at `b=10`;
no universal value matches. This is the one open item and it is a question about the source
document, not about the mathematics.

---

## 7. Net

One true theorem extracted and formalised — `Flanks.depth_floor`, correctly stated as `1/(n·b)`
rather than as a universal constant. The extremality claim is empty. The cap route the lemma was
built to serve is closed, and closed by an argument rather than by a sample.
