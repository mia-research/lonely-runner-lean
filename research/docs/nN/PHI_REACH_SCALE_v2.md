# The `φ(n)` reach law at scale

2026-09-13, v2. Scripts `experiments/nN/phi_reach_scale_v2.py`,
`experiments/nN/phi_reach_scale_v3.py` (output `phi_reach_scale_v3.out`),
`experiments/nN/phi_reach_hardness_v1.py`. Exact integer arithmetic throughout; no floats
anywhere in the decision path. No runner is pinned at 0.

**This is the general-`n` line. It does not touch the `n = 8` paper's artefact**
(`LRC/Construction8/`), and nothing here is claimed about LRC at any order.

---

## 0. What was tested, and what "reach" means here

The framework evaluates a runner on its window `[1/n, (n−1)/n]` in the lap variable `u`.
The **spine** is the set of instants `u = p/n` with `gcd(p, n) = 1` — there are `φ(n)` of
them, and they are where the arithmetic progression isolates.

**Spine reach** = the fraction of runner-instances for which at least one spine point is
clear of every reading. It is **one component of the framework's settled cases, not all of
them**: §7.3 of the manuscript also settles the ratio condition of Thm 4.8 and the
all-grid case, and the procedure searches the whole window, not only the spine.

The criterion is the formalised one. Reading `s = a/b` in lowest terms is clear at `u = c/D`
iff, with `r = (a·c) mod (b·D)` and `m = b·D`,

    m ≤ n·r   and   n·r + m ≤ n·m

which is `ConstructionN.coord_iff`. Zones are open, so both comparisons are non-strict and
the endpoints are clear.

**Self-check that the harness is measuring the right object.** For the AP `(1, …, 8)`,
runner 1's reading inside its window comes back as exactly `{1/8, 3/8, 5/8, 7/8}` from a
sweep at denominator 2520, with the six readings `2,3,4,5,6,7` — the manuscript's §1.2
statement, reproduced by the script rather than assumed. An earlier version of the script
searched below `u = 1/n`; the self-check is what caught it.

---

## 1. The comparison that separates the two laws

`φ` is not monotone in `n`, so two candidate laws make opposite predictions:

- **`φ`-law** — the rate is set by `φ(n)`; flat within a `φ`-class.
- **`n`-law** — the rate falls with `n`; more runners means more readings to clear.

They disagree hardest on `n = 12` against `n = 24`. Doubling `n` doubles `φ`.

| | `n = 12`, `φ = 4` | `n = 24`, `φ = 8` |
|---|---|---|
| spine reach, speeds in `[1, 50n]` | `0.7038` | `0.8115` |

**Doubling the number of runners raises the rate by `0.108`, about 85 clustered standard
errors.** The `n`-law predicts a fall. `[EMPIRICAL — 4,000 profiles per cell]`

Within-`φ` flatness, same population (spread in clustered standard errors):

| `φ` | `n` values | spread |
|---|---|---|
| 4 | 8, 10, 12 | `0.0287` (11.6 se) |
| 6 | 7, 9, 14, 18 | `0.0272` (11.5 se) |
| 8 | 15, 16, 20, 24 | `0.0140` (8.8 se) |
| 10 | 11, 22 | `0.0022` (1.3 se) |
| 12 | 13, 21 | `0.0039` (2.5 se) |

Between-class separation over the same range is `0.15` — roughly five times the largest
within-class spread, and about 100 se.

**The honest statement is therefore not "the reach tracks `φ(n)`" without qualification.**
`φ(n)` is the leading term and fixes the ordering. There is a small residual `n`-effect,
consistently negative — within `φ = 6` the rate runs `0.7964` at `n = 7` down to `0.7692`
at `n = 18` — which is real at 11 se and which `φ` alone does not explain.

---

## 2. Controls

**Control A — does coprimality do work, or is it just the count `φ(n)`?**
Replace the spine with `φ(n)` points drawn at random from all of `{1, …, n−1}/n`, coprime
or not. At prime `n` the two coincide by construction, which is the control's own sanity
check. At composite `n` the spine wins every time:

| `n` | spine | control A |
|---|---|---|
| 12 | `0.7038` | `0.5996` |
| 16 | `0.8183` | `0.7777` |
| 24 | `0.8115` | `0.7481` |

**Coprimality is load-bearing.** `[EMPIRICAL]`

**Control B — does the spine beat `φ(n)` arbitrary instants?**
Draw `φ(n)` points uniformly from the window's continuum instead. This control **reverses
with `φ`**:

| `n` | `φ` | spine | control B |
|---|---|---|---|
| 8 | 4 | `0.7325` | `0.5953` |
| 12 | 4 | `0.7038` | `0.5502` |
| 15 | 8 | `0.8043` | `0.7717` |
| 11 | 10 | `0.8418` | `0.8532` |
| 13 | 12 | `0.8566` | `0.8896` |
| 21 | 12 | `0.8527` | `0.8793` |

The spine's advantage over arbitrary instants is **specific to small `φ(n)`** and is gone
by `φ ≈ 10`. The crossover sits between `φ = 8` and `φ = 10`.

**Control C — are the `φ(n)` shots independent?** From the single-shot rate `q` at `u = 1/n`
and the observed reach `R`, the effective number of independent shots is
`k_eff = log(1−R)/log(1−q)`. Independence would give `k_eff = φ(n)`. Observed:

| `φ(n)` | 4 | 6 | 8 | 10 | 12 |
|---|---|---|---|---|---|
| `k_eff` (span `50n`) | `1.9–2.0` | `2.4` | `2.7–2.9` | `3.0–3.1` | `3.2` |

**`k_eff` saturates near 3 while `φ` runs to 12.** The spine points are strongly correlated;
tripling `φ` buys about 1.2 extra independent shots.

---

## 3. Where the correlation lives — and it is not in the runners

`k_eff` saturating admits two readings:

1. the spine points are correlated **with each other** — a fact about the point set;
2. a fixed fraction of runner-instances is blocked **everywhere in the window** — a fact
   about those runners, which no point set would rescue.

Separator: take every instance the spine misses and sweep the whole window on an exact grid
of denominator `55440`.

> **5,608 of 5,608 spine misses have an exact isolation instant elsewhere in the window.**
> Eight values of `n`, two speed populations, no exception.
> `[EMPIRICAL — 25,440 runner-instances swept, exact integer arithmetic]`

Reading 2 does not survive this. **The misses are a property of the spine, not of the
runner.** Each of those instants is exact, not a grid approximation: the test is integer
arithmetic on open zones, so a clear grid point is an actual instant of isolation.

This is consistent with §7.3's zero failures over the `v_8 ≤ 40` sweep, and it locates why
the framework's procedure has to search past the spine. **It is not a proof of anything
about part 7**, and it is bounded to the populations sampled: it says nothing about speed
sets outside them, and a sweep at a fixed denominator cannot certify the absence of a clear
instant, only the presence of one.

---

## 4. Where `n = 8` sits

`φ(8) = 4` is the joint minimum over the range tested, shared with `n = 10` and `n = 12`.
On both measures `n = 8` sits at the bottom of its neighbourhood — reach `0.7325`,
`k_eff = 2.01` against a maximum of `3.2` at `n = 13`. Powers of two minimise `φ(n)/n`,
which is the same obstruction already recorded for the general-`n` manuscript line.

**This does not make `n = 8` hard**, and no difficulty claim is made here. It says the
spine supplies fewer shots there than at neighbouring orders, and that the shots it does
supply are the most correlated.

---

## 5. Scope

- Populations: `n` distinct integers drawn uniformly from `[1, 10n]` and `[1, 50n]`, reduced
  by their gcd. Two populations only. Results move with the population — the `50n` span
  gives both higher reach and higher `k_eff` — so the numbers are not population-free.
- `n ∈ {7, …, 60}`, twenty-six values across the two runs. Nothing is tested above
  `n = 60`.
- 4,000 profiles per cell for §§1–2; 120 profiles per cell for §3, which sweeps `55440`
  instants per runner.
- Standard errors are clustered on the profile, since the `n` runners of one profile are
  not independent.
- Everything here is `[EMPIRICAL]`. No statement in this document is proved, and none of it
  bears on whether LRC holds at any order.

---

## 6. Above `n = 24`  *(new in v2)*

v1 tested `n ≤ 24`, where the widest `φ`-class spanned `n` by 9. `phi_reach_scale_v3.py`
extends to `n ≤ 60`, bringing `φ = 16` at `{32, 40, 48, 60}` and `φ = 20` at
`{25, 33, 44, 50}` — classes spanning `n` by 28 and 25. Sample size falls with `n` to bound
the cost, so standard errors are larger at the top and are reported per row.

**Within-class flatness holds, and tightens.**

| `φ` | `n`-span | spread, `[1,10n]` | spread, `[1,50n]` |
|---|---|---|---|
| 4 | 4 | `0.0393` (38.1 se) | `0.0272` (25.9 se) |
| 8 | 9 | `0.0113` (5.6 se) | `0.0126` (7.1 se) |
| 12 | 23 | `0.0213` (7.2 se) | `0.0090` (3.6 se) |
| 16 | **28** | **`0.0044` (1.1 se)** | `0.0082` (2.8 se) |
| 20 | 25 | `0.0067` (1.7 se) | `0.0135` (4.6 se) |

At `φ = 16` the rate is flat to **1.1 standard errors while `n` nearly doubles**, from 32 to
60. The classes that misbehave are the small ones — `φ = 4` at 38 se — where `n` spans only
4 and the reading count is changing fastest relative to `n`.

**But the size of the `φ` effect is strongly population-dependent, and v1 understated
this.** Across `φ = 4 → 20`:

| population | rate at `φ=4` | rate at `φ=20` | range |
|---|---|---|---|
| speeds in `[1, 10n]` | `0.740` | `0.776` | `0.036` |
| speeds in `[1, 50n]` | `0.730` | `0.901` | `0.171` |

The **ordering** by `φ` survives both populations and the flatness within a class survives
both. The **magnitude** does not: on the narrow population `φ` buys almost nothing, and a
reader given only the `[1,50n]` column would overestimate the law by a factor of five.
`[EMPIRICAL]`

**Control B widens rather than closing.** The reversal found in v1 — `φ(n)` arbitrary window
instants beating the `φ(n)` spine points once `φ` is large — is not a boundary effect. At
`n = 50`, speeds in `[1,10n]`: spine `0.7758`, arbitrary instants `0.9530`. At `n = 60`:
`0.7650` against `0.9183`. **The spine is a poor sampler of its own window at large `φ`**,
and its advantage is confined to small `φ(n)` — the `n = 8` regime.

**`k_eff` still saturates.** At `φ = 20` it reaches `2.24` on the narrow population and
`4.03` on the wide one, against `φ = 20` shots. Tripling `φ` from 4 to 12 and again to 20
never buys more than about two extra independent shots.

### What §6 changes about §1

Nothing in §1 is withdrawn: the `n = 12` against `n = 24` comparison stands, and the
ordering by `φ` now holds over `n` from 8 to 60. What §6 adds is that the effect's size is a
property of the population as much as of `φ`, which §1's single table could not show.
