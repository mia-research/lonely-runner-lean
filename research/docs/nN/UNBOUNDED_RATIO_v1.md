# Unbounded ratio at order five: how it bites, why it mostly does not, and where the bootstrap fails

2026-09-21, version 1. Framework-only. Follows `ORDER5_CERTIFICATE_STRUCTURE_v1.md`.

Artefacts: `experiments/nN/order5_recursion_v1.{py,out}` · `order5_sigma_v1.{py,out}` ·
`order5_finallap_v1.{py,out}` · `order5_growthgap_v1.{py,out}`

---

## 1. The per-move recursion  `[PROVED — arithmetic on the cascade's own definitions]`

A setter is **in the way just before it sets**, at lap `Q`: `|u·t_prev − Q| < 1/n`, so
`Q < u·t_prev + 1/n = u·R_prev/n + 1/n`. It then moves to its own opening,
`t_new = (Q + 1/n)/u`, so `R_new = n·t_new = (nQ + 1)/u`. Therefore

> **`R_new < R_prev + 2/u`** — `R` advances by less than `2/u` per move, `u` the setter's reading.

Order-general: the `2` is `2·(1/n)·n`. Starting from `R_0 = n·t_0 = 1`,

> `R_final < 1 + 2·Σ_moves 1/u(setter)`.

Checked against the certificate's own LP optima (`order5_recursion_v1.out`): it holds on every
word tested, and is **exactly tight** on the Regime B optimum `(1,1),(2,1),(3,1)`, where the
bound equals the true `R = 27/8`.

---

## 2. Why unbounded ratio mostly does not bite

**A large reading is nearly inert.** Three independent statements of the same fact:

1. **The move it makes is tiny.** `move_growth`: a move set at lap `Q` multiplies the instant by
   less than `(nQ+1)/(nQ−1)`, which → 1 as `Q` grows. A runner of reading `u` at instant `t` is
   at lap `Q ≈ u·t`, so large `u` means large `Q` means a negligible step.
2. **Its per-move contribution to `R` is `2/u`** (§1), which → 0.
3. **Its zones are fine.** Zone width is `2/(nu)` — the manuscript's `blocked_width` — so a
   large-`u` runner blocks a `2/n` fraction of the line in very many very small pieces, and the
   cascade steps across them quickly.

This is the mechanism behind the manuscript's **flat sweep**: `sup R = 31/9` at every ratio
bound from `S = 10` through `S = 30`, with the *same* extremal word
`(1,2),(2,1),(1,3),(3,1),(2,2),(1,6)` and the *same* margin `τ = 132/4165`. Raising the bound on
the readings admits new runners, and they are all nearly inert, so the optimum does not move.

It also explains §2 of `ORDER5_CERTIFICATE_STRUCTURE_v1.md`: the extremal configuration has
`u = (9, 27/8, 9/4)` — all small. The adversary's best play never uses a large ratio.

---

## 3. Why it still bites — the bootstrap fails  `[SELF-CORRECTION]`

The tempting next step is a uniform ceiling: a setter of reading `u` can only occupy laps
`Q ≤ u·t`, so if `R < n−1` then `t < (n−1)/n` and it has at most `⌊u(n−1)/n⌋` laps, contributing
at most `2⌊u(n−1)/n⌋/u ≤ 2(n−1)/n = 8/5` at `n = 5` — **independent of `u`** — giving
`R < 1 + 3·(8/5) = 5.8` uniformly in `S`.

**That argument is circular and must not be used.** It assumes `R < n−1` in order to bound the
laps, which is what is to be proved. The manuscript settles that the assumption cannot simply be
waived: §8.2 records annealing maxima on the nearest reading of **8.60, 9.04, 11.66, 10.66 at
`n = 6, 7, 8, 9`**, and a separate search on `R` at order 8 reaching **11.96** — far above
`n − 1 = 7`. So `R < n − 1` is not a background fact; at order 8 it is false.

At order 5 the same bootstrap is open. The saturation in §2 is therefore an *explanation* of the
observed flatness, not a proof of it.

---

## 4. Where the tools run out, quantified

| tool | what it gives on the extremal word | true value | verdict |
|---|---|---|---|
| `move_growth` product `∏ (nQ+1)/(nQ−1)` | 4.106 | 3.444 | **overshoots 4** — cannot prove `R < 4` |
| recursion `1 + 2·Σ 1/u` | 3.741 | 3.444 | holds, but see below |
| sufficient condition `Σ < 3/2` | — | — | **false**: max `Σ = 113/72 = 1.5694` |

The `Σ` maximum is attained at `(1,1),(2,1),(3,1),(1,2),(2,2)`, whose **true `R` is only
3.3611** while the recursion permits 4.139. So the recursion is loose exactly where it would
need to be tight, and no bound of the form `Σ < c` will close the gap.

**What the recursion discards** is *how far inside its zone* the setter sits when it fires. It
uses only `|u·t_prev − Q| < 1/n`, the worst case. The certificate's LP keeps the exact position,
which is why it gets 3.444 where the recursion gets 3.741.

---

## 5. What would actually close unbounded ratio

Either:

- **(a) Bound the move count per setter without assuming `R < n−1`.** The framework's
  `return_lemma` is the candidate: a runner that left at lap `P` is back in the way only after
  growth `(nP+n−1)/(nP+1)`, which after a single move reads `Q(n−2) < 2P+1` — at `n = 5`,
  `3Q < 2P+1`. Observed slack is large: in the extremal word setter 1 has `u = 9`, a nominal
  budget of 7 laps, and **uses 3**. Closing the gap between 3 and 7 non-circularly is the task.
- **(b) Keep the in-zone position.** A per-move accounting that carries the setter's offset
  inside its zone, rather than the worst case, would recover the LP's sharpness in closed form.

Either would make the enumeration independent of `S` and close order five over the reals, in the
framework, with no import.

---

## 6. Why this matters for `n = 8`

Everything in §1–§4 is order-general. The recursion is `R_new < R_prev + 2/u` at every `n`; the
inertness of large readings is `move_growth` and `blocked_width`, both general; and the
bootstrap failure is *worse* at eight, where `R` is observed at 11.96 against a threshold of 7.

The order-5 case is the smallest instance where the bootstrap could conceivably be closed — at
`n = 5` the observed `sup R = 31/9 = 3.444` sits below the threshold 4 with margin, whereas at
`n = 8` the observed maximum is above its threshold. So a non-circular argument at five is a
prerequisite for eight, not a detour from it, and it is precisely the missing ingredient that
`R < n−1` is currently assumed rather than derived.

---

## 7. Grades

| claim | grade |
|---|---|
| `R_new < R_prev + 2/u` per move | `[PROVED — arithmetic; verified against the LP on four words, tight on one]` |
| `R < 1 + 2·Σ 1/u` | `[PROVED — telescoping the above]` |
| large readings are nearly inert (three statements, §2) | `[PROVED — `move_growth`, `blocked_width`, and §1]` |
| the flat sweep `sup R = 31/9`, `S = 10…30` | `[PROVED — certificate outputs]` |
| the uniform ceiling `R < 5.8` | **WITHDRAWN — circular** (assumes `R < n−1`) |
| `Σ < 3/2` | `[REFUTED — max `Σ = 113/72` at an explicit word]` |
| `move_growth` product suffices | `[REFUTED — 4.106 on the extremal word]` |
| order five, unbounded ratio | **`[OPEN]`** |

**Scope.** `Σ` and the lap tables are `S = 14`/`S = 18` exact rational LP data. The certificate
is `S ≤ 30`. Nothing here establishes anything for unbounded `S`.
