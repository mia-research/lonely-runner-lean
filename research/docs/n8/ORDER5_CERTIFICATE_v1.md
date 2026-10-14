# Order 5: a finite certificate, and Existence for bounded spread

2026-09-16. Follows `ORDER5_GROWTH_v2.md`, whose §10 refuted uniform-constant pricing and left the joint structure as the only
route. Script `experiments/n8/order5_certificate_v2.py` (output `order5_certificate_S6_v2.out`), exact rational arithmetic;
`order5_certificate_v1.py` is the same without the boundary discipline, kept because its answer is instructive.

---

## 1. What makes the problem finite

Suppose the cascade reaches `R = 4` and take the **first** step at which it does. Every earlier step has `R < 4`, and after a
setting of `x` at lap `Q` the value is exactly `R = (5Q + 1)/s_x` (`ORDER5_GROWTH_v2` §2). Hence, for an arrangement of spread
`S = d_max/d_min`:

- **the nearest runner never sets** before the exceedance — its reading is 1, so its first setting would give `R = 6`;
- **every lap is bounded**: at the step before the exceedance `R < 4`, so `Q < (4S + 1)/5`; at `S = 6` this is `Q ≤ 4`;
- **laps strictly increase per runner**, so each of the three other runners sets at most `L` times, and the whole word has at
  most `3L` moves.

So the configurations form **finitely many words** `(setter, lap)`, and each word's conditions are linear in the readings once
cleared of denominators:

    | u_{x_j}(Q_{j-1} + 1/5) − Q_j·u_{x_{j-1}} | < u_{x_{j-1}}/5      (the setter is in the way just before it sets)
    (Q_j + 1/5)·u_{x_{j-1}} > (Q_{j-1} + 1/5)·u_{x_j}                 (the instant advances)

with `sup R = (5Q_M + 1)/min u_{x_M}` over the word's polyhedron. These are necessary conditions only — the "setter has the
latest opening" and "the others are clear" conditions are dropped — so the optimum **bounds the true one from above**, which is
the direction a proof of `R < 4` needs.

## 2. The boundary discipline is load-bearing  `[the 4.125 artefact, explained]`

With the inequalities taken closed, the enumeration returns `sup R = 33/8 = 4.125`, on the word `(1,1), (2,1), (1,2), (3,1)` —
the same 4.125 the earlier floating-point linear programs hit (status v6 §3). It is an all-boundary configuration, which the
Boundary Set Method counts as **clear**: zones are open (§1.2 of the manuscript), so a runner sitting exactly on a zone edge is
not in the way and never sets.

Enforcing strictness removes it: each condition is tightened by a margin `τ`, a word counts only if `max τ > 0`, and the optimum
is then taken on the closure (a nonempty open polyhedron is dense in its closure). The 4.125 word has `max τ = 0` and is
discarded.

## 3. The result  `[PROVED — exact finite certificate]`

> **Order 5, spread `S ≤ 6`.** Every arrangement of five runners whose subject has `d_max ≤ 6·d_min` satisfies `R < 4`; in fact
> `sup R = 27/8 = 3.375`, attained in the limit by the word `(1,1), (2,1), (3,1)` with margin `τ = 1/5`. Hence the cascade stops
> and **Existence holds for every such runner** (Corollary 6.4).

The optimum is exactly the lap-1 ladder `(3/2)³ = 27/8`, which earlier work had assumed as a bound for lap-1-only cascades; here
it comes out as the true optimum over all realisable words at this spread, laps and lengths included.

**Consistency.** The exhaustive integer census (every 5-subset of `[1,26]`) never exceeded `R = 3.1429`, and the resonant runs
never exceeded 1.4142 — both below 27/8.

**Scope, stated plainly.** This is a finite exact verification over words, not a general argument: it covers spread at most 6 at
order 5 and says nothing beyond it. The enumeration is complete for that range: every setting before the first exceedance has
`Q < (4S+1)/5`, laps increase per runner, the nearest never sets, so no word is missed.

## 4. Next

- **Push the spread bound.** `S = 8` is running (`L = 6`, words to 18 moves). The word count grows quickly; if it becomes the
  limit, the enumeration can be pruned by the flank criterion, which discards configurations from the sieve side.
- **What a full order-5 proof still needs.** Either an argument that covers unbounded spread, or a reduction of large spread to
  the bounded case. The large-spread regime is where the resonant chains live, and their `R` stays near 1.4 — far from 4 — so
  the target there is different in character from the bounded case settled here.
- **Then Lean.** The certificate's statement is native (setters, laps, readings, instants); formalising it means either checking
  the finite word list inside Lean or proving the linear bound symbolically.
