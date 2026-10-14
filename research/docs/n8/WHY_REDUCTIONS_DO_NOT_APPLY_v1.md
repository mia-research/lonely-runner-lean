# Why the standard reductions do not apply here

2026-09-14. **Not a defence, and not a set of bans.** Each reduction below is a tool for
establishing that something *exists*. This framework's claim is that a time is *produced*.
A tool whose output is "yes, one exists" cannot discharge "here is the time" — so the
reductions are **inapplicable**, in the way a ruler is inapplicable to weighing.

The claim, for reference:

> **For every runner, produce a time at which it is lonely.**

---

## 1. No global clock

The construction runs per runner. Each computes its own exact rational time from its own
speed differences, and the times differ.

Eight runners at speeds `(3, 7, 12, 20, 29, 31, 44, 50)`:

| runner | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 |
|---|---|---|---|---|---|---|---|---|
| lonely at | `1/8` | `1/16` | `1/24` | `1/40` | `1/8` | `1/16` | `11/40` | `1/8` |

Five distinct times. **And there is no instant at which all eight are lonely together** —
checked, zero. The construction never asks for one.

*What this makes inapplicable.* Any reduction whose purpose is to manage a single entangled
global state: the stationary frame, which pins one runner and studies the rest; and any
argument routed through simultaneous isolation. There is no global state here to simplify —
there are eight independent computations.

*And the frame is not a WLOG.* Reading `v_j − v_i` is what "runner `i` is lonely" **means**.
It is not a choice of viewpoint that privileges `i`, and it is performed identically for each
of the eight in turn.

## 2. No reduction to integer speeds

The test is a band condition, and it reads irrational differences directly.

Speeds `(1, 1+√2/100, 3, 4, 5, 6, 7, 8)`, the runner at speed 1, at `t = 71/8`:

| difference | distance | `≥ 1/8` |
|---|---|---|
| `√2/100` | `0.125511453660…` | ✓ |
| 2, 3, 4, 5, 6 | `0.250, 0.375, 0.500, 0.375, 0.250` | ✓ |
| 7 | `0.125` exactly | ✓ |

**No rational approximation of `√2` appears anywhere.** How finely the irrational must be
represented is set by how close `0.12551` sits to `0.125` — the resolution is an output of
the configuration, not an approximation imposed on it.

*What this makes inapplicable.* The real-to-integer reduction. It exists to make a continuous
problem tractable; this one is already exact.

## 3. No measure and no density

For the arithmetic progression, the subject's reading is **isolated points** — sampling 999
points of a period finds exactly 4, and the total length is zero.

So the quantity a size argument would bound below is **exactly zero in the case that
matters**, and no strengthening reaches it.

**The framework's answer for that same case is `t = 1/8`** — a point, named. Where measure has
nothing to weigh, production still delivers.

*What this makes inapplicable.* Measure, density, zero-measure branches, stability radii.
Not forbidden — they have no purchase, and the case that kills them is the framework's own
easiest case.

## 4. No covering, and no complement

A covering argument concludes that obstructions fail to fill something, hence a point
survives. Its output is a fact about a complement.

The claim asks for the time. **A surviving point is not a named point**, and no amount of
sharpening turns one into the other.

This is the failure mode most worth naming, because it is the one that looks like progress. A
bound of the form "the blocked candidates number fewer than the candidates" can reach a high
percentage and still produce nothing.

*What this makes inapplicable.* Covering, set emptiness, and counting arguments over the
candidate set.

## 5. No equidistribution, no induction on the order, no exhaustion

- **Equidistribution** describes limiting behaviour. The times here are exact rationals
  computed from gcds and residues at a fixed configuration. There is no limit taken.
- **Induction on the number of runners** has nothing to recurse on. The construction is fixed
  at `n` and reads `n−1` differences; no smaller instance appears in it.
- **Exhaustion over a bounded family** settles existence and **names nothing** — it is the
  clearest case of a method answering a different question.

---

## 6. The single sentence

Every reduction above answers *whether*. The framework answers *when*. They are not rivals,
and the framework is not refusing them out of preference: **their outputs are the wrong type.**

## 7. What this does not claim

It does not claim the framework's construction is proved to always produce. That is open, and
it is stated as such: three named rules produce the time for `81.9%` of runners immediately,
and the construction reaches the rest by stepping through gaps — every time in everything
tested, at gap 2 to 11, but without a proof that it must.

**The reductions would not close that gap either.** They would establish existence, which is
not the obligation.
