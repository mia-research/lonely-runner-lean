# Lemma S1: Runner-2 Elimination in `sigma_2 = -1` Classes

**Date:** 2026-03-26
**Status:** PROVED — canonical imported lemma.
**Depends on:** slot definitions and bad-interval formula.
**Purpose:** Extract the proved `Lemma S1` content into a dependency-clean theorem note.

---

## Statement

> **Lemma S1.** In every sign class with `sigma_2 = -1`, runner `2` cannot simultaneously satisfy its primary obligation at `I_5` and absorb the unclaimed slot `I_9`.
>
> Equivalently, runner `2` is not the terminal absorber in any `sigma_2 = -1` class.

---

## Setup

Use the standard slots

```text
I_5 = [56/110, 65/110],   I_9 = [100/110, 109/110],
```

and bad intervals

```text
B_{2,j}(a_2) = [(11j+10)/(11a_2), (11j+12)/(11a_2)].
```

In `sigma_2 = -1` classes we have `a_2 < 2`, and runner `2` must close its
primary slot `I_5` from below.

---

## Proof

Runner `2` covers `I_5` via `B_{2,0}` exactly when

```text
10/(11a_2) <= 56/110,
12/(11a_2) >= 65/110.
```

This forces

```text
25/14 <= a_2 <= 24/13.
```

Now determine when runner `2` can overlap `I_9`.

### 1. `B_{2,0}` window

For

```text
B_{2,0}(a_2) = [10/(11a_2), 12/(11a_2)]
```

to overlap `I_9 = [100/110, 109/110]`, we need

```text
12/(11a_2) >= 100/110,
10/(11a_2) <= 109/110.
```

Equivalently,

```text
100/109 <= a_2 <= 6/5.
```

### 2. `B_{2,1}` window

For

```text
B_{2,1}(a_2) = [21/(11a_2), 23/(11a_2)]
```

to overlap `I_9`, we need

```text
23/(11a_2) >= 100/110,
21/(11a_2) <= 109/110.
```

Under `a_2 < 2`, this reduces to

```text
210/109 <= a_2 < 2.
```

### 3. Higher branches

For `j >= 2`,

```text
B_{2,j}[0] = (11j+10)/(11a_2) >= 32/(11a_2) > 32/22 = 16/11 > 1
```

because `a_2 < 2`. So no `B_{2,j}` with `j >= 2` reaches `I_9`.

### 4. Disjointness with the primary window

The primary window is

```text
[25/14, 24/13].
```

The two possible `I_9`-overlap windows are

```text
[100/109, 6/5],   [210/109, 2).
```

Both intersections are empty:

```text
[25/14, 24/13] cap [100/109, 6/5] = empty,
[25/14, 24/13] cap [210/109, 2)   = empty.
```

The decisive gap is

```text
210/109 - 24/13 = (2730 - 2616)/1417 = 114/1417 > 0.
```

Therefore runner `2` cannot satisfy its `I_5` obligation and also overlap
`I_9`. So runner `2` is eliminated as a terminal absorber in every
`sigma_2 = -1` class. □

---

## Exact Summary

| Quantity | Exact value |
|---|---|
| primary `I_5` window | `[25/14, 24/13]` |
| `B_{2,0}` overlap window for `I_9` | `[100/109, 6/5]` |
| `B_{2,1}` overlap window for `I_9` | `[210/109, 2)` |
| decisive separation gap | `114/1417` |
