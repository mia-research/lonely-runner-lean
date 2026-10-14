# `n = 11` AP Static Core Theorem

**Date:** 2026-03-26
**Status:** PROVED — canonical static-front theorem package.
**Depends on:** slot/bad-interval definitions from the algebraic setup, `lrc_n11_universalincompat_v1.md`, `lrc_n11_lemma_s1_runner2_elimination_v1.md`, `lrc_n11_lemma_s2_proof_v2.md`.
**Scope:** Static front only. This file does **not** certify any non-static route.

---

## Statement

> **Static Core Theorem.** In every CB configuration of the `n = 11`
> arithmetic-progression static route, the static obstruction survives.
> More precisely:
>
> 1. if `sigma_2 = +1`, then `GF(I_4) + GF(I_9) > 0`;
> 2. if `sigma_2 = -1`, then `W(I_9) >= 538/54395 > 0`.
>
> Hence no sign class admits full static blocking, and the AP static front is
> closed by a dependency-clean theorem chain.

---

## Imported Components

### 1. `sigma_2 = +1`

`Theorem U` in `lrc_n11_universalincompat_v1.md` proves:

```text
For any CB configuration with sigma_2 = +1, GF(I_4) + GF(I_9) > 0.
```

This closes all `128` sign classes with `sigma_2 = +1`.

### 2. `sigma_2 = -1`

`Lemma S1` in `lrc_n11_lemma_s1_runner2_elimination_v1.md` proves that runner
`2` cannot absorb `I_9` while satisfying its primary `I_5` obligation.

`Lemma S2` in `lrc_n11_lemma_s2_proof_v2.md` then proves that, after this
runner-2 elimination, every `sigma_2 = -1` sign class leaves

```text
W(I_9) >= 538/54395 > 0.
```

This closes all `128` sign classes with `sigma_2 = -1`.

---

## Proof

Split on the sign of runner `2`.

If `sigma_2 = +1`, apply `Theorem U`. Then

```text
GF(I_4) + GF(I_9) > 0,
```

so at least one of `I_4` or `I_9` carries positive good fraction, and the
configuration is statically obstructed.

If `sigma_2 = -1`, apply `Lemma S1` and then `Lemma S2`. Runner `2` is removed
from the terminal absorber role, and the remaining cascade leaves

```text
W(I_9) >= 538/54395 > 0.
```

So `I_9` itself retains positive witness width.

These two cases exhaust all sign classes. Therefore the AP static front is
closed by the chain

```text
algebraic setup  ->  Theorem U
algebraic setup  ->  Lemma S1 -> Lemma S2
```

and does not rely on any dynamic or auxiliary repair route. □

---

## Canonical Interpretation

- This file is the authoritative theorem note for the AP static front.
- It is intentionally narrower than a full `n = 11` proof claim.
- Dynamic and other non-static routes remain outside the canonical proof chain
  until repaired.

---

## Exact Lower Bounds in the Static Core

| Component | Exact bound |
|---|---|
| `Theorem U`, cascade speed threshold | `86/9` |
| `Theorem U`, `I_4` lower bound on `a_2` | `172/81` |
| `Theorem U`, representative right-gap bound | `181/6380` |
| `Theorem U`, `a_9 = 86/9` minimum right gap | `59/9460` |
| `Lemma S2`, case `sigma_3=+1, sigma_4=+1` | `103/3850` |
| `Lemma S2`, minimum over all `sigma_2=-1` classes | `538/54395` |
