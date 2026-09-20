# The one open step: how it is open, and why

Lean: `experiments/n8/FourResidues_v1.lean` (2 theorems, axiom-clean). Scripts:
`why_open_v1.py`, `four_residues_v1.py`, `band_runs_v1.py`, `band_failures_v1.py`.

---

## 1. The step, sharpened — **[PROVED]**

§15R states the remaining step as *"the order-6 rounding must also satisfy the residue conditions
at the moduli `≤ 9`"*. That is loose. The sharp statement:

> The order-6 band implies clearing at **every** modulus except `b ∈ {2, 3, 8, 9}`, and at each of
> those it admits **exactly one** blocked residue.

| `b` | band residues | window residues | admitted but blocked |
|---|---|---|---|
| 2 | `0,1` | `1` | **`0`** |
| 3 | `0,1,2` | `1,2` | **`0`** |
| 4–7 | = window | = window | — |
| 8 | `1…7` | `1…6` | **`7`** |
| 9 | `1…8` | `1…7` | **`8`** |
| ≥10 | ⊆ window | | — |

**[VERIFIED — `b = 2..4000`]** `band \ window` is non-empty at exactly `2, 3, 8, 9`, one residue
each. At `b ∈ {4,5,6,7}` the band **is** the window: the order-6 margin already clears them.

**[PROVED — `FourResidues.window_of_band_away`]** away from those four moduli, band ⟹ window.
**[PROVED — `FourResidues.clear_of_band_and_four`]** a candidate in the band at every modulus and
satisfying

```
    q ≢ 0 (mod 2),   q ≢ 0 (mod 3),   q ≢ 7 (mod 8),   q ≢ 8 (mod 9)
```

for whichever of those moduli the profile carries, **clears the whole profile**. `15` of the `72`
residues mod `72` satisfy all four at once.

## 2. Why it is open — three specific reasons

**(a) No available margin can force it.** At `b = 2` the rounded `q` is odd exactly when
`dist(t, 2ℤ) > 1/2`, i.e. `dist(t/2, ℤ) > 1/4`. Order 6 gives `1/6`. Order 5 gives `1/5`. Order 4
gives `1/4` — **not strict**, so it fails too. Only order 3 (two speeds) suffices, and five active
blockers license order 6. This is a **proof that nearest-integer rounding is insufficient**, not a
statement that it has not yet been made to work. The answer must come from *where* the rounding
lands, not from how much margin it carries.

**(b) Generator choice cannot dodge it.** **[VERIFIED — 8,000 profiles]** `99.86%` carry one of
`{2,3,8,9}` as a modulus at **every** generating reading. The four exclusions are not an artefact
of a bad choice of generator.

**(c) The exclusions are never free.** If the band intersection contained 72 consecutive integers
it would automatically contain an allowed residue. **[VERIFIED — 4,000 profiles]** the longest run
of consecutive integers in that intersection is **median 4, mean 6.0, max 73**, and reaches `72`
in **0.05%** of cases. So the four conditions must be *coordinated* with the band, not absorbed by
it.

## 3. How open it is, measured

**[VERIFIED — 4,000 profiles, generator `s_k = max`]** the band intersection contains a `q`
satisfying all four exclusions in **99.95%**. The **2 failures** are instructive rather than
fatal:

| profile | fails at | succeeds at |
|---|---|---|
| `[1,2,3,4,5,90,360]` | generator `360` (moduli `4,72,90,120,180,360`) | generators `2,3,4,5,90` — **all five others** |
| `[1,2,3,4,5,6,120]` | generator `120` (moduli `20,24,30,40,60,120`) | generators `2,3,4,5,6` — **all five others** |

Both clear at every other generator. So the route is **not universal at a fixed generator**, and
the seven-generator freedom is doing real work, not decoration.

## 4. The statement to prove

> **`[OPEN]`** For every commensurable profile there is a generating reading `s_k` such that the
> order-6 band at its moduli contains a candidate `q` with `q ≢ 0 (mod 2)`, `q ≢ 0 (mod 3)`,
> `q ≢ 7 (mod 8)` and `q ≢ 8 (mod 9)`, for whichever of those moduli occur.

Everything else in the reduction is proved (§15R, `SYNTHESIS_v1`). What §2(a) rules out is the
obvious attack; what §3 shows is that any proof must use the choice of generator, because at a
fixed one the statement is false.

`MANUSCRIPT_v15` is owed to fold §1's two theorems into §15 and replace §15R's loose form with
the four-residue statement. That promotion is gated by `compile-diff`.

Existence at order 8 remains open.
