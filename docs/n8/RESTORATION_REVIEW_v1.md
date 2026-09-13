# Restoring the lost functions: what it affects downstream

2026-09-14. Reviews `LOST_FUNCTIONS_v1.md` item by item against the manuscript.
Measured, not argued. **Nothing has been changed.**

---

## 1. The headline: restoring the lattice roughly halves the open set

Random integer 8-sets, one population per row, exact arithmetic.

| speeds in | Thm 4.8 (T6) | grid | `u = 1/8` | **`u = r/8`, `r ∈ {1,3,5,7}`** | `+` AP tier | `+` enlarged | window search |
|---|---|---|---|---|---|---|---|
| `[1,40]` | `0.3296` | `0.1504` | `0.5817` | **`0.7188`** | `0.7350` | `0.9804` | `1.0000` |
| `[1,120]` | `0.3083` | `0.0571` | `0.5200` | **`0.7471`** | `0.7792` | `0.9875` | `1.0000` |
| `[1,400]` | `0.2908` | `0.0125` | `0.4746` | **`0.7250`** | `0.8096` | `0.9971` | `1.0000` |
| `[1,1500]` | `0.2846` | `0.0037` | `0.4442` | **`0.7142`** | `0.8217` | `0.9992` | `1.0000` |

The `u = 1/8` column reproduces the handover's *"≈ 49.5% of runners"*. The restored column
confirms its *"more than the above"*: **+24 to +27 points**, cutting the open set from about
53% to about 28%.

**It does not close the Claim.** Roughly a quarter of runners remain outside, which is what
the cascade's enlarged tier and the gap-migration attack are for.

---

## 2. Restoring it exposes a structural fact: §7.3's three cases are nested

Not empirical — arithmetic:

- **T6 ⊆ `u = 1/8`.** `d_max ≤ 7·d_min` puts every reading in `[1,7]`, so every reading is at
  distance `≥ 1` from `8ℤ`, so `u = 1/8` clears. (This is `band_identity` plus Thm 4.8's own
  hypothesis.)
- **grid ⊆ `u = 1/8`.** Readings integral with none `≡ 0 (mod 8)` is exactly the band
  condition at `r = 1`.
- **`u = 1/8` ⊆ `u = r/8`.** It is the `r = 1` case.

So §7.3 presents three settled cases of which **two are strictly contained in the third**,
and all three sit inside the dropped fourth. Measured, T6 and grid contribute **nothing** to
the union — the union column equalled the `u = r/8` column in every row.

This is not a claim that 4.8 or the grid theorem are wrong or useless: both are cheap,
checkable **sufficient conditions** that a reader can apply without evaluating the band. It
is a claim that the paper presents them as independent coverage when they are not.

---

## 3. It removes an internal inconsistency the manuscript already carries

**§1.2:** *"the first runner's **reading** … inside its window is exactly the four points
`1/8, 3/8, 5/8, 7/8` and nothing else."*

**§6.1:** *"the subject's own reading inside the window is the four isolated points
`1/8, 3/8, 5/8, 7/8`."*

**§7.3:** tests `u = 1/8`.

**The manuscript names the four points twice and then tests one of them.** Restoring the
lattice makes §7.3 consistent with §1.2 and §6.1 rather than adding anything foreign.

---

## 4. What it breaks: nothing

| | effect |
|---|---|
| Thm 4.8 | stays true; becomes a sufficient condition for the `r = 1` case rather than independent coverage |
| Thm 4.2, 4.3, 4.5, 4.7 | untouched — they concern the reference instant, where `gcd(r,n) = 1` is already the hypothesis |
| §6.1 | **strengthened.** The negative result says the AP's reading is those four points; testing all four is the matching procedure |
| §6.2, §6.3 | untouched |
| §7.2 soundness | untouched — a returned `u` is correct whichever `r` produced it |
| the Lean tree | `returns_at_first_spine` is the `r = 1` case. Generalising it to `r ∈ {1,3,5,7}`, and to `gcd(r,n) = 1` at general `n`, is `band_identity` with `r` carried through — no new machinery |

---

## 5. W1: restoring it removes the first-instant import at no cost

`PROOF_DEV` Part II: *"the moment is always a boundary point of the reading, **the start
spine or** a point one eighth past some lap line (`[PROVED — 91,456/91,456]`)."*

Restoring the dropped case makes the statement **uniform rather than two-part**:
`u = 1/8 = (8·0 + 1)/(8·1)` is the `k = 0` opening of the reading `s = 1`. The start spine
*is* an opening — of the nearest runner's own zone. So W1 reads as one statement:

> the moment is always an opening `(8k+1)/(8s)` for one of the runner's own readings,
> including `s = 1`.

**Independently confirmed here**, `opening_closing_nN_v1.py`: across `n = 5…11`, **zero**
moments were closings, and every window-start case was the `s = 1`, `k = 0` opening.

Restoring W1 therefore **deletes** the manuscript's chronological claim and replaces it with
a graded, proved, uniform one. Strictly an improvement, and it removes the import identified
in `SMUGGLED_MECHANISMS_v1` §1.

---

## 6. The residue reach: restores a class two to twenty times larger than the grid case

`GRID_REFERENCE_REACH_v1`: *"any runner whose `d_min` divides all its differences reads in
integers, and the same residue test decides"* — **7,112 of 7,152** checked cases were not
grids.

Measured, the fraction of runners with `d_min` dividing every difference against the grid
fraction the manuscript kept:

| span | grid (kept) | `d_min │ all d` (dropped) |
|---|---|---|
| `[1,40]` | `0.1504` | `0.3387` |
| `[1,120]` | `0.0571` | `0.1106` |
| `[1,400]` | `0.0125` | `0.0300` |

Two to three times wider at every span. Both are inside `u = 1/8`, so restoring it adds no
coverage to the union — its value is as a **decision procedure**: one modular test per
difference, no band evaluation.

---

## 7. H1, gap migration and the relay anatomy: they bear on the open 26%, not the settled part

These change no coverage number. What they restore is the **stated attack** on what is left.

- **H1** — *same-side runners are in the way together only where their connecting gap is
  within `1/4` of a lap line*. §6.2 currently refutes the relay argument **without stating
  the rule the relay runs on**.
- **Gap migration** — the global start `1/(8·m*)`, the wrap gap as the only possibly
  deficient gap, `spread ≤ 7m*` forcing the AP, the wrap band verified 35/35.
- **The relay anatomy** — 231,294 blocked runner-instances, mean 2.38 stretches, max 19,
  ends p99 `u = 0.304`, max `0.589`, and **0 of 231,294 chains reach the window's end**.

**One reconciliation is required before restoring these, and it is not optional.** §6.2's
four facts do refute Lemma 1 (the `9/7` bound is first-zone only; a single reading blocks
both ends) and Lemma 2's runner-counting (a relay is built from zones, not runners). What
§6.2 does **not** address is the Diophantine condition `k·b ≡ 0 (mod 8a)`. So the material
restores as **evidence and a rule**, not as a re-assertion of the two refuted lemmas, and the
paper must say which.

---

## 8. One live tension the ladder exposes

At `[1,40]` the **cascade reaches `0.9804` while the window search reaches `1.0000`**. The
cascade's enlarged tier is capped at `D ≤ 7·d_min`, and it evaluates four instants per
lattice; the window search evaluates every clear point of one interval. **Neither contains
the other**, and on this population the window search is the stronger of the two.

That is worth settling before either is made canonical, and it is the same question left open
in `AUDIT_WINDOW_ASSUMPTION_v1` §5.

---

## 9. Verdict

| restore | effect |
|---|---|
| **the four-instant lattice** | **improves** — open set 53% → 28%, fixes the §1.2/§6.1/§7.3 inconsistency, breaks nothing |
| **W1 with its start-spine case** | **improves** — removes the first-instant import, yields one graded uniform statement |
| **the residue reach** | **improves** — a decision procedure 2–3× wider than the grid case it replaces |
| **dilation invariance** | **improves** — the reading is a function of the reading vector; this is what makes it so |
| **H1, gap migration, relay anatomy** | **improves, with a required reconciliation against §6.2** |
| **the ten dropped counts** | **improves** — restores grades to results that currently carry none |

**Nothing on this list breaks the proof. Nothing on it closes the Claim either** — after
every restoration about a quarter of runners remain outside the settled cases, which is
exactly where the open work is.
