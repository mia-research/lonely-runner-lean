# Functions lost between the source documents and the manuscript

2026-09-13. Sources: `HANDOVER_2026_09_13_v1.md`, `PROOF_CANDIDATE_v3.md`,
`lrc-n8/notes/PROOF_DEV_v1.md`. Every finding is a term count or a verbatim quote.
**Nothing has been changed.**

---

## A. The AP/grid `d_min` lattice — the four spine instants

**`HANDOVER` §4, "Already proved", four rows:**

| case | coverage |
|---|---|
| `d_max ≤ 7·d_min` | 35,467 / 35,467 |
| every grid **and every dilate** | 485 / 485 |
| any runner with no `s_j` within 1 of a multiple of 8 | ≈ 49.5% of runners |
| **the same at `u = r/8`, `r ∈ {1,3,5,7}`** | **more than the above** |

**`MANUSCRIPT_v4` §7.3, three:**

> the ratio condition of 4.8; every grid with `d_min = g` throughout, where the moment is
> exactly `1/(8g)`; and every runner none of whose readings lies within 1 of a multiple of
> 8, **for which `u = 1/8` returns**.

**The fourth row is gone.** `"1,3,5,7"` appears **0** times in the manuscript. The paper
claims the test at **one** instant, `u = 1/8`; the handover claims it at **all four units mod
8**, and says explicitly that this covers *more*.

That fourth row **is** the lattice: `φ(8) = 4` instants at the runner's own scale, not one.
It is the same object as `PROOF_CANDIDATE` §2(b)'s `gcd(r,n) = 1` and as the grid tier of the
cascade. Dropping it reduced a four-instant test to a one-instant test, which is the
narrowest reading of the framework on record — and is the one I then implemented.

**"every dilate" is also gone** from the second row. `"dilate"` and `"dilation"`: **0** in the
manuscript.

---

## B. The residue mechanism, and its reach far beyond grids

**`PROOF_DEV` Part III:**

> every runner's `d_min = g`, every `s_j` is an integer, and the reading collapses to
> residues: in the way at the start spine ⟺ some difference `≡ 0 (mod 8g)` ⟺ two runners
> share a residue.

and the reach:

> **The reach is wider than gridness:** any runner whose `d_min` **divides all its
> differences** reads in integers, and the same residue test decides
> (`GRID_REFERENCE_REACH_v1`: **7,112 of 7,152** checked cases were not grids).

**Manuscript:** `"residue"` **0**, `"mod 8g"` **0**, `"divides all"` **0**, `"complete
system"` **0**.

The manuscript keeps only the narrow consequence — "every grid with `d_min = g`" — and drops
both the mechanism that produces it and the fact that it reaches **7,112 cases that are not
grids**. A reader is left with a special case where the source has a general test.

---

## C. Ratio-native reading and dilation invariance

**`PROOF_DEV` Part IV:**

> **The reading is ratio-native.** `s_j = d_j / d_min` is invariant under dilation… Grids
> are scalable at any level because the reading never sees the speed magnitudes — only
> ratios to the nearest neighbour.

**Manuscript:** **0** occurrences of dilation in any form.

This is not decoration. It is why the doubled AP `(1,3,5,…,15)` dissolves — *"the case that
looks tricky is the AP wearing a dilate's clothes"* — and it is what makes the reading a
function of the reading vector alone.

---

## D. W1 — and this is where the first-instant import came from

**`PROOF_DEV` Part II:**

> the moment is always a boundary point of the reading, **the start spine or** a point one
> eighth past some lap line (`[PROVED — 91,456/91,456]`).

**`MANUSCRIPT_v4` §7.2, line 335:**

> Additionally, **the first instant** of loneliness, when it exists, is always an *opening*
> `(8k+1)/(8d)` for one of the runner's own differences — never a closing.

Three changes in one sentence:

1. **"the moment" → "the first instant"** — the chronological over-demand the firewall bans.
2. **The start-spine case was dropped.** W1 has two cases; the manuscript keeps one. With the
   start spine removed the statement reads as a claim about which instant comes *first*.
3. **`[PROVED — 91,456/91,456]` → no grade and no count.** A proved two-case statement became
   an ungraded one-case aside.

`"91,456"`: **0** in the manuscript.

---

## E. H1 — half the Diophantine core

**`PROOF_DEV` Part V:**

> H1 (same-side runners are in the way together only where their connecting gap is within
> 1/4 of a lap line)

**Manuscript:** `"same-side"` **0**, `"quarter"` **0**.

H1 is one of the two ingredients that force `k·b ≡ 0 (mod 8a)`. §6.2 of the manuscript
refutes the relay argument without ever stating the rule the relay argument runs on.

---

## F. The wrap gap, the global start, and gap migration

**`PROOF_DEV` Part V:**

> At the global start `1/(8·m*)` (`m*` = the nearest gap anywhere), every speed-gap reads
> `a_k/(8m*) ≥ 1/8` — so the only possibly-deficient gap is the **wrap gap**… `spread ≤ 7·m*`
> forces all seven gaps to equal `m*`… the wrap band `7m* < spread ≤ 8m*` gives exactly six
> lonely with deficient pair `(r1, r8)` — **verified 35/35**.

**Manuscript:** `"global start"` **0**, `"migrat"` **0**, `"m*"` **0**. Its two `"wrap"` hits
are §4.1 on cyclic adjacency — a different thing entirely.

The entire gap-frame half of the attack is absent.

---

## G. The relay anatomy

**`PROOF_DEV` Part V**, measured over every migrated arrangement to `v₈ ≤ 20`:

> **231,294 blocked runner-instances** — mean relay 2.38 stretches, p99 8, max 19; ends p99
> `u = 0.304`, max `0.589`; **0 of 231,294 chains reach the window's end**.

**Manuscript §6.2** keeps one number from this — *"an observed chain ran 11 hops"* — and
drops the rest. `"231,294"`: **0**.

The strongest single piece of evidence about the relay is not in the paper that refutes the
relay.

---

## H. Part II's perturbation mechanisms

`"perturb"` **0**, `"re-anchor"` **0**, `"band runner"` **0**, `"pinch"` **0**.

Window re-anchoring, the far-end band runner, the one-sided-versus-symmetric distinction
(*"a perturbation is hard exactly when it is one-sided"*), and the spine-pinch boundary case
are all absent.

---

## I. Ten of sixteen verification counts did not survive

| count | what it graded | in manuscript |
|---|---|---|
| 35,467 | the ratio condition's coverage | **no** |
| 485 | the grid theorem | **no** |
| 49.5% | the no-reading-within-1 coverage | **no** |
| 91,456 | W1 | **no** |
| 7,112 | the residue test beyond grids | **no** |
| 231,294 | the relay anatomy | **no** |
| 12,135 | Step 6(c), survival | **no** |
| 15,289 | Step 6(b), displacement | **no** |
| 113,145 / 77,400 | the `v₈ ≤ 20` exhaustive | **no** |
| 3,276 / 48,000 | five vs six readings | yes |
| 21,600 | the seven populations | yes |
| 12,870 | Cor 4.4 | yes |
| 24,310 | Thm 4.9 | yes |
| 121,722 | Prop 2.1 | yes |

**The pattern is not random.** What survived is attached to *numbered theorems*. What was
dropped is attached to the *settled cases* and the *mechanisms* — and 12,135 and 15,289 show
that even surviving theorems (4.6, 4.7) lost their evidence.

---

## J. What this adds to `SMUGGLED_MECHANISMS_v1`

That document found what came **in**. This one finds what went **out**, and §D links them:
the first-instant demand is not an invention from nowhere — it is **W1 rewritten**, with its
second case and its grade removed.

The single most consequential loss is **§A**: the manuscript tests one instant where the
framework tests four.
