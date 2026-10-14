# The shadowing count — a RE-DERIVATION OF A CLOSED ROUTE, plus two constructive lemmas

> ## ⛔ READ THIS BEFORE USING ANYTHING BELOW
>
> **§§1 and 3 of this document are covering, and covering is a closed route.** They attempt
> *"the union of blocked sets stays below `e`"*, which is the failure named verbatim as mistake
> **1.3** in `docs/nN/HANDOVER_2026_09_21_v1.md`, written the day before this work — and which
> §6A's firewall bans in terms: *"forms no complement and no set to be shown empty; it runs a
> cascade to a named instant."*
>
> The figure `1.5` reached in §3 is the third derivation of the same coincidence; the handover
> already records the blocking-capacity figures *(1.5 at n=5, 1.75 at n=8)* as that coincidence
> re-derived, and §11.1 records it again as *"six combs at density 1/4 over 12 units … a factor
> of 1.5."*
>
> **How it was entered.** External feedback stated the obligation as *"no valid configuration can
> completely shadow all candidate scales"* / *"the clear set is non-empty"*. The obligation of
> record, **Theorem 6.15**, is *"some candidate scale `e/(8k+1)` is clear for every disparity"* —
> an **existential that is exhibited**. Those two are logically equivalent and methodologically
> opposite. The conversion from the second to the first is the whole error, and the word
> **"shadow"** is the tell.
>
> **Live** (not covering, usable): §2.1 and §2.2 only.
> **Dead** (covering, kept only as evidence that the route decays): §1, §2.3, §3, §4.

*Version 2, 2026-09-22. Supersedes `SHADOW_COUNT_v1.md`, which presented this as a live route.
Artefacts `experiments/nN/shadow_count_v1..v6.py`. Order 8; `c = 7` disparities, middle
`1 ≤ M ≤ 5` where `M = #{d : 8 ∣ d}`.*

**What is actually established.** Two elementary constructive lemmas (§2.1, §2.2), neither new to
the framework — §2.1 is §14.2's rescaling fact read as counting, §2.2 is R6 at `q = n` restated.
**No new route.** The counting bounds of §2.3 are sound and strictly stronger than Theorem 15.50,
and are nonetheless covering and decay with range.

---

## 1. The criterion under test

Theorem 15.50 gives a necessary condition for a flank to be shadowed. The flank is existential, so
the contrapositive is a **rule**:

```
    if  for some e ∈ ds,   Σ_{d ≠ e}  c_d · gcd(d, e)  <  e      then the subject is lonely,
```

`c_d` being the blocked residue classes mod `q_d = e / gcd(d,e)`. **Soundness checked**: the rule
fired on 23,271 seven-element sets from `[1,21]` and a clear opening existed in every one —
**0 unsound cases** (`shadow_count_v1.py`).

---

## 2. Three positive results

**2.1 The zero-contribution lemma.** `[PROVED — elementary]` If `e ∣ d`, write `d = e·m`. The reading
at opening `k` is `e·(m(nk+1) mod n)`, and `nk+1` is a unit mod `n`, so the reading leaves the band
exactly when `n ∣ m`. Hence

> a multiple of the flank blocks **no** opening when `n ∤ (d/e)`, and **every** opening when `n ∣ (d/e)`.

Checked over `e < 40`, `m < 30`: **0 violations**. This is §14.2's rescaling fact read as a counting
statement, and it is the lever that makes short-range counting work at all.

**2.2 The trivial flank is the trichotomy's left end.** `[PROVED — elementary]` At `e = 1` there is
one opening, the reading of `d` is `d mod n`, and it is blocked exactly when `n ∣ d`. So

> the count at flank `e = 1` equals `M` exactly,

and the rule at that flank reads `M < 1`, i.e. `M = 0` — **precisely the closed left end of the
trichotomy**. Checked over all seven-element sets from `[1,19]`: **0 violations**. Two consequences.
Theorem 15.50 at the trivial flank *is* R3/R6-at-`q=n`, so the count subsumes that rule rather than
supplementing it. And in the middle `M ≥ 1`, so the trivial flank always fails, and **by exactly one
when `M = 1`** — which is where most of the residue sits.

**2.3 Two strengthenings of Theorem 15.50, both sound.** `[PROVED — elementary set theory]` Since
`⋃ B_d = B_p ∪ ⋃_{d≠p}(B_d \ B_p)` and `|B_d \ B_p| = |B_d| − |B_d ∩ B_p|`:

```
  one-pivot :  |⋃ B_d|  ≤  |B_p| + Σ_{d≠p} ( |B_d| − |B_d ∩ B_p| )                     any pivot p
  two-pivot :  |⋃ B_d|  ≤  |B_p|+|B_r|−|B_p∩B_r| + Σ_{d≠p,r} ( |B_d| − max(|B_d∩B_p|,|B_d∩B_r|) )
```

The two-pivot form uses **pairwise intersection data only**, so it stays computable from gcd
structure. Soundness: **0 violations** of `bound ≥ truth` over 56,056 flank-instances (one-pivot) and
21,021 (two-pivot). Strictly better than the union bound on 46,878 of 56,056 flank-instances.

---

## 3. The negative, which is the point

On the middle of the trichotomy, sets sampled at random (never lexicographically), 1,500 per range:

| range | union bound closes | one-pivot | two-pivot | truth | two-pivot **misses** |
|---|---|---|---|---|---|
| `[1,21]` | 329 | 1,423 | 1,498 | 1,500 | **2** |
| `[1,30]` | 279 | 1,319 | 1,481 | 1,500 | **19** |
| `[1,40]` | 181 | 1,173 | 1,418 | 1,500 | **82** |
| `[1,60]` | 89 | 952 | 1,244 | 1,500 | **256** |
| `[1,80]` | 84 | 780 | 1,025 | 1,500 | **475** |
| `[1,120]` | 42 | 650 | 837 | 1,500 | **663** |

`[EMPIRICAL — 1,500 random middle sets per range, order 8, exact integer arithmetic; bound
soundness 0 violations at every range.]` Counts, not shares, and not progress.

**Why it decays.** Mean over sampled sets of the best ratio `bound/e` achievable over all flanks,
which must fall below 1 to close a set:

| range | union | one-pivot | two-pivot | **truth** |
|---|---|---|---|---|
| `[1,21]` | 0.945 | 0.770 | 0.730 | 0.681 |
| `[1,40]` | 1.022 | 0.862 | 0.819 | 0.718 |
| `[1,80]` | 1.062 | 0.927 | 0.900 | 0.745 |
| `[1,160]` | 1.090 | 0.961 | 0.947 | 0.765 |
| `[1,320]` | 1.102 | 0.987 | 0.979 | 0.782 |

Both pivoted bounds **converge to 1 from below**; the union bound crossed 1 between ranges 21 and 40.
Meanwhile the truth rises much more slowly and stays near `0.78`. **The gap between the two-pivot
bound and the truth widens from 0.05 to 0.20 across the table** — pairwise data captures a shrinking
fraction of the real overlap among the six blocked sets as `e` grows.

**Conditional statement of the negative.** On this sample, at this order, over these ranges, and for
bounds built from pairwise intersection data, the counting route does not close the middle of the
trichotomy, and the trend is against it rather than merely short of it. Nothing here shows that no
counting argument can work; it shows that **this family of them does not**, and names the reason:
the slack the bound must recover is higher-order correlation among the blocked sets, and pairwise
inclusion–exclusion cannot see it.

---

## 4. What this does to the proposed route

The proposal was to replace "force an interior edge witness" — which is circular, since
`EdgeWitness.edge_witness` takes `Sat l q` as a **hypothesis** — with "defeat the shadowing count".
That replacement is non-circular and remains so; the finding is that the count itself does not get
below `e` at scale.

**What survives as a target.** The truth column is the informative one: the best flank's blocked
fraction sits near `0.78` and is bounded away from 1 across a 15-fold range increase. The clear set
is not marginally non-empty — roughly a fifth of a good flank's openings are clear. Any argument that
reaches that fifth must use structure the pairwise count discards.

**What this corroborates.** §14C's measured mean of 1.1867 blockers where an argument needs below 1,
and §11.1's factor of 1.5, are the same wall; this note maps it as a function of range and shows it
is not an artefact of a particular statistic.

---

## 5. Method note

The `[1,21]` row alone would have read as a near-complete closure of the middle — 1,498 of 1,500 —
and the two-pivot bound would have looked like the missing rule. It is recorded here because the
range was varied, which §13A's retraction is the standing reason to do.
