# Audit: which search did the recent work actually measure?

2026-09-13. Owner's instruction: pause, read the manuscript, and go back over the attempts
to generalise and enlarge the `n = 8` work. **No conclusion below is a defence of that
work.**

---

## 1. The finding: two different procedures are on record

**`MANUSCRIPT_v4.md` §7.1** — *the window search*:

> For each runner: form `d_min` from the two speed-neighbours; form the window
> `u ∈ [1/8, 7/8]`; read the other six inside it; **return the first point at which all are
> clear**.

and §1.3: *"The construction confines its evaluation to that first window."*

**`SKETCH_v7.md` §7c** — *the cascade*:

> Three tiers, tried in order for each runner. `g` is the gcd of all differences; `d_min(i)`
> the runner's nearest difference; **the candidate instants are always `t = p/(8D)`,
> `p ∈ {1,3,5,7}`.**
>
> | tier | step `D` |
> |---|---|
> | AP | `g` |
> | grid | `d_min(i)` |
> | enlarged | some `D` beyond those |

**These are not the same search, and neither contains the other.**

- The cascade evaluates **four instants per lattice**. It does not search an interval.
- The window search evaluates **every clear point of an interval**, at the single lattice
  `D = d_min`.
- Cascade instants at `D ≠ d_min` lie outside the window; window points other than `p/8` are
  not cascade candidates.

The manuscript contains **no mention** of the cascade, of `g`, of enlarging `D`, or of a
lattice — a grep for all of them returns nothing. The sketch contains no window search.

**I implemented the manuscript.** That is the error behind the retraction in
`CLAIM_REFUTED_v2.md`, and it is not confined to that document.

---

## 2. What each search actually reaches

Random 8-sets, exact arithmetic, 2,000 runner-instances per row.

| speeds in | AP tier `D=g` | `+` grid tier `D=d_min` | `+` enlarged `D ≤ 7d_min` | window search |
|---|---|---|---|---|
| `[1,40]` | `0.4370` | `0.7185` | `0.9790` | `1.0000` |
| `[1,120]` | `0.4180` | `0.7740` | `0.9895` | `1.0000` |
| `[1,400]` | `0.3985` | `0.8020` | `0.9965` | `1.0000` |
| `[1,1500]` | `0.3935` | `0.8200` | `1.0000` | `1.0000` |

The grid-tier column reproduces `SKETCH_v7` §7b's own figure — *"about 72% of runners named
outright"* — which is the cross-check that the tiers are implemented as §7c defines them.

---

## 3. Artefact-by-artefact

| artefact | what it measured | verdict |
|---|---|---|
| `PHI_REACH_SCALE_v1–v3` | `u = p/n`, `gcd(p,n)=1`, at `D = d_min` | **SOUND.** This is exactly the **grid tier**. Its `n = 8` figures (`0.71`–`0.75`) sit on the grid-tier column above. It was named "spine reach" and scoped in §0 as "one component of the framework's settled cases, not all of them", which is correct. It does **not** measure the cascade, and never claimed to. |
| `EXHAUSTIVE_OTHER_ORDERS_v1` | the **window search** | **FRAMING WRONG.** Its numbers are true of the window search. Its headline — *"does the procedure return"*, 4,025,986 instances, zero failures — names an object the framework does not use. The zero-failure result is unsurprising for the window search, which reaches `1.0000` above. |
| `TIGHTEST_v1` | clear **components of the window** | **FRAMING WRONG** for the same reason. "A clear set of one instant" is a fact about the window, not about the four instants the procedure tries. Its §4 Lean theorem (`near_ap_top_returns`, clear at `u = 1/n`) is about the `p = 1` grid-tier instant and **is** sound. |
| `CLAIM_REFUTED_v1` | the window search | **RETRACTED** already, in `CLAIM_REFUTED_v2.md`. |
| `failure_hunt_v1`, `failure_laps_v1`, `margin_count_v1` | the window search | **WRONG OBJECT.** Withdrawn as evidence about the framework. |
| `CASCADE_SHARPENED_v1` | the cascade, `t = p/(8D)`, `D ≤ 7d_min` | **SOUND** — it is the only recent empirical document that measured the framework's own search. |

### The Lean

The formal work is **not affected**, because every theorem carries its hypotheses
explicitly and none asserts that the window is the search space.

- `window_iff` is true and is part 4 of the construction: the nearest runner is clear
  exactly on `[1/n, (n−1)/n]`. That the framework evaluates four instants rather than
  searching that interval does not touch it.
- `coord_iff` is **the cascade's own clearing test** — `D ≤ (d·p) mod 8D ≤ 7D` at `n = 8`.
  The formalisation is aligned with §7c, not with the window.
- `returns_at_first_spine`, `near_ap_top_returns`, `band_identity` are about `u = 1/n`, the
  `p = 1` grid-tier instant. Sound.
- `Instants.lean` (part 2(b)) involves no window. Sound.
- **One name overreaches**: `procedure_sound`. The theorem is true — window plus clear
  readings gives loneliness — but "the procedure" in §7c does not use a window, so the name
  claims more than the statement. It should be renamed for what it is: soundness of a point
  in the window.

---

## 4. What I should have done

`CASCADE_SHARPENED_v1.md` §1 ran the cascade on the arrangement and found **419 clearing
lattices**. §2 identified the band `D ∈ [1241, 1451]` and called the owner's `~1200` "the
right object and the right magnitude". Both were written the same day, by me, before the
refutation claim. The evidence that the framework handles the case was already in hand.

The check that separates the two procedures is one line — *does the search evaluate an
interval or a finite set of instants?* — and reading §7c answers it. I read §7.1 instead and
did not reconcile the two.

---

## 5. Open, and the owner's call

1. **Which document is authoritative** — `MANUSCRIPT_v4` §7.1's window search, or
   `SKETCH_v7` §7c's cascade? They are different claims with different truth values, and
   §7.3's Claim inherits whichever is meant.
2. If the cascade is authoritative, **the manuscript's §1.3, §7.1, §7.2 and §7.3 describe a
   procedure the framework has moved past**, and §7.3's Claim is a claim about the old one.
3. The window search reaches `1.0000` where the cascade reaches `0.979`–`1.000` on the same
   samples, so neither dominates. That is worth knowing before either is made canonical.

**Nothing in the manuscript has been changed, and nothing in the Lean tree has been renamed.**
