# The small-denominator route: what it restructures, and why no finite bound exists

2026-09-11. Scripts `experiments/n8/ok_dmin_v1.py`, `ok_dmin_v2.py`, `ok_dmin_v3.py`.
Follows `SMALL_DENOMINATOR_WITNESS_v1.md`. Contains a conjecture of mine and its refutation,
both from this session.

---

## 1. The sharper bound the lemma was hiding  `[PROVED]`

At `t = a/d`, `gcd(a,d)=1`, put `g = gcd(e,d)`, `e = ge'`, `d = gd'`. Then `ea/d = e'a/d'` is
in lowest terms, so `‖e·a/d‖` is a **nonzero** multiple of `1/d'`:

> `‖e·a/d‖ ≥ gcd(e,d)/d`, hence `e` clears `1/8` whenever `2 ≤ d/gcd(e,d) ≤ 8`.

`SMALL_DENOMINATOR_WITNESS_v1`'s lemma is the case `d ≤ 8`. The sharper form permits large
`d` provided every speed shares enough of it. **Measured gain on the residual: 206 of 6250 =
3.30%.** Real but small — recorded so it is not re-derived as a fresh idea.

## 2. The right frame: a CSP over `a`, with CRT as independence  `[PROVED]`

Runner `j`'s condition at `t = a/d` depends on `a` only through `a mod d_j`,
`d_j = d/gcd(e_j,d)`, and as `a` runs over `(ℤ/d)*`, `e'_j a` is uniform over `(ℤ/d_j)*`. So
the problem is a constraint-satisfaction problem whose constraint `j` lives on modulus `d_j`,
and a prime `p` couples constraints `i` and `j` exactly when `v_p(e_i) < v_p(d)` **and**
`v_p(e_j) < v_p(d)` — `p` touches only the speeds it fails to divide. `gcd(e,d)` selects
which covering problem; CRT is independence.

This is the same hypergraph as `CRT_STAR_STRUCTURE_v2` §1: with `8 | d` the 2-part misses
almost everything and touches every constraint (the star), while odd primes touch only the
speeds they miss.

**Full decoupling is impossible, and the reason is a counting one.** Seven pairwise-coprime
`d_j > 1` all divide `d`, and `gcd(e_j,d) ≤ e_max` gives `d_j ≥ d/e_max`, so
`(d/e_max)^7 ≤ d`, i.e. `d ≤ e_max^{7/6}`. At `e_max = 14` that is `d ≤ 21`, which cannot
carry seven distinct primes. Every certificate must therefore survive correlation; it cannot
avoid it.

## 3. The reduction that is genuinely box-free  `[PROVED]`

Whether `t = a/d` is a witness depends only on `E mod d`. Hence

> `dmin(E) ≤ D` is a condition on `E mod lcm(1..D)` — finitely many residue vectors, no
> speed box.

This is the useful structural output of the route: it converts "search over tuples" into
"decide over residue vectors", and it means enlarging a speed box past `lcm(1..D)` is the
only way to see new behaviour.

## 4. My conjecture, and its refutation  `[CONJECTURED then REFUTED — same session]`

`dmin` measured flat across five orders of magnitude — max `dmin` = 28, 27, 26, 28, 29 over
200k–300k sampled residual tuples from `[1..30]`, `[1..60]`, `[1..150]`, `[1..600]`,
`[1..5000]`; 25–26 under adversarial constructions forcing the residual structure and forcing
3-term relations. Over the complete residual in `[1..18]` (6250 tuples) the max is **23**, and
100% are covered by `d ≤ 23`. That invites: *some universal `D` works.*

**False, by an elementary construction.** Let one speed be `lcm(1..D)`. Every `d ≤ D` divides
it, so that runner sits exactly at `0` for every `a`, and `dmin > D`. Measured, with
`E = (1,2,3,5,7,11, lcm(1..D))`:

| `D` | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 |
|---|---|---|---|---|---|---|---|---|---|
| `dmin` | 8 | 13 | 13 | 17 | 17 | 17 | 23 | 25 | 25 |

Witness verified independently at `d = 17`, `a = 4` for the `D = 12` case (all seven
`8‖e a/d‖·d ≥ d`). **No finite `D` suffices**, and random sampling cannot find this —
`lcm(1..29) ≈ 2.3×10¹²`, so a tuple drawn from `[1..5000]` never contains one. The flat table
in §4's first paragraph is an artefact of the sampling distribution, not a fact about `dmin`.

`dmin` tracks the smallest prime outside `E`'s prime content, so it grows, but only
logarithmically in that content.

## 5. The obvious repair, killed before proposing it  `[PROVED]`

Two runners with `e_i ≡ ±e_j (mod d)` impose the *same* condition, so the effective constraint
count is `k±(d) = |{±e_j mod d}|` — which is exactly the GECT collapse law's `k`, used as a
proof tool. A union bound over `k±` conditions each excluding a `≈1/4` fraction of units
closes whenever `k± ≤ 3`.

**It adds nothing.** `k±(d) ≤ 3` with no `e_j ≡ 0 (mod d)` forces `d ≤ 7`, which
`SMALL_DENOMINATOR_WITNESS_v1` already covers automatically and with no union bound. At
`d = 9` the bad fraction among units is `1/3`, not `1/4`, so the threshold *tightens* to
`k± ≤ 2`. The collapse mechanism is strictly inside the small-denominator mechanism.

## 6. Where this leaves n=8

The route restructures the problem and does not close it. What it establishes:

- Case 1 plus **69.29% of Case 2** close by an explicit three-line certificate.
- The residual is exactly "`E` hits every `d ≤ 8`", forcing multiples of 5, 6, 7 and 8 among
  seven speeds, hence `840 | lcm(E)`.
- Membership in every layer of the tower is a **residue** condition, not a speed condition.
- The tower does not terminate: for each `D` there are tuples needing `d > D`.

**What it does not touch.** The `lcm` adversaries are not the hard cases — `E*` is, and `E*`
has `dmin = 15`. The hard instances are those with *small* speeds hitting every `d ≤ 8`, and
for them the certificate exists and is cheap. The open part is the same as before: there is no
argument that *some* `d` always works, and by §4 that argument cannot take the form of a
universal bound. It must bound `dmin` in terms of `E`'s own arithmetic — for which the natural
statistic is the smallest prime dividing no `e_j`, untested here.

## 7. Ledger

`[PROVED]` §1 the `gcd` bound; §2 the CSP frame and the `d ≤ e_max^{7/6}` decoupling
obstruction; §3 the residue reduction; §5 that `k± ≤ 3` forces `d ≤ 7`.
`[VERIFIED — exhaustive]` §4's `dmin ≤ 23` over the complete `[1..18]` residual;
`[VERIFIED — exact]` the `lcm` adversary table and the independently checked witness.
`[REFUTED]` the universal-`D` conjecture — mine, raised and killed in this session. The flat
sampled table is reported with its blind spot named rather than deleted.
`[EMPIRICAL — sampled, blind spot named]` the five box rows of §4.
`[UNTESTED]` bounding `dmin` by the smallest prime dividing no `e_j`.

`n = 8` is **not proved**, and nothing here moves a grade.
