# Barajas–Serra at order 8: the dictionary is exact, and the cage is what breaks it

Follows `NEIGHBOUR_DEFORMATION_v2.md` §3. v2 called the BS parallel "an observation, stated not
exploited, and their argument does not transfer". **Read against the source, that was too weak in
one direction and too vague in the other**: the machinery is not analogous, it is the same, and
"does not transfer" has an exact cause which this note names.

Source read first, per CLAUDE.md §5: `sources_barajas_serra_2008.txt` §2, lines 84–145.

---

## 1. The dictionary

| Barajas–Serra 2008, §2 | this framework |
|---|---|
| `ν_p(x) = max{k : x ≡ 0 mod p^k}`, and `ν_p(x) = ν_p((x)_N)` | the offset's 2-adic valuation |
| multiplier `λ ∈ U(ℤ_N)` | the grid instant `p` |
| `q(x) = ⌊x/p^m⌋ mod p`, the arc index | the slot `(d·p) mod n` |
| goal `q(λ·D₀) ∩ {0, p−1} = ∅` | every runner clear of the subject |
| which is `|λd|_N ≥ N/p` | circle distance `≥ 1/n` — the threshold |
| **eq. (2): `ν_p(λ·x) = ν_p(x)`** | **`slot_gcd`** |
| `p`–levels `D_p(i) = {d : ν_p(d) = i}` | the orbit classes of the cage |

These are not analogies. BS's `ν` is the valuation of a disparity reduced mod `N`; §3 of v2 uses the
valuation of a residue offset, which is the same number. Their multiplier action `d ↦ λd` is the
instant action. Their eq. (2) is `slot_gcd`, which the Lean file proves for **arbitrary `n`**, not
just prime powers — BS state it only where they need it.

Their objective, unwound, is the loneliness condition at threshold `1/p`. The whole of BS §2 is a
search for an isolation instant.

---

## 2. What breaks, exactly

BS's Lemma 2 (Prime Filtering) proof opens:

> *"For each `d ∈ D(m)` we have `q(Λ_m,p · d) = Λ_m,p`."*

with `Λ_m,p = {1, 2, …, p−1}`. **That step needs `p` prime**: it asserts the top-level disparities
can be sent to *any* arc, which holds because every element of `{1,…,p−1}` is a unit mod `p`. The
unit group acts transitively on the nonzero residues.

At `n = 8` the units are `{1,3,5,7}` only. `(ℤ/8)ˣ` is the Klein four-group and does **not** act
transitively — its orbits are `{1,3,5,7}`, `{2,6}`, `{4}`. So `q(Λ · d) ≠ Λ`, and Lemma 2's proof
has no first step.

**The cage and the obstruction are the same fact.** What makes offsets 2, 4, 6 permanently harmless
is what stops the multiplier group from moving them where the counting needs them.

Across orders (`cage_by_order_v1.py`, exhaustive):

```
   n   φ(n)  rigid/total   caged offsets                    cage empty?
   3     2     2/2         –                                 YES (prime)
   5     4     4/4         –                                 YES (prime)
   6     2     2/5         g=2:[2,4]  g=3:[3]                 no
   7     6     6/6         –                                 YES (prime)   <- BS's order
   8     4     4/7         g=2:[2,6]  g=4:[4]                 no           <- ours
   9     6     6/8         g=3:[3,6]                          no
  11    10     10/10       –                                 YES (prime)
```

`[PROVED]` — this is `slot_gcd` plus `gcd(d,n) = 1 ⟺ d` a unit; no sampling.

---

## 3. The lever: BS do not stay at `N = n`

BS work at `N = p^(m+1)`, a lattice much finer than `p` itself, chosen so the disparities have
controlled valuation — and they leave prime powers entirely when they must (§7 is resolved at
`N' = 98 = 2·7²`, CLAUDE.md §11). The same freedom exists here. At modulus `N = 8M`, a disparity is
**auto-clear** when `M | d` and `8M ∤ d`: its whole orbit is caged at distance `≥ M/N = 1/8`.

So the question is whether choosing `M` cages enough disparities for the counting to close. Measured
on 1200 subjects, `M` searched over `1..60` (`prime_filtering_v1.py`, `_v2.py`):

```
  BS union bound  Σ_d |BAD(d)| < |U|   certifies : 918 of 1200   (0.7650)
  a good multiplier ACTUALLY exists              : 1200 of 1200  (1.0000)
  bound fails but a multiplier exists            : 282
  bound fails AND none found                     : 0

  |∪_d BAD(d)| / |U| where one exists:  min 0.719   median 0.859   max 0.984
```

The ratios quantise at exact multiples of `1/4` — each uncaged disparity costs precisely a quarter
of the multiplier group — so the union bound closes exactly when **at most 3 of the 7 disparities
survive the cage**. Without the cage the bound would read `7 × 1/4 = 1.75` and never close; the
cage is what does the work.

**The 23.5% shortfall is counting slack, not absence.** In every one of the 282 failures a good
multiplier exists; the `BAD` sets overlap and the union bound cannot see it. That is precisely the
situation BS meet at `n = 7`, and precisely why their paper is a long case analysis rather than one
lemma.

`[EMPIRICAL]` — bound to this sampler (speeds drawn from `1..89`, 150 arrangements × 8 subjects),
to `M ≤ 60`, and to moduli of the form `8M`. `0.984` is a sample maximum, not a bound. Nothing here
says a multiplier always exists; it says one was found every time in this sample.

---

## 4. ⚠ Firewall question for the owner — this is a ruling, not my call

**The §6A firewall bans covering and emptiness language.** §3's argument is literally *"the bad sets
do not cover the multiplier group"*. That is a direct collision, and I am not treating it as
resolved.

The case for allowing it: this counts elements of a **finite group** — pigeonhole, the same move the
project already uses — not measure or density on the real line, which is what §6A was erected
against. It is also exactly BS's Lemma 2, and BS is the verified `n = 7` source already in the Lean
tree.

The case against: the firewall does not carve out "finite" covering, and the reason it exists is
that covering framings previously smuggled in a stationary frame and a global clock. A multiplier
group indexed by `λ` is arguably a global clock in disguise.

**Nothing in §3 should be built on until this is ruled.** Sections 1, 2 and the cage itself are
independent of it and stand either way.

---

## 5. What this does and does not establish

**Does.** The BS framework is not foreign to order 8 — it is the same objects under different names,
and `slot_gcd` proves its central invariance in more generality than BS state it. The reason Lemma 2
cannot be quoted at `n = 8` is now exact and it is a group-theoretic fact, not a vague "structurally
unrelated". It also revises CLAUDE.md §11's warning usefully: the warning is against reusing the
**BHK geometry** at `n = 7`, and separately BS is called structurally unrelated to BHK — neither
statement says BS's *own* machinery is inapplicable at order 8, and §1 shows it is not.

**Does not.** No proof of anything at order 8. §3 is empirical, on a sampler, at moduli `8M` with
`M ≤ 60`. The union bound's 23.5% shortfall is measured, not closed, and closing it is the entire
difficulty — at `n = 7` that took Barajas and Serra a long paper. The prime/composite table does not
say primality is what makes an order tractable: `n = 4` and `n = 6` are composite and solved. It
says BS's *particular* lemma needs it.

One further caution against reading the table strategically: at `n = 11` the mechanism of Lemma 2 is
restored by primality, but the counting is not — 10 disparities at roughly `2/11` each gives `20/11
> 1`. Primality repairs the mechanism, not its sufficiency.

---

## 6. Artefacts

```bash
cd LonelyRunner && lake env lean ../experiments/n8/GridNeighbour_v1.lean   # slot_gcd = BS eq. (2)
python3 experiments/n8/cage_by_order_v1.py      # the prime/composite table, exhaustive
python3 experiments/n8/prime_filtering_v1.py    # the union bound, minimised over M
python3 experiments/n8/prime_filtering_v2.py    # bound vs truth, the 282
```
