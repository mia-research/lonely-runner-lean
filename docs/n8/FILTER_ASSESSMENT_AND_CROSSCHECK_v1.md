# Is the instant-variance filter worth keeping, and a cross-check of the parallel session

Two questions, answered separately because they have different answers.

---

## Part A — the filter: what it is worth

`INSTANT_INVARIANCE_v1` §5 proposed: *to see the multiplier structure, ask a question whose answer
varies across the four grid instants.* Assessed against the three things asked of it.

### A.1 Does it get us close to Existence? **No, and there is a structural reason.**

Loneliness of subject `i` at time `t` is `∀ d ∈ ds, ‖d·t‖ ≥ 1/8` — **a function of the disparity
multiset alone.** So the target is a `ds`-level predicate, and `INSTANT_INVARIANCE_v1` §3 says
`ds`-level objects are group-blind. The filter therefore cannot be applied to the target at all.

That is not a proof that no multiplier argument can work — BS's own conclusion `χ_r(D) ≤ p` is
`ds`-level while its machinery is multiplier-level, so group structure may be used and cancelled
before the conclusion. But it does mean **the filter is not a route**, and I should not have
implied otherwise by pairing it with the open sub-problem the way §5 did.

### A.2 Does it help with collisions? **Marginally, and nothing new.**

The cage gives: at a grid instant, offset `0` is the *only* failure mode, and every other offset
carries quantified slack (`2^ν₂/8`). That is a clean statement about collisions — but it is the
residue partition plus the cage restated, both already on file. The filter adds no collision fact
that `NEIGHBOUR_DEFORMATION_v2` §3 did not already carry.

### A.3 Does it help with bounding? **At grid instants yes; off them no, and that is where the work is.**

`NEIGHBOUR_DEFORMATION_v2` §4 gives exact perturbation budgets per offset (`min(d,8−d)−1` at
`p = 1`). Those are bounds and they are exact. They apply only at grid instants. The cascade lives
off them, and §6 of that note measured depth as not determined by either coordinate. So for
bounding the cascade: no.

### A.4 Verdict

**Keep it as a cheap screen; do not build on it as a strategy.** It is decidable, costs one script,
and it retro-explained one null (the 10.4%) rather than leaving it a brute fact. It is a *necessary*
condition only — the neighbour varies across instants and still failed to predict depth. It says
what cannot work, never what does.

The one concrete thing it still supports is `BS_TRANSFER_v2` §4's open sub-problem: if an affine
multiplier family at order 8 exists, §2 of that note says it is detectable in the assignment and
never in the multiset. That is a statement about where to look, not a reason to expect success.

### A.5 A new measurement that closes the most natural bridge

BS Corollary 3's hypothesis is *every 2-adic level of the disparity set below the top has at most
3 elements*. Measured on the primitive sweep (speeds 1..17, 91,456 subject-instances,
`corollary3_hypothesis_v1.py`):

```
  Corollary 3 hypothesis holds : 37640 of 91456   (0.4116)
  largest level below the top  : {0:232, 2:4112, 3:33296, 4:33672, 5:16560, 6:3584}
```

**41.2%** — and `BS_TRANSFER_v1` §3's *unfiltered* union bound over the whole unit group reached
**76.5%**. So the 2-adic filtration route is quantifiably **worse** than the route already measured,
which confirms `BS_TRANSFER_v2` §4's qualitative claim (at `p = 2` the digit is always `1`, so
levels buy almost nothing) with a number. `[EMPIRICAL]`, bound to this sweep.

---

## Part B — cross-check of the parallel session

Their sweep was reimplemented independently. **Their headline reproduces exactly: 45468 unique-
residue subjects of 91456 (49.72%)**, so the same code that confirms (A) below also produces the
refutations, which is why they are trustworthy.

### B.1 Their claim (A): lonely at `t = 1/(8g)` ⟺ unique reduced residue — **confirmed**

45468 / 91456, zero disagreements. Independently reproduces `residue_partition_v1.py` (32,000 /
32,000) on a different enumeration. This one is sound and is `spine_all_or_nothing` read as a
partition.

### B.2 Their claim (B): *"At n=8, no slot mod 8 ever holds more than 3 runners"* — **forced by their bound**

A residue class has representatives `r, r+8, r+16, …`, so a sweep capped at `16` makes **at most 3
available**. The observation is an artifact of the enumeration, not a property of order 8. Witnesses
at every multiplicity (`slot_multiplicity_v1.py`, all primitive, all speeds positive):

```
  k=4: [1,2,3,4,5,9,17,25]     k=5: [1,2,3,4,9,17,25,33]
  k=6: [1,2,3,9,17,25,33,41]   k=7: [1,2,9,17,25,33,41,49]
```

**The true bound is 7**, by a one-line argument: all 8 in one slot forces every pairwise difference
divisible by 8, hence `g ≥ 8`, contradicting primitivity. This matters — 3 would have fed
Corollary 3's hypothesis directly; 7 does not.

### B.3 Their claim (C): the proposed Lean theorem — **false as stated, both directions**

The plan asserts `candidateScale 8 (d_min) 0 = d_min`, *"which is the grid scale `D_0`"*, and
proposes `clear at k=0 ⟺ IsUniqueResidueMod8`.

**`d_min` is not the grid scale.** `g` is the gcd of the disparities and `d_min` their minimum;
`g ∣ d_min`, and they coincide in only **63.5%** of cases. Their Python verified the predicate at
scale `g`; the Lean plan states it at scale `d_min`. Different predicates:

```
  clear at scale d_min (their k=0) : 60998  (0.6670)
  unique residue       (their (A)) : 45468  (0.4972)
  DISAGREEMENTS                    : 17378  (0.1900)
```

Minimal witnesses, both directions:

```
  ->  v = [1,2,3,4,5,6,7,9]    subject 9   ds = [2,3,4,5,6,7,8]  d_min = 2, g = 1
      clear at d_min: TRUE     residue unique: FALSE  (disparity 8 ≡ 0 mod 8)

  <-  v = [1,2,3,4,5,6,14,16]  subject 16  ds = [2,10,11,12,13,14,15]  d_min = 2
      residue unique: TRUE     clear at d_min: FALSE
```

The first is the AP with one runner moved. **The `Iff` should not be attempted as written**; the
sound statement is at scale `g`, which is `spine_all_or_nothing` and already proved. Note also that
their stated `IsUniqueResidueMod8` takes `g` as a parameter with `hg : g = gcd_diffs v i` — so the
definition is already at `g` while the surrounding claim is at `d_min`. That inconsistency is
internal to the proposal, not introduced here.

### B.4 Presentation, not a defect: `0 = v_0`

Their enumeration writes `0 = v_0 < v_1 < … < v_7 ≤ 16`. Register item 12 bans a stationary runner,
but disparities are shift-invariant, so this is the allowed reduction and **every number is
unaffected** — reproduced here with speeds `1..17` and the count matches to the unit. Worth
correcting in presentation (per the owner's standing correction), not a reason to doubt (A).

---

## C — What none of this establishes

No proof at order 8. Part A concludes the filter is a screen, not a route, and A.5 closes a bridge
rather than opening one. Part B confirms one of three claims and refutes two; refuting the
mechanism of (B) and (C) says nothing about whether their broader direction is right — check thesis
and mechanism separately, thesis first.

## D — Artefacts

```bash
python3 experiments/n8/crosscheck_other_session_v1.py   # reproduces 45468; refutes (B) and (C)
python3 experiments/n8/slot_multiplicity_v1.py          # true bound is 7, witnesses k=2..7
python3 experiments/n8/corollary3_hypothesis_v1.py      # Corollary 3 hypothesis: 41.2%
```
