# Why the BS intersection surfaced at the neighbour and nowhere else

**Owner, 2026-09-18:** *"What is interesting is that the possible intersection only comes up when
looking at the neighbours' interaction, not the isolation."*

That is correct, and it has a mechanism. This note states it, measures it, and draws the
prescriptive consequence.

---

## 1. The mechanism, in one line each

- **The isolation verdict at a grid instant is `n ∤ (w j − w i)`** — offset `≠ 0`. That condition
  does not mention `p`. It is **instant-independent**.
- **The neighbour at instant `p` is the runner at offset `≡ ±p`.** That is **instant-determined**.

The four grid instants are the action of the unit group `(ℤ/8)ˣ`. A yes/no question whose answer is
constant across the orbit cannot detect a group that acts *within* the orbit. The neighbour resolves
the orbit; the verdict factors through it. So the multiplier structure — BS's whole apparatus — is
invisible to isolation and visible to the neighbour. `[PROVED]`: the verdict half is
`ConstructionN.spine_all_or_nothing`; the neighbour half is `GridNeighbour.slot_gcd` plus the `±p`
rule.

---

## 2. Measured

Fraction of subjects for which a quantity is **constant across all four grid instants**
(`instant_invariance_v1.py`, 800 grid subjects and 800 general subjects):

| quantity | grids | general arrangements |
|---|---|---|
| isolation verdict | **1.0000** | **1.0000** |
| distance multiset | **1.0000** | 0.1800 |
| slot set | **1.0000** | 0.0025 |
| `d_min` (tightness) | **1.0000** | 0.9525 |
| **neighbour pair** | **0.0000** | **0.0000** |

On a grid the result is as sharp as it can be: **every scalar and multiset quantity is invariant,
and the neighbour is invariant never.** The group permutes *which runner gets which distance* and
moves nothing else. `[EMPIRICAL]` on this sampler; the grid column's `1.0000`s follow from §1.

---

## 3. The consequence: `ds`-level statements cannot express it

`ds` is the multiset `{|w j − w i|}`. It determines each offset **up to sign** — so it fixes
`|offset|`, and loses orientation. The neighbour ahead is at offset `+p` and behind at `−p`, so
orientation is exactly what is lost.

Measured: among disparity multisets seen more than once, with **tied subjects excluded** (ties broken
arbitrarily would have manufactured the effect — 180,906 dropped):

```
  carry > 1 ORDERED  (ahead, behind) offset pair : 0.3869
  carry > 1 UNORDERED |offset| pair              : 0.3421
```

So `ds` does not fix *which is ahead*, and does not even fix **which two runners bind**. A witness
(`ds_blindness_v1.py`), both subjects with reduced disparities `[3,4,6,9,12,15,19]`:

```
  arrangement [2,9,12,18,21,25,27,36]  subject 21 -> neighbours (9, 36)
  arrangement [7,15,19,22,25,28,34,38] subject 19 -> neighbours (28, 34)
```

**The reading and scale apparatus is therefore group-blind by construction.** `d_min`, `S`, the
readings `d/d_min`, `R`, and the cascade itself are all functions of `ds` alone. They can see
`|offset|`; they cannot see offset. Nothing stated in them can express the multiplier structure.

That also explains a negative already on file rather than leaving it unexplained:
`NEIGHBOUR_DEFORMATION_v2` §5 found the cascade's neighbour only 10.4% residue-determined. The
cascade takes `ds`; the neighbour needs the signed offset; `ds` does not carry it.

---

## 4. Convergence with the target amendment

The n=8 target was amended on 2026-09-18 from `ExistenceAt8` — quantified over a difference set
`ds` — to `LRC.Spec.LonelyRunnerAt8` on an **arrangement** `v : Fin 8 → ℝ`, on the recorded ground
that *a Finset collapses duplicates and discards the arrangement*, with the related note that
speed-rank and interior/endpoint are arrangement facts so a theorem stated in them adds nothing.

**This note is a second, independent instance of that same principle**, and the general principle is
already on record — the new part is the specific consequence: the multiplier/orbit structure is
arrangement-level, so it is expressible against `LonelyRunnerAt8` and not against `ExistenceAt8`.
The amendment was made for a different reason and turns out to be what makes BS-type structure
sayable at all. Stated as convergence, not as a discovery of the reason.

---

## 5. Prescriptive consequence

A usable filter, and the first concrete thing to come out of this line:

> **To see the multiplier structure, ask a question whose answer varies across the four grid
> instants.** Anything constant over them — and on a grid that is every scalar in the framework —
> is blind to it by construction, no matter how it is sharpened.

`BS_TRANSFER_v2` §4 left a well-posed open sub-problem: exhibit an affine multiplier family at
order 8. §2 here says where such a thing could possibly be detected — in the assignment, never in
the multiset.

---

## 6. What this does not establish

No proof at order 8, and no claim that the neighbour is the *only* group-sensitive object — only
that the quantities tested are blind and it is not. §2's general-arrangement column shows the
invariance is clean for grids and partial otherwise (`d_min` still 0.9525), so "constant across the
orbit" is a grid statement, not a universal one. §3's percentages are sampler frequencies, bound to
speeds drawn from `1..39` and 40,000 arrangements. Nothing here touches the firewall question left
open in `BS_TRANSFER_v1` §4.

## 7. Artefacts

```bash
python3 experiments/n8/instant_invariance_v1.py   # the invariance table
python3 experiments/n8/ds_blindness_v1.py         # witness: same ds, different neighbours
python3 experiments/n8/ds_blindness_v3.py         # ties excluded -- v2 was tie-contaminated
```
