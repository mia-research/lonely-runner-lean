# Candidate inputs for MANUSCRIPT v11

Record of what this session produced that is manuscript-grade, what is not, and what must be
corrected. **Promotion is the author's ruling** — this is a list, not a decision.

Current record: `MANUSCRIPT_v10.md` (1,878 lines, gate PASS, 4,759 theorems, digest `c54d9843`).

---

## A. New Lean results — 27 theorems, five files, all axiom-clean, zero `sorry`

⚠ **They currently live in `experiments/n8/`, not in `LonelyRunner/LRC/`.** They are therefore *not*
gate-covered and not counted in the manuscript's figures. Moving them into the tree would change
every figure in §7 and the gate's counts. **That is the first decision needed.**

| file | thms | content |
|---|---|---|
| `DminClearance_v1.lean` | 8 | the clearance criterion, general `n` |
| `GridNeighbour_v1.lean` | 8 | the cage; laps invisible; `slot_gcd` |
| `ExactBlock_v1.lean` | 5 | only colliding disparities block exactly |
| `SingleLevelGeneral_v1.lean` | 3 | BS pigeonhole off a prime modulus |
| `MoveRule_v1.lean` | 2 | the move's lap is exactly `M` |

### A.1 The clearance criterion — **the most consequential**

> **clear at scale `e/(8N+1)` ⟺ for every disparity `a`, `e ≤ a(8N+1) mod 8e ≤ 7e`**
> (`clear_at_scale_iff`; `clear_iff` is the `d_min` case)

and at arbitrary order, with constant `n−1` (`bad_iff_gen`, `clear_of_reading_le_gen`). Verified
32,000/32,000 at `d_min` and **46,353/46,353 at every scale the cascade visits**.

**Consequence for the manuscript: Theorem 4.8's constant `7` becomes a corollary.** A reading in
`[1, n−1]` is inside the band already, so `S ≤ n−1 ⟹` clearance at `d_min`. §3 and §4 of v10 would
need rewriting around this, and the constant stops being order-8-specific.

Also: `dmin_always_clear` — `d_min` never blocks at its own scale, so at most `n−2` of the `n−1`
disparities can fail. Ceiling attained (witness `[1,2,9,17,25,33,41,49]`).

### A.2 The move in closed form

`move_lap`: if `a` blocks at scale `e/(8N+1)` then the next opening's lap is **exactly** `M` — no
rounding case. Hence

```
  λ = max over blockers (8M_a+1)/s_a        D' = a·g/(8M_a+1)
```

verified 18,286/18,286. **Every cascade scale is `Cascade.candidateScale 8 (a·g) M_a`** — the
cascade never leaves that family. This completes §6's recursion: no step lacks a closed form.

### A.3 The cage

`slot_gcd` (arbitrary `n`), `gridPos_caged`, `even_offset_caged`: a runner whose residue offset
shares a factor with `n` can never approach the subject. At `n = 8` the closest approach is exactly
`2^ν₂(d)/8`, so **offsets 2, 4, 6 are barred from ever binding at a grid instant** — the grid-instant
problem is a 4-runner problem. Perturbation budget `min(d, 8−d) − 1` at `p = 1`.

### A.4 Laps are invisible

`laps_invisible`, `neighbour_laps_invisible`: two arrangements sharing residues hand the subject the
*identical* position function, so the whole cyclic order agrees. Supports the 2026-09-18 target
amendment to `LonelyRunnerAt8` — the multiplier structure is arrangement-level and is not
expressible against `ExistenceAt8`.

### A.5 Exact blocks

`exact_block_is_colliding`: `s = 8M` forces `8 ∣ a` since `8N+1` is odd. So non-colliding disparities
block exactly **0** times (theorem, matched 0/12,152). `near_block_host_large`: a near block needs
`c > 8`, so a host `≤ 8` admits only exact blocks.

---

## B. Empirical results, gradeable

| result | figure | grade |
|---|---|---|
| depth stratification by rung | `k=0` 53.0%, `≤1` 74.8%, `≤2` 88.0%, `≤3` 95.0%, `≤4` 97.7% | `[EMPIRICAL]` |
| depth concentrates just above `S = 7` | mean 2.09 in `(7.25,7.5)` vs 1.02 above `S=9`, n = 60,000 | `[EMPIRICAL]` |
| cell-width law | `log width = 3.710 − 0.1754·depth`, corr −0.718, 96 cells | `[EMPIRICAL]` |
| walls are `q·a_i = p·a_j` | 6/7 recovered by enumeration; `big = 7c` exact to 10⁻¹² | mixed |
| colliding disparities drive the cascade | 31.3% of setters on 19.2% of the pack; 1.93× after size control | `[EMPIRICAL]` |
| 81.3% of colliding blocks are exact | criterion `r = 0 ⟺ c ∣ b(8N+1)`, 5305/5305 | `[EMPIRICAL]` + `[PROVED]` half |

---

## C. Corrections v11 must carry

1. **§6.7 / the adversarial record.** v10 records 28 moves at `(27,70,107,137,159,188,344,393)`,
   subject 393, `t* = 49/1872` — **independently reproduced this session, correct as written.**
   Band-directed search reached 27, which does not beat it.
2. **A new deep-case datum**: both deep cases have `S ≈ 7.47` (7.467 and 7.469).
3. **Theorem 4.8's constant** is `n−1` at every order, not a fact about 8 (A.1).

## D. Should NOT go in

* **`BS_TRANSFER_v1` §3** — the multiplier union-bound work. Its form is "the bad sets do not cover
  the multiplier group", which collides with the §6A firewall, and **that question is unruled**.
  §1, §2 and the cage are independent and may go in.
* **The witness-complexity comparison** — the owner's ruling was to note it as an interesting fact,
  not to build on it.
* **The instant-variance filter as a route** — it is a screen; §A.4 carries what matters.

## E. Open items to state honestly in §9

* depth is determined by neither `π` nor `q`, and by no tested input feature (all |corr| < 0.22);
* `M` in the multiplier frame is unbounded as far as search goes (reached 20);
* the k=1 rung exists in closed form but has no residue-band reduction;
* which enumerable walls are *realised* is trajectory-dependent — 399 candidates, ~8 realised.

---

## F. Decisions needed before drafting

1. **Do the 27 theorems move into `LonelyRunner/LRC/`?** If yes, §7 and every gate figure change,
   and `scripts/cascade/gate.sh` must be re-run. If no, they are cited as development artefacts.
2. **Does A.1 restructure §3–§4**, with Theorem 4.8 demoted to a corollary?
3. **Is the firewall question (D, first bullet) ruled** before or after v11?
