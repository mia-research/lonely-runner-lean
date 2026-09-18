# The session's theorems: consequences and interactions

**Owner:** *"what are the downhill consequences, implications, have we thought them all through and
their interactions?"*

Honest answer: **not all of them.** Working through it produced two consequences I had not drawn,
one refactor opportunity in the verified n=7 tree, and a short list of interactions still unexamined.

## 0. Inventory — 22 theorems, four files, all axiom-clean, zero `sorry`

| file | thms | core content |
|---|---|---|
| `GridNeighbour_v1.lean` | 8 | `slot_gcd` (= BS eq. 2, **general `n`**), the cage, laps invisible |
| `SingleLevelGeneral_v1.lean` | 3 | the BS pigeonhole off a prime modulus, + a falsity witness at `ZMod 8` |
| `ExactBlock_v1.lean` | 4 | only colliding disparities block exactly; near blocks need `c > 8` |
| `DminClearance_v1.lean` | 7 | the `d_min` criterion, `S ≤ n−1` corollary, **general `n`** |

---

## 1. Consequences drawn *by* this exercise

### 1.1 The `d_min` criterion is a general-`n` theorem — the `8` was never used

Nothing in `bad_iff` uses the value `8`. `bad_iff_gen` and `clear_of_reading_le_gen` are the
arbitrary-order versions, and the constant is `n − 1`:

> **At any order `n`, a subject clears at its own `d_min` whenever `S ≤ n − 1`** — and exactly when
> every disparity satisfies `c ≤ a mod nc ≤ (n−1)c`.

At `n = 8` the constant is `7`, which is Theorem 4.8's. **So Theorem 4.8's constant is not special to
order 8**; it is "one below the first multiple of `n`", at every order. This was sitting in the
proof and I wrote the `n = 8` case without noticing.

### 1.2 `near_block_host_large` × `clear_iff`: small hosts force coincidence

At scale `d_min` the host is `c = d_min/g`, so `N = 0`. A colliding disparity `a = 8b` fails there
iff `b mod c` is in an end zone, and `near_block_host_large` says a *near* failure needs `c > 8`.
Hence:

> **If `d_min/g ≤ 8`, every colliding failure at `d_min` is exact** — the disparity is an exact
> multiple of `8·d_min` and that runner is exactly *on* the subject.

Measured: **zero violations** over 6,578 colliding failures (of which 6,460 exact). Neither theorem
says this alone; it is the product.

---

## 2. A refactor this makes available — **proposed, not done**

`recovers_n7` proves the existing `IntLRC7BS.single_level_avoid` is the `N = 7` instance of
`single_level_avoid_general`. So the n=7 tree's copy could be replaced by the general lemma, which
would **isolate that proof's use of primality to a single `IsUnit ↔ ≠ 0` step** — making explicit,
in the verified tree, exactly where order 7 and order 8 part company.

**Not done, and it should not be done casually.** It edits a complete, axiom-clean tree whose
done-check is `scripts/n7/gate.sh`, and the benefit is expository rather than mathematical. The
owner's call.

---

## 3. Interactions checked for conflict — none found

| pair | relation |
|---|---|
| `clear_iff` vs `spine_all_or_nothing` | different scales (`d_min` vs `g`); they **coincide exactly when `c = 1`**, which is why the parallel session's theorem is the `d_min = g` case |
| `clear_of_reading_le_seven` vs Theorem 4.8 | not a conflict — §1.1 shows 4.8's constant is a corollary of the residue band |
| the cage vs Theorem 4.8 | disjoint: the cage is about grid instants, 4.8 about the clear band |
| `single_level_avoid_false_at_8` vs the n=7 tree | none — it refutes a statement at `ZMod 8` that nothing asserts |
| `dmin_always_clear` vs the cascade's start | supports it: the cascade starts at `1/(8·d_min)` and `d_min` provably never blocks there, so step 0 is well defined |

---

## 4. Not thought through — named

1. **The k=1 rung.** `clear_iff` characterises depth 0 (**53.4%**). Depth 1 adds **21.7%**, reaching
   75.1%. The move after a failure is forced once the blockers are known, so a k=1 criterion exists
   in closed form; whether it reduces to a residue band like k=0 is open. **This is the most
   valuable unexplored consequence.**
2. **Does `slot_gcd` (general `n`) simplify anything in the n=7 tree?** BS state eq. (2) only for
   prime powers. Not investigated.
3. **Does the cage improve Localisation's bound?** Localisation bounds every blocker's next opening;
   the cage gives offsets 2, 4, 6 a slack of `1/4` or `1/2`. Only at grid instants, so probably not —
   but not checked.
4. **Does `clear_of_reading_le_gen` say anything at orders already closed** (`n = 3,4,5,6,7`)? It is
   a general-`n` statement now, so it applies there; whether it is new or a restatement of something
   in those proofs is unchecked.
5. **The 6-failure ceiling** bounds the first move to a max over ≤ 6 blockers. No consequence drawn.

## 5. What none of this establishes

No proof at order 8. §1.1 is a generalisation of a criterion for cascade *entry*, not for Existence;
§1.2 describes how colliding disparities fail, not how deep. The depth figures in §4.1 are from one
sampler (speeds `1..89`, 24,000 subjects). The firewall question in `BS_TRANSFER_v1` §4 is still
open and nothing here depends on it.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/DminClearance_v1.lean   # 7 thms incl. general n
python3 experiments/n8/interactions_v1.py    # zero violations; the depth stratification
```
