# What makes the orbit predictable — and the reason a bound is not on offer

With the move in closed form (`MOVE_RULE_v1`), the cascade is a one-dimensional deterministic map,
so "is the orbit predictable" splits into three questions with three different answers.

---

## 1. The trajectory: **fully predictable** — it is a closed form

Setting `x = t`, clearance is `‖a·x‖ ≥ 1/8` for every reduced disparity, so the cascade is a
rightward walk through overlapping bad intervals. Given the reading profile `(1, s₂, …, s₇)` the
entire orbit is computable without simulation:

```
  clear test   e ≤ a(8N+1) mod 8e ≤ 7e              clear_at_scale_iff
  blockers     |s_a − 8M_a| < 1,  M_a = round(s_a/8)
  dilation     λ = max over blockers (8M_a+1)/s_a    move_lap
  next scale   D' = a·g/(8M_a+1)
```

`[PROVED]` + verified 46,353/46,353 (clearance) and 18,286/18,286 (move).

## 2. The length: a **law**, but it is a consistency relation, not a predictor

Depth is the number of bad intervals crossed. Disparity `a` contributes one per `1/a` of `t`, so
over a walk of length `t_final − t₀ = (R−1)/(8·d_min)`:

> **depth ≈ (R − 1) · Σ / 8**, with `Σ = Σ dᵢ/d_min`, divided by the overlap factor

Measured: correlation **0.860** with depth; `pred/depth` converges to ≈1.3 against a measured
**1.371 blockers per step**, which is exactly the overlap. The law is sound.

**But `R` is an output.** The law says *depth = travel distance × obstacle density*. Predicting the
travel distance is predicting where the isolation is.

## 3. From inputs alone: **nothing predicts it**, and the correlations are near zero

```
  spread_ratio  Σ/S    +0.1481
  Σ                    +0.1106
  S                    +0.0867
  n_block0             −0.0542        n = 9252, depth ≥ 1
```

And max depth does **not** grow with spread under random sampling:

```
  S cap      8    10    15    20    30    50   100   300
  max depth  9     8    12    13    10    10    10     9
  max R    3.68  3.15  4.29  4.61  3.55  2.92  2.79  3.06
```

Flat. The deep cases on file — 23 and 28 moves, `R = 11.96` — were all found by *adversarial
search*, never by sampling. (This does not contradict the recorded "k bounded given S": that figure
is the **minimum** `k`, a different quantity from cascade depth.)

---

## 4. Why — and this is already a theorem in the tree, not a conjecture of mine

`LRC/Spec/Target.lean` defines

```lean
def CascadeCapped : Prop :=
  ∀ ds, … ∃ U : ℝ, ∀ N : ℕ, (move 8 ds)^[N] (1 / (8 * m)) ≤ U
```

and proves **both directions**: `existence_of_capped : CascadeCapped → ExistenceAt8` and
`capped_of_existence : ExistenceAt8 → CascadeCapped`. The file states it plainly — *"a uniform cap
on the cascade's instants is all that is missing."*

> **A uniform bound on the cascade is equivalent to Existence.**

So the search for a depth predictor is not a side quest that might pay off; **it is the open problem
wearing different clothes.** Every negative in §3, and the earlier ones — `π` does not determine
depth, `q` does not, the two arms sat on the forced floor of 0.3758 — are consequences of this. A
feature that predicted depth uniformly *would be* the proof.

This is worth stating because it is a genuine scope result: it converts "we have not found a
predictor yet" into "finding one is the whole task", and it retires that line as an investigation
separate from the proof.

## 5. What is therefore still worth doing

The equivalence is with a **uniform** cap. It says nothing against:

* **conditional bounds** — a cap on a restricted class (e.g. `S ≤ 7` is already `depth = 0`, proved);
  a chain of such classes covering everything would compose to the cap;
* **the stratification** — `k=0` covers 53.0%, `k≤1` 74.8%, `k≤2` 88.0%, `k≤3` 95.0%, `k≤4` 97.7%;
  each rung is the same residue-band test at the rung's `(e, N)`. A closed form for the rung-`k`
  region would be a partial result of the right shape;
* **adversarial search** — the deep cases are reachable only that way, so the empirical frontier for
  large depth is a search problem, not a sampling one.

## 6. What this does not establish

No proof at order 8. §2's law is empirical (correlation 0.860, one sampler, 20,000 subjects) and
§3's flatness is a statement about *random sampling*, not about the true maximum — the adversarial
cases already exceed it. §4 is a reading of theorems already in the tree, not a new result.

```bash
python3 experiments/n8/orbit_law_v1.py    # the depth law, correlation 0.860
python3 experiments/n8/orbit_law_v2.py    # input features; S-cap flatness
sed -n '100,140p' LonelyRunner/LonelyRunner/LRC/Spec/Target.lean   # the equivalence
```
