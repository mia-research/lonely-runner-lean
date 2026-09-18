# The move, in closed form — and a correction about "deterministic"

Answers the two questions left open in `FIVE_ITEMS_v1`.

---

## 1. Which `(e, N)` does the move land on?

**A deterministic argmin, with a closed form.**

At scale `D = e·g/(8N+1)`, disparity `a·g` has reading `s_a = a(8N+1)/e`, and `d·t = s_a/8`.
Blocking is `|s_a − 8M_a| < 1` with `M_a = round(s_a/8)`. The step that makes it closed:

> **`MoveRule.move_lap`** — the next opening's lap is *exactly* `M_a`. `M` is the least `k` with
> `(8k+1)e ≥ a(8N+1)`, so there is no rounding decision: the move's lap is the `M` the blocking
> condition already names.

Hence blocker `a` offers the candidate scale `a·g/(8M_a+1)`, and

```
    D'  =  D · min over blockers of  s_a/(8M_a + 1)
    λ   =  D/D'  =  max over blockers of  (8M_a + 1)/s_a
```

**Verified: 18,286 / 18,286 moves** match on the scale, and `λ = (8M+1)/s` matches 18,286/18,286.
(Three moves name a *different* blocker — ties yielding the identical scale — so the rule is exact
on the scale, which is what the recursion consumes.)

### 1.1 The recursion is now fully explicit

```
  readings     s_a = a(8N+1)/e
  blockers     |s_a − 8M_a| < 1,   M_a = round(s_a/8)
  clear test   e ≤ a(8N+1) mod 8e ≤ 7e          (clear_at_scale_iff)
  dilation     λ = max over blockers (8M_a+1)/s_a
  next scale   D' = D/λ = a·g/(8M_a+1)          for the winning a
```

No step without a closed form. Checking their 23-step trace against it: step 0 has `D = 30`, setter
`224`, `M = 1`, reading `s = 224/30 = 7.4667`, so `λ = 9/7.4667 = 1.2054` — their recorded
`1.205357`.

### 1.2 Two consequences

* **The cascade never leaves the candidate-scale family.** `a·g/(8M_a+1)` is exactly
  `Cascade.candidateScale 8 (a·g) M_a`, so every scale it visits is one, with `k = M_a`.
* **"Smallest lap wins" is a heuristic, not a theorem.** The ratio is `(8M+δ)/(8M+1)` with
  `δ = s − 8M ∈ (−1,1)`, increasing in both `M` and `δ`. So a later-lap blocker sitting far enough
  *below* its multiple beats an earlier one sitting above. It holds **97.3%**, and the failures have
  the winner at median `δ = −0.50` — below its multiple, as the algebra says.

---

## 2. "What is deterministic for the rest?" — the premise was mine and it was loose

I wrote that the first move is "deterministic for ~65% of failing subjects". **That was the wrong
word.** The move was always deterministic — it is `max` over a finite explicit set, with no choice
anywhere. What the 65% figure actually measured is that in those cases the max is over a *single*
candidate, so no comparison is needed.

So the answer is: **the move is deterministic for 100%**, and §1 now gives the rule that decides it
in every case, single blocker or not. The remaining distinction between the classes is only how many
candidates the argmin ranges over — at most `n−2 = 6`, since `d_min` never blocks
(`DminClearance.dmin_always_clear`).

This also retires the hope recorded in `FIVE_ITEMS_v1` item 5: single-failure subjects clear at
depth 1 in 0.4620 versus 0.4833 for multi-failure. There was never a determinism gap for that to
exploit.

---

## 3. What this does not do

It explains the *recursion*, not its *length*. The cascade is now a closed-form iteration, but
nothing here bounds how many steps it takes — depth remains determined by neither `π` nor `q`
(`NEIGHBOUR_DEFORMATION_v2` §6), and a closed-form step does not make the orbit predictable. It says
nothing about Existence.

`MoveRule_v1.lean`: 2 theorems, zero `sorry`, axiom-clean. Session total: 25.

```bash
cd LonelyRunner && lake env lean ../experiments/n8/MoveRule_v1.lean
python3 experiments/n8/move_rule_v1.py    # claims 1-5; dilation exact
python3 experiments/n8/move_rule_v2.py    # 18,286/18,286 on the scale; the 3 ties
```
