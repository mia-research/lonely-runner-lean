# Cross-checks of the parallel session (v2)

Supersedes `FILTER_ASSESSMENT_AND_CROSSCHECK_v1.md` (retained). Parts A and B of v1 are unchanged
and still stand; this version adds **Part E**, the colliding-pair analysis, which arrived later.

- **Part A** — the instant-variance filter is a screen, not a route. Unchanged; see v1.
- **Part B** — their sweep: (A) confirmed, (B) forced by the `v ≤ 16` cap (true bound 7, not 3),
  (C) proposed Lean `Iff` false in both directions. Unchanged; see v1.
- **Part E** — colliding-pair Diophantine analysis. Below.

---

## Part E — the colliding-pair analysis

### E.1 The algebra is correct

For a colliding pair, `u_j ≡ u_i (mod 8)`, so `d = 8bg`. Both restatements were checked
symbolically on 2000 random instances (`colliding_blocking_v1.py`):

```
  Case 1:  |d/e − 8M/(8k+1)| < 1/(8k+1)      ⟺  |bg/e − M/(8k+1)| < 1/(8(8k+1))    2000/2000
  Case 2:  |d/(8bg) − 8M/(8k+1)| < 1/(8k+1)  ⟺  |u_d − 64bM/(8k+1)| < 8b/(8k+1)    2000/2000
```

Both derivations are right, and `d = 8bg` for a colliding pair is right.

### E.2 The inferences do not follow

Each restatement divides (or multiplies) **both sides of one inequality** by the same positive
quantity. That cannot change which `(M, k)` satisfy it — which is what the `2000/2000` above
records. So:

- **Case 1's "8× window shrinking → sparse blocking"** does not follow. The tolerance went from
  `1/(8k+1)` to `1/(8(8k+1))`, but the left-hand quantity shrank by the same factor of 8.
- **Case 2's "mod 64 grid alignment → fast exit"** does not follow. The `64 = 8²` appears only
  because both sides were multiplied by `8bg`; in those units the tolerance is `8b/(8k+1)`, which
  is `8b` times *wider*, not tighter.

**This is a move already recorded on this project.** `experiments/n8/Bridge_v1.lean`'s docstring
notes that multiplying the same inequality through by `(8k+1)` yields `|numerator − 8M| < 1` — a
congruence, with the approximation quality `1/q` free, i.e. no Diophantine content. Same rescaling,
same absence of content.

### E.3 The empirical consequences run the other way

If "sparse blocking" and "fast exit" were real they would be visible. Measured over 1500
arrangements × 8 subjects (12,000 subjects, speeds `1..89`):

```
  colliding disparities that ever block :  2984/9624   (0.3101)
  non-colliding that ever block         : 11197/74376  (0.1505)

  subjects WITH a colliding disparity   : n=7060  mean depth 1.053  max 10
  subjects WITHOUT                      : n=4940  mean depth 0.687  max  8
```

**A colliding disparity blocks about twice as often as a non-colliding one**, and subjects carrying
one take *more* cascade moves, not fewer. Both are the reverse of the stated conclusions.

On their reported "mean 2.41 moves": that is a different sampler and is not contradicted here — my
mean is 1.053 on mine. What fails is the **comparative** claim that colliding runners "consistently
resolve within very few candidate steps": on this sampler they resolve in more steps than subjects
with no collision. `[EMPIRICAL — conditional]`, bound to this sampler.

### E.4 Thesis versus mechanism

Refuting these two inferences says nothing about whether colliding pairs are the right object to
study. They plainly are — the residue partition (their own claim (A), confirmed in v1 Part B) makes
collision the exact criterion for needing the cascade at all, and E.3's numbers show collision is
the stronger predictor of blocking, just with the opposite sign to the one claimed. The direction is
sound; these two arguments for it are not.

```bash
python3 experiments/n8/colliding_blocking_v1.py
```
