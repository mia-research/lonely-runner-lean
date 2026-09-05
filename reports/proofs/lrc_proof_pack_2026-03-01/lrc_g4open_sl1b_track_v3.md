# G4.OPEN SL-1.B Track Note (v3)
Date: 2026-03-04
Scope: Near-complete one-divisible Case-2, Case-iiib branch (composite n).

## 1. Reduced objective
To close Case-iiib we need `exists b in B_div` with `U_fix(tau(b)) != Z_n`.
In alpha-space (`alpha=b/L`) this is equivalent to proving:

- `exists r in Z_n` with `Miss(r) != empty`,
  where `Miss(r) = I_div \ union_e Cov_e(r)` and `I_div=[1/n,(n-1)/n]`.

## 2. What is now theorem-grade proved

### P1. Rational endpoint control (PROVED)
For each `e`, each coverage interval endpoint is `t/e`. Therefore every endpoint of every miss interval is rational with denominator `<= e_max <= n`.

### P2. Farey gap lower bound conditional on existence (PROVED)
Let `N=e_max`. If a miss component is non-empty and interior, its endpoints are two distinct Farey-order-`N` rationals. Any two distinct Farey-order-`N` rationals differ by at least `1/(N(N-1))`. Hence:

`nonempty interior Miss(r) => max_component_length(Miss(r)) >= 1/(e_max*(e_max-1))`.

So the quantitative bound in SL-1.B does not require a separate hard proof once existence is known.

### P3. Integer b-lift from alpha interval (PROVED)
If a miss interval has length `ell>0`, then for `L=L0*M` the integer count
`#{b: b/L in interval} >= floor(L*ell)-1`.
In particular for sufficiently large M this is positive; in tested templates it is already positive at `M=1`.

### P4. Auxiliary interval lemmas for `r=1` (PROVED)
The following support facts are now packaged separately:
- for unit `e`, residue `1` is coverable only if `e >= ceil(n/2)`,
- for active unit `e`, `Cov_e(1)` is a single contiguous interval in `alpha`.

Artifact:
- `lrc_g4open_caseb_interval_lemmas_v1.md`

### P5. `alpha=1/a` unit-side separation observation (PROVED)
If dropped `a` is non-unit, then `alpha=1/a` is a floor-change point of `a` but not of any unit runner.
So the unit-side coverage union is locally constant across `alpha=1/a`.

Artifact:
- `lrc_g4open_alpha1_over_a_observation_v1.md`

## 3. What remains open

### O1. Existence-only lemma (single blocker)
Prove:
`exists r with Miss(r) != empty` in Case-iiib.

Once O1 is proved, P2 gives the exact lower bound
`>=1/(e_max*(e_max-1))` automatically.

Recent failed closure attempt:
- `lrc_g4ot_blocker_memo_v1.md`
- key lesson: the repair must stay in fixed-side `Miss(r)` / `U_fix(tau)` language and must not use dropped-runner coverage as if it were part of `U_fix`.
- additional lesson: `alpha=1/a` freezes only the unit side, not the full fixed-side union.

## 4. Extended empirical support (reproducible)
Probe artifact: `lrc_sl1b_extended_probe_v1.py` (composite n=10..30).

- Case-iiib templates checked: 694
- Existence failures (`best_miss=0`): 0
- Bound failures (`best_miss < 1/(e_max*(e_max-1))`): 0
- Denominator failures (`den>n`): 0
- Best miss touching boundary of `I_div`: 0
- Zero integer witness at `M=1`: 0

Extremal ratio row:
- n=14, dropped=(6,10), best_r=4,
- best_miss=8/91, bound=1/156, ratio=13.714285...

## 5. Immediate theorem strategy
Reframe SL-1.B as:

1. **Existence lemma (O1):** prove at least one uncovered residue over an interior alpha interval.
2. **Apply P2:** convert existence to explicit lower bound `1/(e_max*(e_max-1))`.
3. **Apply P3:** convert interval to integer witness in B_div.
4. Conclude Case-iiib `=> Lambda_eff>0`.

This isolates the last analytic obstruction to a single existence statement, rather than a joint existence+quantitative bound.
