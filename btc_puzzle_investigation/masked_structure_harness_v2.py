#!/usr/bin/env python3
"""
masked_structure_harness_v2.py  —  v1 + an OPT-IN kfold_gate on the SET verdicts.

Same F / A / D / G statistics and the same exact (int / Fraction) signal path as
masked_structure_harness_v1.  The one addition: the SET verdicts in A and G can be
routed through kfold_gate_v1.KFoldGate, which emits a claim only if the effect
replicates in BOTH deterministic SHA-256 hash-folds.

  *** Gating is BY ACTIVE CHOICE, not always on. ***
  Default run = the pooled verdict (v1 behaviour).  Pass --gate (or gate=True) to
  apply the both-folds discipline.  The gate is meant as a deliberate act at the
  moment you are about to NAME a finding — not a permanent power-halving filter on
  every exploratory pass, and not a rubber stamp to stop thinking about.

Why the gate exists (masked_structure_findings_v35): the "A==0" pattern scored a
pooled p=0.002 and then died out-of-sample.  kfold_gate_demo_Azero_v1.py reproduces
that on real data and shows a 2-fold hash split suppresses it (fold0 2/12 p=0.21,
fold1 6/15 p=0.001).  A RANGE split (the old manual guard) confounds fold with
prime magnitude; the hash split does not.

  F  (reused from v1, unchanged) — an EXACT structural anchor, no verdict to gate.
  A  cubic-moment E[z^3] SET tests — pooled by default; --gate adds the two-sided
     matched-null both-folds rule.  Control ("random-82") should stay null.
  D  (reused from v1, unchanged) — exact orientation read, no matched-null verdict.
  G  82-solved-key single-shot chi_k-vs-(d mod k) MI — pooled by default; --gate
     adds the perm-p both-folds rule.  Orbit SCALING-trend verdicts stay in v1
     (they carry their own across-M replication logic).

Gate operating point when ON: alpha=0.01, K=2.  alpha=0.05 was shown to let a
known artifact through ~30% of splits at N=27, so 0.01 is the default (see demo).

Run: python masked_structure_harness_v2.py            # pooled (gate off)
     python masked_structure_harness_v2.py --gate     # both-folds discipline on
     python -c "import masked_structure_harness_v2 as m; m.section_A(gate=True)"
"""
import sys
import random
from fractions import Fraction

import numpy as np

import masked_structure_harness_v1 as v1
from kfold_gate_v1 import KFoldGate

POOLED_ALPHA = Fraction(1, 20)          # 0.05 two-sided, for the ungated pooled flag (v1 parity)


# ------------------------------------------------------------ gate plumbing
def _two_sided_hits(stat, nulls):
    """Integer two-sided matched-null count: 2*min(#null<=stat, #null>=stat),
    capped at len(nulls).  Small => the observed stat sits in a tail."""
    below = sum(1 for v in nulls if v <= stat)
    above = sum(1 for v in nulls if v >= stat)
    return min(2 * min(below, above), len(nulls)), len(nulls)


def _flag(hits, trials, alpha):
    return hits * alpha.denominator <= alpha.numerator * trials


def _gate_line(res):
    for fo in res.folds:
        role = "disc" if fo.fold == 0 else "val "
        pv = " n/a " if fo.trials == 0 else f"{fo.pvalue:.3f}"  # noqa: float (display)
        print(f"       fold{fo.fold}[{role}] N={fo.n_items:5d} p={pv:>6} "
              f"({fo.hits}/{fo.trials}) {'PASS' if fo.passed else 'fail'}")


# =====================================================================  A
def section_A(gate=False, alpha="0.01", gate_seed=7, N_POOL=6000, B=2000, seed=17):
    print("\n" + "=" * 74)
    tag = "GATE ON (both hash-folds)" if gate else "pooled (gate off)"
    print(f"[A] mu_3-invariant cubic moment E[z^3]   —   {tag}")
    print("=" * 74)
    if gate:
        print(f"  a set prints ANOMALY only if its two-sided matched-null rank clears")
        print(f"  alpha={alpha} in BOTH SHA-256 folds; 'random-82' control should be null.")

    eis_secp, _ = v1.build_secp()
    rng = random.Random(seed)

    print(f"  building random-curve-point pool (M={N_POOL}) ...")
    pool = []
    while len(pool) < N_POOL:
        d = rng.randrange(1, v1.N_ORDER)
        xy = v1.scalar_mul(d)
        if xy:
            pool.append(xy[0])
    cube = [v1.ecube(eis_secp(x)) for x in pool]
    mua = Fraction(sum(c[0] for c in cube), N_POOL)
    mub = Fraction(sum(c[1] for c in cube), N_POOL)

    def stat_of(clist):
        n = len(clist)
        da = Fraction(sum(t[0] for t in clist), n) - mua
        db = Fraction(sum(t[1] for t in clist), n) - mub
        return float(v1.enorm_frac(da, db))                  # noqa: float (ranked statistic)

    def cubes_of(xs):
        return [v1.ecube(eis_secp(x)) for x in xs]

    def null_draws(n):
        return [stat_of([cube[i] for i in rng.choices(range(N_POOL), k=n)]) for _ in range(B)]

    def report(name, xs):
        xs = list(xs)
        st = stat_of(cubes_of(xs))
        h_pool, _ = _two_sided_hits(st, null_draws(len(xs)))
        pooled_tail = _flag(h_pool, B, POOLED_ALPHA)
        if not gate:
            verdict = "ANOMALY (pooled)" if pooled_tail else "null (pooled)"
            print(f"\n  {name:24} N={len(xs):5d}  2sided-p={h_pool / B:.3f}  => {verdict}")  # noqa: float
            return

        def per_fold(f, sub):
            return _two_sided_hits(stat_of(cubes_of(sub)), null_draws(len(sub)))

        res = KFoldGate(alpha, 2, gate_seed).run(xs, per_fold)
        verdict = "ANOMALY (replicated)" if res.emit else "null (gated)"
        print(f"\n  {name:24} N={len(xs):5d}  pooled 2sided-p={h_pool / B:.3f}"  # noqa: float
              f"  => {verdict}")
        _gate_line(res)

    report("[ctrl] random-82", [pool[i] for i in rng.sample(range(N_POOL), 82)])
    orb = v1.orbit_x(40000)
    report("generator orbit (N=82)", orb[:82])
    _d82, x82 = v1.load_82()
    report("82 solved keys SET", x82)


# =====================================================================  G
def section_G(gate=False, alpha="0.01", gate_seed=7, B=2000):
    print("\n" + "=" * 74)
    tag = "GATE ON (both hash-folds)" if gate else "pooled (gate off)"
    print(f"[G] chi_k(x[dG]) vs d mod k on the 82 solved keys   —   {tag}")
    print("=" * 74)
    if gate:
        print(f"  SIGNAL only if perm-p <= alpha={alpha} in BOTH SHA-256 folds of the 82.")

    chi = {k: v1.make_chik(v1.SECP_P, k) for k in (2, 3, 6)}
    d82, x82 = v1.load_82()
    keys = list(zip(x82, d82))

    def feats(sub, k):
        f = np.array([chi[k](x) if chi[k](x) is not None else 0 for x, _ in sub], dtype=np.int64)
        t = np.array([d % k for _, d in sub], dtype=np.int64)
        return f, t

    for k in (2, 3, 6):
        f0, t0 = feats(keys, k)
        raw0 = v1.mi_bits(f0, t0)
        g = np.random.default_rng(999)
        nl0 = np.array([v1.mi_bits(f0, t0[g.permutation(len(t0))]) for _ in range(B)])
        pooled_hits = int((nl0 >= raw0).sum())
        pooled_p = pooled_hits / B                            # noqa: float (display)

        if not gate:
            verdict = "signal? (pooled)" if _flag(pooled_hits, B, POOLED_ALPHA) else "null (pooled)"
            print(f"\n  chi_{k} vs d%{k}:  MI={raw0:.4f} bits  perm-p={pooled_p:.3f}  => {verdict}")
            continue

        def per_fold(fidx, sub, k=k):
            f, t = feats(sub, k)
            raw = v1.mi_bits(f, t)
            gp = np.random.default_rng(4242 + fidx)
            nulls = np.array([v1.mi_bits(f, t[gp.permutation(len(t))]) for _ in range(B)])
            return int((nulls >= raw).sum()), B

        res = KFoldGate(alpha, 2, gate_seed).run(keys, per_fold)
        verdict = "SIGNAL (replicated)" if res.emit else "null (gated)"
        print(f"\n  chi_{k} vs d%{k}:  pooled MI={raw0:.4f} bits  perm-p={pooled_p:.3f}"
              f"  => {verdict}")
        _gate_line(res)


# =====================================================================  main
def main(gate=False):
    mode = "GATE ON" if gate else "pooled (pass --gate to enable the both-folds gate)"
    print(f"MASKED-STRUCTURE HARNESS v2  —  F / A / D / G   [{mode}]")
    p = 100003
    eis100, eps100 = v1.build(p)
    v1.section_F(p, eis100, eps100)
    section_A(gate=gate)
    eis_secp, eps_secp = v1.build_secp()
    v1.section_D([103, 1009, 10009], p, eis100, eps100, eis_secp, eps_secp)
    section_G(gate=gate)
    print("\nDONE.")


if __name__ == "__main__":
    main(gate="--gate" in sys.argv[1:])
