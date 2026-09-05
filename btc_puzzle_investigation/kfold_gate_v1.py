#!/usr/bin/env python3
"""
kfold_gate_v1.py — deterministic hash-partitioned discovery/validation GATE.

WHY THIS EXISTS.
  masked_structure_findings_v35 recorded the THIRD chance-pattern this arc killed
  only by an out-of-sample retest: "A == 0 on the curve" looked enriched in-sample
  (8/27, matched-null p=0.002) and then died out-of-sample (1 vs 1.07, p=0.66).
  The manual guard (_A_zero_matched_null_v1.py) split by a RANGE boundary
  ([100,9000) discovery, [9000,16000) validation) and left the two-number
  comparison to a human eye.

  Two structural weaknesses this gate removes:
    (1) A RANGE split confounds the fold with prime MAGNITUDE. Small vs large
        primes differ in class number, NE-parity balance, flap size, etc., so a
        magnitude-dependent artifact can look reproducible, and a genuine
        structural law can look fold-dependent. A hash split is magnitude-blind:
        the two folds are drawn from the SAME prime-size distribution.
    (2) The gate was advisory. Here a candidate claim is EMITTED only if it clears
        the pre-registered threshold INDEPENDENTLY in every fold; otherwise it is
        SUPPRESSED and the offending fold is named. This is the enforced form of
        the binding anomaly-drill rule "retest out-of-sample before naming a zero."

WHAT THIS PROVIDES (import these into any exploratory script).
    fold_of(item, seed, K)              -> int in [0,K)
        SHA-256 of "seed:repr(item)", deterministic across processes and machines.
        NEVER builtin hash(): it is per-process salted, so folds would not
        reproduce. Balanced in magnitude by construction (split is on the digest).
    KFoldGate(alpha, K, seed).run(items, per_fold_pvalue) -> GateResult
        per_fold_pvalue(fold_index, sub_items) -> (hits:int, trials:int)
            an INTEGER permutation/matched-null count for that fold's items alone.
        GateResult.emit == every fold passed  (empty folds count as NOT passed:
            you cannot validate a claim on zero evidence).

EXACTNESS (btc_puzzle_investigation/CLAUDE.md — no float in the signal path).
  alpha is a Fraction. The per-fold verdict is the integer cross-product
      hits/trials <= alpha   <=>   hits*alpha.denominator <= alpha.numerator*trials
  — no float threshold ever touches the data. Floats appear only in the printed
  p-value column, ranked for display, never deciding a verdict.

Run `python kfold_gate_v1.py` to execute the self-test (positive + negative
controls). It exits 0 iff the gate EMITs a planted signal and SUPPRESSES a
planted null — including the case where one fold gets lucky and dips below alpha
while the other does not (the v35 A==0 situation in miniature).
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Callable, Sequence


# --------------------------------------------------------------- fold assignment
def fold_of(item: Any, seed: int = 0, K: int = 2) -> int:
    """Deterministic fold in [0, K) via SHA-256 of 'seed:repr(item)'.

    Stable across runs and machines. builtin hash() is salted per process and
    MUST NOT be used for a discovery/validation split.
    """
    if K < 2:
        raise ValueError(f"K must be >= 2 (got {K})")
    digest = hashlib.sha256(f"{seed}:{item!r}".encode()).hexdigest()
    return int(digest, 16) % K


def _as_fraction(alpha: Any) -> Fraction:
    """Coerce a threshold to an EXACT Fraction. A float like 0.05 is routed
    through its decimal string so it becomes 1/20, not the binary double."""
    if isinstance(alpha, Fraction):
        return alpha
    if isinstance(alpha, int):
        return Fraction(alpha, 1)
    if isinstance(alpha, str):
        return Fraction(alpha)
    if isinstance(alpha, float):
        return Fraction(str(alpha))            # 0.05 -> Fraction("0.05") == 1/20
    raise TypeError(f"alpha must be Fraction/int/str/float, got {type(alpha)}")


def _passes(hits: int, trials: int, alpha: Fraction) -> bool:
    """Exact test  hits/trials <= alpha  with no division. trials==0 never passes."""
    if trials <= 0:
        return False
    return hits * alpha.denominator <= alpha.numerator * trials


# ------------------------------------------------------------------- result types
@dataclass
class FoldOutcome:
    fold: int
    n_items: int
    hits: int
    trials: int
    passed: bool

    @property
    def pvalue(self) -> float:                 # display only (ranked, never a data threshold)
        return self.hits / self.trials if self.trials else float("nan")  # noqa: float


@dataclass
class GateResult:
    alpha: Fraction
    K: int
    seed: int
    folds: list[FoldOutcome]
    emit: bool
    fold_sizes: list[int] = field(default_factory=list)

    @property
    def empty_folds(self) -> list[int]:
        return [fo.fold for fo in self.folds if fo.n_items == 0]

    def render(self) -> str:
        lines = []
        lines.append(
            f"  GATE  alpha={self.alpha} (~{float(self.alpha):.4g})  K={self.K}  "  # noqa: float
            f"seed={self.seed}"
        )
        for fo in self.folds:
            role = "discovery" if fo.fold == 0 else ("validation" if fo.fold == 1 else f"fold{fo.fold}")
            verdict = "PASS" if fo.passed else "fail"
            pv = "  n/a  " if fo.trials == 0 else f"{fo.pvalue:.4g}"  # noqa: float
            lines.append(
                f"    fold {fo.fold} [{role:10}]  N={fo.n_items:5d}  "
                f"p={pv:>8}  ({fo.hits}/{fo.trials})  => {verdict}"
            )
        if self.emit:
            lines.append("  => EMIT: candidate cleared the threshold in EVERY fold.")
        else:
            failed = [fo.fold for fo in self.folds if not fo.passed]
            empt = self.empty_folds
            passed = [fo.fold for fo in self.folds if fo.passed]
            msg = f"  => SUPPRESS: fold(s) {failed} did not clear the threshold"
            if passed:
                msg += f" (fold(s) {passed} did — a single-fold hit is NOT a claim)"
            if empt:
                msg += f"; fold(s) {empt} were empty (no evidence)"
            lines.append(msg + ".")
        return "\n".join(lines)


# ------------------------------------------------------------------------- the gate
class KFoldGate:
    """Emit a candidate only if it clears `alpha` independently in every fold."""

    def __init__(self, alpha: Any = "0.01", K: int = 2, seed: int = 0):
        self.alpha = _as_fraction(alpha)
        if not (0 < self.alpha <= 1):
            raise ValueError(f"alpha must be in (0,1], got {self.alpha}")
        self.K = K
        self.seed = seed

    def partition(self, items: Sequence[Any]) -> list[list[Any]]:
        buckets: list[list[Any]] = [[] for _ in range(self.K)]
        for it in items:
            buckets[fold_of(it, self.seed, self.K)].append(it)
        return buckets

    def run(
        self,
        items: Sequence[Any],
        per_fold_pvalue: Callable[[int, list[Any]], tuple[int, int]],
    ) -> GateResult:
        """`per_fold_pvalue(fold_index, sub_items) -> (hits, trials)` is the
        INTEGER count of null draws at least as extreme as observed, over `trials`
        matched/permutation draws, run on that fold's items ALONE."""
        buckets = self.partition(items)
        outcomes: list[FoldOutcome] = []
        for f, sub in enumerate(buckets):
            if sub:
                hits, trials = per_fold_pvalue(f, sub)
                hits, trials = int(hits), int(trials)
            else:
                hits, trials = 0, 0
            outcomes.append(FoldOutcome(f, len(sub), hits, trials, _passes(hits, trials, self.alpha)))
        emit = all(fo.passed for fo in outcomes)
        return GateResult(self.alpha, self.K, self.seed, outcomes, emit,
                          fold_sizes=[len(b) for b in buckets])


# ================================================================== self-test ====
# The gate's job is one thing: EMIT a planted signal, SUPPRESS a planted null —
# including when one fold gets lucky. Both controls must behave or the gate is
# broken (assert -> nonzero exit).

def _matched_null_zero_rate(pm1_values, B: int, seed: int) -> tuple[int, int]:
    """Realistic matched null mirroring _A_zero_matched_null_v1.matched_null:
    for a set of +-1 orbit values, how often does a resampled fair sign assignment
    give sum == 0? Returns (hits_at_least_as_extreme, trials) where 'extreme' =
    the SUM being exactly 0 (the 'A == 0' event). Integer counts only."""
    import random
    rng = random.Random(seed)
    k = len(pm1_values)
    hits = 0
    for _ in range(B):
        # exact fair coin: getrandbits(1) is an int 0/1, no float threshold
        s = sum(1 if rng.getrandbits(1) else -1 for _ in range(k))
        if s == 0:
            hits += 1
    return hits, B


def _zero_enrichment_pvalue(items, seed_base: int) -> tuple[int, int]:
    """Candidate statistic: are observed A==0 events enriched vs the matched null?
    `items` are (label, pm1_list). Observed = # lists summing to 0. Null hits = the
    number of matched-null draws (pooled over items) with >= observed zeros, via a
    Poisson-free direct resample. Returns (hits, trials) as integer counts."""
    import random
    observed = sum(1 for _, vals in items if sum(vals) == 0)
    B = 4000
    rng = random.Random(seed_base ^ 0x5bd1e995)
    # pooled matched null: each draw reassigns fair signs to every item, counts zeros
    hits = 0
    per_item = [len(vals) for _, vals in items]
    for _ in range(B):
        z = 0
        for k in per_item:
            if sum(1 if rng.getrandbits(1) else -1 for _ in range(k)) == 0:
                z += 1
        if z >= observed:
            hits += 1
    return hits, B


def selftest() -> bool:
    import random
    print("kfold_gate_v1 self-test")
    print("=" * 74)

    ok = True

    # -- pure gate-logic checks (deterministic, no randomness) -------------------
    # AND across folds; one lucky fold must not emit; empty fold must not pass.
    gate = KFoldGate(alpha="0.01", K=2, seed=0)

    def lut(mapping):
        return lambda f, sub: mapping[f]

    r_both = gate.run([1, 2], lut({0: (0, 4000), 1: (10, 4000)}))     # both p<=0.01
    r_one = gate.run([1, 2], lut({0: (0, 4000), 1: (400, 4000)}))     # fold1 p=0.10
    r_empty = KFoldGate("0.01", K=2, seed=0)
    # force everything into fold 0 by using items that all hash to 0? instead test directly:
    r_emptyfold = GateResult(Fraction(1, 100), 2, 0,
                             [FoldOutcome(0, 5, 0, 4000, True), FoldOutcome(1, 0, 0, 0, False)],
                             emit=False)
    assert r_both.emit is True, "both folds passing must EMIT"
    assert r_one.emit is False, "one lucky fold must NOT emit (the v35 case)"
    assert _passes(0, 0, Fraction(1, 100)) is False, "empty fold cannot pass"
    print("  [logic] AND-across-folds, single-lucky-fold, empty-fold : OK")

    # -- negative control: a genuine NULL family (fair +-1) must SUPPRESS ---------
    rng = random.Random(2024)
    null_items = []
    for i in range(60):
        k = rng.choice([6, 8, 10, 12])           # even k so sum==0 is possible
        null_items.append((f"p{i}", [rng.choice([-1, 1]) for _ in range(k)]))
    gate = KFoldGate(alpha="0.01", K=2, seed=7)
    r_null = gate.run(null_items,
                      lambda f, sub: _zero_enrichment_pvalue(sub, seed_base=1000 + f))
    print("\n  [negative control] null +-1 family (no real enrichment):")
    print(r_null.render())
    if r_null.emit:
        ok = False
        print("  !! FAIL: gate emitted a null family")

    # -- positive control: a planted SIGNAL (every list forced to sum 0) ----------
    sig_items = []
    for i in range(60):
        k = rng.choice([6, 8, 10, 12])
        half = [1] * (k // 2) + [-1] * (k // 2)  # forced sum 0 => A==0 always
        rng.shuffle(half)
        sig_items.append((f"q{i}", half))
    gate = KFoldGate(alpha="0.01", K=2, seed=7)
    r_sig = gate.run(sig_items,
                     lambda f, sub: _zero_enrichment_pvalue(sub, seed_base=2000 + f))
    print("\n  [positive control] planted signal (A==0 forced in every item):")
    print(r_sig.render())
    if not r_sig.emit:
        ok = False
        print("  !! FAIL: gate suppressed a real signal")

    print("\n" + "=" * 74)
    print(f"SELF-TEST {'PASSED' if ok else 'FAILED'} — gate "
          f"{'emits signal & suppresses null' if ok else 'MISBEHAVED'}.")
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if selftest() else 1)
