"""
Controls, nulls, and validation — MANDATORY per the methodology.

Rules baked in (from btc_puzzle_hunt_method / findings v2 sec.0):
  * A null without a FIRING positive control is worthless -> plant_leak + a
    detector that must fire, else the WP is discarded as underpowered.
  * SELECTION hypotheses use a MATCHED-MULTISET null (real bit-length multiset,
    real curve arithmetic, only d randomized). Single-scale uniform tests only
    "is it a universal math relation", NOT a selection effect.
  * Cross-validation is GROUPED BY bits (never train and test on the same N).
"""
from __future__ import annotations
import random
import numpy as np
import pandas as pd
from sklearn.model_selection import GroupKFold

import lib_data as L


# ------------------------------------------------------- positive controls ---
def plant_leak(y: np.ndarray, strength: float, n_classes: int | None = None,
               seed: int = 0) -> np.ndarray:
    """A synthetic feature that encodes y with the given strength in [0,1].

    strength=1 -> feature == y (perfectly predictive); 0 -> pure noise. Feed this
    as an EXTRA column to the detector; it MUST be recovered, proving power. If the
    detector cannot find even a strong planted leak at this N, the real null is
    'underpowered', not 'no effect'.
    """
    rng = np.random.default_rng(seed)
    y = np.asarray(y, float)
    noise = rng.normal(0, (y.std() or 1.0), size=y.shape)
    return strength * y + (1 - strength) * noise


# --------------------------------------------------- matched-multiset null ---
def matched_null(df: pd.DataFrame, seed: int = 0) -> pd.DataFrame:
    """Draw a synthetic dataset with the EXACT real bit-length multiset, real
    curve arithmetic, random d per band, recompute (n,k,D). This is the null for
    ANY selection-of-d hypothesis. Returns columns bits,d,X,Y,n,k,D,D_terms.

    NOTE cost: one scalar mult per row. Subsample for large frames.
    """
    pyrng = random.Random(seed)  # Python big-int uniform (numpy int64 overflows >2^63)
    rows = []
    for bits, cnt in df["bits"].value_counts().sort_index().items():
        A = 1 << (bits - 1)
        seen = set()
        for _ in range(int(cnt)):
            # distinct d in band; cap retries (bits==1 band has only 1 key)
            for _try in range(64):
                d = pyrng.randrange(A, 2 * A) if bits > 1 else A
                if d not in seen:
                    seen.add(d)
                    break
            n, k, D, dt = L.decompose(d, bits)
            X, Y = L.ec_mul(d)
            rows.append((bits, d, X, Y, n, k, D, dt))
    return pd.DataFrame(rows, columns=["bits", "d", "X", "Y", "n", "k", "D", "D_terms"])


# --------------------------------------------------------------- validation ---
def grouped_cv_score(X, y, groups, estimator, n_splits: int = 5):
    """Group-k-fold accuracy grouped by `groups` (pass df['bits']). Never trains
    and tests on the same bit-length. Returns (mean_acc, per_fold)."""
    from sklearn.base import clone
    gkf = GroupKFold(n_splits=min(n_splits, len(np.unique(groups))))
    accs = []
    for tr, te in gkf.split(X, y, groups):
        est = clone(estimator).fit(X[tr], y[tr])
        accs.append(est.score(X[te], y[te]))
    return float(np.mean(accs)), [float(a) for a in accs]


def permutation_null(stat_fn, y, n_perm: int = 1000, seed: int = 0):
    """Permutation p-value for a statistic. stat_fn(y_perm) -> scalar.
    Returns (observed, p_two_sided, null_mean, null_p95)."""
    rng = np.random.default_rng(seed)
    obs = stat_fn(y)
    null = np.array([stat_fn(rng.permutation(y)) for _ in range(n_perm)])
    p = (1 + np.sum(np.abs(null - null.mean()) >= abs(obs - null.mean()))) / (n_perm + 1)
    return float(obs), float(p), float(null.mean()), float(np.percentile(null, 95))


def conditional_negative(name: str, stat, floor, n_samples, features, control_z):
    """Format a result as a CONDITIONAL negative (never 'impossible'). Every WP
    result string must go through here so the phrasing stays bounded."""
    fired = control_z is not None and abs(control_z) >= 5
    return {
        "test": name,
        "statistic": stat,
        "noise_floor": floor,
        "n_samples": n_samples,
        "features": features,
        "positive_control_z": control_z,
        "control_fired": fired,
        "reading": (f"not observed with these {len(features)} features at "
                    f"n={n_samples} (floor {floor})."
                    if fired else
                    "INCONCLUSIVE — positive control did not fire; test underpowered, "
                    "null discarded (not reported as a negative)."),
    }
