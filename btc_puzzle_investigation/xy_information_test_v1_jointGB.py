#!/usr/bin/env python3
"""
Channel C, full-strength: can a gradient-boosted model read a d-function from the
WHOLE (X,Y) feature vector jointly (structure no single feature or pair carries)?
Held-out accuracy vs a permutation null -> this is also the OOS confirmation (design 7).
Reuses the feature builder + targets from xy_information_test_v1.
"""
import numpy as np, pandas as pd
from sklearn.ensemble import HistGradientBoostingClassifier
from sklearn.model_selection import train_test_split
import xy_information_test_v1 as H

N, R, SEED = 12000, 100, 7
rng = np.random.default_rng(SEED)
df = pd.read_csv("constructed_keys_1to160_100k.csv",
                usecols=["bits", "d", "X", "Y"], dtype={"d": str})
df = df[df["bits"] >= 8].sample(N, random_state=SEED).reset_index(drop=True)
feats, d, Nbits, X, Y = H.build(df)
tg = H.make_targets(d, Nbits, X, rng)
Fmat = np.column_stack([feats[k] for k in feats]).astype(float)

def adv(Xm, y):
    """Held-out accuracy minus majority-class baseline (y already masked/dense-coded)."""
    Xtr, Xte, ytr, yte = train_test_split(Xm, y, test_size=0.3, random_state=SEED, stratify=y)
    clf = HistGradientBoostingClassifier(max_iter=120, random_state=SEED).fit(Xtr, ytr)
    return clf.score(Xte, yte) - np.bincount(yte).max() / len(yte)

targets = ["PLANT_strong", "PLANT_f0.10", "d%3", "d%7", "u_bin8"]
print(f"# joint GB  keys={N}  features={Fmat.shape[1]}  perms={R}")
print(f"{'target':14s} {'heldout_adv':>11s} {'null_mean':>9s} {'null_sd':>8s} {'z':>7s} {'p':>7s}  verdict")
print("-" * 74)
for t in targets:
    yfull = tg[t]
    m = yfull >= 0
    Xm, y = Fmat[m], yfull[m].astype(int)
    obs = adv(Xm, y)
    null = np.array([adv(Xm, rng.permutation(y)) for _ in range(R)])
    z = (obs - null.mean()) / (null.std() + 1e-12)
    p = (int((null >= obs).sum()) + 1) / (R + 1)
    v = "FIRES" if p < 0.05 else "null"
    tag = "  <-- control" if t.startswith("PLANT") else ""
    print(f"{t:14s} {obs:11.4f} {null.mean():9.4f} {null.std():8.4f} {z:7.2f} {p:7.4f}  {v}{tag}")
