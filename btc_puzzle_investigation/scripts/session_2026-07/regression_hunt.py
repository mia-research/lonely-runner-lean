"""
Continuous-target regression hunt: does (X,Y) alone predict k/n, n, or k as a
CONTINUOUS quantity? Earlier sessions (curve_transforms_hunt*, ml_interaction_hunt,
robustness_check) used discretized targets (mod-m buckets, 16-bin k/n) + mutual
information -- appropriate for detecting categorical/periodic leaks but liable to
dilute a smooth/monotone dependency (e.g. k/n varying continuously with some
feature). This script closes that gap: predict k/n, n, k directly with
HistGradientBoostingRegressor (+ MLPRegressor) on a 70/30 held-out split, R^2.

GUARDRAIL: every feature is a function of (X,Y) only (mod residues, Legendre
symbols, bit slices, Hamming weights, GLV image, slope Y/X, products/sums).
Never derived from n,k,d.

Mandatory controls:
  (a) shuffled-target null: same pipeline, target k/n randomly permuted -> R^2
      should be ~0 or negative (a fit with no true structure can still show
      negative R^2 on held-out data since it's relative to a fresh mean).
  (b) positive control: synthetic target = f(X%251, Y%127) + small noise, i.e.
      a target that BY CONSTRUCTION depends on only two of our features -> R^2
      must recover to confirm the pipeline can detect real signal of this shape.

A real leak claim requires held-out R^2 clearly above the shuffled null AND
comparable in kind (not necessarily magnitude) to how the control recovers.
"""
import time, warnings
import numpy as np
import leak_lib as L
warnings.filterwarnings("ignore")

from sklearn.ensemble import HistGradientBoostingRegressor
from sklearn.neural_network import MLPRegressor
from sklearn.model_selection import train_test_split
from sklearn.metrics import r2_score
from sklearn.preprocessing import StandardScaler
from scipy.stats import spearmanr

t0 = time.time()
d = L.load()
X_list, Y_list = d["X"], d["Y"]
n_arr, k_arr, N = d["n"], d["k"], d["N"]
print(f"loaded N={N} rows in {time.time()-t0:.1f}s")

# ---------------------------------------------------------------------------
# 1. Rich (X,Y)-only feature matrix (~150+ columns)
# ---------------------------------------------------------------------------
cols = {}
for m in L.SMALL_MODS:
    cols[f"X%{m}"] = L.col_mod(X_list, m)
    cols[f"Y%{m}"] = L.col_mod(Y_list, m)
for p in L.SMALL_PRIMES:
    cols[f"legX_{p}"] = L.col_legendre(X_list, p)
    cols[f"legY_{p}"] = L.col_legendre(Y_list, p)
bit_positions = list(range(0, 24)) + [32, 40, 48, 64, 96, 128, 160, 192, 224, 255]
for b in bit_positions:
    cols[f"Xbit{b}"] = L.col_bit(X_list, b)
    cols[f"Ybit{b}"] = L.col_bit(Y_list, b)

hwX = L.col_hamming(X_list); hwY = L.col_hamming(Y_list)
cols["hwX"] = hwX; cols["hwY"] = hwY
cols["hwX%8"] = hwX % 8; cols["hwY%8"] = hwY % 8
cols["hwXY_diff"] = hwX - hwY
cols["hwXY_sum"] = hwX + hwY

glv   = L.tf_glv(X_list)
glv2  = L.tf_glv2(X_list)
slope = L.tf_slope(X_list, Y_list)
prod  = L.tf_prod(X_list, Y_list)
summ  = L.tf_sum(X_list, Y_list)
diff  = L.tf_diff(X_list, Y_list)
derived = {"glv": glv, "glv2": glv2, "slope": slope, "prod": prod, "sum": summ, "diff": diff}
for name, vals in derived.items():
    for m in [3, 5, 7, 8, 11, 13, 16, 17, 31, 127, 251, 256]:
        cols[f"{name}%{m}"] = L.col_mod(vals, m)
    for b in [0, 1, 2, 3, 4, 5, 6, 7, 8, 16, 32]:
        cols[f"{name}_bit{b}"] = L.col_bit(vals, b)
    cols[f"{name}_hw"] = L.col_hamming(vals)

# raw top-bits of X,Y as (roughly) continuous-scale features -- give the
# regressor a literal high-order-magnitude signal to split on, in case the
# leak is "smooth in X" rather than residue-based.
X_arr = np.array([int(x) for x in X_list], dtype=np.float64)
Y_arr = np.array([int(y) for y in Y_list], dtype=np.float64)
cols["X_top32"]  = np.array([int(x) >> 224 for x in X_list], dtype=np.float64)
cols["Y_top32"]  = np.array([int(y) >> 224 for y in Y_list], dtype=np.float64)
cols["X_top16"]  = np.array([int(x) >> 240 for x in X_list], dtype=np.float64)
cols["Y_top16"]  = np.array([int(y) >> 240 for y in Y_list], dtype=np.float64)
cols["X_scaled"] = X_arr / float(L.P)
cols["Y_scaled"] = Y_arr / float(L.P)

feat_names = sorted(cols.keys())
Fmat = np.column_stack([cols[c] for c in feat_names]).astype(np.float64)
print(f"feature matrix: {Fmat.shape} ({len(feat_names)} columns)")

# ---------------------------------------------------------------------------
# 2. Continuous targets
# ---------------------------------------------------------------------------
kn_ratio = k_arr.astype(np.float64) / np.maximum(n_arr.astype(np.float64), 1.0)
targets = {
    "k/n": kn_ratio,
    "n":   n_arr.astype(np.float64),
    "k":   k_arr.astype(np.float64),
}

rng = np.random.default_rng(0)

def fit_gbr(Xtr, ytr, Xte, yte, seed=0):
    # HistGradientBoostingRegressor: histogram-based, ~100x faster than the
    # exact GradientBoostingRegressor on 100k rows; same boosted-tree family.
    m = HistGradientBoostingRegressor(
        max_iter=300, max_depth=4, learning_rate=0.05,
        l2_regularization=1.0, random_state=seed)
    m.fit(Xtr, ytr)
    pred = m.predict(Xte)
    return r2_score(yte, pred), m

def fit_mlp(Xtr, ytr, Xte, yte, seed=0):
    sc = StandardScaler().fit(Xtr)
    Xtr_s, Xte_s = sc.transform(Xtr), sc.transform(Xte)
    ysc = StandardScaler().fit(ytr.reshape(-1, 1))
    ytr_s = ysc.transform(ytr.reshape(-1, 1)).ravel()
    m = MLPRegressor(hidden_layer_sizes=(128, 64), max_iter=500,
                      early_stopping=True, random_state=seed, alpha=1e-3)
    m.fit(Xtr_s, ytr_s)
    pred_s = m.predict(Xte_s)
    pred = ysc.inverse_transform(pred_s.reshape(-1, 1)).ravel()
    return r2_score(yte, pred), m

print("\n" + "=" * 78)
print("STEP 2: HistGradientBoostingRegressor + MLPRegressor on real continuous targets")
print("=" * 78)

results = {}
for tname, y in targets.items():
    Xtr, Xte, ytr, yte = train_test_split(Fmat, y, test_size=0.30, random_state=0)
    t1 = time.time()
    r2_gbr, model_gbr = fit_gbr(Xtr, ytr, Xte, yte, seed=0)
    t_gbr = time.time() - t1
    t1 = time.time()
    r2_mlp, model_mlp = fit_mlp(Xtr, ytr, Xte, yte, seed=0)
    t_mlp = time.time() - t1
    results[tname] = {"gbr": r2_gbr, "mlp": r2_mlp}
    print(f"\ntarget={tname:<6} N_train={len(ytr)} N_test={len(yte)}")
    print(f"  HistGradientBoostingRegressor: held-out R^2 = {r2_gbr:+.6f}  ({t_gbr:.1f}s)")
    print(f"  MLPRegressor:              held-out R^2 = {r2_mlp:+.6f}  ({t_mlp:.1f}s)")

# ---------------------------------------------------------------------------
# 3. Best single-feature Spearman correlation vs k/n (rank ALL ~150 features)
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("STEP 3: single-feature Spearman rank correlation vs k/n (all features)")
print("=" * 78)
spearman_rows = []
y_kn = targets["k/n"]
for i, fn in enumerate(feat_names):
    col = Fmat[:, i]
    if np.all(col == col[0]):
        continue
    rho, p = spearmanr(col, y_kn)
    spearman_rows.append((abs(rho), rho, p, fn))
spearman_rows.sort(reverse=True)
M = len(spearman_rows)
print(f"{'|rho|':>8} {'rho':>8} {'p-value':>10} {'Bonf-p':>10}  feature")
for absrho, rho, p, fn in spearman_rows[:25]:
    print(f"{absrho:8.4f} {rho:+8.4f} {p:10.3e} {min(1,p*M):10.3e}  {fn}")

top_feature = spearman_rows[0]
print(f"\nTOP single feature vs k/n: {top_feature[3]}  rho={top_feature[1]:+.4f}  p={top_feature[2]:.3e}  (Bonferroni over {M} features: {min(1,top_feature[2]*M):.3e})")

# also rank vs n and k raw, for completeness
for extra_name, y_extra in [("n", targets["n"]), ("k", targets["k"])]:
    rows = []
    for i, fn in enumerate(feat_names):
        col = Fmat[:, i]
        if np.all(col == col[0]):
            continue
        rho, p = spearmanr(col, y_extra)
        rows.append((abs(rho), rho, p, fn))
    rows.sort(reverse=True)
    best = rows[0]
    print(f"TOP single feature vs {extra_name}: {best[3]}  rho={best[1]:+.4f}  p={best[2]:.3e}  (Bonferroni: {min(1,best[2]*len(rows)):.3e})")

# ---------------------------------------------------------------------------
# 4a. MANDATORY shuffled-target null
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("STEP 4a: shuffled-target null (retrain GBR on shuffled k/n, n, k)")
print("=" * 78)
null_results = {}
for tname, y in targets.items():
    y_shuf = rng.permutation(y)
    Xtr, Xte, ytr, yte = train_test_split(Fmat, y_shuf, test_size=0.30, random_state=0)
    r2_null, _ = fit_gbr(Xtr, ytr, Xte, yte, seed=0)
    null_results[tname] = r2_null
    print(f"  shuffled {tname:<6} -> held-out R^2 = {r2_null:+.6f}")

# repeat shuffled null over multiple seeds for k/n specifically, to get a
# distribution rather than a single draw
print("\n  k/n shuffled null over 5 independent permutations (GBR):")
null_kn_multi = []
for seed in range(5):
    y_shuf = np.random.default_rng(seed + 100).permutation(targets["k/n"])
    Xtr, Xte, ytr, yte = train_test_split(Fmat, y_shuf, test_size=0.30, random_state=seed)
    r2_s, _ = fit_gbr(Xtr, ytr, Xte, yte, seed=seed)
    null_kn_multi.append(r2_s)
    print(f"    seed={seed}: R^2 = {r2_s:+.6f}")
print(f"  mean={np.mean(null_kn_multi):+.6f}  std={np.std(null_kn_multi):.6f}")

# ---------------------------------------------------------------------------
# 4b. MANDATORY positive control: target genuinely depends on X%251, Y%127
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("STEP 4b: positive control (target = f(X%251, Y%127) + small noise)")
print("=" * 78)
x251 = cols["X%251"]; y127 = cols["Y%127"]
noise = rng.normal(0, 0.02, size=N)
control_target = (x251 / 251.0) * 0.6 + (y127 / 127.0) * 0.4 + noise
Xtr, Xte, ytr, yte = train_test_split(Fmat, control_target, test_size=0.30, random_state=0)
r2_control, _ = fit_gbr(Xtr, ytr, Xte, yte, seed=0)
print(f"  control target R^2 (GBR) = {r2_control:+.6f}  (should be high, confirms pipeline sensitivity)")

# also confirm MLP recovers it
r2_control_mlp, _ = fit_mlp(Xtr, ytr, Xte, yte, seed=0)
print(f"  control target R^2 (MLP) = {r2_control_mlp:+.6f}")

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("SUMMARY")
print("=" * 78)
print(f"{'target':<8} {'GBR R^2':>12} {'MLP R^2':>12} {'shuffle-null R^2':>18}")
for tname in targets:
    print(f"{tname:<8} {results[tname]['gbr']:12.6f} {results[tname]['mlp']:12.6f} {null_results[tname]:18.6f}")
print(f"\npositive control R^2 (GBR): {r2_control:+.6f}  (MLP: {r2_control_mlp:+.6f})")
print(f"top single-feature |Spearman rho| vs k/n: {top_feature[3]} = {top_feature[1]:+.4f} (p={top_feature[2]:.3e})")
print(f"\ntotal runtime: {time.time()-t0:.1f}s")
