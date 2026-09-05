"""
Raw-bit learned-representation leak hunt: no hand-engineered features (no mod-m
residues, no Legendre symbols) -- just the 256 raw bits of X and the 256 raw
bits of Y (optionally + raw bits of (X+Y)%P and (X*Y)%P), fed straight into an
MLPClassifier / MLPRegressor. The point is to let the network's hidden layers
discover any structure a human feature-engineer might miss, since n,k are
DERIVED from (X,Y) via the same curve arithmetic and could in principle be
recoverable via some bit-mixing the model can approximate.

GUARDRAIL: every feature column below is a bit of X, Y, (X+Y)%P, or (X*Y)%P.
Never n, k, d, or bit-length ("bits") go into the feature matrix.

Targets (from d['n'], d['k'] directly, NOT from L.build_target_set to keep
control over exact definitions matching the task spec):
    n%6, n%8, k%6, k%8, n_isprime, kn_bucket16 = clip(int(k/n*16), 0, 15)

Method:
  1. Raw-bit feature matrix: 512 columns (bits 0..255 of X, then Y), optionally
     +512 more from (X+Y)%P and (X*Y)%P bits = up to 1024 columns.
  2. MLPClassifier(hidden_layer_sizes=(256,128), early_stopping=True) per
     classification target, 70/30 train/test split (stratified where possible).
     MLPRegressor(hidden_layer_sizes=(256,128), early_stopping=True) for the
     continuous k/n target, plain R^2.
  3. MANDATORY controls, run through the IDENTICAL pipeline/model:
       (a) POSITIVE: planted_parity = XOR of bit 3 of X and bit 7 of Y (a
           genuine deterministic function of a couple of input bits) -- if the
           net can't recover this, the pipeline has no power at this N and
           architecture, full stop.
       (b) NEGATIVE: shuffle the real labels (breaks (X,Y)<->target
           correspondence, same class balance) and retrain -- null floor from
           model flexibility / overfitting alone.
  4. Report held-out accuracy vs base rate (most-frequent-class) and vs
     shuffled null, side by side, for every real target, the positive control,
     and the negative control. Same for R^2 on k/n.

No feature/target here is n, k, or d directly -- only (X,Y)-derived bits as
features, and n/k-derived quantities as targets (which is the whole point:
can (X,Y) bits predict n,k derived quantities).
"""
import time, warnings
import numpy as np
import leak_lib as L

warnings.filterwarnings("ignore")

from sklearn.neural_network import MLPClassifier, MLPRegressor
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score, r2_score
from sklearn.dummy import DummyClassifier, DummyRegressor

RNG_SEED = 12345
rng = np.random.default_rng(RNG_SEED)

t0 = time.time()
d = L.load()
X_list, Y_list = d["X"], d["Y"]
n = d["n"]; k = d["k"]; N = d["N"]
print(f"loaded N={N} in {time.time()-t0:.2f}s")

# ---------------------------------------------------------------------------
# 1. RAW-BIT FEATURE MATRIX (X,Y and X,Y-derived values ONLY)
# ---------------------------------------------------------------------------
t0 = time.time()

def bit_matrix(vals, nbits=256):
    """columns = bit b of vals, for b in range(nbits). Shape (N, nbits)."""
    cols = [L.col_bit(vals, b) for b in range(nbits)]
    return np.stack(cols, axis=1).astype(np.float32)

Xbits = bit_matrix(X_list, 256)
Ybits = bit_matrix(Y_list, 256)

sum_vals = L.tf_sum(X_list, Y_list)   # (X+Y) % P
prod_vals = L.tf_prod(X_list, Y_list) # (X*Y) % P
Sbits = bit_matrix(sum_vals, 256)
Pbits = bit_matrix(prod_vals, 256)

F512 = np.concatenate([Xbits, Ybits], axis=1)              # 512 cols: raw X,Y bits
F1024 = np.concatenate([Xbits, Ybits, Sbits, Pbits], axis=1)  # 1024 cols: + derived

print(f"feature matrices built in {time.time()-t0:.2f}s  "
      f"F512={F512.shape}  F1024={F1024.shape}")

# ---------------------------------------------------------------------------
# 2. TARGETS
# ---------------------------------------------------------------------------
def is_prime(x):
    x = int(x)
    if x < 2: return 0
    if x < 4: return 1
    if x % 2 == 0: return 0
    i = 3
    while i * i <= x:
        if x % i == 0: return 0
        i += 2
    return 1

targets_cls = {
    "n%6": n % 6,
    "n%8": n % 8,
    "k%6": k % 6,
    "k%8": k % 8,
    "n_isprime": np.array([is_prime(x) for x in n]),
    "kn_bucket16": np.clip((k.astype(np.float64) / n.astype(np.float64) * 16).astype(int), 0, 15),
}
target_cont = (k.astype(np.float64) / n.astype(np.float64))  # k/n continuous

# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------
def run_classifier(feat, y, label, feat_label, hidden=(256, 128), test_size=0.30,
                    seed=0, max_iter=300):
    Xtr, Xte, ytr, yte = train_test_split(
        feat, y, test_size=test_size, random_state=seed,
        stratify=y if len(np.unique(y)) <= 50 else None
    )
    clf = MLPClassifier(hidden_layer_sizes=hidden, early_stopping=True,
                         max_iter=max_iter, random_state=seed)
    clf.fit(Xtr, ytr)
    pred = clf.predict(Xte)
    acc = accuracy_score(yte, pred)

    dummy = DummyClassifier(strategy="most_frequent")
    dummy.fit(Xtr, ytr)
    base = accuracy_score(yte, dummy.predict(Xte))

    print(f"  [{feat_label}] {label:16s} n_classes={len(np.unique(y)):3d}  "
          f"held-out acc={acc:.4f}   base-rate(most-freq)={base:.4f}   "
          f"lift={acc-base:+.4f}")
    return acc, base


def run_regressor(feat, y, label, feat_label, hidden=(256, 128), test_size=0.30,
                   seed=0, max_iter=300):
    Xtr, Xte, ytr, yte = train_test_split(feat, y, test_size=test_size, random_state=seed)
    reg = MLPRegressor(hidden_layer_sizes=hidden, early_stopping=True,
                        max_iter=max_iter, random_state=seed)
    reg.fit(Xtr, ytr)
    pred = reg.predict(Xte)
    r2 = r2_score(yte, pred)

    dummy = DummyRegressor(strategy="mean")
    dummy.fit(Xtr, ytr)
    r2_base = r2_score(yte, dummy.predict(Xte))  # by definition ~0

    print(f"  [{feat_label}] {label:16s} held-out R^2={r2:.5f}   "
          f"(mean-predictor R^2={r2_base:.5f})")
    return r2


# ---------------------------------------------------------------------------
# 3. MAIN SWEEP: classification targets, both feature sets
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("CLASSIFICATION TARGETS (MLPClassifier, hidden=(256,128), 70/30 split)")
print("=" * 78)

results_cls = {}
for feat_label, feat in [("rawbits512(X,Y)", F512), ("rawbits1024(X,Y,+sum,+prod)", F1024)]:
    print(f"\n--- feature set: {feat_label} ---")
    for tname, y in targets_cls.items():
        acc, base = run_classifier(feat, y, tname, feat_label)
        results_cls[(feat_label, tname)] = (acc, base)

# ---------------------------------------------------------------------------
# 4. MAIN SWEEP: continuous target k/n
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("CONTINUOUS TARGET k/n (MLPRegressor, hidden=(256,128), 70/30 split)")
print("=" * 78)

results_reg = {}
for feat_label, feat in [("rawbits512(X,Y)", F512), ("rawbits1024(X,Y,+sum,+prod)", F1024)]:
    r2 = run_regressor(feat, target_cont, "k/n", feat_label)
    results_reg[feat_label] = r2

# ---------------------------------------------------------------------------
# 5. MANDATORY CONTROLS -- on the F512 feature set (representative, fastest)
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("MANDATORY CONTROLS (feature set = rawbits512(X,Y))")
print("=" * 78)

# (a) POSITIVE CONTROL: planted deterministic function of a couple of input bits.
#     parity of bit3(X) XOR bit7(Y) -- genuinely present as columns in F512,
#     so this tests whether the net + pipeline can recover a real signal here.
bit3_X = L.col_bit(X_list, 3)
bit7_Y = L.col_bit(Y_list, 7)
planted_parity = (bit3_X ^ bit7_Y).astype(int)

print("\n-- (a) POSITIVE control: planted_parity = bit3(X) XOR bit7(Y) --")
acc_pos, base_pos = run_classifier(F512, planted_parity, "planted_parity", "rawbits512(X,Y)")

# also a "harder" planted control: bucket of a 3-bit combination (8 classes),
# analogous difficulty to kn_bucket16 / n%8, to calibrate power at that class count
bit_combo = (L.col_bit(X_list, 3) | (L.col_bit(X_list, 11) << 1) | (L.col_bit(Y_list, 7) << 2)).astype(int)
print("\n-- (a2) POSITIVE control (8-class): 3-bit combo of X,Y bits --")
acc_pos8, base_pos8 = run_classifier(F512, bit_combo, "planted_3bitcombo", "rawbits512(X,Y)")

# (b) NEGATIVE CONTROL: shuffle real labels, breaking (X,Y)<->target link.
print("\n-- (b) NEGATIVE control: shuffled real-label null --")
results_null = {}
for tname, y in targets_cls.items():
    y_shuffled = rng.permutation(y)
    acc_null, base_null = run_classifier(F512, y_shuffled, f"shuffled({tname})", "rawbits512(X,Y)")
    results_null[tname] = (acc_null, base_null)

# shuffled null for the continuous regression target too
kn_shuffled = rng.permutation(target_cont)
print("\n-- (b) NEGATIVE control: shuffled k/n regression null --")
r2_null = run_regressor(F512, kn_shuffled, "shuffled(k/n)", "rawbits512(X,Y)")

# ---------------------------------------------------------------------------
# 6. SUMMARY TABLE
# ---------------------------------------------------------------------------
print("\n" + "=" * 78)
print("SUMMARY: held-out accuracy, real vs base-rate vs shuffled-null")
print("=" * 78)
print(f"{'target':16s} {'feat_set':28s} {'acc':>8s} {'base':>8s} {'lift':>8s} "
      f"{'null_acc':>9s} {'null_base':>9s} {'null_lift':>9s}")
for feat_label in ["rawbits512(X,Y)", "rawbits1024(X,Y,+sum,+prod)"]:
    for tname in targets_cls:
        acc, base = results_cls[(feat_label, tname)]
        if feat_label == "rawbits512(X,Y)":
            null_acc, null_base = results_null[tname]
            print(f"{tname:16s} {feat_label:28s} {acc:8.4f} {base:8.4f} {acc-base:+8.4f} "
                  f"{null_acc:9.4f} {null_base:9.4f} {null_acc-null_base:+9.4f}")
        else:
            print(f"{tname:16s} {feat_label:28s} {acc:8.4f} {base:8.4f} {acc-base:+8.4f} "
                  f"{'--':>9s} {'--':>9s} {'--':>9s}")

print(f"\n{'planted_parity':16s} {'rawbits512(X,Y)':28s} {acc_pos:8.4f} {base_pos:8.4f} {acc_pos-base_pos:+8.4f}   (positive control, 2-class)")
print(f"{'planted_3bitcombo':16s} {'rawbits512(X,Y)':28s} {acc_pos8:8.4f} {base_pos8:8.4f} {acc_pos8-base_pos8:+8.4f}   (positive control, 8-class)")

print("\nREGRESSION (k/n):")
for feat_label, r2 in results_reg.items():
    print(f"  [{feat_label}] held-out R^2 = {r2:.5f}")
print(f"  [rawbits512(X,Y)] shuffled-null R^2 = {r2_null:.5f}")

print(f"\ntotal runtime: {time.time()-t0:.1f}s (from control section start)")
print("\nDONE.")
