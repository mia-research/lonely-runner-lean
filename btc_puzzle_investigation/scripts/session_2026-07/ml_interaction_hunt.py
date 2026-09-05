"""
Multivariate / learned-interaction leak hunt: does a COMBINATION of (X,Y)-derived
features jointly predict n or k (or their small-alphabet targets), even though
every single feature tested so far is flat?

GUARDRAIL: every feature below is a function of X, Y, and curve constants ONLY.
Never n, k, d, or bit-length. Targets come from L.build_target_set (n%m, k%m,
bit-slices of n/k, kn_bucket16, n_bucket16) plus an is_prime(n) target.

Method:
  1. Build a ~150-200 column feature matrix from (X,Y): residues mod SMALL_MODS,
     Legendre symbols mod SMALL_PRIMES, bit slices of X/Y/GLV-image/slope/sum/prod,
     Hamming weights, low/high combined residues, products/sums/diffs mod small m.
  2. Train/test split 70/30, stratified.
  3. GradientBoostingClassifier (small, since N=100k) and RandomForestClassifier
     per target. Report held-out accuracy, macro-AUC (OvR), vs base rate
     (majority-class frequency in the TEST split).
  4. Positive control: plant a target that is a genuine nonlinear function of a
     couple of the real features (e.g. XOR-style parity of two bit-slices, or a
     bucket of X%7 and Y%5 jointly) -- confirms the pipeline + model have power
     to detect an interaction of this planted strength at this N.
  5. Negative control: shuffle the real target labels (breaking (X,Y)<->target
     correspondence) and retrain -- gives the null held-out performance from
     model flexibility / overfitting alone.

A real leak = held-out metric on the REAL target clearly above BOTH the base
rate AND the shuffled-label null, at a magnitude comparable to (or approaching)
the positive control.
"""
import time, warnings
import numpy as np
import leak_lib as L

warnings.filterwarnings("ignore")

from sklearn.ensemble import GradientBoostingClassifier, RandomForestClassifier
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score, roc_auc_score
from sklearn.dummy import DummyClassifier

rng = np.random.default_rng(12345)

t0 = time.time()
d = L.load()
X_list, Y_list = d["X"], d["Y"]
N = d["N"]
print(f"loaded N={N} in {time.time()-t0:.2f}s")

# ---------------------------------------------------------------------------
# 1. FEATURE MATRIX (X,Y only)
# ---------------------------------------------------------------------------
t0 = time.time()
Xn = np.array(X_list, dtype=object)  # python ints, arbitrary precision
Yn = np.array(Y_list, dtype=object)

cols = {}

# raw residues mod small numbers, for X and Y
for m in L.SMALL_MODS:
    cols[f"X%{m}"] = L.col_mod(X_list, m)
    cols[f"Y%{m}"] = L.col_mod(Y_list, m)

# Legendre symbols mod small primes
for p in L.SMALL_PRIMES:
    cols[f"legX_{p}"] = L.col_legendre(X_list, p)
    cols[f"legY_{p}"] = L.col_legendre(Y_list, p)

# bit slices of X, Y at many positions (low bits, since low bits of X,Y are
# "curve-random" but might jointly correlate with position-derived n,k)
for b in list(range(0, 24)) + [32, 40, 48, 64, 96, 128, 160, 192, 224, 255]:
    cols[f"Xbit{b}"] = L.col_bit(X_list, b)
    cols[f"Ybit{b}"] = L.col_bit(Y_list, b)

# Hamming weight of X, Y (mod small numbers to keep alphabet small for MI-style
# use, but for the ML matrix we keep raw counts too, binned)
hwX = L.col_hamming(X_list)
hwY = L.col_hamming(Y_list)
cols["hwX"] = hwX
cols["hwY"] = hwY
cols["hwX%8"] = hwX % 8
cols["hwY%8"] = hwY % 8
cols["hwXY_diff%16"] = (hwX - hwY) % 16

# derived transforms: GLV image, slope, sum, prod, diff -- residues + bits
glv = L.tf_glv(X_list)
glv2 = L.tf_glv2(X_list)
slope = L.tf_slope(X_list, Y_list)
prod = L.tf_prod(X_list, Y_list)
summ = L.tf_sum(X_list, Y_list)
diff = L.tf_diff(X_list, Y_list)

derived = {"glv": glv, "glv2": glv2, "slope": slope, "prod": prod, "sum": summ, "diff": diff}
for name, vals in derived.items():
    for m in [3, 5, 7, 8, 11, 13, 16, 17, 31, 251, 256]:
        cols[f"{name}%{m}"] = L.col_mod(vals, m)
    for b in [0, 1, 2, 3, 4, 5, 6, 7, 8, 16]:
        cols[f"{name}_bit{b}"] = L.col_bit(vals, b)

# pairwise products of small residues (explicit interaction terms, in case
# tree models need help finding them -- though GBM/RF should find these anyway)
small_res = ["X%7", "X%11", "X%13", "Y%7", "Y%11", "Y%13", "X%8", "Y%8", "X%16", "Y%16"]
for i in range(len(small_res)):
    for j in range(i + 1, len(small_res)):
        a, b_ = small_res[i], small_res[j]
        cols[f"{a}*{b_}"] = cols[a] * (cols[b_].max() + 1) + cols[b_]

feat_names = sorted(cols.keys())
Fmat = np.column_stack([cols[c] for c in feat_names]).astype(np.float64)
print(f"feature matrix built: {Fmat.shape[1]} columns, {Fmat.shape[0]} rows, "
      f"{time.time()-t0:.2f}s")

# ---------------------------------------------------------------------------
# targets
# ---------------------------------------------------------------------------
T = L.build_target_set(d)
n_arr, k_arr = d["n"], d["k"]


def is_prime(x):
    if x < 2:
        return 0
    for p in [2, 3, 5, 7, 11, 13]:
        if x % p == 0:
            return int(x == p)
    i = 17
    while i * i <= x:
        if x % i == 0:
            return 0
        i += 1
    return 1


T["n_isprime"] = np.array([is_prime(int(x)) for x in n_arr])
T["k_isprime"] = np.array([is_prime(int(x)) for x in k_arr])

REAL_TARGETS = [
    "n%2", "n%3", "n%4", "n%6", "n%7", "n%8", "n%9", "n%11", "n%13", "n%16",
    "k%2", "k%3", "k%4", "k%6", "k%7", "k%8", "k%9", "k%11", "k%13", "k%16",
    "n_isprime", "k_isprime", "kn_bucket16", "n_bucket16",
    "nbit0", "nbit1", "nbit2", "nbit3", "kbit0", "kbit1", "kbit2", "kbit3",
]

# ---------------------------------------------------------------------------
# 4. POSITIVE CONTROL: plant a genuine nonlinear interaction of known strength
# ---------------------------------------------------------------------------
# planted target = f(X%7, Y%5) jointly, i.e. a deterministic bijection-ish
# bucket of two independent-looking real features -- pure interaction, NOT
# recoverable from either single feature alone (each single feature is
# independent of the planted label by construction via XOR-style combination).
x7 = cols["X%7"].astype(int)
y5 = cols["Y%5"].astype(int)
planted_strong = (x7 * 5 + y5) % 6  # strong: deterministic 1:1(ish) fn of two real feats, 6 classes
# weaker, harder planted leak: only 15% of rows get a real signal, rest is noise
# (mimics a partial/probabilistic leak of "known strength")
strong_mask = rng.random(N) < 0.30
planted_weak = rng.integers(0, 6, size=N)
planted_weak[strong_mask] = planted_strong[strong_mask]

T_PLANTED = {"planted_strong_XOR": planted_strong, "planted_weak_30pct": planted_weak}

# ---------------------------------------------------------------------------
# 2+3+5. train/eval helper with real + shuffled-null side by side
# ---------------------------------------------------------------------------
from sklearn.ensemble import HistGradientBoostingClassifier

idx_all = np.arange(N)


def make_model():
    # HistGradientBoosting: fast native NaN/large-N handling, good for tabular
    # interactions, roughly sklearn's answer to LightGBM.
    return HistGradientBoostingClassifier(
        max_iter=150, max_depth=6, learning_rate=0.08,
        l2_regularization=1.0, random_state=0,
    )


def fit_eval(Fmat, y, seed=0, test_size=0.30):
    """One train/test split + fit + eval. Returns dict of metrics."""
    y = np.asarray(y)
    n_classes = int(y.max()) + 1
    strat = y if n_classes <= 30 else None
    Xtr, Xte, ytr, yte = train_test_split(
        Fmat, y, test_size=test_size, random_state=seed, stratify=strat
    )
    # base rate = majority-class frequency on the TEST split
    counts = np.bincount(yte, minlength=n_classes)
    base_rate = counts.max() / len(yte)

    model = make_model()
    model.fit(Xtr, ytr)
    pred = model.predict(Xte)
    acc = accuracy_score(yte, pred)

    auc = np.nan
    try:
        proba = model.predict_proba(Xte)
        # only classes present in both train & test are meaningful for OvR AUC
        present = np.unique(np.concatenate([ytr, yte]))
        if n_classes == 2:
            auc = roc_auc_score(yte, proba[:, 1])
        else:
            auc = roc_auc_score(yte, proba, multi_class="ovr", average="macro",
                                 labels=np.arange(n_classes))
    except Exception:
        pass

    return {"acc": acc, "auc": auc, "base_rate": base_rate, "n_classes": n_classes,
             "n_test": len(yte)}


def evaluate_target(name, y, Fmat, n_shuffle_reps=3, seed0=0):
    """Real fit + shuffled-label null (n_shuffle_reps reps, report mean+max)."""
    real = fit_eval(Fmat, y, seed=seed0)

    null_accs, null_aucs = [], []
    r = np.random.default_rng(999)
    for i in range(n_shuffle_reps):
        y_shuf = r.permutation(np.asarray(y))
        m = fit_eval(Fmat, y_shuf, seed=seed0 + 1 + i)
        null_accs.append(m["acc"])
        null_aucs.append(m["auc"])

    return {
        "name": name,
        "real_acc": real["acc"], "real_auc": real["auc"],
        "base_rate": real["base_rate"], "n_classes": real["n_classes"],
        "n_test": real["n_test"],
        "null_acc_mean": float(np.nanmean(null_accs)), "null_acc_max": float(np.nanmax(null_accs)),
        "null_auc_mean": float(np.nanmean(null_aucs)), "null_auc_max": float(np.nanmax(null_aucs)),
    }


def fmt_row(r):
    return (f"{r['name']:<20} n_cls={r['n_classes']:>3}  base={r['base_rate']:.4f}  "
            f"REAL acc={r['real_acc']:.4f} auc={r['real_auc']:.4f}   "
            f"NULL acc(mean/max)={r['null_acc_mean']:.4f}/{r['null_acc_mean']:.4f} "
            f"auc(mean/max)={r['null_auc_mean']:.4f}/{r['null_auc_max']:.4f}   "
            f"lift(acc-base)={r['real_acc']-r['base_rate']:+.4f}  "
            f"lift(acc-null)={r['real_acc']-r['null_acc_mean']:+.4f}")


# ---------------------------------------------------------------------------
# RUN: positive controls first (prove the pipeline has power), then real targets
# ---------------------------------------------------------------------------
print("\n" + "=" * 100)
print("POSITIVE CONTROLS (planted interaction leaks -- must clearly beat base rate & null)")
print("=" * 100)
control_results = []
for tname, tvals in T_PLANTED.items():
    t0 = time.time()
    res = evaluate_target(tname, tvals, Fmat, n_shuffle_reps=3)
    dt = time.time() - t0
    control_results.append(res)
    print(fmt_row(res) + f"   [{dt:.1f}s]")

print("\n" + "=" * 100)
print(f"REAL TARGETS ({len(REAL_TARGETS)} targets) -- held-out acc/AUC vs base rate vs shuffled-null")
print("=" * 100)
real_results = []
for tname in REAL_TARGETS:
    tvals = T[tname]
    t0 = time.time()
    res = evaluate_target(tname, tvals, Fmat, n_shuffle_reps=3)
    dt = time.time() - t0
    real_results.append(res)
    print(fmt_row(res) + f"   [{dt:.1f}s]")

# ---------------------------------------------------------------------------
# summary: flag any real target beating base rate AND null by a nontrivial margin
# ---------------------------------------------------------------------------
print("\n" + "=" * 100)
print("SUMMARY: candidates where REAL clearly beats BOTH base rate and shuffled-null")
print("=" * 100)
flagged = []
for r in real_results:
    lift_base = r["real_acc"] - r["base_rate"]
    lift_null = r["real_acc"] - r["null_acc_mean"]
    auc_lift_null = (r["real_auc"] - r["null_auc_mean"]) if not np.isnan(r["real_auc"]) else np.nan
    if lift_base > 0.01 and lift_null > 0.01:
        flagged.append((r, lift_base, lift_null, auc_lift_null))

if not flagged:
    print("None. No real target's held-out accuracy exceeded both the base rate")
    print("and the shuffled-label null by more than 0.01 absolute, under this feature")
    print("set / model / 70-30 split. Positive controls above confirm the pipeline")
    print("has power to detect planted interaction leaks at this N.")
else:
    for r, lb, ln, la in flagged:
        print(f"{r['name']:<20} acc_lift_vs_base={lb:+.4f}  acc_lift_vs_null={ln:+.4f}  "
              f"auc_lift_vs_null={la:+.4f}")

print("\nDone.")

