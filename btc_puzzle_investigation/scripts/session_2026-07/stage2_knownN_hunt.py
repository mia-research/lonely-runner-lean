"""
STAGE-2 HUNT: given the KNOWN stage-1 output n (and public bit-length `bits`),
does (X,Y) reduced mod n reveal the secret k?

Two-stage attacker model:
  stage 1: recover n from (X,Y)  [GIVEN here -- n is the known stage-1 output]
  stage 2: THIS SCRIPT. Using (X, Y, n, bits) -- all public/known -- predict
           the SECRET k (never a feature), k mod m (m=2..13), and k/n position.

GUARDRAIL: n and bits are ALLOWED inputs (stage-1 output / public bit-length).
k and d are the SECRETS -> only targets, never features.

Features (fns of X,Y,n,bits ONLY):
  X mod n, Y mod n, (X*Y) mod n^2 (+ normalized), (X*Y) mod n, (X+Y) mod n,
  X*modinv(Y,n) mod n (sentinel where gcd!=1), X mod n^2, bits,
  and curve-native X,Y residues mod small primes.

Targets: k (regression), k%m for m=2..13, k/n (bucket16 classif + raw regression).

Setups:
  (a) POOLED: all rows, n & bits as features, GBM, 70/30 split.
  (b) PER-N STRATIFIED at 100k: group by n, evaluate within each large group,
      report aggregate (test-size-weighted) lift.

MANDATORY side-by-side: shuffled-k NULL and a planted POSITIVE CONTROL feature
that genuinely carries k, through the identical pipeline.

Report ACTUAL held-out lift above base rate. No "closed"/"settled"/"flat".
"""
import sys, time, math
import numpy as np
import leak_lib as L
from sklearn.ensemble import HistGradientBoostingClassifier, HistGradientBoostingRegressor
from sklearn.model_selection import train_test_split
from sklearn.metrics import accuracy_score, mean_absolute_error, r2_score

def log(*a):
    print(*a, flush=True)

SEED = 20260706
rng = np.random.default_rng(SEED)
t0 = time.time()

log("Loading dataset...")
d = L.load()
X_list, Y_list = d["X"], d["Y"]
n_arr = d["n"].astype(np.int64)
k_arr = d["k"].astype(np.int64)
bits_arr = d["bits"].astype(np.int64)
N = d["N"]
log(f"  N={N}  bits[{bits_arr.min()},{bits_arr.max()}]  n[{n_arr.min()},{n_arr.max()}]  "
    f"k[{k_arr.min()},{k_arr.max()}]  ({time.time()-t0:.1f}s)")

SMALL_PRIMES = L.SMALL_PRIMES

# ---------------------------------------------------------------------------
# Per-row modular features (256-bit ints -> unavoidable python loop, done ONCE).
# ---------------------------------------------------------------------------
log("Building features (X,Y,n,bits only; never k,d)...")
M = N
Xmodn = np.empty(M, np.int64); Ymodn = np.empty(M, np.int64)
XYmodn2 = np.empty(M, np.int64); XYmodn2n = np.empty(M, np.float64)
XYmodn = np.empty(M, np.int64); XpY = np.empty(M, np.int64)
Xinvy = np.empty(M, np.int64); haveinv = np.empty(M, np.int64)
Xmodn2 = np.empty(M, np.int64)
for i in range(M):
    Xi = X_list[i]; Yi = Y_list[i]; ni = int(n_arr[i]); n2 = ni*ni
    xr = Xi % ni; yr = Yi % ni
    Xmodn[i] = xr; Ymodn[i] = yr
    xy2 = (Xi * Yi) % n2
    XYmodn2[i] = xy2; XYmodn2n[i] = xy2 / n2
    XYmodn[i] = (Xi * Yi) % ni
    XpY[i] = (Xi + Yi) % ni
    Xmodn2[i] = Xi % n2
    if ni > 1 and math.gcd(yr, ni) == 1:
        Xinvy[i] = (Xi * pow(yr, -1, ni)) % ni; haveinv[i] = 1
    else:
        Xinvy[i] = -1; haveinv[i] = 0
log(f"  per-row modular features done ({time.time()-t0:.1f}s)")

feats = {
    "X_mod_n": Xmodn, "Y_mod_n": Ymodn, "XY_mod_n2": XYmodn2, "XY_mod_n2_norm": XYmodn2n,
    "XY_mod_n": XYmodn, "XplusY_mod_n": XpY, "X_mod_n2": Xmodn2,
    "X_Yinv_mod_n": Xinvy, "have_Yinv": haveinv, "n": n_arr.copy(), "bits": bits_arr.copy(),
}
for p in SMALL_PRIMES:
    feats[f"X_mod_{p}"] = np.fromiter((Xi % p for Xi in X_list), np.int64, M)
    feats[f"Y_mod_{p}"] = np.fromiter((Yi % p for Yi in Y_list), np.int64, M)

feat_names = list(feats.keys())
Xmat = np.column_stack([feats[fn] for fn in feat_names]).astype(np.float32)
log(f"  feature matrix {Xmat.shape}  ({time.time()-t0:.1f}s)")

# ---------------------------------------------------------------------------
# Targets
# ---------------------------------------------------------------------------
def build_targets(narr, karr):
    T = {"k": karr.astype(np.float64)}
    for m in range(2, 14):
        T[f"k_mod_{m}"] = (karr % m).astype(np.int64)
    kn = karr.astype(np.float64) / np.maximum(narr.astype(np.float64), 1.0)
    T["k_over_n_bucket16"] = np.clip((kn*16).astype(np.int64), 0, 15)
    T["k_over_n_raw"] = kn
    return T

targets = build_targets(n_arr, k_arr)

# NULL: shuffle k (breaks any real (X,Y,n)->k link), same pipeline.
k_shuf = k_arr[rng.permutation(N)]
targets_null = build_targets(n_arr, k_shuf)

# POSITIVE CONTROL: a feature genuinely carrying k = (k mod 97) with 20% noise.
noise = rng.random(N) < 0.20
ctrl = (k_arr % 97).astype(np.int64)
ctrl_noisy = ctrl.copy(); ctrl_noisy[noise] = rng.integers(0, 97, noise.sum())

# ---------------------------------------------------------------------------
# Fast GBM helpers (small models so 100k completes quickly).
# ---------------------------------------------------------------------------
CLF_KW = dict(max_iter=60, max_depth=6, learning_rate=0.2, random_state=SEED, early_stopping=True)
REG_KW = dict(max_iter=60, max_depth=6, learning_rate=0.2, random_state=SEED, early_stopping=True)

def clf_lift(Xm, y, ts=0.30):
    Xtr, Xte, ytr, yte = train_test_split(Xm, y, test_size=ts, random_state=SEED)
    base = np.bincount(yte.astype(np.int64)).max()/len(yte)
    c = HistGradientBoostingClassifier(**CLF_KW).fit(Xtr, ytr)
    acc = accuracy_score(yte, c.predict(Xte))
    return acc, base, acc-base, int(len(np.unique(ytr))), len(yte)

def reg_lift(Xm, y, ts=0.30):
    Xtr, Xte, ytr, yte = train_test_split(Xm, y, test_size=ts, random_state=SEED)
    r = HistGradientBoostingRegressor(**REG_KW).fit(Xtr, ytr)
    pred = r.predict(Xte)
    mae = mean_absolute_error(yte, pred)
    base = mean_absolute_error(yte, np.full_like(yte, np.median(ytr)))
    return mae, base, base-mae, r2_score(yte, pred), len(yte)

MODS = list(range(2, 14))

def pooled_block(Xm, T, tag):
    log(f"\n{'='*96}\n{tag}\n{'='*96}")
    out = {}
    mae, base, lift, r2, nt = reg_lift(Xm, T["k"])
    out["k"] = dict(mae=mae, base=base, lift=lift, r2=r2)
    log(f"  k (reg):            MAE={mae:.4g} base_MAE={base:.4g} MAE-lift={lift:+.4g} R2={r2:.5f} n_test={nt}")
    for m in MODS:
        acc, b, lift, ncl, nt = clf_lift(Xm, T[f"k_mod_{m}"])
        out[f"k_mod_{m}"] = dict(acc=acc, base=b, lift=lift)
        log(f"  k mod {m:2d} ({ncl:2d} cls): acc={acc:.4f} base={b:.4f} lift={lift:+.4f} n_test={nt}")
    acc, b, lift, ncl, nt = clf_lift(Xm, T["k_over_n_bucket16"])
    out["k_over_n_bucket16"] = dict(acc=acc, base=b, lift=lift)
    log(f"  k/n bucket16 (16): acc={acc:.4f} base={b:.4f} lift={lift:+.4f} n_test={nt}")
    mae, base, lift, r2, nt = reg_lift(Xm, T["k_over_n_raw"])
    out["k_over_n_raw"] = dict(mae=mae, base=base, lift=lift, r2=r2)
    log(f"  k/n (reg):          MAE={mae:.4g} base_MAE={base:.4g} MAE-lift={lift:+.4g} R2={r2:.5f} n_test={nt}")
    return out

real_pool = pooled_block(Xmat, targets, "POOLED  (REAL k)")
null_pool = pooled_block(Xmat, targets_null, "POOLED  (NULL: k shuffled)")

# POSITIVE CONTROL: add planted feature, same pipeline.
Xctrl = np.column_stack([Xmat, ctrl_noisy.astype(np.float32)])
log(f"\n{'='*96}\nPOOLED  (POSITIVE CONTROL: +planted feature (k mod 97, 20% noise))\n{'='*96}")
ctrl_pool = {}
for m in (7, 13):
    acc, b, lift, ncl, nt = clf_lift(Xctrl, targets[f"k_mod_{m}"])
    ctrl_pool[f"k_mod_{m}"] = dict(acc=acc, base=b, lift=lift)
    log(f"  k mod {m:2d} (+planted): acc={acc:.4f} base={b:.4f} lift={lift:+.4f} n_test={nt}")
acc, b, lift, ncl, nt = clf_lift(Xctrl, targets["k_over_n_bucket16"])
ctrl_pool["k_over_n_bucket16"] = dict(acc=acc, base=b, lift=lift)
log(f"  k/n bucket16 (+planted): acc={acc:.4f} base={b:.4f} lift={lift:+.4f} n_test={nt}")

# ---------------------------------------------------------------------------
# (b) PER-N STRATIFIED. feature set excludes 'n' (constant within group).
# ---------------------------------------------------------------------------
log(f"\n{'='*96}\nPER-N STRATIFIED (group by n, min 300 rows)\n{'='*96}")
feat_pern = [fn for fn in feat_names if fn != "n"]
Xpern = np.column_stack([feats[fn] for fn in feat_pern]).astype(np.float32)
uniq, cnt = np.unique(n_arr, return_counts=True)
big_n = uniq[cnt >= 300]
log(f"  n with >=300 rows: {sorted(big_n.tolist())}  ({len(big_n)} groups, "
    f"{int(cnt[cnt>=300].sum())}/{N} rows)")

def per_n(karr_src, T_src, tag):
    res = {}
    for tname in ("k_mod_7", "k_mod_13", "k_over_n_bucket16"):
        lifts=[]; accs=[]; bases=[]; w=[]
        for nv in big_n:
            mask = n_arr == nv
            yg = T_src[tname][mask]; Xg = Xpern[mask]
            if len(np.unique(yg)) < 2: continue
            try:
                Xtr, Xte, ytr, yte = train_test_split(Xg, yg, test_size=0.30, random_state=SEED)
            except ValueError:
                continue
            if len(np.unique(ytr)) < 2: continue
            # per-n groups are small; disable early_stopping (its internal
            # stratified val-split fails on singleton classes) for robustness.
            try:
                c = HistGradientBoostingClassifier(
                    max_iter=60, max_depth=6, learning_rate=0.2,
                    random_state=SEED, early_stopping=False).fit(Xtr, ytr)
            except ValueError:
                continue
            acc = accuracy_score(yte, c.predict(Xte))
            base = np.bincount(yte.astype(np.int64)).max()/len(yte)
            lifts.append(acc-base); accs.append(acc); bases.append(base); w.append(len(yte))
        if w:
            wv = np.array(w, float); wv/=wv.sum()
            ml = float(np.average(lifts, weights=wv)); ma=float(np.average(accs, weights=wv)); mb=float(np.average(bases, weights=wv))
        else:
            ml=ma=mb=float('nan')
        res[tname] = dict(mean_lift=ml, mean_acc=ma, mean_base=mb, groups=len(w))
        log(f"  [{tag}] {tname:18s}: groups={len(w):2d} mean_acc={ma:.4f} mean_base={mb:.4f} mean_lift={ml:+.4f}")
    return res

pern_real = per_n(k_arr, targets, "REAL")
pern_null = per_n(k_shuf, targets_null, "NULL")

# ---------------------------------------------------------------------------
# SUMMARY
# ---------------------------------------------------------------------------
log(f"\n{'='*96}\nSUMMARY: pooled held-out lift above base rate  REAL vs NULL vs CONTROL\n{'='*96}")
log(f"{'target':20s} {'REAL lift':>10s} {'NULL lift':>10s} {'CONTROL lift':>13s}")
for key in [f"k_mod_{m}" for m in MODS] + ["k_over_n_bucket16"]:
    rl = real_pool[key]["lift"]; nl = null_pool[key]["lift"]
    cl = ctrl_pool.get(key, {}).get("lift")
    cs = f"{cl:+.4f}" if cl is not None else "n/a"
    log(f"{key:20s} {rl:+10.4f} {nl:+10.4f} {cs:>13s}")
log("\nregression (MAE-lift = base_MAE - model_MAE; positive => beats median baseline):")
log(f"{'target':20s} {'REAL MAE-lift':>14s} {'NULL MAE-lift':>14s} {'REAL R2':>10s} {'NULL R2':>10s}")
for key in ["k", "k_over_n_raw"]:
    r=real_pool[key]; n=null_pool[key]
    log(f"{key:20s} {r['lift']:+14.4g} {n['lift']:+14.4g} {r['r2']:10.5f} {n['r2']:10.5f}")
log("\nPER-N STRATIFIED mean lift (test-size weighted)  REAL vs NULL:")
for tn in ("k_mod_7","k_mod_13","k_over_n_bucket16"):
    r=pern_real[tn]; n=pern_null[tn]
    log(f"  {tn:18s} REAL={r['mean_lift']:+.4f} (g={r['groups']})   NULL={n['mean_lift']:+.4f} (g={n['groups']})")
log(f"\nTotal runtime: {time.time()-t0:.1f}s")
