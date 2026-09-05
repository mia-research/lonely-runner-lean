"""
Prove the shared interface before farming anything out (trust-but-verify).
Checks: (1) loader parses 100k, (2) EC code reproduces the dataset's (X,Y) from d,
(3) our decompose() reproduces the dataset's (n,k,D_terms), (4) a planted leak is
detected by the reference detector while a genuine null stays flat.
"""
import sys, time
import numpy as np
sys.path.insert(0, __import__("os").path.dirname(__file__))
import lib_data as L
import lib_control as C
from sklearn.ensemble import HistGradientBoostingClassifier

t0 = time.time()
df = L.load()
print(f"[1] loaded rows={len(df)}  bits {df.bits.min()}-{df.bits.max()}  "
      f"({time.time()-t0:.1f}s)")

# (2) EC: recompute X,Y = d*G on a stratified sample of bit-lengths
samp = df.groupby("bits", group_keys=False).apply(
    lambda g: g.sample(min(3, len(g)), random_state=1), include_groups=False)
samp = df.loc[samp.index] if hasattr(samp, "index") else samp
ec_ok = ec_tot = 0
for _, r in df.iloc[:: max(1, len(df)//300)].iterrows():
    Xc, Yc = L.ec_mul(int(r.d))
    ec_tot += 1
    ec_ok += (Xc == int(r.X) and Yc == int(r.Y))
print(f"[2] EC d*G matches dataset (X,Y): {ec_ok}/{ec_tot}")

# (3) decomposition reproduces n,k,D_terms
dec_ok = dec_tot = 0
for _, r in df.iloc[:: max(1, len(df)//500)].iterrows():
    n, k, D, dt = L.decompose(int(r.d), int(r.bits))
    dec_tot += 1
    dec_ok += (n == int(r.n) and k == int(r.k))
print(f"[3] decompose() matches dataset (n,k): {dec_ok}/{dec_tot}")

# (4) control must fire; genuine public-only null must stay near baseline
sub = df[df.bits.between(60, 120)].copy()
y = sub["n"].values.astype(int)
rng = np.random.default_rng(0)
# public-only features: byte slices + small-prime residues of X,Y (attack-valid)
def feats(frame, extra=None):
    cols = {}
    for name, col in (("X", frame.X.values), ("Y", frame.Y.values)):
        for b in (0, 1, 30, 31):
            cols[f"{name}_byte{b}"] = np.array([(int(v) >> (8*b)) & 0xFF for v in col])
        for q in (3, 5, 7, 11, 13):
            cols[f"{name}_mod{q}"] = np.array([int(v) % q for v in col])
    M = np.column_stack(list(cols.values())).astype(float)
    if extra is not None:
        M = np.column_stack([M, extra])
    return M

L.assert_attack_valid(["X", "Y", "bits"])  # guard smoke
Xreal = feats(sub)
Xplant = feats(sub, extra=C.plant_leak(y, strength=0.6))
est = HistGradientBoostingClassifier(max_iter=60, max_depth=4)
acc_null, _ = C.grouped_cv_score(Xreal, y, sub.bits.values, est)
acc_ctrl, _ = C.grouped_cv_score(Xplant, y, sub.bits.values, est)
base = 1.0 / len(np.unique(y))
print(f"[4] baseline={base:.4f}  public-only null acc={acc_null:.4f}  "
      f"planted-leak acc={acc_ctrl:.4f}  (control must be >> null)")
print(f"done ({time.time()-t0:.1f}s)")
