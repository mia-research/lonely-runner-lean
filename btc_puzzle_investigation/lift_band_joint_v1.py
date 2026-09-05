#!/usr/bin/env python3
"""
lift_band_joint_v1.py -- BUILD + TEST the joint object (curve-side Eisenstein LIFT residual of x)
x (scalar-side BAND / Farey residual of d).  The Part V closure is proved only for BOUNDED-DEGREE
readouts (KS/Weil); eis(X)->(u,v), flap eps, norm s are LATTICE REDUCTIONS (CVP), NOT bounded-degree
rational functions on E -- they sit OUTSIDE the closure.  Every lift LAW we proved is about the
MARGINAL of eis(x_d) over d; none of it touches the JOINT (eis(x_d), derr(d)).  This file builds that
joint and tests it honestly.

DISCIPLINE (btc CLAUDE.md + memory):
 * NO FLOAT in the signal path: eis / enorm / sextant / derr all exact int.  Float only inside the MI
   statistic, and only as a monotone quantity ranked against a MATCHED permutation null (never a
   threshold on the data).
 * Feature computable from PUBLIC (X,Y) -- so a real association would be a leak, not a study of d.
 * FIXED-bits stratum only (App A: derr<->cap is a bit-length confound that dissolves at fixed bits).
 * Matched permutation null (shuffle the target column; preserves both marginals incl. the feature's
   own symmetry) -> bias-corrected I_c = I_raw - mean_null, z = I_c/std_null.
 * Power-scaling discriminator (signal: I_c plateaus, z~sqrt(N); noise: I_c~1/N, z flat).
 * INSTRUMENT CONTROLS every run: a PLANTED-leak target must FIRE; a RANDOM target must stay flat;
   a raw-lowbit feature (X mod 8) is the generic baseline the lift features must BEAT to matter.
 * Grade every line.  A null here is a scoped fact, not a closure.
"""
import sys, csv, math
import numpy as np
from int1_frame_operator_v1 import build_secp
from lift_sextant_rhombus_law_proof_v2 import enorm, sextant

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
EIS, EPS = build_secp()

# ----------------------------------------------------------------------------- exact features
def features(X, Y):
    """All exact-int; keys public.  Return dict name-> (small int cell)."""
    z = EIS(X); u, v = z
    s = enorm(z)                      # in [0, p*3/4], exact int
    sx = sextant(u, v)                # 0..5
    ep = EPS(X)                       # flap 0/1/2
    sig = (u > v) - (u < v)           # sigma = sign(u-v) in {-1,0,1}
    xy = (X * Y) % P
    sign_xy = 1 if xy < (P >> 1) else 0
    return {
        'sextant':  sx,               # 6 cells
        'flap_eps': ep,               # 3
        'sigma':    sig + 1,          # 3
        'u_sign':   (1 if u >= 0 else 0),
        'v_sign':   (1 if v >= 0 else 0),
        'sign_xy':  sign_xy,          # odd-in-d (needs y): the shadow-subspace bit
        's_raw':    s,                # continuous -> quantile-binned later
        'CTRL_Xlow': X & 7,           # generic baseline (raw low bits of X); must be at floor
    }

# ----------------------------------------------------------------------------- exact targets
def targets(d, n, k, D, bits):
    A = 1 << (bits - 1)
    off = d - A
    derr = abs(n * off - k * A)       # exact residual with the STORED (n,k)
    return {
        'derr':   derr,               # continuous -> quantile
        'k_mod8': k & 7,
        'n_mod8': n % 8,
        'D_mod8': D & 7,              # low bits of the curve-identity residual (signature lives low)
        'D_mod16': D & 15,
        'D_abs':  abs(D),             # continuous -> quantile
    }

def quantile_cells(vals, q=8):
    """Rank-based binning into q cells; exact integer ranks, no float threshold on data."""
    order = np.argsort(np.argsort(vals, kind='stable'), kind='stable')
    n = len(vals)
    return (order * q // n).astype(np.int64)

# ----------------------------------------------------------------------------- MI + matched null
def mi_bits(fc, tc):
    """MI in bits from integer cell labels via contingency counts."""
    nf = fc.max() + 1; nt = tc.max() + 1
    joint = np.zeros((nf, nt), dtype=np.float64)
    np.add.at(joint, (fc, tc), 1.0)
    N = joint.sum(); joint /= N
    pf = joint.sum(1, keepdims=True); pt = joint.sum(0, keepdims=True)
    with np.errstate(divide='ignore', invalid='ignore'):
        r = joint / (pf * pt)
        term = joint * np.log2(np.where(joint > 0, r, 1.0))
    return float(np.nansum(term))

def test_pair(fc, tc, R=200, rng=None):
    rng = rng or np.random.default_rng(0)
    Iraw = mi_bits(fc, tc)
    nulls = np.empty(R)
    tcs = tc.copy()
    for i in range(R):
        rng.shuffle(tcs)
        nulls[i] = mi_bits(fc, tcs)
    mu, sd = nulls.mean(), nulls.std() + 1e-12
    return Iraw - mu, (Iraw - mu) / sd            # I_c (bits), z

# ----------------------------------------------------------------------------- data loader
def load_stratum(path, bits, cols, cap=None):
    rows = []
    with open(path) as f:
        r = csv.DictReader(f)
        bkey = 'N' if 'N' in r.fieldnames else 'bits'
        for row in r:
            if int(row[bkey]) != bits:
                continue
            rows.append(row)
            if cap and len(rows) >= cap:
                break
    out = {c: [] for c in cols}
    for row in rows:
        for c in cols:
            out[c].append(row[c])
    return out

# ----------------------------------------------------------------------------- main
def run(path, bits, label, R=200, cap=None):
    print("=" * 92)
    print("JOINT LIFT-RESIDUAL x BAND-RESIDUAL  --  %s  bits=%d  (%s)" % (label, bits, path))
    print("=" * 92)
    need = ['d', 'X', 'Y', 'n', 'k', 'D']
    D = load_stratum(path, bits, need, cap=cap)
    Nrows = len(D['d'])
    print("stratum rows = %d" % Nrows)
    ds = [int(x) for x in D['d']]
    Xs = [int(x, 16) for x in D['X']]
    Ys = [int(x, 16) for x in D['Y']]
    ns = [int(x) for x in D['n']]
    ks = [int(x) for x in D['k']]
    Ds = [int(x) for x in D['D']]

    # ---- exact feature + target columns
    Fnames = ['sextant', 'flap_eps', 'sigma', 'u_sign', 'v_sign', 'sign_xy', 's_raw', 'CTRL_Xlow']
    Fcols = {nm: [] for nm in Fnames}
    for X, Y in zip(Xs, Ys):
        fv = features(X, Y)
        for nm in Fnames:
            Fcols[nm].append(fv[nm])
    Tnames = ['derr', 'k_mod8', 'n_mod8', 'D_mod8', 'D_mod16', 'D_abs']
    Tcols = {nm: [] for nm in Tnames}
    for d, n, k, Dd in zip(ds, ns, ks, Ds):
        tv = targets(d, n, k, Dd, bits)
        for nm in Tnames:
            Tcols[nm].append(tv[nm])

    # ---- to cell arrays (quantile-bin the continuous ones)
    def cells(name, vals):
        if name in ('s_raw', 'derr', 'D_abs'):
            ranks = _rankvals(vals)                 # exact integer ranks (arbitrary-precision safe)
            return (ranks * 8 // len(vals)).astype(np.int64)
        return np.array([int(x) for x in vals], dtype=np.int64)
    Fc = {nm: cells(nm, Fcols[nm]) for nm in Fnames}
    Tc = {nm: cells(nm, Tcols[nm]) for nm in Tnames}

    rng = np.random.default_rng(12345)
    # ---- INSTRUMENT CONTROLS -----------------------------------------------------------
    print("\n-- instrument controls (must behave before trusting any cell) --")
    base = Fc['sextant']
    # positive: target = feature-derived, planted at strength f
    for f in (0.30, 0.05):
        planted = base.copy()
        m = rng.random(Nrows) > f          # keep fraction f aligned, rest randomized
        planted[m] = rng.integers(0, 6, m.sum())
        Ic, z = test_pair(base, planted % 8, R=R, rng=rng)
        print("  PLANTED f=%.2f (sextant->target): I_c=%+.5f bits  z=%+.1f   [want FIRE]" % (f, Ic, z))
    # negative: random target
    Ic, z = test_pair(base, rng.integers(0, 8, Nrows), R=R, rng=rng)
    print("  RANDOM target:                       I_c=%+.5f bits  z=%+.1f   [want FLAT]" % (Ic, z))

    # ---- FULL GRID ---------------------------------------------------------------------
    print("\n-- feature x target grid:  I_c (bits, bias-corrected) / z  (R=%d shuffles) --" % R)
    hdr = "%-11s" % "feature\\tgt" + "".join("%13s" % t for t in Tnames)
    print(hdr)
    results = []
    for fn in Fnames:
        line = "%-11s" % fn
        for tn in Tnames:
            Ic, z = test_pair(Fc[fn], Tc[tn], R=R, rng=rng)
            results.append((abs(z), z, Ic, fn, tn))
            line += "%13s" % ("%+.4f/%+.1f" % (Ic, z))
        print(line)

    # ---- rank + flag top cells (excluding CTRL baseline reference) ----------------------
    results.sort(reverse=True)
    print("\n-- top cells by |z| (lift feature must beat CTRL_Xlow baseline to matter) --")
    ctrl_z = max(abs(z) for az, z, Ic, fn, tn in results if fn == 'CTRL_Xlow')
    print("   CTRL_Xlow baseline |z|_max = %.1f  (generic floor)" % ctrl_z)
    for az, z, Ic, fn, tn in results[:8]:
        flag = "  <-- ABOVE baseline" if (az > ctrl_z + 1.0 and fn != 'CTRL_Xlow') else ""
        print("   %-11s x %-8s  I_c=%+.5f  z=%+.1f%s" % (fn, tn, Ic, z, flag))
    return Fc, Tc, results

def _rankvals(vals):
    # accept python ints (arbitrary precision) -> exact rank order without float
    idx = sorted(range(len(vals)), key=lambda i: int(vals[i]))
    r = np.empty(len(vals), dtype=np.int64)
    for rank, i in enumerate(idx):
        r[i] = rank
    return r

# ---- power-scaling of a chosen (feature,target) cell -----------------------------------
def power_scale(Fc, Tc, fn, tn, Ngrid, reps=6, R=120):
    print("\n-- POWER-SCALING  %s x %s  (signal: I_c plateau + z~sqrt(N); noise: I_c~1/N, z flat) --"
          % (fn, tn))
    fcell, tcell = Fc[fn], Tc[tn]
    Ntot = len(fcell)
    rng = np.random.default_rng(7)
    xs, ys_ic, ys_z = [], [], []
    for N in Ngrid:
        if N > Ntot:
            continue
        ics, zs = [], []
        for _ in range(reps):
            sel = rng.choice(Ntot, N, replace=False)
            Ic, z = test_pair(fcell[sel], tcell[sel], R=R, rng=rng)
            ics.append(Ic); zs.append(z)
        xs.append(N); ys_ic.append(np.mean(ics)); ys_z.append(np.mean(zs))
        print("   N=%6d  I_c=%+.6f  z=%+.2f" % (N, np.mean(ics), np.mean(zs)))
    if len(xs) >= 3:
        lx = np.log(np.array(xs)); lic = np.log(np.abs(np.array(ys_ic)) + 1e-12)
        slope = np.polyfit(lx, lic, 1)[0]
        print("   log-log slope of |I_c| vs N = %+.2f   (~0 => SIGNAL plateau ; ~-1 => NOISE)" % slope)

def run_real82(path='solved_keys_augmented_v1.csv', R=400):
    """Real 82 solved keys.  Pooled across bit-lengths (1 key/bits => cannot fix bits) so the App-A
    bit-length confound is UNCONTROLLED here; underpowered (n=82).  Consistency check only, not a
    powered test.  derr is stored directly."""
    print("\n" + "=" * 92)
    print("REAL 82 solved keys -- pooled (bit-length confound UNCONTROLLED; n=82 underpowered)")
    print("=" * 92)
    rows = list(csv.DictReader(open(path)))
    Fnames = ['sextant', 'flap_eps', 'sigma', 'sign_xy', 's_raw', 'CTRL_Xlow']
    Fcols = {nm: [] for nm in Fnames}
    derr = []; kk = []; nn = []; nD = []
    for row in rows:
        X = int(row['X'], 16); Y = int(row['Y'], 16)
        fv = features(X, Y)
        for nm in Fnames:
            Fcols[nm].append(fv[nm])
        derr.append(int(row['derr'])); kk.append(int(row['k'])); nn.append(int(row['n']))
        nD.append(int(row['n_Dterms']))
    N = len(rows)
    def qc(vals, q=4):
        r = _rankvals(vals); return (r * q // len(vals)).astype(np.int64)
    Fc = {nm: (qc(Fcols[nm]) if nm == 's_raw' else np.array([int(v) for v in Fcols[nm]]))
          for nm in Fnames}
    Tc = {'derr': qc(derr), 'k_mod4': np.array([v & 3 for v in kk]),
          'n_mod4': np.array([v % 4 for v in nn]), 'nDterms': np.array(nD) - min(nD)}
    rng = np.random.default_rng(99)
    print("rows=%d   feature x target  I_c (bits) / z   (coarse 4-cell bins; R=%d)" % (N, R))
    for fn in Fnames:
        line = "%-10s" % fn
        for tn in ['derr', 'k_mod4', 'n_mod4', 'nDterms']:
            Ic, z = test_pair(Fc[fn], Tc[tn], R=R, rng=rng)
            line += "%13s" % ("%+.3f/%+.1f" % (Ic, z))
        print(line + "   [tgts: derr k_mod4 n_mod4 nDterms]")


if __name__ == '__main__':
    FULL = 'constructed_keys_fullrange_v1.csv'
    Fc, Tc, res = run(FULL, 256, 'constructed(MT-pipeline)', R=200)
    # power-scale the single strongest lift cell + one reference
    top = next((r for r in res if r[3] != 'CTRL_Xlow'), None)
    if top:
        power_scale(Fc, Tc, top[3], top[4], [500, 1000, 2000, 5000, 10000, 20000])
    # positive-control power-scaling proof the ramp works on THIS instrument
    print("\n-- (sanity) power-scaling a PLANTED f=0.05 leak on the same N grid --")
    rng = np.random.default_rng(1)
    base = Fc['sextant']; Nrows = len(base)
    planted = base.copy(); m = rng.random(Nrows) > 0.05
    planted[m] = rng.integers(0, 6, m.sum())
    Tc2 = dict(Tc); Tc2['_PLANT'] = planted % 8
    power_scale(Fc, Tc2, 'sextant', '_PLANT', [500, 1000, 2000, 5000, 10000, 20000])
    run_real82()
