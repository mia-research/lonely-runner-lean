#!/usr/bin/env python3
"""
row_budget_run_v1.py — executes PREREG_row_budget_lowtail_v1.md (frontier #17).

Primary   N_LOW(f) = #{a != 0 : |U(a,f)|^2 < 0.01 (n-1)}      integer count
          Nbar(p)  = mean over the frozen frequency list
Verdict   z_p, exact rank-p of Nbar_char in the MN-mu6 replicate distribution.

NULL LADDER (all are d-relabellings, so all preserve unit modulus, the exact
value multiset, the row budget sum_a rho = n, and the a=0 row -- exactly):
    MN-mu6   pi commutes with d -> +-lambda^i d     (PRIMARY)
    MN-neg   pi commutes with d -> -d
    MN-free  any permutation (= prior MC2, transposed)   generic stratum only
    REF-RAY  analytic reference (n-1)(1-e^-0.01); a scale, never a verdict null

Exact integers in the signal path: the exponent (b*x_d + c*y_d) mod p, the
orbit/permutation index arithmetic, and every count.  Float only in the FFT and
the moments taken from it, never as a threshold applied to raw data.
"""
import argparse, hashlib, json, sys
import numpy as np
from row_budget_core_v1 import curve_orbit

FREQS = "PREREG_row_budget_lowtail_v1_FREQS.txt"
FREQS_SHA = "9695989bcd52777dc3e3012477dd460f5f29ffcd0da099d09bf7294d983005f3"
R_DEFAULT = 64
THRESH = 0.01                      # rho < 0.01  <=>  r < 0.10
SPEC_N = {163: 139, 211: 199, 349: 313, 433: 397, 577: 613, 991: 1009,
          2089: 2143, 4159: 4243, 9319: 9127, 19231: 19501}
SPEC_BETA = {163: 58, 211: 14, 349: 122, 433: 198, 577: 213, 991: 113,
             2089: 826, 4159: 1604, 9319: 3138, 19231: 9365}


# ------------------------------------------------------------------ inputs
def load_freqs(path=FREQS, sha=FREQS_SHA):
    raw = open(path, "rb").read()
    h = hashlib.sha256(raw).hexdigest()
    assert h == sha, f"FREQ LIST HASH MISMATCH {h}"
    out = {}
    for line in raw.decode().splitlines():
        if line.startswith("#") or not line.strip():
            continue
        p, b, c = (int(t) for t in line.split())
        out.setdefault(p, []).append((b, c))
    return out, h


# --------------------------------------------------------- mu6 orbit machinery
def mu6_orbits(n, lam):
    """{1..n-1} under <lambda,-1>; returns rep[], orb_of[], unit_of[], g."""
    g = (n - lam) % n                       # -lambda has order 6 (3 x 2, coprime)
    pw = [1] * 6
    for i in range(1, 6):
        pw[i] = pw[i - 1] * g % n
    assert pw[1] != 1 and pow(g, 6, n) == 1 and len({x for x in pw}) == 6, "g not order 6"
    orb_of = np.full(n, -1, dtype=np.int64)
    unit_of = np.zeros(n, dtype=np.int64)
    reps = []
    for d in range(1, n):
        if orb_of[d] >= 0:
            continue
        o = len(reps); reps.append(d)
        for k in range(6):
            e = pw[k] * d % n
            orb_of[e] = o; unit_of[e] = k
    return np.array(reps, dtype=np.int64), orb_of, unit_of, np.array(pw, dtype=np.int64)


def neg_orbits(n):
    orb_of = np.full(n, -1, dtype=np.int64)
    unit_of = np.zeros(n, dtype=np.int64)
    reps = []
    for d in range(1, n):
        if orb_of[d] >= 0:
            continue
        o = len(reps); reps.append(d)
        orb_of[d] = o; unit_of[d] = 0
        orb_of[n - d] = o; unit_of[n - d] = 1
    return np.array(reps, dtype=np.int64), orb_of, unit_of, np.array([1, n - 1], dtype=np.int64)


class Permuter:
    """pi commuting with the given unit group; exact integer index arithmetic."""

    def __init__(self, n, reps, orb_of, unit_of, pw):
        self.n, self.reps, self.orb_of, self.unit_of, self.pw = n, reps, orb_of, unit_of, pw
        self.U = len(pw)
        self.d = np.arange(n, dtype=np.int64)

    def draw(self, rng):
        n, U = self.n, self.U
        no = len(self.reps)
        sig = rng.permutation(no)
        uo = rng.integers(0, U, no)
        # pi(d) = g^{k(d)} * g^{u_{o(d)}} * rep[sigma(o(d))]
        o = self.orb_of[1:]; k = self.unit_of[1:]
        newk = (k + uo[o]) % U
        pi = self.pw[newk] * self.reps[sig[o]] % n
        out = np.empty(n, dtype=np.int64); out[0] = 0; out[1:] = pi
        return out


def free_perm(n, rng):
    out = np.empty(n, dtype=np.int64); out[0] = 0
    out[1:] = rng.permutation(np.arange(1, n, dtype=np.int64))
    return out


# ------------------------------------------------------------------- statistic
def nlow_batch(S, n):
    """S: (rows, n) complex targets with S[:,0]=0. Returns N_LOW per row, budgets."""
    U2 = np.abs(np.fft.fft(S, axis=1)) ** 2
    budget = U2.sum(1)
    rho = U2 / (n - 1)
    return (rho[:, 1:] < THRESH).sum(1), budget, rho


def run_prime(p, freqs, R, rng, verbose=True):
    r = curve_orbit(p)
    assert r is not None, f"p={p} no prime-order curve"
    X, Y, n = r
    assert n == SPEC_N[p], f"n mismatch {n} vs spec {SPEC_N[p]}"
    beta = SPEC_BETA[p]
    assert pow(beta, 3, p) == 1 and beta != 1, f"beta {beta} not order 3 mod {p}"

    # lambda from the curve data, then C-EQ-int
    xb = beta * X[1] % p
    lam = int(np.nonzero((X == xb) & (Y == Y[1]))[0][0])
    idx = (lam * np.arange(n)) % n
    ceq = int(np.max((X[idx] - beta * X) % p))
    assert ceq == 0, f"C-EQ-int FAILED at p={p}: {ceq}"

    reps6, orb6, unit6, pw6 = mu6_orbits(n, lam)
    reps2, orb2, unit2, pw2 = neg_orbits(n)
    P6 = Permuter(n, reps6, orb6, unit6, pw6)
    P2 = Permuter(n, reps2, orb2, unit2, pw2)
    assert len(reps6) == (n - 1) // 6, "mu6 orbit count wrong"

    tab = np.exp(2j * np.pi * np.arange(p) / p)
    F = freqs[p]; m = len(F)

    tot = {"char": 0.0, "mu6": np.zeros(R), "neg": np.zeros(R), "free": np.zeros(R)}
    budget_worst = 0.0; a0_worst = 0.0
    s3_char = []; s3_mu6 = []
    s5_counts = np.zeros(len(reps6))

    for (b, c) in F:
        e = (b * X + c * Y) % p                       # exact integer exponent
        s = tab[e]; s[0] = 0.0

        rows = [s]
        for _ in range(R): rows.append(s[P6.draw(rng)])
        for _ in range(R): rows.append(s[P2.draw(rng)])
        for _ in range(R): rows.append(s[free_perm(n, rng)])
        S = np.array(rows)
        NL, bud, rho = nlow_batch(S, n)

        budget_worst = max(budget_worst, float(np.max(np.abs(bud - n * (n - 1)))) / (n * (n - 1)))
        # C-A0: the a=0 row is identical in every arm
        U0 = np.fft.fft(S, axis=1)[:, 0]
        a0_worst = max(a0_worst, float(np.max(np.abs(U0 - U0[0]))) / max(1e-30, abs(U0[0])))

        tot["char"] += NL[0]
        tot["mu6"] += NL[1:1 + R]
        tot["neg"] += NL[1 + R:1 + 2 * R]
        tot["free"] += NL[1 + 2 * R:]

        kk = int(np.ceil(THRESH * (n - 1)))
        s3_char.append(np.partition(rho[0, 1:], kk - 1)[kk - 1])
        s3_mu6.append(np.partition(rho[1, 1:], kk - 1)[kk - 1])
        low = np.nonzero(rho[0, 1:] < THRESH)[0] + 1
        if low.size:
            s5_counts += np.bincount(orb6[low], minlength=len(reps6))

    Nbar = {k: (v / m if k == "char" else v / m) for k, v in tot.items()}
    ref = (n - 1) * (1 - np.exp(-THRESH))
    z = float((Nbar["char"] - Nbar["mu6"].mean()) / Nbar["mu6"].std(ddof=1))
    rank = (1 + int((Nbar["mu6"] >= Nbar["char"]).sum())) / (R + 1.0)

    # exact realizable extremes on THIS n
    d = np.arange(n)
    chirp = np.exp(2j * np.pi * (d * d % n) / n); chirp[0] = 0
    tone = np.exp(-2j * np.pi * (3 * d % n) / n); tone[0] = 0
    ext, _, _ = nlow_batch(np.array([chirp, tone]), n)

    # S5: mu6-orbit occupancy of the low set, chi^2 vs uniform-over-orbits
    exp5 = s5_counts.sum() / len(reps6)
    s5chi = float(((s5_counts - exp5) ** 2 / exp5).sum()) if exp5 > 0 else float("nan")
    s5df = len(reps6) - 1
    s5z = (s5chi - s5df) / np.sqrt(2 * s5df)

    out = dict(p=p, n=n, m=m, lam=lam, beta=beta, ceq=ceq,
               Nbar_char=float(Nbar["char"]),
               Nbar_mu6=float(Nbar["mu6"].mean()), sd_mu6=float(Nbar["mu6"].std(ddof=1)),
               Nbar_neg=float(Nbar["neg"].mean()), Nbar_free=float(Nbar["free"].mean()),
               ref_ray=float(ref), z=z, rank_p=rank,
               chirp=int(ext[0]), tone=int(ext[1]), tone_expect=n - 2,
               budget_relerr=budget_worst, a0_relerr=a0_worst,
               s3_char=float(np.median(s3_char)), s3_mu6=float(np.median(s3_mu6)),
               s5_chi2=s5chi, s5_df=s5df, s5_z=float(s5z))
    if verbose:
        print(f"  p={p:>6} n={n:>6} m={m:>6}  lam={lam}  "
              f"C-EQ-int={ceq}  C-BUDGET={budget_worst:.1e}  C-A0={a0_worst:.1e}")
        print(f"     N_LOW  char {out['Nbar_char']:>10.3f} | MN-mu6 {out['Nbar_mu6']:>10.3f}"
              f" +-{out['sd_mu6']:.3f} | MN-neg {out['Nbar_neg']:>10.3f}"
              f" | MN-free {out['Nbar_free']:>10.3f} | REF-RAY {ref:>10.3f}")
        print(f"     chirp={out['chirp']} (must be 0)   tone={out['tone']} "
              f"(must be {n-2})   z={z:+.2f}  rank-p={rank:.4f}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--primes", default="163,211,349,433")
    ap.add_argument("--R", type=int, default=R_DEFAULT)
    ap.add_argument("--out", default="row_budget_run_v1_rows.json")
    a = ap.parse_args()
    freqs, h = load_freqs()
    print(f"  frozen frequency list sha256 {h[:24]}...  OK")
    rng = np.random.default_rng(20260724)
    rows = []
    for p in [int(t) for t in a.primes.split(",")]:
        rows.append(run_prime(p, freqs, a.R, rng))
        json.dump(rows, open(a.out, "w"), indent=1)
    zs = np.array([r["z"] for r in rows])
    print(f"\n  pooled Stouffer Z = {zs.sum()/np.sqrt(len(zs)):+.3f}   "
          f"sign test {int((zs<0).sum())}/{len(zs)} negative")


if __name__ == "__main__":
    main()
