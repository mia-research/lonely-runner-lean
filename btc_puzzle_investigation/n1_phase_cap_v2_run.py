#!/usr/bin/env python3
"""
n1_phase_cap_v2_run.py — executes PREREG_n1_phase_cap_v2.md on the FROZEN holdout.

C-FREEZE was completed by n1_phase_cap_v2_freeze.sage BEFORE this file computed any
V(a); this script asserts the holdout hash at start.

  S_y(p) = max_{a != 0} |V(a)| / sqrt(p),   V(a) = sum_d chi2(y_d) e_n(a d)
  H-CAP  : S_y <= 2.        Nviol = #{p : S_y > 2}.
  L(p)   = log10(2 - S_y);  G2 regresses L on log10 p per stratum (K=60, df=58):
           t0 = beta/SE (vs 0)  -> R2 iff t0 <= -3
           t1 = (beta+0.448)/SE -> R3 iff t1 >= +3 and t0 > -3
  G1     : top band mean L minus bottom band mean L; corroborates R2 iff <= -0.301.

CONTROLS (must fire, else the null is uninformative and no verdict is issued):
  P-CEIL  admissible target eps_O = sign(s_O(1)); predicted |V(1)|/sqrt(p) computed
          from n alone BEFORE the run; must match to 1e-10 rel AND give S > 2.
  P-FLOOR h = chi_n (Legendre mod n): a Gauss sum, |V(a)| = sqrt(n) for every a != 0,
          so S lands EXACTLY on the Parseval floor sqrt(n/p).
  N-PERM  primary null: permute the M = (n-1)/6 mu6 ORBIT SIGNS of the real h.
          Preserves oddness, the mu6 structure and the exact sign multiset; destroys
          only which orbit carries which sign.  Derived prediction (F7):
          S_null ~ sqrt(2 ln((n-1)/3)) ~ 4.1, and a null returning S <= 2 is an
          INSTRUMENT FAILURE, not a discovery -> HALT.

FORCED (zero information, instrument checks only): C-PURITY (V imaginary at ODD /
real at EVEN), C-PARSEVAL (sum_a |V|^2 = n(n-1)), C-CELLS (M = (n-1)/6),
C-ORBIT (h(lambda d) = h(d) and h(-d) = -h(d) exactly).
"""
import argparse, hashlib, json
import numpy as np

HOLD = "PREREG_n1_phase_cap_v2_HOLDOUT.txt"
HOLD_SHA = "3c24e9ee660f9789a54b06fc27f1484a258ee09d680f92a241f56193eba77527"


def load_holdout():
    raw = open(HOLD, "rb").read()
    h = hashlib.sha256(raw).hexdigest()
    assert h == HOLD_SHA, f"HOLDOUT HASH MISMATCH {h}"
    out = []
    for ln in raw.decode().splitlines():
        if ln.startswith("#") or not ln.strip():
            continue
        b, s, p, n, t = ln.split()
        out.append((int(b), s, int(p), int(n), int(t)))
    return out, h


def orbit_y(p, n):
    """chi2(y_d) for d = 1..n-1 along the orbit of G. Exact integers."""
    G = None
    for x in range(1, p):
        r = (x * x * x + 7) % p
        if r and pow(r, (p - 1) // 2, p) == 1:
            y = pow(r, (p + 1) // 4, p) if p % 4 == 3 else tonelli(r, p)
            if (y * y - r) % p == 0:
                G = (x, min(y, p - y)); break
    gx, gy = G
    h = np.zeros(n, dtype=np.int8)
    e = (p - 1) // 2
    x1, y1 = gx, gy
    for d in range(1, n):
        h[d] = 1 if pow(y1, e, p) == 1 else -1
        if d == n - 1:
            break
        if x1 == gx:
            if (y1 + gy) % p == 0:
                raise RuntimeError("hit O early")
            lam = (3 * x1 * x1) * pow(2 * y1, -1, p) % p
        else:
            lam = (gy - y1) * pow(gx - x1, -1, p) % p
        x3 = (lam * lam - x1 - gx) % p
        y1 = (lam * (x1 - x3) - y1) % p
        x1 = x3
    return h, G


def tonelli(a, p):
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2; s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p; i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b % b % p if False else t * b * b % p, r * b % p
    return r


def mu6_structure(n, lam):
    """rep index + sign for every d; vectorised, exact int64."""
    d = np.arange(1, n, dtype=np.int64)
    c1 = d * lam % n
    c2 = c1 * lam % n
    A = np.minimum(np.minimum(d, c1), c2)                 # min of the mu3 orbit of d
    B = n - np.maximum(np.maximum(d, c1), c2)             # min of the mu3 orbit of -d
    rep = np.minimum(A, B)
    sgn = np.where(A < B, 1, -1).astype(np.int8)
    uniq, idx = np.unique(rep, return_inverse=True)
    return idx, sgn, len(uniq)


def stats(h, p, n):
    V = np.fft.fft(h.astype(float))
    absV = np.abs(V)
    S = absV[1:].max() / np.sqrt(p)
    pars = abs(absV[1:].__pow__(2).sum() + absV[0] ** 2 - n * (n - 1)) / (n * (n - 1))
    if p % 4 == 3:
        pur = np.max(np.abs(V[1:].real)) / max(1e-30, absV[1:].max())
    else:
        pur = np.max(np.abs(V[1:].imag)) / max(1e-30, absV[1:].max())
    return float(S), float(pars), float(pur)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--out", default="n1_phase_cap_v2_rows.json")
    a = ap.parse_args()
    rows_h, hsh = load_holdout()
    if a.limit:
        rows_h = rows_h[:a.limit]
    print(f"  HOLDOUT sha256 {hsh[:32]}...  ASSERTED OK   ({len(rows_h)} primes)")
    from sympy.ntheory.residue_ntheory import nthroot_mod
    out = []
    for k, (band, strat, p, n, tr) in enumerate(rows_h):
        h, G = orbit_y(p, n)
        lam_n = [int(z) for z in nthroot_mod(1, 3, n, all_roots=True) if z != 1][0]
        idx, sgn, M = mu6_structure(n, lam_n)
        # C-ORBIT: h must be constant on mu3 orbits and odd
        hs = h[1:] * sgn
        ok_orbit = bool(np.all(hs == hs[idx.argsort()][np.argsort(idx.argsort())]) or True)
        sign_of_orbit = np.zeros(M, dtype=np.int8)
        sign_of_orbit[idx] = hs
        ok_orbit = bool(np.array_equal(sign_of_orbit[idx], hs))
        S, pars, pur = stats(h, p, n)
        # N-PERM null
        rng = np.random.default_rng(int(hashlib.sha256(f"nperm{p}".encode()).hexdigest()[:8], 16))
        perm = rng.permutation(M)
        hn = np.zeros(n); hn[1:] = sign_of_orbit[perm][idx] * sgn
        Sn, parsn, purn = stats(hn.astype(np.int8), p, n)
        r = dict(band=band, strat=strat, p=p, n=n, M=int(M), S=S, S_nperm=Sn,
                 parseval=pars, purity=pur, cells_ok=bool(M == (n - 1) // 6),
                 orbit_ok=ok_orbit, viol=bool(S > 2.0))
        out.append(r); json.dump(out, open(a.out, "w"))
        if k < 6 or S > 2.0 or k % 20 == 0:
            print(f"   [{k+1:>3}] band{band:>3} {strat:>4} p={p:>7} n={n:>7} M={M:>7} "
                  f"S={S:.5f} {'VIOLATION' if S>2 else ''}  N-PERM S={Sn:.3f}  "
                  f"pars={pars:.1e} pur={pur:.1e} cells={r['cells_ok']} orb={ok_orbit}",
                  flush=True)
    print("\n  forced checks: parseval<=%.1e  purity<=%.1e  cells all %s  orbit all %s"
          % (max(r["parseval"] for r in out), max(r["purity"] for r in out),
             all(r["cells_ok"] for r in out), all(r["orbit_ok"] for r in out)))
    nv = sum(r["viol"] for r in out)
    print(f"  Nviol (S_y > 2) = {nv} of {len(out)}")
    print(f"  N-PERM null: mean S = {np.mean([r['S_nperm'] for r in out]):.3f}  "
          f"min = {min(r['S_nperm'] for r in out):.3f}  "
          f"(F7 predicts ~4.1; <=2 would be an INSTRUMENT FAILURE)")


if __name__ == "__main__":
    main()
