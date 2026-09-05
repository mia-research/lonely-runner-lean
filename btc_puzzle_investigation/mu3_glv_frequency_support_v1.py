#!/usr/bin/env python3
"""
mu3_glv_frequency_support_v1.py — runner for PREREG_mu3_glv_frequency_support_v1/v2.md.

Tests whether the sub-Rayleigh deficit's near-zero harmonics of U(a0,b,c) are mu3/GLV-clustered
in the b-frequency, on the CM curve y^2=x^3+7, vs a matched marginal-preserving null (Null-B).

  U(a,b,c) = sum_{d=1}^{n-1} e_p(b x_d + c y_d) e_n(a d),  (x_d,y_d)=coords of [d]G.

PRIMARY  S = sum_{a0-reps, c, mu6-orbits O} C(k_{O,c},2), k = #near-zeros (rho<tau) in the mu3-triple.
NULL-B   within column c, random equipartition of the K near-zero labels into the R/3 triples
         (marginal-preserving). Exact moments used (validated vs empirical perm in --selftest).
SECONDARY S_GLV = Var(orbit means of |U|^2) / Var(|U|^2)   [descriptive, high-tail tracking].
CONTROLS  plant (must fire), negative-scatter (must not), forced-diagonal implementation self-test.

Exact int point/index path; float carve-out only in |U| magnitudes (roots of unity, no key in path).
The rho<tau label is monotone and ranked against the INTEGER equipartition null; no float decides a verdict.
"""
import sys, math, argparse
import numpy as np

# ---------------- exact EC arithmetic over F_p ----------------
def inv(x, m): return pow(x % m, -1, m)
def legendre(a, q):
    a %= q
    return 0 if a == 0 else (1 if pow(a, (q-1)//2, q) == 1 else -1)
def sqrt_mod(a, m):
    a %= m
    if a == 0: return 0
    if pow(a, (m-1)//2, m) != 1: return None
    if m % 4 == 3: return pow(a, (m+1)//4, m)
    q = m-1; s = 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (m-1)//2, m) != m-1: z += 1
    M, c, t, R = s, pow(z, q, m), pow(a, q, m), pow(a, (q+1)//2, m)
    while t != 1:
        i, tt = 0, t
        while tt != 1: tt = tt*tt % m; i += 1
        be = pow(c, 1 << (M-i-1), m); M, c, t, R = i, be*be % m, t*be*be % m, R*be % m
    return R
def croots1(m):  # roots of x^2+x+1=0 mod m  = cube roots of unity != 1
    s = sqrt_mod((-3) % m, m)
    if s is None: return []
    i2 = inv(2, m); return sorted({(-1+s)*i2 % m, (-1-s)*i2 % m})

def mk_ops(p, a):
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        (x1, y1), (x2, y2) = P, Q
        if x1 == x2 and (y1+y2) % p == 0: return None
        m = (3*x1*x1+a)*inv(2*y1, p) % p if P == Q else (y2-y1)*inv((x2-x1) % p, p) % p
        x3 = (m*m-x1-x2) % p
        return (x3, (m*(x1-x3)-y1) % p)
    def mul(k, P, n):
        Rr = None; k %= n
        while k:
            if k & 1: Rr = add(Rr, P)
            P = add(P, P); k >>= 1
        return Rr
    return add, mul

def count_order(p, a, b):
    m = p+1
    for x in range(p): m += legendre((x*x*x+a*x+b) % p, p)
    return m
def is_prime(n):
    if n < 2: return False
    for r in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % r == 0: return n == r
    d = n-1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for r in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(r, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def setup_curve(p, a, b, want_lambda=True):
    """Return (p,n,G,Xarr,Yarr,beta,lam). beta = order-3 elt of F_p*; lam matches phi(G)=[lam]G (CM only)."""
    assert p % 3 == 1, "need 3 | p-1 for beta"
    n = count_order(p, a, b)
    assert is_prime(n), f"order {n} not prime"
    add, mul = mk_ops(p, a)
    G = None
    for x0 in range(1, p):
        r = (x0*x0*x0+a*x0+b) % p
        if legendre(r, p) == 1: G = (x0, sqrt_mod(r, p)); break
    betas = croots1(p)
    beta = betas[0]
    lam = None
    if want_lambda:
        Q = (beta*G[0] % p, G[1])
        for ll in croots1(n):
            if mul(ll, G, n) == Q: lam = ll; break
        if lam is None:  # try the other beta so phi(G)=(beta x,y)=[lam]G is consistent
            beta = betas[1]; Q = (beta*G[0] % p, G[1])
            for ll in croots1(n):
                if mul(ll, G, n) == Q: lam = ll; break
    # enumerate points [d]G, d=1..n-1
    X = np.empty(n-1, dtype=np.int64); Y = np.empty(n-1, dtype=np.int64)
    P = None
    for d in range(1, n):
        P = add(P, G); X[d-1], Y[d-1] = P
    return p, n, G, X, Y, beta, lam

# ---------------- frequency-orbit structure ----------------
def build_triples(p, beta):
    """Partition +/- reps {1..(p-1)/2} into (p-1)/6 mu3-triples under b->beta b (folded by +-1)."""
    half = (p-1)//2
    fold = lambda b: min(b % p, p-(b % p))
    pos = {b: i for i, b in enumerate(range(1, half+1))}
    reps = np.arange(1, half+1, dtype=np.int64)
    visited = set(); triple_pos = []
    for b in range(1, half+1):
        if b in visited: continue
        b1 = fold(beta*b); b2 = fold(beta*beta % p * b)
        if b1 == b or b2 == b or b1 == b2:
            raise RuntimeError("degenerate mu3 orbit (beta order != 3?)")
        triple_pos.append((pos[b], pos[b1], pos[b2]))
        visited.update((b, b1, b2))
    return reps, np.array(triple_pos, dtype=np.int64)

def a_reps(n, lam, count):
    """smallest-index reps of distinct <lam>-orbits in F_n* (exclude 0)."""
    if lam is None:  # non-CM: no lam-orbit; take smallest nonzero a
        return list(range(1, count+1))
    seen = set(); out = []
    a = 1
    while len(out) < count and a < n:
        if a not in seen:
            out.append(a); seen.update((a, lam*a % n, lam*lam % n*a % n))
        a += 1
    return out

# ---------------- core: |U(a0,.,c)| via FFT ----------------
def M_column(Warr, Xarr, Yarr, c, p):
    """|U(a0,b,c)| for all b in 0..p-1, given W[d]=e_n(a0 d). Uses forced mu2: |fft(g)|[b]=M(b,c)."""
    ecy = np.exp(2j*np.pi*((c*Yarr) % p)/p)
    g = np.zeros(p, dtype=np.complex128)
    np.add.at(g, Xarr, Warr*ecy)
    return np.abs(np.fft.fft(g))

def U_direct(a0, b, c, Xarr, Yarr, p, n):
    """direct O(n) evaluation of U(a0,b,c) (for selftest / implementation control)."""
    d = np.arange(1, n)
    ph = np.exp(2j*np.pi*a0*d/n)*np.exp(2j*np.pi*((b*Xarr+c*Yarr) % p)/p)
    return ph.sum()

# ---------------- Null-B exact moments (equipartition of K marks into R/3 triples) ----------------
def null_moments(K, R):
    """E, Var of X = sum_t C(k_t,2), K marks equipartitioned into R/3 triples (size 3)."""
    if R < 3 or K < 2: return 0.0, 0.0
    def ff(a, j):  # falling factorial a*(a-1)*...*(a-j+1)
        r = 1.0
        for t in range(j): r *= (a-t)
        return r
    p2 = ff(K, 2)/ff(R, 2)
    p3 = ff(K, 3)/ff(R, 3) if R >= 3 else 0.0
    p4 = ff(K, 4)/ff(R, 4) if R >= 4 else 0.0
    E = R*p2                                   # within-triple pairs = R (=3T)
    EX2 = R*p2 + 2*R*p3 + R*(R-3)*p4
    return E, max(EX2 - E*E, 0.0)

# ---------------- run one curve ----------------
def run_curve(p, a, b, n_areps, tau, label, want_lambda=True, plant_frac=0.0, scatter=False, rng=None):
    p, n, G, X, Y, beta, lam = setup_curve(p, a, b, want_lambda)
    reps, tri = build_triples(p, beta)
    R = len(reps); s = math.sqrt(n-1)
    areps = a_reps(n, lam, n_areps)
    d = np.arange(1, n)
    S_obs = 0.0; E_sum = 0.0; V_sum = 0.0
    sglv_vals = []
    nplant_tot = 0
    for a0 in areps:
        W = np.exp(2j*np.pi*a0*d/n)
        for c in range(1, p):  # exclude c=0 (pure-x axis, v1 F3); scan c in 1..p-1
            M = M_column(W, X, Y, c, p)
            Mr = M[reps]                       # magnitudes at +- reps
            z = (Mr/s < tau).astype(np.int64)
            if plant_frac > 0.0:
                ntr = tri.shape[0]
                if scatter:                    # negative control: same # extra near-zeros, scattered
                    nadd = int(round(plant_frac*ntr))*3
                    idx = rng.choice(R, size=min(nadd, R), replace=False); z[idx] = 1
                    nplant_tot += nadd
                else:                          # positive control: whole triples forced near-zero
                    npl = int(round(plant_frac*ntr))
                    sel = rng.choice(ntr, size=npl, replace=False)
                    z[tri[sel].ravel()] = 1
                    nplant_tot += npl
            k = z[tri].sum(axis=1)
            S_obs += float((k*(k-1)//2).sum())
            K = int(z.sum())
            E, V = null_moments(K, R); E_sum += E; V_sum += V
            # secondary S_GLV (descriptive)
            M2 = (Mr.astype(np.float64))**2
            mu = M2[tri].mean(axis=1)
            vt = M2.var()
            if vt > 0: sglv_vals.append(mu.var()/vt)
    Z = (S_obs - E_sum)/math.sqrt(V_sum) if V_sum > 0 else 0.0
    return {"label": label, "p": p, "n": n, "R": R, "triples": tri.shape[0], "areps": len(areps),
            "tau": tau, "S_obs": S_obs, "E_null": E_sum, "Z": Z,
            "S_GLV_med": float(np.median(sglv_vals)) if sglv_vals else float('nan'),
            "nplant": nplant_tot, "beta": beta, "lam": lam}

# ---------------- selftest ----------------
def selftest():
    p, a, b = 61, 0, 7
    p, n, G, X, Y, beta, lam = setup_curve(p, a, b)
    print(f"[selftest] curve y^2=x^3+7/F_{p}, n={n}, beta={beta}, lam={lam}")
    # (i) brute U vs FFT-path M
    a0 = 1; W = np.exp(2j*np.pi*a0*np.arange(1, n)/n); c = 3
    M = M_column(W, X, Y, c, p)
    err = max(abs(M[bb] - abs(U_direct(a0, bb, c, X, Y, p, n))) for bb in range(p))
    print(f"[selftest] (i) brute-U vs FFT-path |U| max err = {err:.2e}  ok={err < 1e-8}")
    # (ii) forced-diagonal implementation control (var == 0 on {(a0,b),(lam a0,beta b),(lam^2 a0,b^2)})
    l2 = lam*lam % n; mx = 0.0
    for (aa, bb, cc) in [(1, 2, 3), (5, 7, 11), (13, 4, 9), (20, 30, 40)]:
        v = [abs(U_direct(aa, bb, cc, X, Y, p, n)),
             abs(U_direct(lam*aa % n, beta*bb % p, cc, X, Y, p, n)),
             abs(U_direct(l2*aa % n, beta*beta % p*bb % p, cc, X, Y, p, n))]
        mx = max(mx, np.var(v))
    print(f"[selftest] (ii) forced-diagonal intra-orbit Var(|U|) max = {mx:.2e}  ok={mx < 1e-6}")
    # (iii) analytic Null-B moments vs empirical equipartition permutation
    reps, tri = build_triples(p, beta); R = len(reps); ntr = tri.shape[0]
    rng = np.random.default_rng(0); K = 8
    emp = []
    for _ in range(20000):
        z = np.zeros(R, dtype=np.int64); z[rng.choice(R, K, replace=False)] = 1
        k = z[tri].sum(axis=1); emp.append(int((k*(k-1)//2).sum()))
    emp = np.array(emp); E, V = null_moments(K, R)
    print(f"[selftest] (iii) Null-B  analytic E={E:.4f} Var={V:.4f} | empirical E={emp.mean():.4f} "
          f"Var={emp.var():.4f}  ok={abs(E-emp.mean())<0.05 and abs(V-emp.var())<0.1*max(V,1)}")
    ok = err < 1e-8 and mx < 1e-6 and abs(E-emp.mean()) < 0.05
    print(f"[selftest] PASS={ok}")
    return ok

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--primes", default="")           # comma list, CM curve y^2=x^3+7
    ap.add_argument("--areps", type=int, default=24)
    ap.add_argument("--tau", type=float, default=0.10)
    ap.add_argument("--controls", action="store_true") # plant + negative on the first prime
    ap.add_argument("--seed", type=int, default=12345)
    args = ap.parse_args()
    if args.selftest:
        sys.exit(0 if selftest() else 1)
    rng = np.random.default_rng(args.seed)
    primes = [int(x) for x in args.primes.split(",") if x]
    zlist = []
    for p in primes:
        r = run_curve(p, 0, 7, args.areps, args.tau, f"CM p={p}")
        zlist.append(r["Z"])
        print(f"[{r['label']}] n={r['n']} R={r['R']} triples={r['triples']} areps={r['areps']} "
              f"tau={r['tau']}  S_obs={r['S_obs']:.0f} E_null={r['E_null']:.0f}  Z={r['Z']:+.3f}  "
              f"S_GLV_med={r['S_GLV_med']:.4f}", flush=True)
        if args.controls and p == primes[0]:
            rp = run_curve(p, 0, 7, args.areps, args.tau, "PLANT", plant_frac=0.05, rng=rng)
            rnv = run_curve(p, 0, 7, args.areps, args.tau, "NEG-scatter", plant_frac=0.05, scatter=True, rng=rng)
            print(f"[CONTROL plant   ] Z={rp['Z']:+.3f} (must FIRE >> 0)", flush=True)
            print(f"[CONTROL scatter ] Z={rnv['Z']:+.3f} (must stay ~0)", flush=True)
    if len(zlist) > 1:
        stouffer = sum(zlist)/math.sqrt(len(zlist))
        print(f"[POOLED] Stouffer Z = {stouffer:+.3f} over {len(zlist)} primes", flush=True)
