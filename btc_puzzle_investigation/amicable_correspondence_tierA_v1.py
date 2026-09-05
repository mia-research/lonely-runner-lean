"""
Tier A exact arm of PREREG_amicable_correspondence_bits_v2.md.

Carries: ARM-A exact arm (PhiA..PhiD, N0), A2-1, A2-2, plant ladder P1.
NOT here (Tier B, per spec S6): graded arm (S2b), A2-3.

EXACTNESS (spec S8 + btc_puzzle_investigation/CLAUDE.md): int throughout the signal
path.  numpy int64 is used only as a vector of exact integers; every modulus in this
tier satisfies p,n < 2e5 so all intermediate products stay < 2^63.  No float anywhere
in feature construction, Gamma* membership, image histograms or fibre multisets.
"""
import sys, json, time
import numpy as np
from sympy import isprime, primerange, divisors, primitive_root

sys.set_int_max_str_digits(100000)

# ---------------------------------------------------------------- curve utilities

def sqrt_mod(a, p):
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
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
        m, c = i, b * b % p
        t, r = t * c % p, r * b % p
    return r


def isqrt_exact(x):
    if x < 0:
        return None
    lo, hi = 0, 1 << ((x.bit_length() + 1) // 2 + 1)
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid * mid <= x:
            lo = mid
        else:
            hi = mid - 1
    return lo if lo * lo == x else None


def cornacchia_a2_3b2(p):
    r0 = sqrt_mod(p - 3, p)
    if r0 is None:
        return None
    if 2 * r0 > p:
        r0 = p - r0
    a, b = p, r0
    while b * b > p:
        a, b = b, a % b
    rem = p - b * b
    if rem % 3 != 0:
        return None
    c = isqrt_exact(rem // 3)
    return None if c is None else (b, c)


def ec_add(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        if y1 == 0: return None
        lam = (3 * x1 * x1) % p * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def ec_mul(k, P, p):
    R, Q = None, P
    while k > 0:
        if k & 1: R = ec_add(R, Q, p)
        Q = ec_add(Q, Q, p); k >>= 1
    return R


def find_point(q, b=7, start=1):
    """canonical-ish point search: smallest x >= start with a square RHS."""
    for x in range(start, q + start + 500):
        xx = x % q
        v = (xx * xx % q * xx + b) % q
        y = sqrt_mod(v, q)
        if y is not None and v != 0:
            return (xx, min(y, q - y))
    return None


def canonical_gen(q, b=7):
    """smallest x, then smallest y -- spec S6 'Generator'."""
    return find_point(q, b, 1)


def order_E7(q):
    """#E_7(F_q), exact.  CM route + annihilation selection, O(q) fallback (D2)."""
    if q % 3 == 2:
        return q + 1                       # j=0 supersingular
    sol = cornacchia_a2_3b2(q)
    if sol is None:
        return count_naive(q)
    a, bb = sol
    cands = {q + 1 - t for t in (2 * a, -2 * a, a + 3 * bb, -(a + 3 * bb),
                                 a - 3 * bb, -(a - 3 * bb))}
    pts = [find_point(q, 7, s) for s in (1, 2, 3, 5, 7)]
    pts = [P for P in pts if P is not None]
    ok = [N for N in cands if all(ec_mul(N, P, q) is None for P in pts)]
    if len(ok) == 1:
        return ok[0]
    return count_naive(q)                   # ambiguous -> exact fallback


def count_naive(q, b=7):
    tot = q + 1
    half = (q - 1) // 2
    for x in range(q):
        v = (x * x % q * x + b) % q
        if v == 0: continue
        tot += 1 if pow(v, half, q) == 1 else -1
    return tot


# ---------------------------------------------------------------- vectorized helpers

def vec_modpow(base, e, m):
    """base: int64 array, e: int scalar, m: int scalar.  exact."""
    result = np.ones_like(base)
    b = base % m
    while e > 0:
        if e & 1:
            result = result * b % m
        b = b * b % m
        e >>= 1
    return result


def enumerate_points(p, n, G):
    """X[j], Y[j] = coords of [j]G for j = 1..n-1.  index 0 unused.
    Sequential affine walk, exact ints."""
    X = np.zeros(n, dtype=np.int64)
    Y = np.zeros(n, dtype=np.int64)
    gx, gy = G
    cx, cy = gx, gy
    X[1], Y[1] = cx, cy
    for j in range(2, n):
        # cP = cP + G
        if cx == gx and (cy + gy) % p == 0:
            cx = cy = None
            break
        if cx == gx and cy == gy:
            lam = (3 * cx * cx) % p * pow(2 * cy, p - 2, p) % p
        else:
            lam = (gy - cy) % p * pow((gx - cx) % p, p - 2, p) % p
        nx = (lam * lam - cx - gx) % p
        ny = (lam * (cx - nx) - cy) % p
        cx, cy = nx, ny
        X[j], Y[j] = cx, cy
    return X, Y


def dlog_table_mult(n, g):
    """dl[j] = a with g^a = j mod n, for j in 1..n-1."""
    dl = np.zeros(n, dtype=np.int64)
    cur = 1
    for a in range(n - 1):
        dl[cur] = a
        cur = cur * g % n
    return dl


def gamma_star_id(labels, n, dl, g, divs):
    """largest k | (n-1) with labels[t_k * j] == labels[j] for all j.  Sigma = {id}."""
    J = np.arange(1, n, dtype=np.int64)
    lab = labels[1:]
    best = 1
    for k in divs:
        t = pow(g, (n - 1) // k, n)
        idx = (t * J) % n
        if np.array_equal(labels[idx], lab):
            if k > best:
                best = k
    return best


def gamma_star_equivariant(e_lab, n, g, divs, mod_e):
    """Gamma* for PhiD: exists u with e[t*j] == +-u*e[j] (mod mod_e), BOT preserved.
    e_lab uses -1 for BOT."""
    from math import gcd
    J = np.arange(1, n, dtype=np.int64)
    ev = e_lab[1:]
    valid = ev >= 0
    if not valid.any():
        return 1
    # reference index must have e invertible mod mod_e: #Etilde is composite on
    # the control arm, so e[j] need not be a unit.  no unit anywhere -> undetermined.
    ref = -1
    for i in range(len(ev)):
        if valid[i] and gcd(int(ev[i]), mod_e) == 1:
            ref = i
            break
    if ref < 0:
        return 1
    first = ref
    best = 1
    for k in divs:
        t = pow(g, (n - 1) // k, n)
        idx = (t * J) % n
        et = e_lab[idx]
        if not np.array_equal(et >= 0, valid):
            continue
        a0, b0 = int(ev[first]), int(et[first])
        if a0 == 0:
            continue
        ok = False
        for sgn in (1, -1):
            u = (sgn * b0) % mod_e * pow(a0, -1, mod_e) % mod_e
            pred = (ev * u) % mod_e
            tgt = et % mod_e
            if np.array_equal(np.minimum(pred, (mod_e - pred) % mod_e)[valid],
                              np.minimum(tgt, (mod_e - tgt) % mod_e)[valid]):
                ok = True
                break
        if ok and k > best:
            best = k
    return best


def coset_min_labels(enc, n, dl, k):
    """P1 plant: label(j) = lex-min encoded (X,Y) over the coset j*Gamma_k."""
    ncos = (n - 1) // k
    cid = dl[1:] % ncos
    out = np.full(ncos, np.iinfo(np.int64).max, dtype=np.int64)
    np.minimum.at(out, cid, enc[1:])
    lab = np.zeros(n, dtype=np.int64)
    lab[1:] = out[cid]
    return lab


def fibre_multiset(labels, n):
    _, cnt = np.unique(labels[1:], return_counts=True)
    vals, hist = np.unique(cnt, return_counts=True)
    return {int(v): int(h) for v, h in zip(vals, hist)}


# ---------------------------------------------------------------- per-curve run

def run_curve(p, n, verbose=False):
    """all Tier-A statistics for one curve.  returns dict."""
    G = canonical_gen(p)
    X, Y = enumerate_points(p, n, G)
    if X[n - 1] == 0 and Y[n - 1] == 0:
        return {"p": p, "n": n, "error": "enumeration_incomplete"}

    g = primitive_root(n)
    dl = dlog_table_mult(n, g)
    divs = [k for k in divisors(n - 1) if k > 1]

    xb = X % n
    yb = Y % n
    x3 = (xb * xb % n) * xb % n
    rhs = (x3 + 7) % n
    delta = (yb * yb % n - x3 - 7) % n

    half = (n - 1) // 2
    chi_rhs = vec_modpow(rhs, half, n)
    chi_rhs = np.where(rhs == 0, 0, np.where(chi_rhs == 1, 1, -1))
    chi_del = vec_modpow(delta, half, n)
    chi_del = np.where(delta == 0, 0, np.where(chi_del == 1, 1, -1))

    res = {"p": p, "n": n, "orientation": "p<n" if p < n else "p>n",
           "n_divisors_gt6": sum(1 for k in divisors(n - 1) if k > 6)}

    # ---- v3 S2A mandatory row: (|Gamma*|, |Gamma*_inv|, |image|, orbit_exact, DEG)
    def row(lab, forced, gamma=None):
        lab = lab.astype(np.int64)
        lab[0] = -999
        g_inv = gamma_star_id(lab, n, dl, g, divs)     # Sigma = {id} kernel
        gam = g_inv if gamma is None else gamma
        img = int(len(np.unique(lab[1:])))
        return {"gamma": gam, "gamma_inv": g_inv, "image": img,
                "orbit_exact": bool(img * g_inv == n - 1),
                "DEG": bool(img == 1),
                "gate_ok": bool(img * g_inv <= n - 1 and (n - 1) % g_inv == 0),
                "forced": forced,
                "fibres": fibre_multiset(lab, n)}

    # ---- PhiA, PhiB, PhiC  (Sigma = {id}  =>  Gamma* = Gamma*_inv)
    for name, lab, forced in (("PhiA", chi_rhs, 2), ("PhiB", chi_del, 1),
                              ("PhiC", delta, 1)):
        res[name] = row(lab, forced)

    # ---- A2-1  rho = (xbar, ybar)
    res["A2_1_rho"] = row((xb * n + yb), 1)

    # ---- N_const : degeneracy control, DEG must trigger (v3 S2A / S4, D8)
    res["N_const"] = row(np.zeros(n, dtype=np.int64), 1)

    # ---- partner curve Etilde over F_n : dlog table by enumeration
    nE = order_E7(n)
    res["nE_tilde"] = nE
    res["amicable"] = bool(nE == p)
    Gt = canonical_gen(n)
    xt_to_j = {}
    ordmap = {}
    cx, cy = Gt
    for j in range(1, nE + 1):
        if cx is None:
            break
        xt_to_j.setdefault(cx, j)
        cx_cy = ec_add((cx, cy), Gt, n)
        if cx_cy is None:
            break
        cx, cy = cx_cy
    # PhiD: +- class of dlog of the point with X = xbar ; BOT off-curve
    e_lab = np.full(n, -1, dtype=np.int64)
    for j in range(1, n):
        v = int(xb[j])
        jj = xt_to_j.get(v)
        if jj is not None:
            e_lab[j] = jj % nE
    # PhiD: Sigma != {id}, so Gamma* (equivariant) and Gamma*_inv (sigma = id) differ.
    # The S2A inequality is on Gamma*_inv only (v3 D7).
    k_D = gamma_star_equivariant(e_lab, n, g, divs, nE)
    res["PhiD"] = row(e_lab.copy(), 2, gamma=k_D)
    res["PhiD"]["bot_rate_num"] = int((e_lab[1:] < 0).sum())
    res["PhiD"]["bot_rate_den"] = n - 1

    # ---- N0 : retained as DISCLOSED-REDUNDANT diagnostic only (D8).
    # It is a coarsening of PhiA and is counted in no tally and no K.
    n0 = np.where(e_lab >= 0, nE, -1).astype(np.int64)
    res["N0_diagnostic"] = row(n0, 1)
    res["N0_diagnostic"]["note"] = "coarsening of PhiA; no tally, no K (D8)"

    # ---- A2-2 : does GLV/beta descend affinely through r(x) = x mod n ?
    beta = None
    for c in range(2, p):
        if pow(c, 3, p) == 1 and c != 1:
            beta = c
            break
    if beta is not None:
        xs = np.arange(0, p, dtype=np.int64)
        rx = xs % n
        rbx = (beta * xs % p) % n
        noncol = xs < n if p > n else np.ones(p, dtype=bool)
        idx = np.flatnonzero(noncol)[:2]
        if len(idx) == 2:
            x1, x2 = int(idx[0]), int(idx[1])
            a1, b1 = int(rx[x1]), int(rbx[x1])
            a2, b2 = int(rx[x2]), int(rbx[x2])
            da = (a2 - a1) % n
            if da != 0:
                u = (b2 - b1) % n * pow(da, -1, n) % n
                v = (b1 - u * a1) % n
                agree = int((((u * rx + v) % n) == rbx)[noncol].sum())
                res["A2_2"] = {"beta": beta, "u": u, "v": v,
                               "agree": agree, "tested": int(noncol.sum()),
                               "forced_collisions": int(max(0, p - n))}
    return res


# ---------------------------------------------------------------- P1 plant ladder

def plant_ladder(p, n):
    """P1 must fire: Gamma*(Phi^plant_k) >= k and names Gamma_k, every k | n-1, k > 6."""
    G = canonical_gen(p)
    X, Y = enumerate_points(p, n, G)
    g = primitive_root(n)
    dl = dlog_table_mult(n, g)
    divs = [k for k in divisors(n - 1) if k > 1]
    enc = (X * p + Y).astype(np.int64)
    misses = []
    for k in [d for d in divisors(n - 1) if d > 6]:
        lab = coset_min_labels(enc, n, dl, k)
        got = gamma_star_id(lab, n, dl, g, divs)
        if got % k != 0:
            misses.append({"k": k, "got": got})
    return misses


# ---------------------------------------------------------------- frame

def build_frame(limit):
    amic, nonamic = [], []
    for q in primerange(11, limit):
        if q % 3 != 1 or q == 7:
            continue
        m = order_E7(q)
        if m is None or m == q or not isprime(m):
            continue
        (amic if order_E7(m) == q else nonamic).append((q, m))
    return amic, nonamic


def tier_rows(limit):
    amic, nonamic = build_frame(limit)
    A = sorted((q, m) for q, m in amic)              # BOTH orientations (D3)
    used, ctrl = set(), []
    for q, m in A:
        same = [z for z in nonamic
                if z[0] < limit and ((z[0] < z[1]) == (q < m)) and z[0] not in used]
        best = min(same, key=lambda z: (abs(z[0] - q), z[0]))
        used.add(best[0]); ctrl.append(best)
    return A, ctrl


if __name__ == "__main__":
    LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    t0 = time.time()
    A, ctrl = tier_rows(LIMIT)
    print(f"Tier rows: {len(A)} amicable curves, {len(ctrl)} matched controls "
          f"(limit {LIMIT}), frame built in {time.time()-t0:.0f}s", flush=True)

    out = {"limit": LIMIT, "amicable": [], "control": [], "plant_misses": []}
    for tag, rows in (("amicable", A), ("control", ctrl)):
        for i, (q, m) in enumerate(rows):
            r = run_curve(q, m)
            r["arm"] = tag
            out[tag].append(r)
            if i % 10 == 0:
                print(f"  [{tag} {i+1}/{len(rows)}] p={q} n={m} "
                      f"A={r.get('PhiA',{}).get('gamma')} "
                      f"rho={r.get('A2_1_rho',{}).get('gamma')} "
                      f"({time.time()-t0:.0f}s)", flush=True)
    # P1 plant ladder -- spec S4: every k | (n-1), k > 6, on EVERY curve.
    for i, (q, m) in enumerate(A + ctrl):
        ms = plant_ladder(q, m)
        out["plant_misses"].append({"p": q, "n": m, "misses": ms})
        if i % 25 == 0:
            print(f"  [plant {i+1}/{len(A)+len(ctrl)}] p={q} misses={len(ms)} "
                  f"({time.time()-t0:.0f}s)", flush=True)

    with open(f"amicable_tierA_results_{LIMIT}.json", "w") as f:
        json.dump(out, f)
    print(f"done in {time.time()-t0:.0f}s -> amicable_tierA_results_{LIMIT}.json")
