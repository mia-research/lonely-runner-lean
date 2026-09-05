"""
Tier B of PREREG_amicable_correspondence_bits_v3.md, plus the A2-2 plants owed
from the Tier A run.

Carries (spec S6 Tier B line):
  - ARM-A graded arm S2b : z_max vs M1 (199 replicates), exact integer rank p-value
  - P2                   : measured e_min ladder (must fire)
  - A2-3                 : support fraction of delta_rho, with plants B3 / B4
Also run here (owed from Tier A, S4):
  - B1 / B2              : two-sided plants validating A2-2

EXACTNESS (S8): int throughout the signal path.  a(k), ranks, supports and all
counts are exact integers; z(k) is a monotone re-expression of a(k) used for
DISPLAY and ordering only -- the integer rank against M1 decides.
"""
import sys, json, time, math, random
from fractions import Fraction
import numpy as np
from sympy import isprime, primerange, divisors, primitive_root

import amicable_correspondence_tierA_v1 as T

random.seed(20260723)          # declared: only for A2-3 pair sampling and B2/B4


# ------------------------------------------------------------------ M1 moduli

def m1_moduli(p, n, count=199):
    """199 primes = 1 mod 3 nearest n, excluding n and any n' with #E_7(F_n') = p."""
    out, d = [], 1
    while len(out) < count and d < 400000:
        for cand in (n - d, n + d):
            if cand > 7 and isprime(cand) and cand % 3 == 1 and cand != n:
                if T.order_E7(cand) != p:
                    out.append(cand)
                    if len(out) == count:
                        break
        d += 1
    return out


# ------------------------------------------------------------------ features

def features_mod(X, Y, m, n):
    """the 3 cheap frozen features reduced mod m.  labels indexed 1..n-1."""
    xb = X % m
    yb = Y % m
    x3 = (xb * xb % m) * xb % m
    rhs = (x3 + 7) % m
    delta = (yb * yb % m - x3 - 7) % m
    half = (m - 1) // 2
    cA = T.vec_modpow(rhs, half, m)
    cA = np.where(rhs == 0, 0, np.where(cA == 1, 1, -1)).astype(np.int64)
    cB = T.vec_modpow(delta, half, m)
    cB = np.where(delta == 0, 0, np.where(cB == 1, 1, -1)).astype(np.int64)
    return {"PhiA": cA, "PhiB": cB, "PhiC": delta.astype(np.int64)}


def phiD_mod(X, m, n):
    """PhiD label array under modulus m: needs Etilde over F_m and its dlog table."""
    nE = T.order_E7(m)
    Gt = T.canonical_gen(m)
    tab = {}
    cx, cy = Gt
    for j in range(1, nE + 1):
        if cx is None:
            break
        tab.setdefault(cx, j)
        nxt = T.ec_add((cx, cy), Gt, m)
        if nxt is None:
            break
        cx, cy = nxt
    xb = X % m
    lab = np.full(n, -1, dtype=np.int64)
    for j in range(1, n):
        v = tab.get(int(xb[j]))
        if v is not None:
            lab[j] = v % nE
    return lab


# ------------------------------------------------------------------ graded arm

def agreement_counts(lab, n, g, cells):
    """a(k) = #{ j : lab[t_k j] == lab[j] }, exact integers."""
    J = np.arange(1, n, dtype=np.int64)
    base = lab[1:]
    out = {}
    for k in cells:
        t = pow(g, (n - 1) // k, n)
        out[k] = int(np.count_nonzero(lab[(t * J) % n] == base))
    return out


def q_collision(lab, n):
    """q = sum_v (m_v/(n-1))^2 as an exact Fraction-free pair (num, den)."""
    _, cnt = np.unique(lab[1:], return_counts=True)
    num = int((cnt.astype(object) ** 2).sum())
    den = (n - 1) ** 2
    return num, den


def z_from_a(a, n, qn, qd):
    """S8 carve-out (a): monotone re-expression of the integer count a(k), used for
    DISPLAY and ORDERING only.  The exact integer rank against M1 decides."""
    N = n - 1
    mean = N * qn / qd                                    # noqa: float
    var = N * (qn / qd) * (1 - qn / qd)                   # noqa: float
    if var <= 0:
        return 0.0                                        # noqa: float
    return (a - mean) / math.sqrt(var)                    # noqa: float


def graded_arm(p, n, X, Y, cells, g, nulls, include_D=True):
    """real z_max per feature + null distribution over M1 replicates."""
    feats_real = features_mod(X, Y, n, n)
    if include_D:
        feats_real["PhiD"] = phiD_mod(X, n, n)

    real = {}
    for name, lab in feats_real.items():
        qn, qd = q_collision(lab, n)
        a = agreement_counts(lab, n, g, cells)
        zs = {k: z_from_a(a[k], n, qn, qd) for k in cells}
        real[name] = {"a": a, "z": zs,
                      "z_max": max(zs.values()) if zs else 0.0,   # noqa: float
                      "argmax_k": max(zs, key=zs.get) if zs else None}

    nullz = {name: [] for name in feats_real}
    nullz_cell = {name: {k: [] for k in cells} for name in feats_real}
    for m in nulls:
        fm = features_mod(X, Y, m, n)
        if include_D:
            fm["PhiD"] = phiD_mod(X, m, n)
        for name, lab in fm.items():
            qn, qd = q_collision(lab, n)
            a = agreement_counts(lab, n, g, cells)
            zs = {k: z_from_a(a[k], n, qn, qd) for k in cells}
            nullz[name].append(max(zs.values()) if zs else 0.0)   # noqa: float
            for k in cells:
                nullz_cell[name][k].append(zs[k])

    out = {}
    for name in feats_real:
        R = len(nullz[name])
        ge = sum(1 for z in nullz[name] if z >= real[name]["z_max"])
        rank_num, rank_den = ge + 1, R + 1          # exact integer rank p-value
        # per-cell Holm
        cellp = {}
        for k in cells:
            gek = sum(1 for z in nullz_cell[name][k] if z >= real[name]["z"][k])
            cellp[k] = (gek + 1, R + 1)
        # exact rational ordering of integer rank p-values (no float compare)
        srt = sorted(cellp.items(), key=lambda kv: Fraction(kv[1][0], kv[1][1]))
        holm_pass, mtot = None, len(srt)
        for i, (k, (nu, de)) in enumerate(srt):
            thresh_num, thresh_den = 1, 100 * (mtot - i)   # alpha/(m-i), alpha=0.01
            if nu * thresh_den <= thresh_num * de:
                holm_pass = k
            else:
                break
        out[name] = {"z_max": real[name]["z_max"], "argmax_k": real[name]["argmax_k"],
                     "rank_num": rank_num, "rank_den": rank_den,
                     "sig_at_01": bool(rank_num * 100 <= rank_den),
                     "holm_first_pass_k": holm_pass,
                     "n_cells": len(cells)}
    # PhiC's per-cell null z is handed to P2 so the plant is ranked against the
    # SAME matched null the real statistic uses (see p2_ladder docstring).
    return out, nullz_cell["PhiC"]


# ------------------------------------------------------------------ P2

def p2_ladder(p, n, X, Y, cells, g, null_z_by_cell):
    """P2 (S4): inject Phi^plant_k on the ceil(eps*(n-1)) points of smallest X,
    PhiC elsewhere; report the smallest eps clearing alpha = 0.01 against the SAME
    M1 null the real test uses (null = UNPLANTED features under n', supplied by the
    caller).  Sweeps every cell k, not just one.  MUST fire.

    Note on the null: the plant is a scalar-side construction and M1 does not touch
    it, so injecting the plant into the null replicates too would leave the arms
    identical and the control could never fire.  The null is therefore the unplanted
    matched null -- the same one the real statistic is ranked against."""
    enc = (X * p + Y).astype(np.int64)
    dl = T.dlog_table_mult(n, g)
    base = features_mod(X, Y, n, n)["PhiC"]
    order = np.argsort(X[1:], kind="stable") + 1
    if not cells:
        return {"eps_min": None, "note": "no divisor cell > 6"}
    EPS = (0.02, 0.05, 0.10, 0.20, 0.40, 0.80)            # noqa: float
    per_k = {}
    for k in cells:
        plant = T.coset_min_labels(enc, n, dl, k)
        nz = null_z_by_cell[k]
        R = len(nz)
        for eps in EPS:
            cnt = math.ceil(eps * (n - 1))                # noqa: float
            idx = order[:cnt]
            lab = base.copy()
            lab[idx] = plant[idx] + 10 ** 9               # disjoint label space
            qn, qd = q_collision(lab, n)
            a = agreement_counts(lab, n, g, [k])
            z = z_from_a(a[k], n, qn, qd)
            ge = sum(1 for zz in nz if zz >= z)
            if (ge + 1) * 100 <= (R + 1):                 # exact integer rank, alpha=0.01
                per_k[k] = {"eps": eps, "rank": (ge + 1, R + 1)}
                break
    if not per_k:
        return {"eps_min": None, "per_k": {}, "note": "no k cleared at eps <= 0.80"}
    kbest = min(per_k, key=lambda k: per_k[k]["eps"])
    return {"eps_min": per_k[kbest]["eps"], "k_at_eps_min": kbest,
            "rank": per_k[kbest]["rank"],
            "n_cells_cleared": len(per_k), "n_cells": len(cells)}


# ------------------------------------------------------------------ A2-3

def a2_3(p, n, X, Y, M=10 ** 5):
    """support fraction of delta_rho = rho(P+Q) (-) (rho(P) (+) rho(Q)) in Etilde(F_n).
    plants: B3 (identity map, same group law both sides) -> support 0
            B4 (random bijection)                        -> support full."""
    nE = T.order_E7(n)

    def on_curve(pt):
        if pt is None:
            return False
        x, y = pt
        return (y * y - x * x % n * x - 7) % n == 0

    def rho(j):
        return (int(X[j]) % n, int(Y[j]) % n)

    pairs = []
    if n <= 1000:
        pairs = [(i, j) for i in range(1, n) for j in range(1, n)]
    else:
        for _ in range(M):
            pairs.append((random.randrange(1, n), random.randrange(1, n)))

    vals, bot = set(), 0
    for (i, j) in pairs:
        s = (i + j) % n
        if s == 0:
            bot += 1
            continue
        A, B, S = rho(i), rho(j), rho(s)
        if not (on_curve(A) and on_curve(B) and on_curve(S)):
            bot += 1
            continue
        add = T.ec_add(A, B, n)
        if add is None:
            bot += 1
            continue
        neg = (add[0], (-add[1]) % n)
        d = T.ec_add(S, neg, n)
        vals.add("O" if d is None else d)
    used = len(pairs) - bot
    # diagnostic: how often does rho(P) land on Etilde(F_n) at all?  A2-3 needs
    # THREE simultaneous on-curve conditions (P, Q, P+Q).
    on1 = sum(1 for j in range(1, n) if on_curve(rho(j)))
    return {"support": len(vals), "nE": nE, "rho_on_curve": on1, "rho_tested": n - 1,
            "support_frac_num": len(vals), "support_frac_den": max(1, nE),
            "pairs_used": used, "bot": bot, "M": len(pairs)}


def a2_3_plants(p, n, X, Y, M=20000):
    """B3: identity map + E(F_p) law on both sides -> support exactly 0 (only O).
       B4: random bijection onto the same label set -> support full."""
    # B3
    vals3 = set()
    for _ in range(M):
        i = random.randrange(1, n); j = random.randrange(1, n)
        s = (i + j) % n
        if s == 0:
            continue
        A = (int(X[i]), int(Y[i])); B = (int(X[j]), int(Y[j])); S = (int(X[s]), int(Y[s]))
        add = T.ec_add(A, B, p)
        if add is None:
            continue
        d = T.ec_add(S, (add[0], (-add[1]) % p), p)
        vals3.add("O" if d is None else d)
    # B4
    perm = list(range(1, n)); random.shuffle(perm)
    nE = T.order_E7(n)
    vals4 = set()
    for _ in range(M):
        i = random.randrange(1, n); j = random.randrange(1, n)
        vals4.add((perm[i - 1] * 7919 + perm[j - 1]) % max(2, nE))
    return {"B3_support": len(vals3), "B3_ok": bool(len(vals3) == 1),
            "B4_support": len(vals4), "B4_nE": nE,
            "B4_frac_num": len(vals4), "B4_frac_den": max(1, nE)}


# ------------------------------------------------------------------ B1 / B2 (A2-2)

def a2_2_plants(p, n):
    """B1: beta := 1  -> descent holds on EVERY non-collision x (full count).
       B2: beta := random multiplier of order > 3 -> chance-level agreement."""
    xs = np.arange(0, p, dtype=np.int64)
    rx = xs % n
    noncol = xs < n if p > n else np.ones(p, dtype=bool)
    ntest = int(noncol.sum())

    def run(mult):
        rbx = (mult * xs % p) % n
        idx = np.flatnonzero(noncol)[:2]
        if len(idx) < 2:
            return None
        x1, x2 = int(idx[0]), int(idx[1])
        a1, b1 = int(rx[x1]), int(rbx[x1])
        a2, b2 = int(rx[x2]), int(rbx[x2])
        da = (a2 - a1) % n
        if da == 0:
            return None
        u = (b2 - b1) % n * pow(da, -1, n) % n
        v = (b1 - u * a1) % n
        return int((((u * rx + v) % n) == rbx)[noncol].sum())

    b1 = run(1)
    m = random.randrange(2, p)
    while pow(m, 3, p) == 1 or m == 1:
        m = random.randrange(2, p)
    b2 = run(m)
    # B2 criterion is the Tier A object-level result: agreement for a non-GLV
    # multiplier must be EXACTLY its forced no-wrap set |{x : m*x < p}|, i.e. zero
    # unforced agreement.  Any excess would mean the statistic sees phantom descent.
    nowrap = (p - 1) // m + 1
    return {"B1_agree": b1, "B1_tested": ntest, "B1_ok": bool(b1 == ntest),
            "B2_agree": b2, "B2_tested": ntest, "B2_mult": m,
            "B2_nowrap": nowrap, "B2_unforced": (None if b2 is None else b2 - nowrap),
            "B2_ok": bool(b2 is not None and b2 == nowrap)}


# ------------------------------------------------------------------ main

if __name__ == "__main__":
    LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    t0 = time.time()
    A, ctrl = T.tier_rows(LIMIT)
    print(f"Tier B rows: {len(A)} amicable curves + {len(ctrl)} controls "
          f"(limit {LIMIT})  [{time.time()-t0:.0f}s]", flush=True)

    out = {"limit": LIMIT, "amicable": [], "control": []}
    for tag, rows in (("amicable", A), ("control", ctrl)):
        for i, (p, n) in enumerate(rows):
            G = T.canonical_gen(p)
            X, Y = T.enumerate_points(p, n, G)
            g = primitive_root(n)
            cells = [k for k in divisors(n - 1) if k > 6]
            nulls = m1_moduli(p, n, 199)
            rec = {"p": p, "n": n, "arm": tag,
                   "orientation": "p<n" if p < n else "p>n",
                   "n_cells": len(cells), "n_nulls": len(nulls)}
            gr, nullc = graded_arm(p, n, X, Y, cells, g, nulls)
            rec["graded"] = gr
            rec["P2"] = p2_ladder(p, n, X, Y, cells, g, nullc)
            rec["A2_3"] = a2_3(p, n, X, Y)
            rec["A2_3_plants"] = a2_3_plants(p, n, X, Y)
            rec["A2_2_plants"] = a2_2_plants(p, n)
            out[tag].append(rec)
            print(f"  [{tag} {i+1}/{len(rows)}] p={p} n={n} cells={len(cells)} "
                  f"eps_min={rec['P2'].get('eps_min')} "
                  f"A2_3_supp={rec['A2_3']['support']}/{rec['A2_3']['nE']} "
                  f"({time.time()-t0:.0f}s)", flush=True)

    with open(f"amicable_tierB_results_{LIMIT}.json", "w") as f:
        json.dump(out, f)
    print(f"done in {time.time()-t0:.0f}s -> amicable_tierB_results_{LIMIT}.json")
