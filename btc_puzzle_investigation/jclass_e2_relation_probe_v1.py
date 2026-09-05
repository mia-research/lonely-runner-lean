#!/usr/bin/env python3
"""jclass_e2_relation_probe_v1.py

RELEVANCE CHECK for queue item B (NEXT_SESSION_PROMPT_2026-08-01_v2.md), via the reduction in
RESULT_120deg_certificate_regrade_v1.md section 5.

QUESTION (definitional, decides B outright, strictly precedes any arm-building):
    Is the V1/V2 convolution structure -- and hence the quartic L* and the e2 relation -- DEFINED
    at j != 0, or is it j=0-specific?

THE STATISTIC (identical to verify_120deg_exact_certificate_v2.py, generalized to y^2 = x^3+Ax+B):
    h1[d] = sum over P in E(F_p) with dlog(P)=d of chi2(y_P)
    h2[d] = sum over P in E(F_{p^2}) with dlog(Tr P)=d of chi2^{(2)}(y_P)     [Tr P = P + P^p]
    f[d]  = h2[d] - (h1 conv h1)[d]   in Z[x]/(x^n - 1)

TWO SEPARATE READOUTS, and they answer two different questions:
  (R1) IS f CONSTANT off d=0?   <-- the DEFINITIONAL question.  If yes, V2(a)-V1(a)^2 is a single
       integer independent of a (for gcd(a,n)=1), i.e. the object B needs EXISTS at this j.
  (R2) IF SO, does that integer equal -2*chi2(-1)*p?  <-- the MECHANISM question B was built to ask.
       R2 is only meaningful when R1 holds.  R1 failing is the "B evaporates" outcome.

ARMS (Aut(E) over Fbar, ordinary case):
    j = 0     -> mu_6  (contains mu_3)   POSITIVE CONTROL: must reproduce the established result
    j = 1728  -> mu_4  (no mu_3)         the discriminating arm
    j generic -> mu_2  (no mu_3)         the discriminating arm

POSITIVE CONTROL IS LOAD-BEARING: this is new code.  A null at j != 0 means nothing unless the SAME
code reproduces the known j=0 answer (f constant off 0, f[0]-c = -2*chi2(-1)*p).  The control is
ordered FIRST and the run HALTS if it fails.

E(F_p) is required CYCLIC (so dlog is a clean Z/n index); prime order is NOT required -- that
requirement was an artifact of the cell/gcd construction, and j=1728 can never have prime order
(rational 2-torsion at (0,0)).

EXACT INTEGER ARITHMETIC ONLY.  No float anywhere.
"""
import sys, time, json
import audit_n1_vsign_v2_core as core


# ---------------------------------------------------------------- general Weierstrass over F_p
def ec_add_p(P, Q, p, A):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        lam = (3 * x1 * x1 + A) % p * pow(2 * y1 % p, p - 2, p) % p
    else:
        lam = (y2 - y1) * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def curve_order_p(p, A, B):
    n = p + 1
    for x in range(p):
        n += core.legendre((x * x % p * x + A * x + B) % p, p)
    return n


def points_p(p, A, B):
    pts = []
    for x in range(p):
        r = (x * x % p * x + A * x + B) % p
        if r == 0:
            pts.append((x, 0)); continue
        if core.legendre(r, p) != 1: continue
        y = core.tonelli(r, p)
        pts.append((x, y)); pts.append((x, (-y) % p))
    return pts


def dlog_table_p(p, A, B, n):
    """Requires E(F_p) cyclic of order n.  Returns (table, ok)."""
    for G in points_p(p, A, B):
        tbl = {}; P = None
        for m in range(n):
            key = (0, 0) if P is None else P
            if P is not None: tbl[P] = m
            P = ec_add_p(P, G, p, A)
        if P is None and len(tbl) == n - 1:
            return tbl, True                      # G has order exactly n -> cyclic
    return None, False


# ---------------------------------------------------------------- general Weierstrass over F_{p^2}
def ec_add_2(F, P, Q, A2):
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2 and F.add(y1, y2) == (0, 0): return None
    if P == Q:
        num = F.add(F.mul((3 % F.p, 0), F.sq(x1)), A2)
        den = F.add(y1, y1)
    else:
        num = F.sub(y2, y1); den = F.sub(x2, x1)
    lam = F.mul(num, F.inv(den))
    x3 = F.sub(F.sub(F.sq(lam), x1), x2)
    return (x3, F.sub(F.mul(lam, F.sub(x1, x3)), y1))


def histograms(p, A, B, n, dl):
    """h1 over E(F_p); h2 over E(F_{p^2}) binned by dlog of the trace.  Mirrors core exactly."""
    half1 = (p - 1) // 2
    h1 = [0] * n
    for x in range(p):
        r = (x * x % p * x + A * x + B) % p
        if r == 0 or core.legendre(r, p) != 1: continue
        y = core.tonelli(r, p)
        for yy in (y, (-y) % p):
            c = 1 if pow(yy, half1, p) == 1 else -1
            h1[dl[(x, yy)]] += c

    F = core.F2(p)
    q = p * p; half2 = (q - 1) // 2
    A2 = (A % p, 0); B2 = (B % p, 0)
    sqrt_tab = {}
    for a in range(p):
        for b in range(p):
            sqrt_tab[F.sq((a, b))] = (a, b)
    h2 = [0] * n
    for a in range(p):
        for b in range(p):
            x = (a, b)
            r = F.add(F.add(F.mul(F.sq(x), x), F.mul(A2, x)), B2)
            if r == (0, 0): continue
            y = sqrt_tab.get(r)
            if y is None: continue
            for yy in (y, F.neg(y)):
                c = 1 if F.pw(yy, half2) == (1, 0) else -1
                P = (x, yy)
                T = ec_add_2(F, P, (F.frob(x), F.frob(yy)), A2)
                if T is None:
                    d = 0
                else:
                    if not (T[0][1] == 0 and T[1][1] == 0):
                        return None, None, "trace not in E(F_p)"
                    d = dl[(T[0][0], T[1][0])]
                h2[d] += c
    return h1, h2, None


# ---------------------------------------------------------------- the statistic
def probe(p, A, B, label):
    t0 = time.time()
    n = curve_order_p(p, A, B)
    dl, cyc = dlog_table_p(p, A, B, n)
    if not cyc:
        print("  [%s] p=%4d (A,B)=(%d,%d) n=%4d -> NOT CYCLIC, skipped" % (label, p, A, B, n))
        return None
    h1, h2, err = histograms(p, A, B, n, dl)
    if err:
        print("  [%s] p=%4d (A,B)=(%d,%d) -> %s" % (label, p, A, B, err))
        return None
    conv = core.polymul_mod_cyc(h1, h1, n)
    f = [h2[d] - conv[d] for d in range(n)]
    off = f[1:]
    c = off[0]
    const_ok = all(v == c for v in off)
    distinct = len(set(off))
    eps = core.legendre(-1, p)
    measured = f[0] - c
    target = -2 * eps * p
    r = {"label": label, "p": p, "A": A, "B": B, "n": n, "n_prime": core.is_prime(n),
         "eps": eps, "R1_const_off_zero": const_ok, "distinct_off_zero": distinct,
         "c": c, "measured": measured, "target": target,
         "R2_holds": const_ok and measured == target, "secs": time.time() - t0}
    print("  [%s] p=%4d (A,B)=(%3d,%3d) n=%4d%s eps=%+d | R1 const_off_0=%-5s (distinct=%-4d) | "
          "R2 V2-V1^2=%-7s target=%-7d %s | %.1fs"
          % (label, p, A, B, n, "P" if r["n_prime"] else " ", eps, const_ok, distinct,
             measured if const_ok else "n/a", target,
             ("HOLDS" if r["R2_holds"] else "differs") if const_ok else "(R2 undefined)",
             r["secs"]))
    sys.stdout.flush()
    return r


def j_invariant(p, A, B):
    """j = 1728 * 4A^3 / (4A^3 + 27B^2)  in F_p, as an exact modular value."""
    d = (4 * pow(A, 3, p) + 27 * pow(B, 2, p)) % p
    if d == 0: return None                      # singular
    return 1728 * (4 * pow(A, 3, p)) % p * pow(d, p - 2, p) % p


if __name__ == "__main__":
    PS = (43, 67, 79, 127, 163, 211)

    out = {"j0": [], "j1728": [], "jgen": []}

    print("=== ARM j=0  (Aut = mu_6, contains mu_3) -- POSITIVE CONTROL, must reproduce the record ===")
    for p in PS:
        r = probe(p, 0, 7, "j0   ")
        if r: out["j0"].append(r)
    ctl = [r for r in out["j0"] if r["n_prime"]]
    ctl_ok = len(ctl) > 0 and all(r["R1_const_off_zero"] and r["R2_holds"] for r in ctl)
    print("  CONTROL VERDICT: %s (%d/%d prime-order j=0 curves reproduce f const + f[0]-c = -2*eps*p)"
          % ("PASS" if ctl_ok else "*** FAIL -- new code disagrees with the record, HALT ***",
             sum(1 for r in ctl if r["R2_holds"]), len(ctl)))
    assert ctl_ok, "positive control failed -> the generalized instrument is not trustworthy"

    print("\n=== ARM j=1728  (Aut = mu_4, NO mu_3) ===")
    for p in PS:
        for A in range(1, p):
            if core.legendre(A, p) == 1 and A != 0:
                r = probe(p, A, 0, "j1728")
                if r: out["j1728"].append(r)
                break

    print("\n=== ARM j generic  (Aut = mu_2, NO mu_3) ===")
    for p in PS:
        found = 0
        for A in range(1, p):
            for B in range(1, p):
                jv = j_invariant(p, A, B)
                if jv is None or jv == 0 or jv == 1728 % p: continue
                r = probe(p, A, B, "jgen ")
                if r:
                    out["jgen"].append(r); found = 1
                break
            if found: break

    with open("RESULT_jclass_e2_relation_probe_v1.json", "w") as fh:
        json.dump(out, fh, indent=1)

    print("\n=== VERDICT ===")
    for k in ("j0", "j1728", "jgen"):
        rows = out[k]
        if not rows:
            print("  %-6s : no curves", k); continue
        r1 = sum(1 for r in rows if r["R1_const_off_zero"])
        r2 = sum(1 for r in rows if r["R2_holds"])
        print("  %-6s : R1 (f constant off 0) %d/%d | R2 (= -2*eps*p) %d/%d | distinct-off-0 seen: %s"
              % (k, r1, len(rows), r2, len(rows), sorted({r["distinct_off_zero"] for r in rows})))
    print("\n  R1 is the DEFINITIONAL readout: if R1 fails off j=0, the quartic/e2 object is")
    print("  j=0-specific and queue item B evaporates in the form proposed.")
