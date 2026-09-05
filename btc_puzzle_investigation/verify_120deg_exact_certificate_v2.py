#!/usr/bin/env python3
"""verify_120deg_exact_certificate_v2.py

v2 of PART 2.  Supersedes v1 in ONE respect: v1 hard-asserted `sum(h2) == 2p`, a normalization
constant imported from RESULT_e2_identity_extended_verification_v1.md section 1 -- where it was
established only on the p = 3 mod 4 branch.  It fired at the first p = 1 mod 4 prime
(p=577: sum h2 = 1150, not 1154).  The assert was testing an ASSUMPTION, not the claim.

v2 therefore RECORDS sum(h2) as a diagnostic and lets the identity be measured on its own terms.
v1's IN + S results (17 primes, p = 3 mod 4) stand unchanged and are reproduced here.

PART 1 (verify_120deg_symbolic_factorization_v1.py) PROVED symbolically, e1 and p free
indeterminates, both branches:

    e2 = e1^2 - eps*p ,  e3 = eps*p*e1 ,  e4 = p^2      [eps = chi2(-1)]
      ==> L(T) = D(T)*Dbar(T),  L(wT) = w*(T^2+e1*T+eps*p)*D(T),
          D(T) = T^2 + w*e1*T + eps*p*w^2   monic, never degenerate
      ==> deg gcd(L(T), L(wT)) >= 2  UNCONDITIONALLY.

This script measures the one remaining input, exactly, via the circular-convolution route:
    f[d] := h2[d] - (h1 conv h1)[d];  if f is CONSTANT = c on d != 0 then
    V2(a) - V1(a)^2 = f[0] - c  for EVERY a != 0   (no `a` on the right: uniform over all cells).

EXACT INTEGER ARITHMETIC ONLY.  No float anywhere in the signal path.
"""
import sys, time, json
import audit_n1_vsign_v2_core as core


def convolution_residual(h1, h2, n):
    conv = core.polymul_mod_cyc(h1, h1, n)
    return [h2[d] - conv[d] for d in range(n)]


def check_identity(p, n, h1, h2):
    f = convolution_residual(h1, h2, n)
    off = f[1:]
    c = off[0]
    const_ok = all(v == c for v in off)
    bad = [(d + 1, v) for d, v in enumerate(off) if v != c][:5]
    eps = core.legendre(-1, p)
    measured = f[0] - c
    return {
        "p": p, "n": n, "eps": eps,
        "sum_h1": sum(h1), "sum_h2": sum(h2), "two_p": 2 * p,
        "sum_h2_minus_2p": sum(h2) - 2 * p,
        "const_off_zero": const_ok, "c": c, "bad": bad,
        "measured_V2_minus_V1sq": measured,
        "target_this_branch": -2 * eps * p,
        "holds": const_ok and measured == -2 * eps * p,
        "flipped_also_holds": const_ok and measured == +2 * eps * p,
    }


def cube_roots_of_negB(p, B=7):
    """#{x in F_{p^2} : x^3 + B = 0} -- the y=0 points the enumeration treats specially."""
    F = core.F2(p)
    cnt = 0
    negB = ((-B) % p, 0)
    for a in range(p):
        for b in range(p):
            x = (a, b)
            if F.mul(F.sq(x), x) == negB:
                cnt += 1
    return cnt


def plant_controls(p, n, h1, h2):
    res = []
    for idx, delta in ((0, 1), (3, 1), (1, -2), (0, 2 * p)):
        h2p = list(h2)
        h2p[idx % n] += delta
        r = check_identity(p, n, h1, h2p)
        res.append({"idx": idx % n, "delta": delta, "holds": r["holds"],
                    "const": r["const_off_zero"], "measured": r["measured_V2_minus_V1sq"]})
    return res, not any(r["holds"] for r in res)


def run(p, tag, diag=False):
    t0 = time.time()
    n = core.curve_order(p)
    assert core.is_prime(n), (p, n)
    dl = core.dlog_table(p, n)
    h1 = core.hist_k1(p, n, dl)
    h2 = core.hist_k2(p, n, dl)
    r = check_identity(p, n, h1, h2)
    if diag:
        r["y0_points"] = cube_roots_of_negB(p)
    r["secs"] = time.time() - t0
    r["tag"] = tag
    print("  [%s] p=%5d n=%5d p%%4=%d eps=%+d | const_off_0=%-5s c=%-3d | sum_h2-2p=%-4d | "
          "V2-V1^2 = %-8d target = %-8d | %s | %.1fs"
          % (tag, p, n, p % 4, r["eps"], r["const_off_zero"], r["c"], r["sum_h2_minus_2p"],
             r["measured_V2_minus_V1sq"], r["target_this_branch"],
             "HOLDS" if r["holds"] else "*** FAILS *** " + str(r["bad"][:3]), r["secs"]))
    sys.stdout.flush()
    return r, (h1, h2, n)


if __name__ == "__main__":
    IN_P = (43, 67, 79, 127, 163, 211, 547)
    S_P = (823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503)
    C_P = (577, 733, 1237, 1249, 1669)

    print("=== PLANT CONTROLS (checker must FAIL on perturbed h2) ===")
    _, (h1c, h2c, nc) = run(43, "ctl")
    plants, ctl_ok = plant_controls(43, nc, h1c, h2c)
    for pl in plants:
        print("   plant h2[%d] += %-5d -> const=%-5s measured=%-6d holds=%s"
              % (pl["idx"], pl["delta"], pl["const"], pl["measured"], pl["holds"]))
    print("   PLANT VERDICT:", "PASS (checker is not vacuous)" if ctl_ok else "*** FAIL ***")
    assert ctl_ok, "plant controls failed -> HALT"

    out = {"IN": [], "S": [], "C": []}
    print("\n=== IN-SAMPLE (p = 3 mod 4, eps = -1) ===")
    for p in IN_P:
        r, _ = run(p, "IN")
        out["IN"].append(r)
    print("\n=== STRATUM S (p = 3 mod 4, eps = -1 : census primary) ===")
    for p in S_P:
        r, _ = run(p, "S ")
        out["S"].append(r)
    print("\n=== STRATUM C (p = 1 mod 4, eps = +1 : the NEW branch, target -2p) ===")
    for p in C_P:
        r, _ = run(p, "C ", diag=True)
        out["C"].append(r)

    with open("RESULT_120deg_exact_certificate_v2.json", "w") as fh:
        json.dump(out, fh, indent=1)

    print("\n=== DIAGNOSTIC: sum(h2) - 2p by branch ===")
    for k in ("IN", "S", "C"):
        print("  %-3s eps=%s : sum_h2-2p = %s%s"
              % (k, sorted({r["eps"] for r in out[k]}),
                 sorted({r["sum_h2_minus_2p"] for r in out[k]}),
                 "   y=0 points: %s" % sorted({r.get("y0_points") for r in out[k]}) if k == "C" else ""))

    print("\n=== VERDICT ===")
    allr = out["IN"] + out["S"] + out["C"]
    for k in ("IN", "S", "C"):
        rows = out[k]
        print("  %-3s : %d/%d primes hold  (eps = %s)"
              % (k, sum(1 for r in rows if r["holds"]), len(rows), sorted({r["eps"] for r in rows})))
    flipped = [r["p"] for r in allr if r["flipped_also_holds"]]
    print("  sign-control (flipped branch must NOT also hold): %s"
          % ("PASS" if not flipped else "*** FAIL *** " + str(flipped)))
    print("  OVERALL: %d/%d primes satisfy  e2 = e1^2 - chi2(-1)*p  exactly, all cells."
          % (sum(1 for r in allr if r["holds"]), len(allr)))
