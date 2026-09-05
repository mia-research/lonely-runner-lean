#!/usr/bin/env python3
"""verify_120deg_exact_certificate_v1.py

PART 2 of the exact 120-degree certificate.  PART 1 = verify_120deg_symbolic_factorization_v1.py,
which PROVED (symbolically, e1 and p free indeterminates, both chi2(-1) branches):

    e2 = e1^2 - eps*p ,  e3 = eps*p*e1 ,  e4 = p^2      [eps = chi2(-1)]
        ==>  L(T) = D(T)*Dbar(T)  and  L(wT) = w*(T^2+e1*T+eps*p)*D(T)
        with  D(T) = T^2 + w*e1*T + eps*p*w^2   (monic, never degenerate)
        ==>  deg gcd(L(T), L(wT)) >= 2   UNCONDITIONALLY.

That is the LOWER bound the multi-modular census cannot certify
(CORRECTION_120deg_census_certification_direction_v1.md: min_l g_l >= g_true, an UPPER bound only).

This script supplies the one MEASURED premise, exactly, in Z[zeta_n]:

    e2(a) = e1(a)^2 - eps*p  for all a != 0   <==>   V2(a) = V1(a)^2 - 2*eps*p  for all a != 0

via the record's float-free circular-convolution route (RESULT_e2_identity_extended_verification_v1.md
section 1):  f[d] := h2[d] - (h1 conv h1)[d].  Since sum_{d!=0} zeta^{ad} = -1 for a != 0,

    V2(a) - V1(a)^2 = f[0] - c   provided f[d] = c is CONSTANT on d != 0.

Note the right-hand side carries no `a`: constancy of f on d != 0 gives UNIFORMITY OVER ALL CELLS
of a single prime for free.  It is one integer check per prime, not one per cell.

WHAT IS NEW HERE vs the record: the record verified this at 7 primes, ALL p = 3 mod 4 (eps = -1),
target +2p.  The eps = +1 branch (p = 1 mod 4, target -2p) was never derived and never checked --
yet stratum C of the census (577, 733, 1237, 1249, 1669) lives entirely there.

hist_k2 normalization: core.hist_k2 bins trace-zero points of E(F_{p^2}) into d=0
(`if T is None: d = 0`), i.e. the record's "count into bin 0" convention, sum h2 = 2p.
The target f[0]-c is convention-dependent; this script asserts sum(h2)==2p so the convention
cannot drift silently.

EXACT INTEGER ARITHMETIC ONLY.  No float anywhere in the signal path.
"""
import sys, time, json
import audit_n1_vsign_v2_core as core


def convolution_residual(h1, h2, n):
    """f[d] = h2[d] - (h1 conv h1)[d]  in Z[x]/(x^n - 1).  Exact integers."""
    conv = core.polymul_mod_cyc(h1, h1, n)
    return [h2[d] - conv[d] for d in range(n)]


def check_identity(p, n, h1, h2):
    """Returns dict: constancy of f off 0, the measured V2 - V1^2, and the two branch targets."""
    f = convolution_residual(h1, h2, n)
    off = f[1:]
    c = off[0]
    const_ok = all(v == c for v in off)
    bad = [(d + 1, v) for d, v in enumerate(off) if v != c][:5]
    eps = core.legendre(-1, p)                       # chi2(-1): +1 if p=1 mod 4 else -1
    measured = f[0] - c                              # = V2(a) - V1(a)^2 for EVERY a != 0
    return {
        "p": p, "n": n, "eps": eps,
        "sum_h2": sum(h2), "sum_h2_expected": 2 * p,
        "const_off_zero": const_ok, "c": c, "bad": bad,
        "measured_V2_minus_V1sq": measured,
        "target_this_branch": -2 * eps * p,          # the claim:  V2 = V1^2 - 2*eps*p
        "target_flipped_branch": +2 * eps * p,       # sign control: must NOT match
        "holds": const_ok and measured == -2 * eps * p,
        "flipped_also_holds": const_ok and measured == +2 * eps * p,
    }


def plant_controls(p, n, h1, h2):
    """The checker must FAIL on perturbed data.  If a plant passes, the check is vacuous."""
    res = []
    for idx, delta in ((0, 1), (3, 1), (1, -2), (0, 2 * p)):
        h2p = list(h2)
        h2p[idx % n] += delta
        r = check_identity(p, n, h1, h2p)
        res.append({"idx": idx % n, "delta": delta, "holds": r["holds"],
                    "const": r["const_off_zero"], "measured": r["measured_V2_minus_V1sq"]})
    fired = [r for r in res if r["holds"]]
    return res, (len(fired) == 0)


def run(p, tag):
    t0 = time.time()
    n = core.curve_order(p)
    assert core.is_prime(n), (p, n)
    dl = core.dlog_table(p, n)
    h1 = core.hist_k1(p, n, dl)
    h2 = core.hist_k2(p, n, dl)
    assert sum(h2) == 2 * p, ("hist_k2 normalization drifted", p, sum(h2), 2 * p)
    r = check_identity(p, n, h1, h2)
    r["secs"] = time.time() - t0
    r["tag"] = tag
    r["p_mod_4"] = p % 4
    print("  [%s] p=%5d n=%5d p%%4=%d eps=%+d | const_off_0=%-5s c=%-3d | V2-V1^2 = %-8d "
          "target(-2*eps*p) = %-8d | %s | %.1fs"
          % (tag, p, n, p % 4, r["eps"], r["const_off_zero"], r["c"],
             r["measured_V2_minus_V1sq"], r["target_this_branch"],
             "HOLDS" if r["holds"] else "*** FAILS ***" + str(r["bad"]), r["secs"]))
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
    print("\n=== IN-SAMPLE (p = 3 mod 4, eps = -1 : the record's verified branch) ===")
    for p in IN_P:
        r, _ = run(p, "IN")
        out["IN"].append(r)
    print("\n=== STRATUM S (p = 3 mod 4, eps = -1 : census primary, e2-relation NEVER checked here) ===")
    for p in S_P:
        r, _ = run(p, "S ")
        out["S"].append(r)
    print("\n=== STRATUM C (p = 1 mod 4, eps = +1 : the NEW branch, target -2p) ===")
    for p in C_P:
        r, _ = run(p, "C ")
        out["C"].append(r)

    with open("RESULT_120deg_exact_certificate_v1.json", "w") as fh:
        json.dump(out, fh, indent=1)

    print("\n=== VERDICT ===")
    allr = out["IN"] + out["S"] + out["C"]
    for k in ("IN", "S", "C"):
        rows = out[k]
        print("  %-3s : %d/%d primes hold  (eps = %s)"
              % (k, sum(1 for r in rows if r["holds"]), len(rows),
                 sorted({r["eps"] for r in rows})))
    flipped = [r["p"] for r in allr if r["flipped_also_holds"]]
    print("  sign-control (flipped branch must NOT also hold): %s"
          % ("PASS" if not flipped else "*** FAIL *** " + str(flipped)))
    print("  OVERALL: %d/%d primes satisfy  e2 = e1^2 - chi2(-1)*p  exactly, all cells."
          % (sum(1 for r in allr if r["holds"]), len(allr)))
