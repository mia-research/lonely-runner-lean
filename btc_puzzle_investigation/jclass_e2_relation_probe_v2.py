#!/usr/bin/env python3
"""jclass_e2_relation_probe_v2.py -- CONFOUNDER CHECK on v1.

v1 result: R1 (f constant off d=0, i.e. the object EXISTS) held 6/6 at j=0, 0/6 at j=1728,
2/6 at generic j.  But the split is perfectly explained by a variable v1 did not control:

    every R1 FAILURE had EVEN n = #E(F_p);  every R1 SUCCESS had ODD n.
    (j=0 arm n = 31,79,67,127,139,199 all odd; j=1728 arm n = 44,68,80,128,164,212 all even;
     jgen failures n = 34,76,86,126 even; jgen successes n = 189,223 odd.)

j and parity-of-n are CONFOUNDED in v1 because j=1728 (rational 2-torsion at (0,0)) forces n even
ALWAYS, and the j=0 curve y^2=x^3+7 happened to be sampled only at odd n.

This script breaks the confound: sample MANY generic-j curves at ODD cyclic n, and MANY at EVEN
cyclic n, and see which variable R1 tracks.

  H_j      : R1 tracks j (mu_3 in Aut)  -> generic-j odd-n curves should FAIL R1
  H_parity : R1 tracks parity of n      -> generic-j odd-n curves should PASS R1

These make OPPOSITE predictions on the same cells, so the run discriminates.

NOTE ON SCOPE -- read before using R2.  R1 is definitional and is what this script is for.  R2
(does the constant equal -2*chi2(-1)*p) is REPORTED but NOT graded here: if R2 holds at generic j
that is a mechanism claim of consequence, and per CLAUDE.md section 2 a mechanism sweep requires
experiment-designer pre-registration, which this run does NOT have.  R2 numbers here are
descriptive only.

EXACT INTEGER ARITHMETIC ONLY.
"""
import sys, json
import audit_n1_vsign_v2_core as core
from jclass_e2_relation_probe_v1 import (curve_order_p, dlog_table_p, histograms,
                                         j_invariant, probe)


def sample(p, want_odd, n_curves, seen):
    """Find up to n_curves generic-j (j != 0, 1728) cyclic curves over F_p with n parity as asked."""
    out = []
    for A in range(1, p):
        for B in range(1, p):
            if len(out) >= n_curves:
                return out
            jv = j_invariant(p, A, B)
            if jv is None or jv == 0 or jv == 1728 % p:
                continue
            n = curve_order_p(p, A, B)
            if (n % 2 == 1) != want_odd:
                continue
            if (p, jv) in seen:
                continue
            dl, cyc = dlog_table_p(p, A, B, n)
            if not cyc:
                continue
            seen.add((p, jv))
            out.append((A, B, n))
    return out


if __name__ == "__main__":
    PS = (43, 67, 79, 127, 163, 211)
    out = {"gen_odd": [], "gen_even": [], "j0_even": []}

    print("=== generic j, ODD n   (H_j predicts R1 FAIL ; H_parity predicts R1 PASS) ===")
    for p in PS:
        seen = set()
        for (A, B, n) in sample(p, True, 3, seen):
            r = probe(p, A, B, "gOdd ")
            if r: out["gen_odd"].append(r)

    print("\n=== generic j, EVEN n  (both hypotheses predict R1 FAIL) ===")
    for p in PS:
        seen = set()
        for (A, B, n) in sample(p, False, 2, seen):
            r = probe(p, A, B, "gEven")
            if r: out["gen_even"].append(r)

    print("\n=== j = 0, EVEN n  (the cell H_j cannot explain: mu_3 PRESENT, n even) ===")
    for p in PS:
        for B in range(1, p):
            n = curve_order_p(p, 0, B)
            if n % 2 == 1:
                continue
            dl, cyc = dlog_table_p(p, 0, B, n)
            if not cyc:
                continue
            r = probe(p, 0, B, "j0Evn")
            if r: out["j0_even"].append(r)
            break

    with open("RESULT_jclass_e2_relation_probe_v2.json", "w") as fh:
        json.dump(out, fh, indent=1)

    print("\n=== VERDICT (R1 only -- R2 is descriptive, not graded, see docstring) ===")
    for k in ("gen_odd", "gen_even", "j0_even"):
        rows = out[k]
        if not rows:
            print("  %-9s : no curves found" % k); continue
        r1 = sum(1 for r in rows if r["R1_const_off_zero"])
        r2 = sum(1 for r in rows if r["R2_holds"])
        print("  %-9s : R1 %d/%d | (descriptive) R2 %d/%d | n parity: %s"
              % (k, r1, len(rows), r2, len(rows),
                 sorted({"odd" if r["n"] % 2 else "even" for r in rows})))
    go = out["gen_odd"]; j0e = out["j0_even"]
    if go and j0e:
        a = all(r["R1_const_off_zero"] for r in go)
        b = any(r["R1_const_off_zero"] for r in j0e)
        print("\n  generic-j ODD-n  R1 all pass : %s   <- H_parity predicts True, H_j predicts False" % a)
        print("  j=0     EVEN-n  R1 any pass : %s   <- H_parity predicts False, H_j predicts True" % b)
        if a and not b:
            print("  => R1 TRACKS PARITY OF n, NOT j.  H_j is refuted for the DEFINITIONAL readout.")
        elif b and not a:
            print("  => R1 TRACKS j.  H_parity refuted.")
        else:
            print("  => mixed / neither hypothesis cleanly separates -- do not conclude.")
