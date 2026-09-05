"""
Analysis of the Tier A exact arm against PREREG_amicable_correspondence_bits_v3.md.

Firing (v3 S9, D7):  |Gamma*| / |Gamma*_forced| > 1, with forced | gamma, AND DEG false.
orbit_exact does NOT gate firing -- it CLASSIFIES a positive into cell 1a vs 1b.

Validity gates that void the run (v3 S9 cell 9 / cell 6):
  - P1 plant misses any k
  - S2A inequality |image| <= (n-1)/|Gamma*_inv| violated anywhere
  - DEG(N_const) false on any curve
  - a DEG-true hypothesis feature reported as firing

Exactness: Fisher one-sided via math.comb on Fraction. No float decides anything.
"""
import json, sys
from math import comb
from fractions import Fraction
from collections import Counter

HYP = ["PhiA", "PhiB", "PhiC", "PhiD"]      # the 4 frozen hypothesis features
ARMB = ["A2_1_rho"]


def fisher_1sided(a, m1, b, m2):
    k = a + b
    N = m1 + m2
    num = sum(comb(m1, i) * comb(m2, k - i)
              for i in range(a, min(m1, k) + 1) if 0 <= k - i <= m2)
    return Fraction(num, comb(N, k))


def fires(row, feat):
    f = row.get(feat)
    if not f:
        return None
    if f["DEG"]:
        return False
    g, fo = f["gamma"], f.get("forced", 1)
    return bool(g % fo == 0 and g // fo > 1)


def analyze(path):
    d = json.load(open(path))
    A, C = d["amicable"], d["control"]
    print(f"Tier A: amicable curves = {len(A)}, matched controls = {len(C)}")
    print(f"(108 2-cycles x 2 orientations; spec v3 S6 Tier A line)\n")

    # ================= VALIDITY GATES =================
    print("=" * 66)
    print("VALIDITY GATES (v3 S9 cells 6 and 9)")
    print("=" * 66)
    voids = []

    miss = [m for m in d["plant_misses"] if m["misses"]]
    print(f"P1 plant ladder: curves with a missed k = {len(miss)} / {len(d['plant_misses'])}")
    if miss:
        voids.append("P1 missed k -> cell 6")
        for m in miss[:5]:
            print("   ", m)

    bad_gate = [(r["p"], f) for r in A + C for f in HYP + ARMB + ["N_const", "N0_diagnostic"]
                if f in r and not r[f]["gate_ok"]]
    print(f"S2A inequality gate violations: {len(bad_gate)}")
    if bad_gate:
        voids.append("inequality violated -> cell 9")
        print("   ", bad_gate[:5])

    nc_bad = [r["p"] for r in A + C if not r["N_const"]["DEG"]]
    print(f"DEG(N_const) false on: {len(nc_bad)} curves")
    if nc_bad:
        voids.append("DEG(N_const) false -> cell 9")

    deg_fire = [(r["p"], f) for r in A + C for f in HYP
                if f in r and r[f]["DEG"] and fires(r, f)]
    print(f"DEG-true hypothesis feature reported firing: {len(deg_fire)}")
    if deg_fire:
        voids.append("DEG-true fired -> cell 9")

    if voids:
        print("\n*** RUN VOID: " + "; ".join(voids) + " ***")
        return
    print("\nAll validity gates pass. Statistics may be read.\n")

    # ================= ARM-A =================
    print("=" * 66)
    print("ARM-A  exact arm  (firing = |Gamma*|/|forced| > 1, DEG false)")
    print("=" * 66)
    for feat in HYP:
        a = sum(1 for r in A if fires(r, feat))
        b = sum(1 for r in C if fires(r, feat))
        print(f"\n{feat}:  amicable {a}/{len(A)}   control {b}/{len(C)}"
              f"   [threshold for cell 1: >= 77/108 per stratum]")
        if a > 0 or b > 0:
            p = fisher_1sided(a, len(A), b, len(C))
            print(f"   Fisher one-sided P = {float(p):.4g}  sig@0.01 = {p < Fraction(1,100)}")
        for tag, rs in (("amic", A), ("ctrl", C)):
            gd = Counter(r[feat]["gamma"] for r in rs if feat in r)
            gi = Counter(r[feat]["gamma_inv"] for r in rs if feat in r)
            oe = Counter(r[feat]["orbit_exact"] for r in rs if feat in r)
            print(f"   [{tag}] |Gamma*| {dict(sorted(gd.items()))}"
                  f"  |Gamma*_inv| {dict(sorted(gi.items()))}"
                  f"  orbit_exact {dict(oe)}")

    print("\n--- orientation strata (D3): cell 1 needs BOTH strata ---")
    for feat in HYP:
        line = f"  {feat:6s}"
        for orient in ("p<n", "p>n"):
            a = sum(1 for r in A if r["orientation"] == orient and fires(r, feat))
            na = sum(1 for r in A if r["orientation"] == orient)
            b = sum(1 for r in C if r["orientation"] == orient and fires(r, feat))
            nb = sum(1 for r in C if r["orientation"] == orient)
            line += f"   {orient}: amic {a}/{na} ctrl {b}/{nb}"
        print(line)

    # ================= ARM-B =================
    print("\n" + "=" * 66)
    print("ARM-B  channel-width statistics (reported separately; S9 cells 11-16)")
    print("=" * 66)
    feat = "A2_1_rho"
    a = sum(1 for r in A if fires(r, feat))
    b = sum(1 for r in C if fires(r, feat))
    print(f"\nA2-1  Gamma*(rho), rho = (x mod n, y mod n)  -- the family-level floor")
    print(f"   amicable {a}/{len(A)}   control {b}/{len(C)}   [cell 11 needs >= 77/108]")
    for tag, rs in (("amic", A), ("ctrl", C)):
        gi = Counter(r[feat]["gamma_inv"] for r in rs if feat in r)
        oe = Counter(r[feat]["orbit_exact"] for r in rs if feat in r)
        print(f"   [{tag}] |Gamma*(rho)| {dict(sorted(gi.items()))}  orbit_exact {dict(oe)}")

    print(f"\nA2-2  does the GLV action descend affinely through r(x) = x mod n")
    for tag, rs in (("amic", A), ("ctrl", C)):
        ag = te = perfect = 0
        for r in rs:
            s = r.get("A2_2")
            if not s:
                continue
            ag += s["agree"]; te += s["tested"]
            if s["agree"] == s["tested"]:
                perfect += 1
        print(f"   [{tag}] pooled agreement {ag}/{te}   curves with FULL descent {perfect}/{len(rs)}")

    # ================= diagnostics =================
    print("\n" + "=" * 66)
    print("DISCLOSED DIAGNOSTICS (no tally, no K)")
    print("=" * 66)
    for tag, rs in (("amic", A), ("ctrl", C)):
        gi = Counter(r["N0_diagnostic"]["image"] for r in rs if "N0_diagnostic" in r)
        print(f"  N0 (coarsening of PhiA, D8) [{tag}] |image| dist {dict(sorted(gi.items()))}")
    for tag, rs in (("amic", A), ("ctrl", C)):
        bd = [r["PhiD"]["bot_rate_num"] for r in rs if "PhiD" in r]
        dn = [r["PhiD"]["bot_rate_den"] for r in rs if "PhiD" in r]
        print(f"  PhiD BOT rate [{tag}]: pooled {sum(bd)}/{sum(dn)}")
    for tag, rs in (("amic", A), ("ctrl", C)):
        ne = Counter("prime_p" if r["nE_tilde"] == r["p"] else "other" for r in rs)
        print(f"  #Etilde(F_n) [{tag}]: {dict(ne)}")


if __name__ == "__main__":
    analyze(sys.argv[1] if len(sys.argv) > 1 else "amicable_tierA_results_200000.json")
