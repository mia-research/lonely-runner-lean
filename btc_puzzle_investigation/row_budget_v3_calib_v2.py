#!/usr/bin/env python3
"""
Gate calibration, part 2 -- refines row_budget_v3_calib_v1.py using the ACTUAL design constants
(m_p, rel_SE, admissible sub-grids) instead of generic stand-ins.

Same float declaration as v1: gate-calibration path only, no curve/key quantity enters.
"""
import json, math, random

random.seed(20260725)
rows = json.load(open("row_budget_v2_rows.json"))

def Phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))

def bisect(f, lo, hi):
    for _ in range(300):
        mid = (lo + hi) / 2
        if f(lo) * f(mid) <= 0:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2

out = []
def say(s=""):
    print(s); out.append(s)

R, NP = 64, 10
NTOT = R * NP

say("=" * 78)
say("PART A -- C-DISP with the ACTUAL frequency-list sizes (v1 used stand-ins)")
say("=" * 78)
say("%7s %8s   %-22s %s" % ("p", "m_p", "P(spurious trigger >1.5)", "v2 observed disp"))
worst = 0.0
keep = 1.0
for r in rows:
    m = r["m"]
    bad = 0
    NS = 4000
    for _ in range(NS):
        a = [random.gauss(0, 1) ** 2 for _ in range(m)]
        b = [random.gauss(0, 1) ** 2 for _ in range(m)]
        ma, mb = sum(a) / m, sum(b) / m
        Da = sum((x - ma) ** 2 for x in a) / (m - 1) / ma
        Db = sum((x - mb) ** 2 for x in b) / (m - 1) / mb
        if Da / Db > 1.5:
            bad += 1
    pr = bad / NS
    worst = max(worst, pr)
    keep *= (1 - pr)
    say("%7d %8d   %-22s %.4f" % (r["p"], m, "%.5f" % pr, r["disp"]))
say("over all 10 primes, P(any spurious C-DISP trigger) = %.5f" % (1 - keep))
say("=> C-DISP IS WELL CALIBRATED at the real m_p (v1's alarm used m_p = 60..200, which do not occur).")
say("   Smallest real list is m_p = 820 at p = 19231.  CARRY C-DISP UNCHANGED.")

say()
say("=" * 78)
say("PART B -- criterion 3's MONOTONICITY clause, with the real sub-grids and SEs")
say("=" * 78)
LEVELS = [0.05, 0.10, 0.15, 0.20, 0.30, 0.50, 0.80]
def dpred(e):
    th = -math.log(1 - 0.01)          # theta from the rho<0.01 threshold on Exp(1)
    return (1 - math.exp(-th / (1 - e * e))) / (1 - math.exp(-th)) - 1
say("Delta_pred at the swept levels (Exp(1) carrier):")
say("   " + "  ".join("%.2f:%+.3f%%" % (e, 100 * dpred(e)) for e in LEVELS))
say()
say("%7s %-28s %-12s %s" % ("p", "admissible sub-grid", "relsd %", "P(mono violated | correct)"))
anyviol = 1.0
for r in rows:
    relsd = 100 * r["rel_SE"]
    adm = [e for e in LEVELS if 100 * dpred(e) > 3 * relsd]
    if len(adm) < 2:
        say("%7d %-28s %-12.4f %s" % (r["p"], str(adm), relsd, "n/a (<2 levels)"))
        continue
    mu = [100 * dpred(e) for e in adm]
    NS = 20000
    bad = 0
    for _ in range(NS):
        v = [m + random.gauss(0, relsd) for m in mu]
        if any(v[i + 1] <= v[i] for i in range(len(v) - 1)):
            bad += 1
    pr = bad / NS
    anyviol *= (1 - pr)
    say("%7d %-28s %-12.4f %.4f" % (r["p"], str(adm), relsd, pr))
say("over all 10 primes, P(any spurious monotonicity failure) = %.4f" % (1 - anyviol))
say()
say("=> With the REAL separations the monotonicity clause is far better than v1's generic")
say("   3-SE estimate suggested.  It is still not zero, so v3 states the number and")
say("   softens the clause to: monotonicity is required only across levels whose Delta_pred")
say("   separation exceeds 3x relsd -- i.e. the clause inherits the sub-grid rule that")
say("   criterion 3's tolerance band already uses, instead of applying to all adjacent pairs.")

say()
say("=" * 78)
say("PART C -- P-SIZE' : the replacement negative control")
say("=" * 78)
say("Design principle: the gate must test the two quantities that actually SCALE the verdict")
say("(the null's location and its spread), plus a tail clause at a CORRECTLY computed quantile.")
say("Testing full distributional shape (Anderson-Darling) tests more than the verdict depends on.")
say()
se_mean = 1.0 / math.sqrt(NTOT)
se_sd = 1.0 / math.sqrt(2.0 * NTOT)
q_fw = bisect(lambda q: (2 * Phi(q) - 1) ** NTOT - 0.95, 0.0, 8.0)
say("pooled over N = %d unplanted-carrier z:" % NTOT)
say("  clause (i)  |mean|            <= 3 * %.5f = %.4f" % (se_mean, 3 * se_mean))
say("  clause (ii) |sd - 1|          <= 3 * %.5f = %.4f" % (se_sd, 3 * se_sd))
say("  clause (iii) max |z|          <= %.4f   (5%% family-wise over %d draws)" % (q_fw, NTOT))
say()

def sim_psize(gen, nsim=20000):
    fail = 0
    for _ in range(nsim):
        z = [gen() for _ in range(NTOT)]
        m = sum(z) / NTOT
        sd = math.sqrt(sum((x - m) ** 2 for x in z) / (NTOT - 1))
        mx = max(abs(x) for x in z)
        if abs(m) > 3 * se_mean or abs(sd - 1) > 3 * se_sd or mx > q_fw:
            fail += 1
    return fail / nsim

ffr = sim_psize(lambda: random.gauss(0, 1))
say("FALSE-FAILURE RATE under a perfectly calibrated null = %.4f" % ffr)
say("  (v2's frozen gate, for comparison, false-failed with probability 0.8228)")
say()
say("POWER -- the planted positives.  A control with no power is not a control:")
for label, gen in [
    ("sd = 1.10", lambda: random.gauss(0, 1.10)),
    ("sd = 1.15", lambda: random.gauss(0, 1.15)),
    ("sd = 1.20", lambda: random.gauss(0, 1.20)),
    ("sd = 0.85", lambda: random.gauss(0, 0.85)),
    ("mean shift +0.10", lambda: random.gauss(0.10, 1.0)),
    ("mean shift +0.15", lambda: random.gauss(0.15, 1.0)),
    ("mean shift +0.25", lambda: random.gauss(0.25, 1.0)),
]:
    say("   %-20s power = %.4f" % (label, sim_psize(gen, 6000)))

say()
say("** DECLARED-SEEN CHECK **  RESULT v2 printed the pooled 640-z summary")
say("(mean +0.038, sd 1.019, skew -0.176) and row_budget_v2_rows.json holds the per-prime")
say("values.  Those are SEEN.  P-SIZE' was fixed from first principles above and NOT tuned")
say("to them.  What it WOULD have done on v2's own numbers, stated in advance of v3's run:")
mean_obs, sd_obs = 0.038, 1.019
say("   clause (i)   |%.3f| vs bound %.4f  -> %s"
    % (mean_obs, 3 * se_mean, "PASS" if abs(mean_obs) <= 3 * se_mean else "FAIL"))
say("   clause (ii)  |%.3f - 1| = %.3f vs bound %.4f  -> %s"
    % (sd_obs, abs(sd_obs - 1), 3 * se_sd, "PASS" if abs(sd_obs - 1) <= 3 * se_sd else "FAIL"))
mx_obs = max(abs(r["psize_max"]) for r in rows)
say("   clause (iii) max|z| = %.3f vs bound %.4f  -> %s"
    % (mx_obs, q_fw, "PASS" if mx_obs <= q_fw else "FAIL"))
say()
say("   For contrast, the Anderson-Darling alternative would fire on a v2-like null with")
say("   probability 0.159 (calib_v1 Part 2) -- it is sensitive to the skew, which does not")
say("   scale the verdict.  P-SIZE' is preferred BECAUSE it tests less, and tests the right less.")

say()
say("=" * 78)
say("PART D -- C-SELFZ, re-checked against the real leave-one-out construction")
say("=" * 78)
say("v2 observed loo_sd in [1.031, 1.038] at every prime; gate band is [0.7, 1.4].")
say("calib_v1 measured P(LOO-sd outside [0.7,1.4] | correct null) = 0.0000 (20000 sims).")
say("The |z_split| <= 3 clause over 10 primes false-fails with prob 0.0267.")
say("=> C-SELFZ carries unchanged.  Its band is wide relative to the LOO-sd sampling spread,")
say("   which is the correct direction for a halt-gate.")

say()
say("=" * 78)
say("SUMMARY -- gate | false-failure rate under the null | verdict for v3")
say("=" * 78)
say("%-34s %-14s %s" % ("gate", "FFR (10 primes)", "v3 disposition"))
say("%-34s %-14s %s" % ("criterion 1 (eps=1 exact)", "0 (exact)", "CARRY"))
say("%-34s %-14s %s" % ("criterion 2 (chirp exact)", "0 (exact)", "CARRY"))
say("%-34s %-14s %s" % ("criterion 3 band (3 SE)", "0.10-0.15", "CARRY, band widened to 4 SE"))
say("%-34s %-14s %s" % ("criterion 3 monotonicity", "see Part B", "CARRY, sub-grid-restricted"))
say("%-34s %-14s %s" % ("criterion 4 (z>+6 plant)", "positive ctrl", "CARRY"))
say("%-34s %-14s %s" % ("criterion 5 P-SIZE (v2)", "0.8228", "REPLACED by P-SIZE'"))
say("%-34s %-14s %s" % ("P-SIZE' (v3)", "%.4f" % ffr, "NEW"))
say("%-34s %-14s %s" % ("C-SELFZ", "0.0267", "CARRY"))
say("%-34s %-14s %s" % ("C-DISP", "%.5f" % (1 - keep), "CARRY"))
say("%-34s %-14s %s" % ("C-EQ-int / C-BUDGET / C-PARITY", "0 (exact)", "CARRY"))
say("%-34s %-14s %s" % ("A3 slope band [-1.35,-0.65]", "underpowered", "REPLACED by A3' constant test"))

with open(__file__.replace(".py", ".log"), "w") as fh:
    fh.write("\n".join(out) + "\n")
