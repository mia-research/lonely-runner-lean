#!/usr/bin/env python3
"""
Gate calibration, part 3 -- FINAL P-SIZE' design.

Part B below is not a calibration but a CORRECTION: RESULT_row_budget_lowtail_v2.md section 3
mis-states which primes failed its own criterion 5, and the omitted prime is the one where the
null spread is genuinely wrong.  Recorded here with the recomputation.

Float declaration as in calib_v1/v2: gate-calibration path only.
"""
import json, math, random, statistics

random.seed(20260725)
rows = json.load(open("row_budget_v2_rows.json"))
R, NP = 64, 10
NTOT = R * NP

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

say("=" * 78)
say("PART A -- CORRECTION to RESULT_row_budget_lowtail_v2.md section 3")
say("=" * 78)
say("That file states:")
say('  "The second clause passes everywhere (0.031...0.094). The max-clause fails at')
say('   p=211 (4.04) and p=433 (3.87)."')
say()
say("Recomputed from row_budget_v2_rows.json (the run's own output):")
mx_fail = [r["p"] for r in rows if r["psize_max"] > 3]
fr_fail = [r["p"] for r in rows if r["psize_frac"] > 0.10]
say("  primes failing max|z| > 3      : %s   (v2 named only [211, 433])" % mx_fail)
say("  primes failing frac|z|>2 > 0.10: %s   (v2 said NONE)" % fr_fail)
say("  observed frac range            : %.4f ... %.4f   (v2 said 0.031...0.094)"
    % (min(r["psize_frac"] for r in rows), max(r["psize_frac"] for r in rows)))
say()
say("=> p = 19231 fails BOTH clauses (max|z| = 4.8889, frac = 0.1406) and is absent from")
say("   v2's account.  It is the LARGEST violation, not a marginal one.")

say()
say("=" * 78)
say("PART B -- is that a gate artifact, or a genuinely mis-calibrated null?")
say("=" * 78)
se_sd = 1.0 / math.sqrt(2 * (R - 1))
say("SE of a sd estimated from R=64 draws = %.4f" % se_sd)
say("%7s %8s %9s %10s" % ("p", "m_p", "sd", "(sd-1)/SE"))
for r in rows:
    say("%7d %8d %9.4f %10.2f" % (r["p"], r["m"], r["psize_sd"], (r["psize_sd"] - 1) / se_sd))
r = [x for x in rows if x["p"] == 19231][0]
zs = sorted(r["psize_z"], key=abs, reverse=True)
say()
say("p=19231 largest |z|: %s" % ["%.2f" % v for v in zs[:6]])
say("sd after dropping the single largest draw = %.4f  -> still %.2f SE high"
    % (statistics.stdev(zs[1:]), (statistics.stdev(zs[1:]) - 1) / se_sd))
say()
say("=> NOT one outlier.  And the deviation tracks m_p monotonically at the top end:")
say("   m_p =  820 (p=19231) -> sd 1.368 ;  m_p = 1753 (p=9319) -> sd 1.191 ;  rest ~1.0")
say("=> v2's diagnosis (\"the null is calibrated, the criterion is not\") is correct POOLED")
say("   and WRONG PER-PRIME.  Pooling 640 z hid a real spread defect at the two largest primes.")
say("   The pooled sd 1.019 is a PROXY; the per-prime spread is the OBJECT.")

say()
say("=" * 78)
say("PART C -- P-SIZE' final: FOUR clauses, because pooling alone demonstrably hides the defect")
say("=" * 78)
se_mean = 1.0 / math.sqrt(NTOT)
se_sdp = 1.0 / math.sqrt(2.0 * NTOT)
q_fw = bisect(lambda q: (2 * Phi(q) - 1) ** NTOT - 0.95, 0.0, 8.0)
b_mean, b_sd, b_sdp = 3 * se_mean, 3 * se_sdp, 3 * se_sd
say("  (i)   pooled |mean|      <= %.4f" % b_mean)
say("  (ii)  pooled |sd - 1|    <= %.4f" % b_sd)
say("  (iii) pooled max|z|      <= %.4f   (5%% family-wise over %d draws)" % (q_fw, NTOT))
say("  (iv)  PER-PRIME |sd_p-1| <= %.4f   at every prime   <-- the clause v2 lacked" % b_sdp)

def gate(z_by_prime):
    z = [v for zz in z_by_prime for v in zz]
    m = sum(z) / len(z)
    sd = math.sqrt(sum((x - m) ** 2 for x in z) / (len(z) - 1))
    if abs(m) > b_mean or abs(sd - 1) > b_sd or max(abs(x) for x in z) > q_fw:
        return True
    for zz in z_by_prime:
        mp = sum(zz) / len(zz)
        sdp = math.sqrt(sum((x - mp) ** 2 for x in zz) / (len(zz) - 1))
        if abs(sdp - 1) > b_sdp:
            return True
    return False

def sim(gen, nsim=8000):
    return sum(gate([[gen() for _ in range(R)] for _ in range(NP)]) for _ in range(nsim)) / nsim

ffr = sim(lambda: random.gauss(0, 1), 12000)
say()
say("FALSE-FAILURE RATE under a perfectly calibrated null = %.4f" % ffr)
say("  v2's frozen gate, same null                        = 0.8228")
say()
say("POWER (planted positives -- a control with no power is not a control):")
for label, gen in [("sd = 1.10", lambda: random.gauss(0, 1.10)),
                   ("sd = 1.15", lambda: random.gauss(0, 1.15)),
                   ("sd = 1.20", lambda: random.gauss(0, 1.20)),
                   ("sd = 0.85", lambda: random.gauss(0, 0.85)),
                   ("mean shift +0.15", lambda: random.gauss(0.15, 1.0)),
                   ("mean shift +0.25", lambda: random.gauss(0.25, 1.0))]:
    say("   %-20s power = %.4f" % (label, sim(gen, 4000)))
say()
say("POWER against the defect ACTUALLY PRESENT (one prime with sd 1.37, nine clean):")
def one_bad(sd_bad):
    def g():
        return None
    hits = 0
    NS = 4000
    for _ in range(NS):
        zbp = [[random.gauss(0, 1) for _ in range(R)] for _ in range(NP - 1)]
        zbp.append([random.gauss(0, sd_bad) for _ in range(R)])
        if gate(zbp):
            hits += 1
    return hits / NS
for sd_bad in (1.20, 1.30, 1.37, 1.50):
    say("   one prime at sd = %.2f  -> power = %.4f" % (sd_bad, one_bad(sd_bad)))

say()
say("** DECLARED-SEEN CHECK ** what P-SIZE' does on v2's own (SEEN) numbers:")
say("   (i)   |mean| = 0.038  vs %.4f -> PASS" % b_mean)
say("   (ii)  |sd-1| = 0.019  vs %.4f -> PASS" % b_sd)
say("   (iii) max|z| = 4.889  vs %.4f -> FAIL" % q_fw)
bad_primes = [r["p"] for r in rows if abs(r["psize_sd"] - 1) > b_sdp]
say("   (iv)  per-prime spread FAILS at %s -> FAIL" % bad_primes)
say()
say("   So P-SIZE' ALSO fails on v2's data -- but for a REAL reason (a genuinely wide null at")
say("   p=19231), not the 82%-false-failure reason v2's gate failed for.  That is the point of")
say("   a calibrated gate: it still fires, and now the firing means something.")

say()
say("=" * 78)
say("PART D -- the remediation rule v3 must carry (a gate that only halts is not enough)")
say("=" * 78)
say("A per-prime spread failure does not have to void the run.  Pre-committed rule:")
say("  if clause (iv) fires at prime p, that prime's verdict z_p is DEFLATED by its measured")
say("  carrier spread sd_p, and BOTH the raw and deflated z_p are printed, the deflated one")
say("  governing -- exactly the structure C-DISP already uses for dispersion.")
say()
say("Effect on v2's own numbers, computed now so v3 cannot be accused of choosing after:")
tot_raw = tot_def = 0.0
say("%7s %9s %9s %9s" % ("p", "z_raw", "sd_p", "z_deflated"))
for r in rows:
    zr = r["z"]
    sdp = r["psize_sd"]
    zd = zr / sdp if abs(sdp - 1) > b_sdp else zr
    tot_raw += zr
    tot_def += zd
    flag = "  <-- deflated" if abs(sdp - 1) > b_sdp else ""
    say("%7d %9.2f %9.4f %9.2f%s" % (r["p"], zr, sdp, zd, flag))
say()
say("pooled Stouffer Z raw       = %+.2f" % (tot_raw / math.sqrt(NP)))
say("pooled Stouffer Z deflated  = %+.2f" % (tot_def / math.sqrt(NP)))
say("=> the deflation does NOT move Arm A across any pre-registered boundary; it is a")
say("   magnitude correction, not a sign change.  Stated in advance, and it remains SEEN-DATA.")

with open(__file__.replace(".py", ".log"), "w") as fh:
    fh.write("\n".join(out) + "\n")
