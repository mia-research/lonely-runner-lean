#!/usr/bin/env python3
"""
Gate calibration for PREREG_row_budget_lowtail_v3.md.

Computes, for every gate v3 will contain, its FALSE-FAILURE RATE under the null, and for the
replacement negative control its POWER against stated mis-calibrations.

FLOAT DECLARATION (btc_puzzle_investigation/CLAUDE.md): every float below is in the
GATE-CALIBRATION path, not the signal path.  No key, index, coordinate or curve quantity enters
this file at all -- it consumes only (a) distributional assumptions stated in the spec and
(b) summary statistics already printed in RESULT_row_budget_lowtail_v2.md.  Nothing here decides
a verdict; it decides how a gate is written.
"""
import math, random

random.seed(20260725)          # frozen
NSIM = 200000

def Phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))

def bisect(f, lo, hi, tol=1e-12):
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(lo) * f(mid) <= 0:
            hi = mid
        else:
            lo = mid
        if hi - lo < tol:
            break
    return (lo + hi) / 2

out = []
def say(s=""):
    print(s); out.append(s)

R, NPRIME = 64, 10
N_TOT = R * NPRIME

say("=" * 78)
say("PART 1 -- the v2 P-SIZE gate as frozen, and why it false-failed")
say("=" * 78)
p_one = 2 * Phi(3.0) - 1
say("P(|z| <= 3) for one N(0,1) draw            = %.6f" % p_one)
ff_prime = 1 - p_one ** R
say("P(max|z| > 3 over R=64 draws), per prime   = %.4f" % ff_prime)
ff_all = 1 - p_one ** N_TOT
say("P(at least one of 10 primes exceeds 3)     = %.4f" % ff_all)
say("=> expected number of the 10 primes failing = %.2f   (v2 observed 2)" % (10 * ff_prime))
say()
say("The second clause (fraction with |z|>2 <= 0.10):")
q2 = 2 * Phi(2.0) - 1
exp2 = 1 - q2
say("  E[fraction |z|>2] = %.4f ; gate at 0.10" % exp2)
cnt = 0
for _ in range(NSIM // 10):
    k = sum(1 for _ in range(R) if abs(random.gauss(0, 1)) > 2)
    if k / R > 0.10:
        cnt += 1
ff_clause2 = cnt / (NSIM // 10)
say("  P(fraction > 0.10) per prime = %.4f ; over 10 primes = %.4f"
    % (ff_clause2, 1 - (1 - ff_clause2) ** 10))

say()
say("=" * 78)
say("PART 2 -- candidate replacements, false-failure rate AND power")
say("=" * 78)

# --- (a) correctly-quantiled per-prime max
q_prime = bisect(lambda q: (2 * Phi(q) - 1) ** R - 0.95, 0.0, 8.0)
q_bonf = bisect(lambda q: (2 * Phi(q) - 1) ** N_TOT - 0.95, 0.0, 8.0)
say("(a) per-prime max bound at 5%%/prime : q = %.4f" % q_prime)
say("    family-wise over 640 draws (5%%)  : q = %.4f" % q_bonf)
say("    NOTE a per-prime 5%% gate still false-fails somewhere with prob %.3f over 10 primes"
    % (1 - 0.95 ** 10))

# --- (b) pooled Anderson-Darling against a FULLY SPECIFIED N(0,1)
def anderson_darling(zs):
    n = len(zs)
    x = sorted(zs)
    s = 0.0
    for i, v in enumerate(x):
        u = Phi(v)
        u = min(max(u, 1e-300), 1 - 1e-16)
        w = Phi(x[n - 1 - i])
        w = min(max(w, 1e-300), 1 - 1e-16)
        s += (2 * (i + 1) - 1) * (math.log(u) + math.log1p(-w))
    return -n - s / n

def sim_AD(gen, nsim=20000):
    return [anderson_darling([gen() for _ in range(N_TOT)]) for _ in range(nsim)]

null_AD = sorted(sim_AD(lambda: random.gauss(0, 1)))
crit95 = null_AD[int(0.95 * len(null_AD))]
crit99 = null_AD[int(0.99 * len(null_AD))]
say()
say("(b) pooled Anderson-Darling, 640 draws vs fully specified N(0,1)")
say("    simulated critical values : A2(95%%) = %.4f   A2(99%%) = %.4f" % (crit95, crit99))
say("    (textbook fully-specified asymptotic 5%% value is 2.492 -- agreement is the check)")
say("    false-failure rate at the 95%% gate, BY CONSTRUCTION = 0.050")

def power_AD(gen, crit, nsim=4000):
    hit = 0
    for _ in range(nsim):
        if anderson_darling([gen() for _ in range(N_TOT)]) > crit:
            hit += 1
    return hit / nsim

say()
say("    POWER of the AD gate against stated mis-calibrations (this is the planted positive):")
for label, gen in [
    ("sd = 1.10 (spread 10%% too wide)", lambda: random.gauss(0, 1.10)),
    ("sd = 1.20", lambda: random.gauss(0, 1.20)),
    ("sd = 0.85 (spread too narrow)", lambda: random.gauss(0, 0.85)),
    ("mean shift +0.15", lambda: random.gauss(0.15, 1.0)),
    ("mean shift +0.25", lambda: random.gauss(0.25, 1.0)),
    ("t_5 heavy tails (sd-matched)", lambda: random.gauss(0, 1) / math.sqrt(
        max(1e-9, sum(random.gauss(0, 1) ** 2 for _ in range(5)) / 5))),
]:
    say("      %-34s power = %.3f" % (label, power_AD(gen, crit95)))

say()
say("    ** DECLARED-SEEN SENSITIVITY **  RESULT v2 printed the observed 640-z summary")
say("    (mean +0.038, sd 1.019, skew -0.176).  Those are SEEN.  The gate above was fixed from")
say("    first principles (alpha=0.05, fully-specified null) and NOT tuned to them.  What the")
say("    gate would do on a distribution matching that summary, computed in advance:")
def skewed(mean, sd, skew_target):
    # sinh-arcsinh style: use a skew-normal via the standard construction
    d = skew_target
    u0, v0 = random.gauss(0, 1), random.gauss(0, 1)
    a = 0.55 if d < 0 else -0.55
    dd = a / math.sqrt(1 + a * a)
    z = dd * abs(u0) + math.sqrt(1 - dd * dd) * v0
    z = (z - dd * math.sqrt(2 / math.pi)) / math.sqrt(1 - 2 * dd * dd / math.pi)
    return mean + sd * z
pw = power_AD(lambda: skewed(0.038, 1.019, -0.176), crit95)
say("      P(AD gate fires on a v2-like null)  = %.3f" % pw)
say("      -> if this is large the gate would reject v2's own calibrated null; reported so the")
say("         choice is made with eyes open, not discovered after the run.")

say()
say("=" * 78)
say("PART 3 -- false-failure rate of EVERY other gate v3 carries")
say("=" * 78)

say("Criterion 1 (eps=1 => N_LOW = n-1 exactly)   : exact integer assertion, FFR = 0 by construction")
say("Criterion 2 (chirp => N_LOW = 0 exactly)     : exact integer assertion, FFR = 0 by construction")
say("C-EQ-int, C-BUDGET, C-PARITY, C-PREC         : exact/forced, FFR = 0 by construction")

# criterion 3: |D_meas - D_pred| <= max(3 SE, 0.5 |D_pred|), plus strict monotonicity on sub-grid
say()
say("Criterion 3 (response-model band) -- FFR under a CORRECT instrument:")
for k in (4, 5, 6):
    ff_band = 1 - (2 * Phi(3.0) - 1) ** k
    say("    sub-grid of %d levels, 3-SE band, per prime  = %.4f ; over 10 primes = %.4f"
        % (k, ff_band, 1 - (1 - ff_band) ** 10))
say("    plus the strict-monotonicity clause, simulated (levels iid about a monotone truth):")
for k in (4, 5, 6):
    bad = 0
    for _ in range(20000):
        # separations >= 3 SE apart on the admissible sub-grid, by its definition
        vals = [i * 3.0 + random.gauss(0, 1) for i in range(k)]
        if any(vals[i + 1] <= vals[i] for i in range(k - 1)):
            bad += 1
    say("      %d levels : P(monotonicity violated | correct instrument) = %.4f ; over 10 primes = %.4f"
        % (k, bad / 20000, 1 - (1 - bad / 20000) ** 10))

say()
say("C-SELFZ -- |z_split| <= 3 every prime, AND sd of 64 leave-one-out z in [0.7, 1.4]:")
ff_split = 1 - (2 * Phi(3.0) - 1) ** NPRIME
say("    |z_split| clause, 10 primes                = %.4f" % ff_split)
bad = 0
for _ in range(20000):
    draws = [random.gauss(0, 1) for _ in range(R)]
    tot = sum(draws)
    loo = []
    for i in range(R):
        rest = [draws[j] for j in range(R) if j != i]
        m = sum(rest) / (R - 1)
        sd = math.sqrt(sum((x - m) ** 2 for x in rest) / (R - 2))
        loo.append((draws[i] - m) / sd)
    mL = sum(loo) / R
    sdL = math.sqrt(sum((x - mL) ** 2 for x in loo) / (R - 1))
    if not (0.7 <= sdL <= 1.4):
        bad += 1
ff_loo = bad / 20000
say("    LOO-sd in [0.7,1.4] clause, per prime      = %.4f ; over 10 primes = %.4f"
    % (ff_loo, 1 - (1 - ff_loo) ** 10))

say()
say("C-DISP -- trigger if D_char/D_null > 1.5 at any prime (D = Var_f/mean_f over m_p freqs):")
for m in (60, 200, 1000):
    bad = 0
    for _ in range(20000):
        a = [random.gauss(0, 1) ** 2 for _ in range(m)]
        b = [random.gauss(0, 1) ** 2 for _ in range(m)]
        Da = sum((x - sum(a) / m) ** 2 for x in a) / (m - 1) / (sum(a) / m)
        Db = sum((x - sum(b) / m) ** 2 for x in b) / (m - 1) / (sum(b) / m)
        if Da / Db > 1.5:
            bad += 1
    say("    m_p = %4d frequencies : P(spurious trigger) per prime = %.4f ; over 10 = %.4f"
        % (m, bad / 20000, 1 - (1 - bad / 20000) ** 10))

say()
say("=" * 78)
say("PART 4 -- Arm A3 : why the slope band was the wrong test, and the replacement")
say("=" * 78)
say("F11 predicts   layer(p) = -0.4950 / (n-1)   [percent of REF-RAY].")
say("From RESULT v2's own A3 table, noise floor = predicted%% / (S/N):")
tab = [(163, -0.359, 1.50), (433, -0.125, 2.42), (991, -0.049, 1.51),
       (2089, -0.023, 0.72), (4159, -0.012, 0.36), (9319, -0.005, 0.16),
       (19231, -0.003, 0.08)]
say("      p        predicted%%    S/N     implied noise sd %%")
for p, pr, sn in tab:
    say("   %7d   %9.3f   %5.2f        %8.4f" % (p, pr, sn, abs(pr) / sn))
say()
say("The floor is ~constant in p (the layer SE does not shrink with n), while the signal falls")
say("as 1/(n-1).  So a log-log SLOPE fit is dominated by primes where the target is invisible.")
say()
say("Restriction approach (what RESULT v2 suggested):")
for thr in (0.8, 1.0, 1.5, 2.0):
    keep = [p for p, pr, sn in tab if sn >= thr]
    if len(keep) >= 2:
        span = math.log(max(keep) / min(keep))
        say("    S/N >= %.1f keeps %d primes %s ; log-range = %.2f" % (thr, len(keep), keep, span))
    else:
        say("    S/N >= %.1f keeps %d primes %s ; TOO FEW FOR A SLOPE" % (thr, len(keep), keep))
say("  => at any defensible S/N bar the slope fit has <=3 points over <2 decades. NOT SUPPORTABLE.")
say()
say("REPLACEMENT A3' : test the CONSTANT, not the slope.")
say("  F11 <=> C := (n-1) * layer(p) = -0.4950 for every p.")
say("  Inverse-variance-weighted mean of the per-prime C_p, tested against -0.4950.")
say("  Weight w_p = 1/((n-1)*sigma_p)^2 downweights the out-of-floor primes AUTOMATICALLY,")
say("  so no prime has to be discarded by hand and no post-hoc range is chosen.")
sig = [(p, abs(pr) / sn) for p, pr, sn in tab]
wsum = 0.0
for p, s in sig:
    w = 1.0 / ((p - 1) * s / 100.0) ** 2
    wsum += w
se_C = 1.0 / math.sqrt(wsum)
say("  Using v2's own implied sigmas, SE of the weighted C-hat = %.4f" % se_C)
say("  |C| = 0.4950, so |C|/SE = %.2f  -> the constant IS resolvable where the slope was not."
    % (0.4950 / se_C))
say("  Effective weight share by prime (shows the automatic downweighting):")
for p, s in sig:
    w = 1.0 / ((p - 1) * s / 100.0) ** 2
    say("     p=%7d   weight share = %6.2f%%" % (p, 100 * w / wsum))

say()
say("=" * 78)
say("PART 5 -- A3' contamination ledger")
say("=" * 78)
say("RESULT v2's A3 table printed per-prime layer values for:")
say("   163, 433, 991, 2089, 4159, 9319, 19231   -> SEEN (7 primes)")
say("The 10-prime frozen list also contains:")
say("   211, 349, 577                            -> NOT printed anywhere -> UNSEEN (3 primes)")
say("=> A3' has a genuinely unseen 3-prime subset.  Both the 10-prime (SEEN) and the 3-prime")
say("   (UNSEEN) versions must be reported; only the 3-prime one may carry a confirmatory tag.")
say("   Power of the 3-prime version, using v2's implied sigmas:")
w3 = 0.0
for p, s in sig:
    pass
sig3 = {211: None, 349: None, 577: None}
say("   sigma at 211/349/577 is NOT printed by v2; interpolating the ~constant floor 0.032-0.24%")
say("   is a DESIGN estimate, not a measurement -- v3 states it as such and the run measures it.")

with open(__file__.replace(".py", ".log"), "w") as fh:
    fh.write("\n".join(out) + "\n")
