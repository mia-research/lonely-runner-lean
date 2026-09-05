#!/usr/bin/env python3
"""
row_budget_v3_calib_a3.py  --  PRE-RUN calibration for PREREG_row_budget_lowtail_v3.md, Arm A3.

Derives the A3 noise floor FROM THE DESIGN (m_p, n_p, R, q) -- not from any v2
measurement -- fixes the in-range prime subset, and computes the estimator sd and
the power of every A3 pass criterion.

NO CURVE DATA IS READ.  Inputs are the frozen design constants of
PREREG_row_budget_lowtail_v2.md section 5 / section 6 and the analytic constants
q = 1-e^-theta and c_F11 = 0.4950.  Float is used for analytic sizes only; no key,
coordinate or index passes through it (btc CLAUDE.md carve-out).
"""
import math

THETA   = 0.01
Q       = 1.0 - math.exp(-THETA)          # generic / c=0 forced low-tail rate
Q_B0    = math.erf(math.sqrt(THETA / 2))  # b=0 forced low-tail rate (F10)
R       = 64
C_F11   = 0.4950                          # F11 coefficient at theta = 0.01

# frozen design constants: p -> (n, m_generic, m_c0, m_b0)   [v2 section 6]
DESIGN = {
    163:   (139,    2187,  27,   81),
    211:   (199,    3675,  35,  105),
    349:   (313,   10092,  58,  174),
    433:   (397,   15552,  72,  216),
    577:   (613,   26143,  96,  288),
    991:   (1009,  15873, 165,  495),
    2089:  (2143,   7469, 348, 1044),
    4159:  (4243,   3771, 693,  942),
    9319:  (9127,   1753, 438,  438),
    19231: (19501,   820, 205,  205),
}
PRIMES = sorted(DESIGN)

# per-prime layer values PRINTED in RESULT_row_budget_lowtail_v2.md section 3 => SEEN
SEEN_A3 = {163, 433, 991, 2089, 4159, 9319, 19231}


def phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def design_floors():
    """sigma_unit  = rel sd of ONE profile-mean over m_p frequencies
       sigma_layer = rel sd of the R-replicate-averaged MN-free mean (the A3 noise floor)"""
    out = {}
    for p in PRIMES:
        n, m, _, _ = DESIGN[p]
        T = m * (n - 1) * Q
        su = math.sqrt((1 - Q) / T)
        out[p] = dict(n=n, m=m, T=T,
                      relsd_v2=su * math.sqrt(1 + 1.0 / R),   # v2 section 5 column
                      sigma_unit=su,
                      sigma_layer=su / math.sqrt(R),
                      pred=-C_F11 / (n - 1),
                      sn=(C_F11 / (n - 1)) / (su / math.sqrt(R)))
    return out


def subset_stability(F):
    """the in-range subset as a function of the S/N threshold tau"""
    sns = sorted((F[p]['sn'], p) for p in PRIMES)
    print("\n  S/N-sorted:  " + "  ".join(f"{p}:{s:.3f}" for s, p in sns))
    print("  subset is CONSTANT for tau in the open interval between consecutive S/N values:")
    for i in range(len(sns) - 1):
        lo, hi = sns[i][0], sns[i + 1][0]
        S = sorted(p for p in PRIMES if F[p]['sn'] > lo)
        print(f"    tau in ({lo:.3f}, {hi:.3f}]  ->  |S|={len(S)}  {S}")


def wls(F, S):
    """weighted-LS coefficient estimator for  L_p = -c/(n_p-1) + N(0,sigma_layer_p)"""
    inv = sum((1.0 / (F[p]['n'] - 1)) ** 2 / F[p]['sigma_layer'] ** 2 for p in S)
    sd = 1.0 / math.sqrt(inv)
    return sd, C_F11 / sd            # sd(chat), and E[chat]/sd(chat) under F11


def main():
    F = design_floors()
    print("=" * 96)
    print("A3 NOISE FLOOR FROM DESIGN   sigma_layer(p) = sqrt((1-q)/T_p)/sqrt(R),  T_p = m_p (n_p-1) q")
    print(f"  q = 1-e^-0.01 = {Q:.9f}   R = {R}   c_F11 = {C_F11}")
    print("=" * 96)
    print(f"{'p':>7} {'n':>7} {'m_p':>7} {'T_p':>10} {'relsd(v2 s5)':>13} "
          f"{'sigma_layer':>12} {'pred layer':>11} {'S/N':>7}  seen?")
    for p in PRIMES:
        d = F[p]
        print(f"{p:>7} {d['n']:>7} {d['m']:>7} {d['T']:>10.0f} {d['relsd_v2']*100:>12.3f}% "
              f"{d['sigma_layer']*100:>11.4f}% {d['pred']*100:>10.4f}% {d['sn']:>7.3f}"
              f"   {'SEEN' if p in SEEN_A3 else 'unseen'}")

    subset_stability(F)

    TAU = 1.30      # design rule: per-prime sign power Phi(tau) >= 0.90
    S_full   = sorted(p for p in PRIMES if F[p]['sn'] >= TAU)
    S_unseen = sorted(p for p in S_full if p not in SEEN_A3)
    S_seen   = sorted(p for p in S_full if p in SEEN_A3)
    print(f"\n  tau = {TAU} (design rule: Phi(tau) = {phi(TAU):.4f} >= 0.90 per-prime sign power)")
    print(f"    A3-FULL   (contaminated on {S_seen}) = {S_full}")
    print(f"    A3-UNSEEN                            = {S_unseen}")

    print("\n" + "=" * 96)
    print("ESTIMATOR sd AND POWER   chat = weighted LS of L_p on -1/(n_p-1)")
    print("=" * 96)
    for name, S in (("A3-UNSEEN", S_unseen), ("A3-FULL", S_full),
                    ("all 10 (v2's A3 range)", PRIMES)):
        sd, snr = wls(F, S)
        # sign test power under F11
        p_all = 1.0
        for p in S:
            p_all *= phi(F[p]['sn'])
        print(f"\n  {name}:  |S| = {len(S)}")
        print(f"    sd(chat)            = {sd:.4f}")
        print(f"    E[chat]/sd  (F11)   = {snr:.3f}")
        for bar in (2.0, 2.5, 3.0, 4.0):
            print(f"    power, existence bar chat/sd >= {bar}: {phi(snr - bar)*100:6.2f}%"
                  f"   (FFR under c=0: {(1-phi(bar))*100:.3f}%)")
        print(f"    magnitude MDE: |c - {C_F11}| detectable at 3 sd  <=>  > {3*sd:.4f}"
              f"   i.e. c outside [{C_F11-3*sd:.4f}, {C_F11+3*sd:.4f}]")
        print(f"    P(all {len(S)} signs negative | F11) = {p_all*100:.2f}%"
              f"     P(all | c=0) = {100/2**len(S):.3f}%")

    print("\n" + "=" * 96)
    print("WHY v2's A3 SLOPE FIT FAILED -- design arithmetic, no v2 data used")
    print("=" * 96)
    print("  A slope fit of log|L_p| on log(n_p-1) over all 10 primes gives the 4 highest primes")
    print("  a weight equal to the 6 lowest, while their S/N is:")
    for p in PRIMES:
        print(f"    p={p:>6}  S/N = {F[p]['sn']:6.3f}   P(sign correct | F11) = {phi(F[p]['sn'])*100:5.1f}%")
    pall10 = 1.0
    for p in PRIMES:
        pall10 *= phi(F[p]['sn'])
    print(f"\n  P(all 10 signs negative | F11, design noise) = {pall10*100:.2f}%")
    print("  => a 10-prime sign-agreement expectation was never available from this design.")
    print("  Also: log|L_p| is UNDEFINED whenever L_p changes sign, which the design predicts")
    print("        happens with probability 1 - Phi(S/N) at each prime; at p=19231 that is"
          f" {(1-phi(F[19231]['sn']))*100:.1f}%.")


if __name__ == "__main__":
    main()
