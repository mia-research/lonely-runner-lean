#!/usr/bin/env python3
"""
AUDIT re-analysis: give the secp single-feature MIs the permutation null the
blinded joint-readout protocol OMITTED (protocol section 8: "single-feature rows
report observed Miller-Madow MI only, no separate null").

At N=82 the JOINT MI (|F|=324 cells) is Miller-Madow-crushed to ~ -2.8 bits and
the plant control does NOT fire (z=0.62) -> the joint-secp test is powerless.
The single-feature MIs are the ONLY quantities with any power at N=82, and they
were never null-tested. This reruns each MI(F_k; T_m) with a real permutation
null, on the EXACT same feature construction (imported from the frozen script).

Statistic: plug-in MI in bits (monotone stat ranked vs permutation null -> the
permitted float carve-out). Null: permute target labels, R resamples, fixed seed.
Also prints Miller-Madow observed to cross-check against the published table.
"""
import sys, math, random
from collections import Counter

sys.path.insert(0, ".")
import blinded_joint_readout_v1 as B

R = 50000
SEED = 20260814

def H(counter, N):
    h = 0.0
    for c in counter.values():
        if c:
            pr = c / N
            h -= pr * math.log2(pr)
    return h

def mi_plugin(xs, ts):
    N = len(xs)
    return H(Counter(xs), N) + H(Counter(ts), N) - H(Counter(zip(xs, ts)), N)

def mi_mm(xs, ts):
    """Miller-Madow: plug-in + (cells-1)/(2N ln2) style correction on each entropy."""
    N = len(xs)
    def Hmm(counter):
        nz = sum(1 for c in counter.values() if c)
        return H(counter, N) + (nz - 1) / (2 * N * math.log(2))
    return Hmm(Counter(xs)) + Hmm(Counter(ts)) - Hmm(Counter(zip(xs, ts)))

def perm_p(xs, ts, R, seed):
    obs = mi_plugin(xs, ts)
    rng = random.Random(seed)
    t = list(ts)
    ge = 0
    nullvals = []
    for _ in range(R):
        rng.shuffle(t)
        v = mi_plugin(xs, t)
        nullvals.append(v)
        if v >= obs - 1e-15:
            ge += 1
    mu = sum(nullvals) / R
    sd = (sum((v - mu) ** 2 for v in nullvals) / R) ** 0.5
    z = (obs - mu) / sd if sd > 0 else 0.0
    return obs, (ge + 1) / (R + 1), z, mu, sd

def main():
    feat_tuples, f1_list, ds = B.build_secp_dataset()
    N = len(ds)
    print(f"secp keys reconstructed: N={N}")
    Fnames = ["F1_chi3", "F2_eps", "F3_sband", "F4_sxt3", "F5_sxtpar", "F6_chi2y"]
    targets = {"T3": 3, "T4": 4, "T5": 5, "T7": 7}

    # cross-check: reproduce published MM single-feature MIs for T3,T5
    print("\n== cross-check Miller-Madow observed (compare to published table) ==")
    for tn, m in targets.items():
        ts = [d % m for d in ds]
        row = [f"{mi_mm([ft[k] for ft in feat_tuples], ts):+.4f}" for k in range(6)]
        print(f"  {tn}: " + " ".join(f"{Fnames[k]}={row[k]}" for k in range(6)))

    print("\n== permutation null (R=%d) : MI_obs(plugin) | perm_p | z ==" % R)
    results = []
    for tn, m in targets.items():
        ts = [d % m for d in ds]
        for k in range(6):
            xs = [ft[k] for ft in feat_tuples]
            obs, p, z, mu, sd = perm_p(xs, ts, R, SEED + k * 13 + m)
            results.append((tn, Fnames[k], obs, p, z))
            flag = "  <-- p<0.05" if p < 0.05 else ""
            print(f"  {tn:3s} {Fnames[k]:10s}  MI={obs:.4f}  p={p:.4f}  z={z:+.2f}{flag}")

    # multiplicity
    ps = sorted((r[3], r) for r in results)
    K = len(results)
    print(f"\n== Holm-Bonferroni over K={K} tests (familywise 0.05) ==")
    any_surv = False
    for i, (p, r) in enumerate(ps):
        thresh = 0.05 / (K - i)
        surv = p <= thresh
        any_surv = any_surv or surv
        if p < 0.10:
            print(f"  {r[0]:3s} {r[1]:10s} p={p:.4f}  Holm_thresh={thresh:.5f}  {'SURVIVES' if surv else 'no'}")
    print(f"\n  any survive Holm 0.05: {any_surv}")
    print(f"  min raw p: {ps[0][0]:.4f} ({ps[0][1][0]} {ps[0][1][1]})")
    # expected #{raw p<0.05} under global null ~ K*0.05
    n_sig = sum(1 for r in results if r[3] < 0.05)
    print(f"  #{{raw p<0.05}} = {n_sig}  (chance expectation ~ {K*0.05:.1f})")

if __name__ == "__main__":
    main()
