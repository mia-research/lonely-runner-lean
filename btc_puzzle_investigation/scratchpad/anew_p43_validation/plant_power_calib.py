#!/usr/bin/env python3
# Synthetic FIRING-PLANT power calibration for the PREREG pipeline (int-only).
# The plant is synthetic (f = corrupted d mod m), so its detection floor as a function of sample
# size N is independent of the A_new realization. This shows the decoder+permutation-null pipeline
# HAS power (fires on a planted leak) and quantifies the N/pi floor the powered run must reach.
# NOT a leakage claim about A_new -- a machinery validation. Verdict decided by integer E (fire<=>E==0).
from val_stats import run_channel, plant_feature

def calib():
    Ns = [10, 20, 50, 100, 200, 500, 1000]
    Ms = [5, 7, 11, 13]
    pis = [(1, 1), (1, 2), (1, 4), (1, 8), (1, 16), (0, 1)]
    print("Synthetic plant-power calibration (fire <=> E==0 at K=9999, i.e. perm p < 1e-4)")
    print("Each cell: smallest pi that FIRES (or 'none'); pi=0 must never fire.\n")
    header = "  N  |" + "".join("  m=%-2d " % m for m in Ms)
    print(header); print("-" * len(header))
    for N in Ns:
        reps = list(range(N))
        row = " %4d |" % N
        for m in Ms:
            labels = [r % m for r in reps]
            smallest = "none"
            fired_pi0 = False
            for (pn, pd) in pis:
                feats = plant_feature(labels, m, pn, pd, "syn|N%d|m%d|pi%d_%d" % (N, m, pn, pd))
                res = run_channel(feats, labels, m, seed=N, key="syn|N%d|m%d|pi%d_%d" % (N, m, pn, pd))
                if res is None: continue
                if pn == 0:
                    fired_pi0 = res["fires"]
                elif res["fires"]:
                    smallest = "%d/%d" % (pn, pd)   # keep last (smallest) firing pi
            flag = "!PI0FIRE" if fired_pi0 else ""
            row += " %5s%s" % (smallest, (" " if not flag else flag))
        print(row)
    print("\n(smallest firing pi is the achieved detection floor at that N; pi=0 firing would be a")
    print(" false-positive defect -- flagged !PI0FIRE if it ever occurs.)")

if __name__ == "__main__":
    calib()
