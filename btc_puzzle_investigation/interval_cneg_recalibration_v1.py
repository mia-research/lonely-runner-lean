#!/usr/bin/env python3
"""interval_cneg_recalibration_v1.py -- discharge the E6 CONTROL DEBT on the interval channel.

THE DEBT (standing repair D of NEXT_SESSION_PROMPT_2026-08-01_v2.md; raised in
RESULT_interval_multireadout_v2.md sections 91-108):

  C-NEG as specified is ONE draw tested against a quantile.  Under a perfectly correct null that
  false-alarms 5% of the time at the 95th.  It voided the spectral run at 96.0, and 20 fresh draws
  then gave 0/20 above the 95th.  Separately, an `E6 = 65101` reading at the 99.7th percentile was
  flagged on the GROUP arm -- one draw among six control readings (2 arms x 3 statistics), for which
  P(>=1 above 99.7%) is about 1.8%.  It is BLOCKING for reading chi_2 / chi_6 on the group-law
  difference, which is item C.2 and has never been run.

THIS IS A CONTROL RECALIBRATION, NOT A LEAKAGE TEST.  No arm number is read here and no k-interval
is touched -- only the C-NEG control itself, re-run as n >= 20 independent draws with their
percentiles checked for uniformity.  Nothing here can produce a positive finding.

PRE-COMMITTED READOUT (fixed before running):
  For each mode x statistic: report #above 95th and #above 99th out of n draws, plus the percentile
  spread.  Under a correct null, #above-95th ~ Binomial(n, 0.05), so 0-3 of 20 is unremarkable and
  >= 5 of 20 indicates the null is genuinely mis-calibrated for that statistic.
  The E6 = 99.7 flag is DISCHARGED as a single-draw artifact if E6's 20 draws show no excess.

EXACT INTEGER ARITHMETIC ONLY (inherits the module's exact curve arithmetic).
"""
import random, time, sys
import interval_multireadout_v3 as MR

N_DRAWS = 20
R_NULL = 3000


def recalibrate(mode, M, NP, rng, label):
    t0 = time.time()
    print("\n" + "=" * 78)
    print("%s   mode=%s M=%d pool=%d  n_draws=%d" % (label, mode, M, NP, N_DRAWS))
    print("=" * 78, flush=True)

    pool = MR.pool_pts(NP, rng)
    T = MR.pool_table(pool, mode)
    print("  pool table built (%d pairs) [%.0fs]" % (NP * (NP - 1) // 2, time.time() - t0), flush=True)

    idx = list(range(NP))
    nl = [MR.stats(MR.counts_from_table(T, rng.sample(idx, M))) for _ in range(R_NULL)]
    cols = list(zip(*nl))
    q = {}
    for i, nm in enumerate(("E2", "E3", "E6")):
        s = sorted(cols[i])
        q[nm] = s
        print("  null %s: median=%d  95th=%d  99th=%d"
              % (nm, s[R_NULL // 2], s[(95 * R_NULL) // 100], s[(99 * R_NULL) // 100]))

    def rank(nm, v):
        """EXACT integer rank: how many of the R_NULL null draws lie strictly below v."""
        return sum(1 for z in q[nm] if z < v)

    def readout(pts):
        cls = MR.field_classes(pts) if mode == "field" else MR.group_classes(pts)
        return MR.stats(MR.counts_of(cls))

    print("  -- C-NEG, %d INDEPENDENT draws (the repaired control) --" % N_DRAWS, flush=True)
    # ranks are integer counts out of R_NULL; a draw is "above the 95th" iff 100*rank >= 95*R_NULL
    rks = {"E2": [], "E3": [], "E6": []}
    for j in range(N_DRAWS):
        e = readout([MR.jmul(rng.randrange(1, MR.N)) for _ in range(M)])
        for i, nm in enumerate(("E2", "E3", "E6")):
            rks[nm].append(rank(nm, e[i]))
        print("    draw %2d | E2 %4d/%d  E3 %4d/%d  E6 %4d/%d"
              % (j + 1, rks["E2"][-1], R_NULL, rks["E3"][-1], R_NULL, rks["E6"][-1], R_NULL), flush=True)

    print("  -- verdict --")
    out = {}
    for nm in ("E2", "E3", "E6"):
        v = sorted(rks[nm])
        a95 = sum(1 for z in v if 100 * z >= 95 * R_NULL)
        a99 = sum(1 for z in v if 100 * z >= 99 * R_NULL)
        out[nm] = (a95, a99)
        print("   %s: above95=%2d/%d  above99=%2d/%d | median rank=%d/%d  min=%d  max=%d | %s"
              % (nm, a95, N_DRAWS, a99, N_DRAWS, v[N_DRAWS // 2], R_NULL, v[0], v[-1],
                 "CALIBRATED" if a95 <= 3 else "*** MIS-CALIBRATED (>=5/20 above 95th) ***"
                 if a95 >= 5 else "borderline (4/20)"))
    print("  [%.0fs]" % (time.time() - t0), flush=True)
    return out


if __name__ == "__main__":
    rng = random.Random(20260801)
    g = recalibrate("group", 160, 600, rng, "GROUP-LAW difference -- the arm carrying the E6=99.7 flag")
    f = recalibrate("field", 400, 1100, rng, "FIELD difference -- comparison arm")

    print("\n" + "=" * 78)
    print("E6 CONTROL DEBT — DISCHARGE STATEMENT")
    print("=" * 78)
    ok = g["E6"][0] <= 3 and f["E6"][0] <= 3
    print("  group E6 above95 = %d/%d ; field E6 above95 = %d/%d" % (g["E6"][0], N_DRAWS, f["E6"][0], N_DRAWS))
    print("  -> %s" % ("DISCHARGED: the E6=99.7 reading does not reproduce over 20 draws; it was a "
                       "single-draw artifact. chi_2/chi_6 on the group arm are UNBLOCKED."
                       if ok else
                       "NOT DISCHARGED: E6 shows genuine excess over 20 draws; the null is "
                       "mis-calibrated for E6 and item C.2 stays blocked."))
