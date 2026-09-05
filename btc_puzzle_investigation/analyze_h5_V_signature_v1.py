#!/usr/bin/env python3
# analyze_h5_V_signature_v1.py
#
# Move 7 (do-not-close #5, cheaper arm): derive/verify the |V|-signature of the
# hypothesized one-sided #E-leak in the Semaev CM relation-yield lever, from the
# FROZEN v4 schedule (SHA f92cb4bb) -- NO re-run, pure re-analysis of
# semaev_cm_relation_yield_v4_results.jsonl.
#
# Statistic (from semaev_cm_relation_yield_v4.py):
#   For each prime p and level |V|: logQ(curve) = log(mean_K quo),
#   quo = #{(x1..xm) in V^m : points sum to target}  (I.vector_space_dimension()).
#   j0 = curve (A=0,B=1) [mu=6]; matched control = NEAREST #E non-CM (greedy).
#   T1_j0(p) = logQ_j0 - logQ_ctrl ;  pooled mean over primes -> T1_j0(|V|).
#
# Curves depend only on p (seed=1000+p), so the j0 curve, the 5 non-CM curves,
# AND the nearest-#E match are IDENTICAL across |V|. Only Dmax/K change with |V|.
#
# Leading heuristic:  logQ ~ m*log|V| + a_p - beta*log(#E).
#   T1_leak(|V|) = beta(|V|) * [log #E_j0 - log #E_ctrl]   (frozen gap; m*log|V| cancels)
# => leak's |V|-signature lives ENTIRELY in beta(|V|) = #E-sensitivity of quo.
#
# PRE-REGISTERED decision rule (stated before reading the numbers below):
#   (A) leak flat/small vs T1_j0 growing  -> #E-leak CANNOT explain the growth;
#       the observed |V|-growth is structural (mu/CM), H1 leg rehabilitates
#       CONDITIONAL on a proper rebuild.  [flat <=> beta(|V|) not growing]
#   (B) leak grows and tracks T1_j0       -> headline is a leak artifact; dead
#       without a bracket-matched re-run.
#   (C) mixed: leak explains part; residual carries the rest -> report the split.
# Threshold: call it (B) only if T1_leak(|V|) reproduces >=50% of the observed
#   0.207->0.834 span AND is monotone increasing; else (A)/(C).
#
# beta(|V|) is estimated from NON-CM curves ONLY (they share |V|,mu; only #E varies)
# via a within-prime (fixed-effects) OLS of logQ on log(order). This avoids using
# j0 to estimate the sensitivity that predicts j0's leak (no circularity).

import json, math
from collections import defaultdict
from fractions import Fraction

JSONL = "semaev_cm_relation_yield_v4_results.jsonl"

# ---- load ----------------------------------------------------------------
rows = []
with open(JSONL) as fh:
    for line in fh:
        line = line.strip()
        if line:
            rows.append(json.loads(line))

# group: by V -> by p -> list of curve dicts
byV = defaultdict(lambda: defaultdict(list))
for r in rows:
    byV[r["V"]][r["p"]].append(r)

Vs = sorted(byV)
print("levels |V| present:", Vs)
print("rows total:", len(rows))

def nearest_noncm(j0_order, noncm):
    """greedy nearest by |order - j0_order| (exact int); ties -> first (lowest index)."""
    best = None; bd = None
    for i, c in enumerate(noncm):
        d = abs(int(c["order"]) - int(j0_order))
        if bd is None or d < bd:
            bd = d; best = i
    return best

# ---- per-level assembly --------------------------------------------------
# We reconstruct T1_j0, T1_j1728, and C4 exactly as the harness does, and record
# per-prime frozen #E-gaps and the non-CM (logQ, log order) pairs for beta.
summary = {}
frozen_gap_logE = {}   # p -> (log order_j0 - log order_ctrl)     [check: |V|-independent]
frozen_ctrl_idx = {}   # p -> matched control index (check identical across V)

for V in Vs:
    dj0 = []; dj17 = []; c4 = []
    noncm_pairs = []      # (p, log_order, logQ) for non-CM curves, this level
    per_prime = {}
    for p, curves in byV[V].items():
        j0 = [c for c in curves if c["lab"] == "j0"]
        j17 = [c for c in curves if c["lab"] == "j1728"]
        noncm = [c for c in curves if c["lab"] == "nonCM"]
        if not j0 or not noncm:
            continue
        j0 = j0[0]
        # matched control (greedy nearest, mirrors harness order of appearance)
        i0 = nearest_noncm(j0["order"], noncm)
        ctrl = noncm[i0]
        frozen_ctrl_idx.setdefault(p, {})[V] = (int(ctrl["order"]), int(ctrl["A"]), int(ctrl["B"]))
        if j0.get("logQ") is not None and ctrl.get("logQ") is not None:
            dj0.append(j0["logQ"] - ctrl["logQ"])
            gap = math.log(int(ctrl["order"])) - math.log(int(j0["order"]))  # log ctrl - log j0
            # T1_leak convention: T1_leak = beta*(log#E_j0 - log#E_ctrl) = -beta*gap
            frozen_gap_logE.setdefault(p, {})[V] = gap
            per_prime[p] = dict(T1=j0["logQ"] - ctrl["logQ"],
                                logE_j0=math.log(int(j0["order"])),
                                logE_ctrl=math.log(int(ctrl["order"])),
                                order_j0=int(j0["order"]), order_ctrl=int(ctrl["order"]))
        if j17 and j17[0].get("logQ") is not None:
            i17 = nearest_noncm(j17[0]["order"], [c for k,c in enumerate(noncm) if k != i0])
            # (harness excludes i0; approximate with same exclusion)
            rem = [c for k,c in enumerate(noncm) if k != i0]
            if rem:
                i17 = nearest_noncm(j17[0]["order"], rem)
                if rem[i17].get("logQ") is not None:
                    dj17.append(j17[0]["logQ"] - rem[i17]["logQ"])
        # C4: remaining non-CM (excl. matched), sort by order, rem[0]-rem[1]
        rem = [c for k,c in enumerate(noncm) if k != i0 and c.get("logQ") is not None]
        if len(rem) >= 2:
            rem.sort(key=lambda c: int(c["order"]))
            c4.append(rem[0]["logQ"] - rem[1]["logQ"])
        for c in noncm:
            if c.get("logQ") is not None:
                noncm_pairs.append((p, math.log(int(c["order"])), c["logQ"]))

    def mean(xs): return sum(xs)/len(xs) if xs else float("nan")
    # beta(|V|): within-prime (fixed effects) OLS of logQ on log(order), non-CM only.
    # De-mean logQ and log(order) within each prime, then pooled slope.
    grp = defaultdict(list)
    for (p, lx, y) in noncm_pairs:
        grp[p].append((lx, y))
    num = den = 0.0
    npts_fe = 0
    for p, pts in grp.items():
        if len(pts) < 2:
            continue
        mx = sum(a for a,_ in pts)/len(pts)
        my = sum(b for _,b in pts)/len(pts)
        for (a,b) in pts:
            num += (a-mx)*(b-my); den += (a-mx)*(a-mx); npts_fe += 1
    beta = (num/den) if den > 0 else float("nan")   # slope of logQ vs log(order)

    # T1_leak per prime = beta*(logE_j0 - logE_ctrl) = -beta*(logE_ctrl-logE_j0)
    leaks = []
    for p, d in per_prime.items():
        leaks.append(beta * (d["logE_j0"] - d["logE_ctrl"]))
    T1 = mean(dj0)
    T1_leak = mean(leaks)
    summary[V] = dict(
        T1_j0=T1, n=len(dj0), T1_j1728=mean(dj17), n17=len(dj17),
        C4=mean(c4), nC4=len(c4),
        beta=beta, npts_fe=npts_fe,
        T1_leak=T1_leak, T1_resid=T1 - T1_leak,
        mean_gap_logE=mean([d["logE_ctrl"]-d["logE_j0"] for d in per_prime.values()]),
    )

# ---- report --------------------------------------------------------------
print("\n" + "="*90)
print("REPRODUCE the harness statistics + the leak decomposition, per |V|")
print("="*90)
print("%-4s %-6s %-8s | %-9s %-9s | %-9s %-9s %-9s | %-9s"
      % ("|V|","n","T1_j0","T1_j1728","C4","beta","T1_leak","T1_resid","gap_logE"))
for V in Vs:
    s = summary[V]
    print("%-4d %-6d %-8.4f | %-9.4f %-9.4f | %-9.4f %-9.4f %-9.4f | %-9.5f"
          % (V, s["n"], s["T1_j0"], s["T1_j1728"], s["C4"],
             s["beta"], s["T1_leak"], s["T1_resid"], s["mean_gap_logE"]))

# ---- checks --------------------------------------------------------------
print("\n" + "="*90)
print("CHECK 1: is the matched control (and thus the frozen #E-gap) |V|-independent?")
print("="*90)
bad = 0
for p, byv in frozen_ctrl_idx.items():
    vals = set(byv.values())
    if len(vals) > 1:
        bad += 1
        print("  p=%d control varies across |V|: %s" % (p, byv))
print("  primes with |V|-varying control: %d / %d  (%s)"
      % (bad, len(frozen_ctrl_idx), "FLAT/frozen OK" if bad == 0 else "NOT flat -- investigate"))

print("\n" + "="*90)
print("CHECK 2: is #E_j0 (B=1) at the EDGE of the non-CM #E distribution? (the audited mechanism)")
print("="*90)
edge_count = 0; tot = 0
for p, curves in byV[Vs[0]].items():
    j0 = [c for c in curves if c["lab"]=="j0"]
    noncm = [c for c in curves if c["lab"]=="nonCM"]
    if not j0 or len(noncm) < 3: continue
    tot += 1
    oj0 = int(j0[0]["order"])
    orders = sorted(int(c["order"]) for c in noncm)
    below = sum(1 for o in orders if o < oj0)
    above = sum(1 for o in orders if o > oj0)
    if below == 0 or above == 0:  # strictly one-sided
        edge_count += 1
print("  strictly one-sided (all non-CM on one side of #E_j0): %d / %d primes" % (edge_count, tot))

print("\n" + "="*90)
print("VERDICT vs pre-registered rule")
print("="*90)
T1s = [summary[V]["T1_j0"] for V in Vs]
leaks = [summary[V]["T1_leak"] for V in Vs]
span_obs = max(T1s) - min(T1s)
span_leak = max(leaks) - min(leaks)
frac = (span_leak/span_obs) if span_obs else float("nan")
print("  observed T1_j0 span over |V|: %.4f  (%.4f -> %.4f)" % (span_obs, T1s[0], T1s[-1]))
print("  leak     T1_leak span over |V|: %.4f  (%.4f -> %.4f)" % (span_leak, leaks[0], leaks[-1]))
print("  leak reproduces %.1f%% of the observed |V|-span" % (100*frac if frac==frac else float('nan')))
mono_leak = all(leaks[i+1] >= leaks[i] for i in range(len(leaks)-1))
print("  leak monotone increasing in |V|: %s" % mono_leak)
if frac >= 0.5 and mono_leak:
    print("  => (B) leak tracks the growth: headline needs a re-run.")
else:
    print("  => (A)/(C) #E-leak is FLAT/small; the observed growth is NOT the one-sided #E-leak.")
