#!/usr/bin/env python3
# analyze_h5_F2b_primedrop_v1.py -- Exp 1, arm E_F2b (prime-drop selection). FREE: re-pools the
# frozen leaky per-prime T1_j0 over the schedule-defined bracketable subset. No new quo.
# Spec: PREREG_h5_factor_isolation_and_orbit_quo_v1.md sec 1.1 E_F2b + 1.2 F2b.
#   bracketable(p) = (exists nonCM order < #E_j0) AND (exists nonCM order > #E_j0)
#   E_F2b = mean(delta | dropped) - mean(delta | kept),  label-permutation null (count fixed).
#   Also report T1_leaky(P_all) vs T1_leaky(P_brk).  Exact ints for orders; float only as ranked stat.

import json, re, random
from collections import defaultdict

sched = json.load(open("_SCHEDULE_semaev_cm_relation_yield_v4.json"))
brk = {}   # p -> bool bracketable
for e in sched:
    p = e["p"]
    oj0 = next(int(c["order"]) for c in e["curves"] if c["lab"] == "j0")
    non = [int(c["order"]) for c in e["curves"] if c["lab"] == "nonCM"]
    brk[p] = any(o < oj0 for o in non) and any(o > oj0 for o in non)

# per-prime T1_j0 by |V| from the leaky log
row_re = re.compile(r"p=(\d+)\s+T1_j0=(-?[\d.]+)")
data = defaultdict(dict)   # V -> {p: T1}
curV = None
for line in open("semaev_cm_relation_yield_v4.log"):
    m = re.search(r"tag=V=(\d+)\s", line)
    if m: curV = int(m.group(1)); continue
    m = row_re.search(line)
    if m and curV is not None:
        data[curV][int(m.group(1))] = float(m.group(2))

def perm_p(deltas, labels, R=200000, seed=20260824):
    # observed = mean(dropped) - mean(kept); labels True=kept(bracketable), False=dropped
    idx = list(range(len(deltas)))
    kept = [deltas[i] for i in idx if labels[i]]
    drop = [deltas[i] for i in idx if not labels[i]]
    if not kept or not drop: return None, None, None, None
    obs = sum(drop)/len(drop) - sum(kept)/len(kept)
    n_drop = len(drop); random.seed(seed); ge = 0
    for _ in range(R):
        s = random.sample(idx, n_drop)
        sd = set(s)
        md = sum(deltas[i] for i in s)/n_drop
        mk = sum(deltas[i] for i in idx if i not in sd)/(len(idx)-n_drop)
        if abs(md-mk) >= abs(obs)-1e-12: ge += 1
    return obs, (ge+1)/(R+1), sum(kept)/len(kept), sum(drop)/len(drop)

nbrk = sum(brk.values()); ndrop = len(brk)-nbrk
print("Bracketable primes: %d / %d  (would-be-dropped: %d)" % (nbrk, len(brk), ndrop))
print("Dropped primes:", sorted(p for p in brk if not brk[p]))
print()
print("%-4s %-8s %-9s %-9s | %-9s %-9s %-9s %-8s"
      % ("|V|","T1_all","T1_kept","T1_drop","mean_kept","mean_drop","E_F2b","perm_p"))
for V in sorted(data):
    ps = sorted(data[V])
    deltas = [data[V][p] for p in ps]
    labels = [brk[p] for p in ps]
    t1_all = sum(deltas)/len(deltas)
    kept = [data[V][p] for p in ps if brk[p]]
    drop = [data[V][p] for p in ps if not brk[p]]
    t1_kept = sum(kept)/len(kept) if kept else float("nan")
    t1_drop = sum(drop)/len(drop) if drop else float("nan")
    obs, pv, mk, md = perm_p(deltas, labels)
    print("%-4d %-8.4f %-9.4f %-9.4f | %-9.4f %-9.4f %-9.4f %-8.4f"
          % (V, t1_all, t1_kept, t1_drop, mk, md, obs, pv))

print()
print("Reading: E_F2b = mean(dropped)-mean(kept). If ~0 or below floor (0.13/0.21/0.29 @|V|=4/5/6),")
print("prime-drop selection is NOT the mechanism, and T1_kept ~ T1_all shows the lever SURVIVES on")
print("the bracketable subset -> bracketing does not kill it by dropping high-delta primes.")
