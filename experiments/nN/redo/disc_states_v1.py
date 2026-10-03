# (3) State sequences R_0=1<R_1<...<R_n=R* of the members: ratios, exit laps, accumulation, empty intervals.
import pickle, numpy as np
from fractions import Fraction as F
from collections import Counter
rec = pickle.load(open('disc_records_v1.pkl', 'rb'))
d = np.load('disc_floats_v1.npz'); S = d['S']; nm = d['nm']; R = d['R']; rho = d['rho']; setter = d['setter']; lap = d['lap']; n = len(R)
print("members", n, "; moves total", int(nm.sum()))
print("\n== 3a. ratios R_{k+1}/R_k ==")
rat = []; rl = []; rr = []; rk = []
for i in range(n):
    for k in range(nm[i]):
        rat.append(S[i, k+1]/S[i, k]); rl.append(lap[i, k]); rr.append(setter[i, k]+1); rk.append(k+1)
rat = np.array(rat); rl = np.array(rl); rr = np.array(rr); rk = np.array(rk)
print("ratio min %.8f max %.8f  (9/7 = %.8f)" % (rat.min(), rat.max(), 9/7), "; quantiles 1/25/50/75/99%:", np.quantile(rat, [.01, .25, .5, .75, .99]).round(4).tolist())
print("moves with ratio >= 9/7 : %d" % (rat >= 9/7).sum())
print("per exit lap j: count, max ratio, bound 1+2/(8j-1), violations (ratio > bound+1e-12):")
for j in sorted(set(rl.tolist())):
    m = rl == j; b = 1+2/(8*j-1)
    print("  j=%2d n=%7d max %.6f bound %.6f viol %d" % (j, m.sum(), rat[m].max(), b, (rat[m] > b+1e-12).sum()))
print("exact: in every move of every member, exit lap j equals round(R_k*rho/8) of the setter at the state it is set from (tautology of the rule): checked on", int(nm.sum()), "moves:", end=" ")
bad = 0
for r in rec:
    st = r[5]
    for k, (y, j) in enumerate(r[6]):
        x = st[k]*r[1][y]/8
        if not (abs(x - j) < F(1, 8)) : bad += 1
print("lap off by >=1/8 of a lap: %d" % bad)
print("mean ln ratio by move index (1..30):", [round(float(np.log(rat[rk == k]).mean()), 4) for k in range(1, 30) if (rk == k).any()])
print("sum of ln ratios = ln R* (identity); nm vs ln R*: ", end="")
lr = np.log(R); A = np.vstack([lr, np.ones(n)]).T; coef, res, *_ = np.linalg.lstsq(A, nm, rcond=None); pred = A @ coef
print("fit nm = %.3f ln R* + %.3f ; R^2 = %.3f ; residual sd %.2f ; nm range among members with R* in [2.9,3.1): %s" % (coef[0], coef[1], 1-((nm-pred)**2).sum()/((nm-nm.mean())**2).sum(), (nm-pred).std(), (np.min(nm[(R >= 2.9) & (R < 3.1)]), np.max(nm[(R >= 2.9) & (R < 3.1)]))))
print("\n== 3b. exit laps and ranks ==")
tab = Counter(zip(rr.tolist(), rl.tolist()))
print("(rank,lap) pairs that occur as an exit: %d ; max lap per rank: %s ; min lap per rank: %s" % (len(tab), {y: max(j for (a, j) in tab if a == y) for y in range(1, 8)}, {y: min(j for (a, j) in tab if a == y) for y in range(1, 8)}))
print("exits by rank:", np.bincount(rr, minlength=8)[1:].tolist(), " ; rank 1 (reading 1) exits: all at lap 1, state 9:", Counter(rl[rr == 1].tolist()))
print("signed offset d = R_k*rho mod 8 (in (-1,1)) of the setter, histogram 0.2 bins:")
dd = []
for r in rec:
    for k, (y, j) in enumerate(r[6]): dd.append(float(r[5][k]*r[1][y]-8*j))
dd = np.array(dd); h, _ = np.histogram(dd, bins=np.arange(-1, 1.0001, 0.2)); print("   ", h.tolist(), " min %.4f max %.4f" % (dd.min(), dd.max()))
print("\n== 3c. setter vs the other blockers at the same state ==")
low = 0; deep = 0; tot = 0; nb = Counter()
for r in rec:
    st = r[5]; rh = r[1]
    for k in range(len(r[6])):
        Rk = st[k]
        bl = []
        for y, x in enumerate(rh):
            p = (Rk*x) % 8
            if min(p, 8-p) < 1: bl.append(y)
        nb[len(bl)] += 1; tot += 1
        s = r[6][k][0]
        if s == min(bl): low += 1
        dmin = min(bl, key=lambda y: abs(((Rk*rh[y]) % 8 + 4) % 8 - 4))
        if s == dmin: deep += 1
print("moves %d ; blockers per state: %s ; setter is lowest-rank blocker: %d (%.1f%%) ; setter is the blocker closest to its zone centre: %d (%.1f%%)" % (tot, sorted(nb.items()), low, 100*low/tot, deep, 100*deep/tot))
print("\n== 3d. where states accumulate ==")
allS = np.concatenate([S[i, 1:nm[i]+1] for i in range(n)])
h, e = np.histogram(allS, bins=np.arange(1, 12.01, 0.5)); print("states in 0.5 bins from 1:", h.tolist())
h, e = np.histogram(allS, bins=np.arange(1, 12.0001, 0.01)); z = np.flatnonzero(h == 0); runs = []
for k in z:
    a = 1+0.01*k
    if runs and abs(runs[-1][1]-a) < 1e-9: runs[-1][1] = a+0.01
    else: runs.append([a, a+0.01])
print("empty 0.01-bins of states in [1,12], runs:", [(round(a, 2), round(b, 2)) for a, b in runs])
rel = np.concatenate([S[i, 1:nm[i]+1]/R[i] for i in range(n)]); h, _ = np.histogram(rel, bins=np.arange(0, 1.0001, 0.1)); print("state/R* deciles (last bin contains R* itself, %d members):" % n, h.tolist())
sc = Counter(st for r in rec for st in r[5][1:]); print("exact state atoms (state value shared by >=1000 member-paths):", [(str(k), v) for k, v in sc.most_common(12) if v >= 1000])
print("first state R_1 range: %.5f .. %.5f ; ratio R_1/R_0 quantiles %s" % (S[:, 1].min(), S[:, 1].max(), np.quantile(S[:, 1], [.01, .5, .99]).round(3).tolist()))
print("R_1 histogram 0.1 bins from 1:", np.histogram(S[:, 1], bins=np.arange(1, 2.01, 0.1))[0].tolist())
print("\n== 3e. last move vs landing ==")
lastr = np.array([S[i, nm[i]]/S[i, nm[i]-1] for i in range(n)]); print("last ratio quantiles", np.quantile(lastr, [0, .01, .5, .99, 1]).round(5).tolist())
print("nm by opener rank (median):", {y: int(np.median(nm[np.array([setter[i, nm[i]-1] for i in range(n)]) == y-1])) for y in range(2, 8)})
