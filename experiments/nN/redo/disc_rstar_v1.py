# (1) Distributions of R* and width over the 110,081 tree members (one LP-witness member per cell). Exact Fractions where an atom/edge is claimed.
import pickle, numpy as np
from fractions import Fraction as F
from collections import Counter
recs = pickle.load(open('disc_records_v1.pkl','rb'))
cells = pickle.load(open('terminals5_J2.pkl','rb'))
Rl = np.array([c[1] for c in cells]); Rh = np.array([c[2] for c in cells])
N = len(recs); print("members", N, "distinct cells", len({r[0] for r in recs}), "(one member per cell)")
def opener(r): s = r[6][-1]; return (s[0]+1, s[1])
Rs = [r[2] for r in recs]; Rf = np.array([float(x) for x in Rs])
print("R* min %s (%.6f) max %.6f; zero-move members %d" % (min(Rs), float(min(Rs)), Rf.max(), sum(1 for r in recs if not r[6])))
print("\n== 1a. gaps of R* (consecutive distinct sorted member values, gap > 0.03) in [1,12] ==")
order = sorted(range(N), key=lambda i: Rs[i]); vals = [Rs[i] for i in order]
edges = [(float(vals[0]) - 1.0, F(1), vals[0], None, order[0])]
gaps = []
for a, b in zip(range(N-1), range(1, N)):
    g = float(vals[b] - vals[a])
    if g > 0.03: gaps.append((g, order[a], order[b]))
print("gap above R*=max: (%.5f, 12): empty" % Rf.max())
print("lowest: members start at %.6f; interval (1,%.6f) empty of members" % (Rf.min(), Rf.min()))
for g, i, j in gaps:
    lo, hi = recs[i][2], recs[j][2]; fl, fh = float(lo), float(hi)
    inter = ((Rl < fh) & (Rh > fl)).sum(); inside = ((Rl >= fl) & (Rh <= fh)).sum()
    print("gap (%.5f, %.5f) width %.4f | lo=%s opener%s | hi=%s opener%s | cells meeting gap: %d, cells fully inside gap: %d" % (fl, fh, g, str(lo) if lo.denominator < 10**6 else '~', opener(recs[i]), str(hi) if hi.denominator < 10**6 else '~', opener(recs[j]), inter, inside))
print("\nlow end: cells meeting (1,%.4f): %d ; members in those cells: %d" % (Rf.min(), ((Rl < Rf.min()) & (Rh > 1)).sum(), sum(1 for r in recs if Rl[r[0]] < Rf.min())))
print("cells with Rlo<=1.0000001: %d" % (Rl < 1.0000001).sum())
print("\n== exact tests: R* in the zone of reading 1 ==")
print("members with 7 < R* < 9: %d ; R*==7: %d ; R*==9: %d (openers %s)" % (sum(1 for x in Rs if 7 < x < 9), sum(1 for x in Rs if x == 7), sum(1 for x in Rs if x == 9), Counter(opener(r) for r in recs if r[2] == 9)))
print("cells whose [Rlo,Rhi] meets (7,9): %d ; cells with Rhi==7.0: %d ; Rlo==9: %d" % (((Rl < 9) & (Rh > 7)).sum(), (Rh == 7.0).sum(), (Rl == 9.0).sum()))
print("members with a reading exactly (8j+1)/7 (so that an exit can equal 7): ", sum(1 for r in recs for x in r[1] if (x * 7 - 1) % 8 == 0 and x * 7 > 1))
top = sorted(((r[2], r[0], opener(r)) for r in recs if r[2] < 7), reverse=True)[:6]
print("largest member R* below 7:", [(float(a), c, o) for a, c, o in top])
print("members with R* in (6.7,7): %d ; (6.6,6.7): %d ; (6.5,6.6): %d" % tuple(sum(1 for x in Rf if lo < x < hi) for lo, hi in [(6.7, 7), (6.6, 6.7), (6.5, 6.6)]))
cm = [i for i in range(len(cells)) if Rl[i] < 7 and Rh[i] > 6.79]
have = {r[0] for r in recs}
print("cells meeting (6.79,7): %d ; of them with a member: %d ; their members' max R*: %.6f" % (len(cm), sum(1 for i in cm if i in have), max([float(r[2]) for r in recs if r[0] in set(cm)] or [0])))
print("\n== 1b. atoms: exact repeated R* ==")
c = Counter(Rs); rep = {k: v for k, v in c.items() if v >= 2}
print("distinct R* values %d ; values repeated >=2: %d, covering %d members (%.1f%%); repeated >=10: %d values covering %d" % (len(c), len(rep), sum(rep.values()), 100*sum(rep.values())/N, sum(1 for v in rep.values() if v >= 10), sum(v for v in rep.values() if v >= 10)))
byatom = {}
for r in recs:
    if r[2] in rep and rep[r[2]] >= 10:
        y, j = r[6][-1][0], r[6][-1][1]; x = r[1][y]
        byatom.setdefault(r[2], Counter())[(y+1, j, str(x) if x.denominator < 100 else 'nonint')] += 1
for k, v in sorted(rep.items(), key=lambda kv: -kv[1])[:25]:
    print("  R*=%-8s %.5f  count %5d  opener (rank,lap,reading): %s" % (k, float(k), v, dict(byatom.get(k, {}))))
# is every atom an exit of an integer-valued opener?
bad = 0; tot = 0
for r in recs:
    if rep.get(r[2], 0) >= 2:
        tot += 1; x = r[1][r[6][-1][0]]
        if x.denominator != 1: bad += 1
print("members in atoms (mult>=2): %d ; with opener reading a non-integer: %d" % (tot, bad))
print("members whose opener reading is an exact integer: %d of %d (%.2f%%)" % (sum(1 for r in recs if r[1][r[6][-1][0]].denominator == 1), N, 100*sum(1 for r in recs if r[1][r[6][-1][0]].denominator == 1)/N))
print("members with rho_7 == 17 exactly: %d" % sum(1 for r in recs if r[1][6] == 17))
print("\n== 1c. histogram of R*, bins 0.1 (all) and (atoms removed) ==")
h, e = np.histogram(Rf, bins=np.arange(1, 12.01, 0.1))
na = np.array([float(r[2]) for r in recs if rep.get(r[2], 0) < 10]); h2, _ = np.histogram(na, bins=e)
for a, b, b2 in zip(e, h, h2): print("%.1f:%d/%d" % (a, b, b2), end="  ")
print("\nmembers removed as atoms (mult>=10): %d" % (N - len(na)))
print("\n== 1d. lower edges of opener bands: (8j+1)/17 ==")
for j in range(2, 15):
    x = 8.0*j/17 + 1/17; cnt = ((Rf >= x - 0.02) & (Rf < x)).sum(), ((Rf >= x) & (Rf < x + 0.02)).sum()
    print("j=%d (8j+1)/17=%.4f  members in [x-.02,x): %d, [x,x+.02): %d" % (j, x, cnt[0], cnt[1]))
print("\n== width ==")
W = [r[3] for r in recs]; Wf = np.array([float(x) for x in W])
print("W min %.3e max %.6f ; exact zero: %d ; <1e-12: %d ; <1e-9: %d ; <1e-6: %d ; <1e-4: %d ; <1e-3: %d ; <1e-2: %d" % (Wf.min(), Wf.max(), sum(1 for x in W if x == 0), (Wf < 1e-12).sum(), (Wf < 1e-9).sum(), (Wf < 1e-6).sum(), (Wf < 1e-4).sum(), (Wf < 1e-3).sum(), (Wf < 1e-2).sum()))
hh, ee = np.histogram(np.log10(Wf[Wf > 0]), bins=np.arange(-17, 0.01, 0.5)); print("log10 W bins of 0.5 from -17:", hh.tolist())
hh, ee = np.histogram(Wf, bins=np.arange(0, 0.5601, 0.02)); print("linear W bins 0.02:", hh.tolist())
cw = Counter(W); print("repeated exact widths (>=2):", sum(1 for v in cw.values() if v >= 2), "values; top", [(str(k), v) for k, v in cw.most_common(4)])
zs = [r for r in recs if r[3] == 0]
for r in zs: 
    k = [i for i, p in enumerate(r[4]) if p == 7]
    print("  zero width: cell %d R*=%s rank at p==7: %s ; opener %s ; reading of that rank %s ; rho_7=%s" % (r[0], r[2], [i+1 for i in k], opener(r), r[1][k[0]], r[1][6]))
cl = np.array([int(np.argmin([(7 - p) / x for p, x in zip(r[4], r[1])])) + 1 for r in recs]); print("closer rank (reading that enters first) counts:", np.bincount(cl)[1:].tolist())
