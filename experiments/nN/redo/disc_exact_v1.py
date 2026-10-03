# Exact (Fraction) versions of every fact stated in disc_outcome_structure_v1.md.  No float, no tolerance in any verdict.
import pickle, re, bisect
from fractions import Fraction as F
from math import floor
from collections import Counter
rec = pickle.load(open('disc_records_v1.pkl', 'rb')); N = len(rec)
def fl(x): return floor(x)
def rnd(x): return floor(x + F(1, 2))
print("members", N)
# ---- E1 witnesses bracketed by consecutive members
vals = sorted(r[2] for r in rec)
wit = [l for l in open('disc_gapwitness_v1.out') if 'EXACT witness' in l]
extra = [("62250 climb", F(55169095435288576, 7881299347899751)), ("62251 climb", F(27584547717644288, 4011964952796309))]
print("\n== E1 exact witnesses (arrangements in cells; outside the member list) bracketed by consecutive member values ==")
for l in wit:
    m = re.search(r'gap (\d+).*cell (\d+), exact R\* = (\d+)/(\d+)', l); extra.append(("gap %s cell %s" % (m.group(1), m.group(2)), F(int(m.group(3)), int(m.group(4)))))
for name, x in extra:
    i = bisect.bisect_left(vals, x); lo = vals[i-1] if i > 0 else None; hi = vals[i] if i < N else None
    print("  %-18s R*=%.10f  nearest member below %s above %s ; gap between them %s" % (name, float(x), None if lo is None else "%.6f" % float(lo), None if hi is None else "%.6f" % float(hi), None if (lo is None or hi is None) else "%.4f" % float(hi-lo)))
# ---- E2 reading 1 and zone (7,9)
print("\n== E2 reading 1 (exact) ==")
b9 = [r for r in rec if any(s == F(9) for s in r[5])]; setter1 = [r for r in rec if any(y == 0 for y, j in r[6])]; big = [r for r in rec if r[2] >= 9]
print("members with a state exactly 9: %d ; with reading 1 as a setter: %d ; with R* >= 9: %d ; with R* > 7: %d ; the three sets equal: %s" % (len(b9), len(setter1), len(big), sum(1 for r in rec if r[2] > 7), {r[0] for r in b9} == {r[0] for r in setter1} == {r[0] for r in big}))
print("members with R* in (7,9): %d ; R*==7: %d ; R*==9: %d" % (sum(1 for r in rec if 7 < r[2] < 9), sum(1 for r in rec if r[2] == 7), sum(1 for r in rec if r[2] == 9)))
inz = [(r[0], max(s for s in r[5] if s < 9 and s > 7)) for r in rec if any(7 < s < 9 for s in r[5])]
print("members with a state in the open interval (7,9): %d (all with reading 1 setting the next move: %s); largest state below 9 over members: %s = %.6f ; smallest state above 7: %.6f" % (len(inz), all(r[0] in {q[0] for q in inz} for r in setter1), max(v for _, v in inz), float(max(v for _, v in inz)), float(min(s for r in rec for s in r[5] if s > 7))))
print("min #moves among R*>=9: %d ; max #moves among R*<7: %d ; min #moves among R*<7: %d" % (min(len(r[6]) for r in big), max(len(r[6]) for r in rec if r[2] < 7), min(len(r[6]) for r in rec if r[2] < 7)))
# ---- E3 ratios exact
print("\n== E3 ratios exact ==")
bound_viol = 0; maxr = {}; first_gt = 0; moves = 0
for r in rec:
    st = r[5]
    for k, (y, j) in enumerate(r[6]):
        q = st[k+1]/st[k]; moves += 1
        if q > 1 + F(2, 8*j-1) or q >= F(9, 7): bound_viol += 1
        if j not in maxr or q > maxr[j]: maxr[j] = q
print("moves %d ; ratio > 1+2/(8j-1) (j the exit lap) or >= 9/7: %d" % (moves, bound_viol))
print("max ratio per exit lap j and its slack to 1+2/(8j-1):", {j: (float(maxr[j]), float(1+F(2, 8*j-1)-maxr[j])) for j in sorted(maxr)[:5]})
print("R_1 exact max over members: %.8f (< 9/7: %s)" % (float(max(r[5][1] for r in rec)), all(r[5][1] < F(9, 7) for r in rec)))
# ---- E4 setter vs blockers + skipped zones
print("\n== E4 setter vs other blockers (exact) ==")
mv = 0; low = 0; exc = []; nb = Counter()
for r in rec:
    st, rh = r[5], r[1]
    for k, (s, j) in enumerate(r[6]):
        Rk = st[k]; bl = []
        for y, x in enumerate(rh):
            p = (Rk*x) % 8
            if p < 1 or p > 7: bl.append((y, rnd(Rk*x/8)))
        nb[len(bl)] += 1; mv += 1
        if s == bl[0][0]: low += 1
        else:
            y0, j0 = bl[0]; d0 = Rk*rh[y0]-8*j0; ds = Rk*rh[s]-8*j; exc.append((d0, ds, y0, s, len(bl)))
print("moves %d ; blockers-per-state counts %s ; setter is the lowest-rank blocker in %d moves ; not in %d moves (all with >=2 blockers)" % (mv, sorted(nb.items()), low, len(exc)))
print("in the exceptions: lowest-rank blocker's signed offset d_low: min %.4f max %.4f ; d_low > 0 in %d of %d ; d_low > d_setter in %d of %d (identity: exit_low < exit_setter forces d_low > d_set when rho_low<rho_set)" % (float(min(e[0] for e in exc)), float(max(e[0] for e in exc)), sum(1 for e in exc if e[0] > 0), len(exc), sum(1 for e in exc if e[0] > e[1]), len(exc)))
print("exceptions by (lowest blocker rank -> setter rank), top 10:", Counter((e[2]+1, e[3]+1) for e in exc).most_common(10))
print("exceptions by number of blockers:", sorted(Counter(e[4] for e in exc).items()))
print("\n== E4b zones passed: for reading y and lap j with exit (8j+1)/rho <= R*, 'visited' if some state R_k (k<n) lies in the open zone, else 'skipped' ==")
vis = Counter(); skp = Counter(); skp_by_setter_lower = 0; skp_total = 0; viol = 0
for r in rec:
    st = r[5]; rh = r[1]; Rs = r[2]
    for y, x in enumerate(rh):
        j = 1
        while (8*j+1)/x <= Rs:
            a, b = F(8*j-1)/x, F(8*j+1)/x
            if b <= 1: j += 1; continue   # zone lies wholly below the start R_0=1
            inside = [k for k in range(len(st)-1) if a < st[k] < b]
            if inside: vis[y+1] += 1
            else:
                skp[y+1] += 1; skp_total += 1
                # the move that jumped over: state k with st[k] <= a and st[k+1] >= b
                k = [k for k in range(len(st)-1) if st[k] <= a and st[k+1] >= b]
                if k and r[6][k[0]][0] >= y: viol += 1
                if not k: viol += 1
            j += 1
print("visited by rank:", sorted(vis.items()), " skipped by rank:", sorted(skp.items()), " skipped zones whose jump was NOT set by a strictly lower rank (or not found): %d of %d" % (viol, skp_total))
# ---- E5 ties exact + closer/opener table
print("\n== E5 exact ties and closer/opener ==")
print("members with k readings exactly at p==1 (opener included):", sorted(Counter(sum(1 for p in r[4] if p == 1) for r in rec).items()), " at p==7:", sorted(Counter(sum(1 for p in r[4] if p == 7) for r in rec).items()))
nontie = [(p-1) for r in rec for y, p in enumerate(r[4]) if p != 1 and y != r[6][-1][0]]
print("smallest exact p-1 over non-opener readings with p != 1: %s (= %.3e) ; smallest 7-p with p != 7: %.3e" % (min(nontie), float(min(nontie)), float(min(7-p for r in rec for p in r[4] if p != 7))))
tab = Counter(); cl_eq = Counter()
for r in rec:
    k = r[6][-1][0]+1
    q = [(7-p)/x for p, x in zip(r[4], r[1])]; c = q.index(min(q))+1; ties = q.count(min(q))
    tab[(k, c)] += 1
    cl_eq['closer<opener' if c < k else ('closer==opener' if c == k else 'closer>opener')] += 1
print("opener rank (rows 1..7) x closer rank (cols 1..7) counts:")
for k in range(1, 8): print("  opener %d: %s" % (k, [tab[(k, c)] for c in range(1, 8)]))
print(dict(cl_eq))
print("members with two readings tied for closer (exact): %d" % sum(1 for r in rec if [ (7-p)/x for p, x in zip(r[4], r[1])].count(min((7-p)/x for p, x in zip(r[4], r[1]))) > 1))
# ---- E6 exact binned counts
print("\n== E6 exact binning (floor of exact value) ==")
h = Counter(fl(r[2]*10) for r in rec); print("R* by tenth, index=floor(10R*):", [(k, h[k]) for k in sorted(h)])
for y in range(1, 7):
    hp = Counter(fl(r[4][y]*50) for r in rec if r[6][-1][0] != y)
    miss = [k for k in range(50, 350) if hp[k] == 0]; print("rank %d non-opener p: empty exact 0.02-bins in [1,7): %d %s ; min %s max %s" % (y+1, len(miss), [round(k/50, 2) for k in miss][:8], float(min(r[4][y] for r in rec if r[6][-1][0] != y)), float(max(r[4][y] for r in rec if r[6][-1][0] != y))))
hp = Counter(fl(r[4][0]*50) for r in rec); miss = [k for k in range(50, 350) if hp[k] == 0]; print("rank 1 p (=R* mod 8): empty exact 0.02-bins: %d ; runs start/end:" % len(miss), (miss[0]/50, miss[-1]/50), " max p_1 over members %.6f" % float(max(r[4][0] for r in rec)))
pairs = []
for a in range(1, 7):
    for b in range(a+1, 7):
        c = Counter((fl(r[4][a]*2), fl(r[4][b]*2)) for r in rec); e = [(i/2, j/2) for i in range(2, 14) for j in range(2, 14) if c[(i, j)] == 0]
        if e: pairs.append((a+1, b+1, len(e), e[:6]))
print("pairs among ranks 2..7 with empty exact 0.5x0.5 cells (of 144):", pairs)
W = [r[3] for r in rec]; Wn = sorted(w for w in W if w > 0)
print("width: exact zero %d ; five smallest positive %s ; largest %s = %.6f ; members with width < 1/10^6: %d ; < 1/10^3: %d" % (sum(1 for w in W if w == 0), [float(x) for x in Wn[:5]], max(W), float(max(W)), sum(1 for w in W if w < F(1, 10**6)), sum(1 for w in W if w < F(1, 1000))))
