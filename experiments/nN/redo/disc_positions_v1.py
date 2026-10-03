# (2) Joint structure of the positions p_y = R* rho_y mod 8 at the landing (members; one witness per cell).
import pickle, numpy as np
from collections import Counter
from scipy.stats import spearmanr
from scipy.cluster.vq import kmeans2
d = np.load('disc_floats_v1.npz'); R = d['R']; W = d['W']; P = d['P']; rho = d['rho']; setter = d['setter']; nm = d['nm']; n = len(R)
op = np.array([setter[i, nm[i]-1] for i in range(n)])
mask = np.ones_like(P, bool); mask[np.arange(n), op] = False
print("members", n)
print("\n== 2a. per rank y: range of p_y, fine-bin emptiness in [1,7] (bin 0.02 => 300 bins), non-opener readings ==")
for y in range(7):
    p = P[mask[:, y], y]; h, _ = np.histogram(p, bins=np.arange(1, 7.0001, 0.02)); emp = np.flatnonzero(h == 0)
    runs = []
    for k in emp:
        a = 1 + 0.02*k
        if runs and abs(runs[-1][1] - a) < 1e-9: runs[-1][1] = a + 0.02
        else: runs.append([a, a + 0.02])
    print("rank %d: n=%d min %.6f max %.6f ; empty 0.02-bins %d ; runs %s" % (y+1, len(p), p.min(), p.max(), len(emp), [(round(a, 2), round(b, 2)) for a, b in runs][:12]))
print("rank 1 all members: p_1 = R* mod 8; p_1<7 for R*<7 ; for R*>9 p_1=R*-8 in", (R[R > 9]-8).min(), (R[R > 9]-8).max(), "; p_1 max over members", P[:, 0].max())
print("\n== 2b. coarse histograms (0.5 bins over [1,7]) per rank: all readings / non-opener ==")
for y in range(7):
    h1, _ = np.histogram(P[:, y], bins=np.arange(1, 7.01, 0.5)); h2, _ = np.histogram(P[mask[:, y], y], bins=np.arange(1, 7.01, 0.5))
    print("rank %d all %s | non-opener %s" % (y+1, h1.tolist(), h2.tolist()))
print("opener is at p == 1 exactly in every member (identity R*=(8j+1)/rho_y); opener rank counts:", np.bincount(op, minlength=7)[:].tolist())
print("\n== 2c. on-face (witness) positions: |p-1|<1e-6 or |p-7|<1e-6 among NON-opener readings ==")
q = P.copy(); q[~mask] = np.nan
near1 = np.abs(q-1) < 1e-6; near7 = np.abs(q-7) < 1e-6
print("non-opener readings with |p-1|<1e-6: %d (members with >=1: %d) ; |p-7|<1e-6: %d (members %d)" % (near1.sum(), near1.any(1).sum(), near7.sum(), near7.any(1).sum()))
print("by rank near1:", near1.sum(0).tolist(), " near7:", near7.sum(0).tolist())
for lo_, hi_ in [(1e-12, 1e-8), (1e-8, 1e-6), (1e-6, 1e-4), (1e-4, 1e-2), (1e-2, 0.25)]:
    print("  non-opener readings with %g<=p-1<%g: %d" % (lo_, hi_, ((q-1 >= lo_) & (q-1 < hi_)).sum()))
print("  exact-equal pattern: members with 1,2,3 readings at p==1 incl opener: see disc_rstar (exact tie counts below)")
rec = pickle.load(open('disc_records_v1.pkl', 'rb'))
tc = Counter(sum(1 for p in r[4] if p == 1) for r in rec); print("  exact ties at p==1 (readings incl. opener) per member:", sorted(tc.items()))
tie_rank = Counter(); tie_rel = Counter()
for r in rec:
    k = r[6][-1][0]; z = [i for i, p in enumerate(r[4]) if p == 1 and i != k]
    for i in z: tie_rank[i+1] += 1; tie_rel[i-k] += 1
print("  tied (non-opener) rank counts", sorted(tie_rank.items()), " rank offset from opener", sorted(tie_rel.items()))
print("  members with every non-opener p-1 > 1e-4:", int((~(np.nan_to_num(np.abs(q-1), nan=9) < 1e-4).any(1)).sum()))
print("\n== 2d. excess of non-opener readings just above p=1 (bin [1,1.25) vs mean of bins 1.25..2.5) per rank, with face-points removed (>1e-4) ==")
for y in range(7):
    p = P[mask[:, y], y]; pf = p[p - 1 > 1e-4]
    h, _ = np.histogram(pf, bins=np.arange(1, 7.01, 0.25)); print("rank %d: [1,1.25) %d  vs mean of next 5 bins %.0f (ratio %.2f)" % (y+1, h[0], h[1:6].mean(), h[0]/h[1:6].mean()))
print("\n== 2e. which rank sits just above 1 (1<p<1.25, off-face) relative to the opener's rank ==")
rel = Counter(); tot = 0
for i in range(n):
    for y in range(7):
        if mask[i, y] and 1e-4 < P[i, y]-1 < 0.25: rel[y-op[i]] += 1; tot += 1
print("offset (rank - opener rank) counts:", sorted(rel.items()), "total", tot)
print("\n== 2f. pairs: Spearman matrix (all members) and empty 0.5-cells of the (p_y,p_z) plane (12x12=144) ==")
print(np.round(spearmanr(P).correlation, 2))
emp = []
for a in range(7):
    for b in range(a+1, 7):
        h, xe, ye = np.histogram2d(P[:, a], P[:, b], bins=[np.arange(1, 7.01, 0.5)]*2)
        if (h == 0).sum(): emp.append((a+1, b+1, int((h == 0).sum()), [(1+0.5*i, 1+0.5*j) for i, j in zip(*np.nonzero(h == 0))][:6]))
print("pairs with empty 0.5-cells:", emp)
for (a, b) in [(2, 3), (3, 4), (4, 5), (5, 6), (6, 7)]:
    h, _, _ = np.histogram2d(P[:, a-1], P[:, b-1], bins=[np.arange(1, 7.01, 0.25)]*2); print("pair (%d,%d) empty 0.25-cells: %d of 576, min nonzero %d" % (a, b, (h == 0).sum(), h[h > 0].min()))
print("\n== 2g. does the vector of positions cluster? k-means inertia: real vs columns independently shuffled ==")
rng = np.random.default_rng(1); Pn = P[:, 1:]
Ps = np.column_stack([rng.permutation(Pn[:, k]) for k in range(Pn.shape[1])])
for k in (2, 3, 4, 6, 8, 12):
    iners = []
    for X in (Pn, Ps):
        best = 1e99
        for seed in range(5):
            c, lab = kmeans2(X, k, seed=seed, minit='++'); best = min(best, ((X - c[lab])**2).sum())
        iners.append(best/((X - X.mean(0))**2).sum())
    print("k=%d  inertia/total: real %.4f  shuffled %.4f" % (k, iners[0], iners[1]))
print("distinct rank-orders of p (permutation of 7):", len(Counter(map(lambda r: tuple(np.argsort(r)), P))), "of 5040 ; top share %.4f" % (Counter(map(lambda r: tuple(np.argsort(r)), P)).most_common(1)[0][1]/n))
L = np.floor(R[:, None]*rho/8 + 0.5).astype(int); cl = Counter(map(tuple, L)); print("distinct lap vectors:", len(cl), "; top 5 shares:", [round(v/n, 4) for _, v in cl.most_common(5)])
print("lap vectors among R*>9:", len(Counter(map(tuple, L[R > 9]))), " among R*<7:", len(Counter(map(tuple, L[R < 7]))))
