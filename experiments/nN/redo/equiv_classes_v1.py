# Part 7: equivalence classes by path / opener over the 9,652 tree cells (terminals5_J1.pkl) and the 20,000 survey arrangements (outcome_survey_v2.pkl).
import sys, pickle, collections
sys.path.insert(0, '.')
import numpy as np
from equiv_lib_v1 import *
cells = pickle.load(open('terminals5_J1.pkl', 'rb')); surv = pickle.load(open('outcome_survey_v2.pkl', 'rb'))
print("CELLS: tuples (path, Rlo, Rhi, 7 reading ranges, witness); n =", len(cells))
# what a cell's path is: compare with outcome() on the witness (witness readings rounded to 1e-9 rationals) -- equal / proper prefix / other
eq = pre = oth = 0
for c in cells:
    w = [F(1)] + [F(float(v)).limit_denominator(10 ** 9) for v in c[4]]
    try: o = outcome(w)['path']
    except Exception: oth += 1; continue
    if o == c[0]: eq += 1
    elif o[:len(c[0])] == c[0]: pre += 1
    elif c[0][:len(o)] == o: pre += 1
    else: oth += 1
print("witness path vs cell path: equal", eq, "| one is a prefix of the other", pre, "| neither", oth, "(the witness is a point of the cell on its boundary, readings at 9.0 and similar; a boundary point can belong to a neighbouring path)")
eq2 = 0
for c in cells:
    w = [F(1)] + [F(float((x[0] + x[1]) / 2)).limit_denominator(10 ** 9) for x in c[3][1:]]
    eq2 += outcome(w)['path'] == c[0]
print("midpoint of the six ranges as the reading vector: its outcome path equals the cell path in", eq2, "of", len(cells), "(cells need not be boxes, so a midpoint need not lie in its cell)")
P = collections.defaultdict(list); O = collections.defaultdict(list)
for i, c in enumerate(cells): P[c[0]].append(i); O[c[0][-1] if c[0] else None].append(i)
sizes = collections.Counter(len(v) for v in P.values())
print("\nCELLS by path: distinct paths", len(P), "; cells in paths shared by >=2 cells:", sum(len(v) for v in P.values() if len(v) > 1), "; families of size >=2:", sum(1 for v in P.values() if len(v) > 1), "; size histogram (size:count):", sorted(sizes.items()))
print("CELLS by opener (last step of the path): distinct openers", len(O), "; largest:", sorted(((len(v), k) for k, v in O.items()), reverse=True)[:5])
R = np.array([[(float(x[0]), float(x[1])) for x in c[3]] for c in cells])           # (ncell, 7, 2)
def disjoint_matrix(idx):
    lo = R[idx, 1:, 0]; hi = R[idx, 1:, 1]
    d = (hi[:, None, :] < lo[None, :, :]) | (hi[None, :, :] < lo[:, None, :])        # strict gap per rank 2..7
    return d
def fam_stats(idx):
    d = disjoint_matrix(idx); nd = d.sum(axis=2); n = len(idx); iu = np.triu_indices(n, 1)
    nd = nd[iu]
    return n, int((nd >= 1).sum()), int((nd == 6).sum()), nd, d
tot_pairs = pair1 = pair6 = 0; fams = []
for p, idx in P.items():
    if len(idx) < 2: continue
    n, a1, a6, nd, d = fam_stats(idx)
    tot_pairs += n * (n - 1) // 2; pair1 += a1; pair6 += a6
    fams.append((n, a1, a6, p, idx))
print("\nPAIRS of cells with the same path: total", tot_pairs, "; pairs with >=1 reading rank (2..7) range disjoint:", pair1, "; pairs with ALL six ranges 2..7 pairwise disjoint:", pair6)
fams6 = sorted([f for f in fams if f[2] > 0], key=lambda f: -f[0])
print("path-families containing at least one all-ranks-disjoint pair:", len(fams6), "of", len(fams))
print("\nTEN LARGEST path-families (cells sharing a path) containing an all-six-ranges-disjoint pair:")
for n, a1, a6, p, idx in fams6[:10]:
    d = disjoint_matrix(idx); nd = d.sum(axis=2); np.fill_diagonal(nd, 0); ii = np.unravel_index(np.argmax(nd * (nd == 6)), nd.shape)
    a, b = idx[ii[0]], idx[ii[1]]
    # greedy set of mutually all-disjoint cells
    chosen = []
    for i in range(n):
        if all(nd[i, j] == 6 for j in chosen): chosen.append(i)
    print(" path length %d, last step %s: %d cells, %d pairs, >=1 disjoint rank %d, all six disjoint %d, greedy mutually-all-disjoint subset size %d" % (len(p), p[-1], n, n * (n - 1) // 2, a1, a6, len(chosen)))
    print("     path = %s" % (p,))
    print("     example pair: cell %d ranges %s ; cell %d ranges %s" % (a, [(round(float(x), 3), round(float(y), 3)) for x, y in R[a, 1:]], b, [(round(float(x), 3), round(float(y), 3)) for x, y in R[b, 1:]]))
print("\nTEN LARGEST path-families regardless of disjointness:", [(len(v), len(k)) for k, v in sorted(P.items(), key=lambda kv: -len(kv[1]))[:10]], "(cells, path length)")
# openers
print("\nCELLS by opener: pairs with same opener but different path, all six ranges disjoint (counted per opener family):")
rows = []
for k, idx in O.items():
    if len(idx) < 2: continue
    n, a1, a6, nd, d = fam_stats(idx)
    # same-opener, different-path pairs
    paths = [cells[i][0] for i in idx]; ii, jj = np.triu_indices(n, 1)
    diffp = np.array([paths[a] != paths[b] for a, b in zip(ii, jj)])
    rows.append((n, k, a1, a6, int(((nd == 6) & diffp).sum()), int(diffp.sum()), len(set(paths))))
for r in sorted(rows, reverse=True)[:10]:
    print("  opener %s: %d cells, %d distinct paths, pairs %d, all-six-ranges-disjoint pairs %d, of which different path %d, pairs with different path %d" % (r[1], r[0], r[6], r[0] * (r[0] - 1) // 2, r[3], r[4], r[5]))
# range sets: cells with identical reading ranges and different path (same region read by two paths)
rk = collections.defaultdict(set)
for c in cells: rk[tuple((float(x[0]), float(x[1])) for x in c[3])].add(c[0])
print("\ncells with identical 7-range boxes but different paths:", sum(1 for v in rk.values() if len(v) > 1), "boxes")

# ---- SURVEY arrangements
print("\n\nSURVEY: n =", len(surv))
SP = collections.defaultdict(list); SO = collections.defaultdict(list); SOC = collections.defaultdict(list); SL = collections.defaultdict(list)
for i, s in enumerate(surv):
    SP[s['path']].append(i); SO[s['opener']].append(i); SOC[(s['opener'], s['closer'])].append(i); SL[s['lap']].append(i)
for nm, D in (("path", SP), ("opener", SO), ("(opener, closer)", SOC), ("lap vector at the landing", SL)):
    sz = [len(v) for v in D.values()]
    print(" classes by %-26s: %5d classes ; singletons %d ; arrangements in classes of size>=2: %d ; largest %s" % (nm, len(D), sum(1 for x in sz if x == 1), sum(x for x in sz if x > 1), sorted(sz, reverse=True)[:6]))
print(" families (paths) by 'fam' of members:", collections.Counter(len(set(surv[i]['fam'] for i in v)) for v in SP.values()))
rho = np.array([[float(x) for x in sorted(s['rho'])[1:]] for s in surv])         # ranks 2..7 in units of d_min
def maxmin(idx):
    """max over pairs in idx of min_y |rho_y - rho'_y| (ranks 2..7), chunked; returns value and pair"""
    X = rho[idx]; best = (-1, None)
    for a in range(0, len(idx), 400):
        D = np.abs(X[a:a + 400, None, :] - X[None, :, :]).min(axis=2)
        m = D.max(); 
        if m > best[0]:
            ii = np.unravel_index(D.argmax(), D.shape); best = (m, (idx[a + ii[0]], idx[ii[1]]))
    return best
def table(D, nm, minsize=2):
    rows = []
    for k, idx in D.items():
        if len(idx) < minsize: continue
        m, pr = maxmin(idx); rows.append((len(idx), k, m, pr))
    return rows
def thr(rows, t): return sum(1 for r in rows if r[2] >= t)
for nm, D in (("path", SP), ("opener", SO), ("(opener, closer)", SOC)):
    rows = table(D, nm)
    print("\n SURVEY families by %s with >=2 members: %d ; with a pair whose six readings (ranks 2..7) ALL differ by at least 1/4: %d ; 1/2: %d ; 1: %d ; 2: %d" % (nm, len(rows), thr(rows, .25), thr(rows, .5), thr(rows, 1), thr(rows, 2)))
    print("   TEN LARGEST families by %s (members, key, max over pairs of min_y|drho_y|, example pair):" % nm)
    for n, k, m, pr in sorted(rows, key=lambda r: -r[0])[:10]:
        print("     %5d  key=%s  maxmin=%.3f  pair rho: %s | %s" % (n, str(k)[:90], m, [str(x) for x in surv[pr[0]]['rho'][1:]], [str(x) for x in surv[pr[1]]['rho'][1:]]))
