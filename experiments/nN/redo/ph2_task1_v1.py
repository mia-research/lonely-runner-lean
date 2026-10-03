# ph2 Task 1: phase 2 of the cascade (from state 9) as an object.  Exact Fractions throughout.
import pickle, sys, collections, math
from fractions import Fraction as F
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
def C2(n): return n*(n-1)//2
def fl(x): return math.floor(x)
def load(name):
    mem = pickle.load(open(name, 'rb')); return mem
def split(r):
    steps, Rend = path(r)
    g = [i for i, s in enumerate(steps) if s['setter'] == 0]
    return steps, Rend, g
def analyse(mem, label, out):
    P = lambda *a: print(*a, file=out, flush=True)
    N = len(mem); rows = []; bad = 0; multi = 0
    for idx, r in mem:
        steps, Rend, g = split(r)
        cross = Rend > 7
        if cross != (len(g) == 1): bad += 1
        if len(g) > 1: multi += 1
        if not cross: continue
        gs = steps[g[0]]
        assert gs['lap'] == 1 and gs['R2'] == 9
        w1 = tuple((s['setter']+1, s['lap']) for s in steps[:g[0]])
        w2 = tuple((s['setter']+1, s['lap']) for s in steps[g[0]+1:])
        rows.append((idx, r, steps, g[0], Rend, w1, w2))
    P('== %s: members %d; gate-crossing (landing>7) %d; (landing>7) xor (reading 1 sets a move) failures %d; members with >1 reading-1 move %d' % (label, N, len(rows), bad, multi))
    return rows
def determinacy(rows, out, label):
    P = lambda *a: print(*a, file=out, flush=True)
    n = len(rows)
    # keys
    def klap(r): return tuple(fl(9*x/8 + F(1, 2)) for x in r[1:])
    def kblock(r): return tuple(y+1 for y in range(1, 7) if blocks(F(9), r[y]))
    def kposlap(r): return (klap(r), kblock(r))
    def kexit(r):  # order of the blockers' exits at 9 (first-move data)
        bl = [y for y in range(1, 7) if blocks(F(9), r[y])]
        return tuple(sorted(((8*round(9*r[y]/8)+1)/r[y], y+1) for y in bl))
    def kexitrank(r):
        return tuple(y for _, y in kexit(r))
    def kend(r, Rend):  # zone-endpoint order type on (9, X], X = 12: all endpoints of readings 2..7
        ev = []
        for y in range(1, 7):
            j = 1
            while True:
                en, ex = F(8*j-1)/r[y], F(8*j+1)/r[y]
                if en > 12: break
                if ex > 9: ev.append((en, 0, y+1, j)); ev.append((ex, 1, y+1, j))
                j += 1
        ev.sort()
        # relative order only: labels, and whether the endpoints lie before/at 9 / after 12 is implicit
        return tuple((k, y, j) for _, k, y, j in ev if _ > 9 and _ <= 12)
    keys = {'w1 (phase-1 word)': lambda row: row[5],
            'lap vector at 9': lambda row: klap(row[1]),
            'lap vector + blocker set at 9': lambda row: kposlap(row[1]),
            'lap vector + blocker set + order of blockers\' exits at 9': lambda row: (kposlap(row[1]), kexitrank(row[1])),
            'endpoint order type of all zones of ranks 2..7 on (9,12]': lambda row: kend(row[1], row[4])}
    w2s = [row[6] for row in rows]
    gw2 = collections.Counter(w2s)
    P('-- %s: %d gate-crossing members; distinct phase-2 words %d; distinct phase-1 words %d' % (label, n, len(gw2), len(set(row[5] for row in rows))))
    for name, f in keys.items():
        kk = [f(row) for row in rows]
        gk = collections.Counter(kk); gkw = collections.Counter(zip(kk, w2s))
        same_k_diff_w2 = sum(C2(c) for c in gk.values()) - sum(C2(c) for c in gkw.values())
        same_k_same_w2 = sum(C2(c) for c in gkw.values())
        # classes of key values with >1 phase-2 word
        by = collections.defaultdict(set)
        for k, w in zip(kk, w2s): by[k].add(w)
        nmulti = sum(1 for s in by.values() if len(s) > 1)
        # converse: same w2, different key
        same_w2_diff_k = sum(C2(c) for c in gw2.values()) - same_k_same_w2
        P('   key [%s]: distinct key values %d; key values carrying >1 phase-2 word %d (of %d); pairs same key & different w2: %d; pairs same w2 & different key: %d; pairs same key & same w2: %d' % (name, len(gk), nmulti, len(gk), same_k_diff_w2, same_w2_diff_k, same_k_same_w2))
def catalogue(rows, out, label, tsv=None):
    P = lambda *a: print(*a, file=out, flush=True)
    cnt = collections.Counter(); land = {}
    for row in rows:
        w2, R = row[6], row[4]
        cnt[w2] += 1
        lo, hi = land.get(w2, (R, R)); land[w2] = (min(lo, R), max(hi, R))
    L = collections.Counter()
    for w, c in cnt.items(): L[len(w)] += 1
    Lm = collections.Counter(len(row[6]) for row in rows)
    P('-- %s catalogue: distinct phase-2 words %d; by length (words): %s; by length (members): %s' % (label, len(cnt), sorted(L.items()), sorted(Lm.items())))
    # prefix closure
    ws = set(cnt)
    nclosed = sum(1 for w in ws if len(w) == 0 or w[:-1] in ws)
    P('   words whose parent (word minus last move) is also an occurring word: %d of %d' % (nclosed, len(ws)))
    firstm = collections.Counter(w[0] for w in ws if w)
    P('   distinct first phase-2 moves (rank,lap) over words: %d; as list with word count: %s' % (len(firstm), sorted(firstm.items())))
    lastm = collections.Counter(w[-1] for w in ws if w)
    P('   distinct last moves (the opener) over words: %d' % len(lastm))
    P('   landing range overall: min %s = %.6f, max %s = %.6f' % (min(v[0] for v in land.values()), float(min(v[0] for v in land.values())), max(v[1] for v in land.values()), float(max(v[1] for v in land.values()))))
    # per length landing range
    for ln in sorted(L):
        lo = min(land[w][0] for w in ws if len(w) == ln); hi = max(land[w][1] for w in ws if len(w) == ln)
        P('   length %d: landing range [%.6f, %.6f]' % (ln, float(lo), float(hi)))
    # words occurring with >1 landing ranges / most frequent
    P('   10 most frequent words (count, landing min..max, word):')
    for w, c in cnt.most_common(10): P('     %d  %.5f..%.5f  %s' % (c, float(land[w][0]), float(land[w][1]), w))
    if tsv:
        with open(tsv, 'w') as f:
            for w, c in sorted(cnt.items(), key=lambda t: (len(t[0]), t[0])):
                f.write('%d\t%d\t%.9f\t%.9f\t%s\n' % (len(w), c, float(land[w][0]), float(land[w][1]), ' '.join('(%d,%d)' % x for x in w)))
    # move rules in phase 2 (and phase 1 for the link rule)
    tot = 0; rl_low = rl_high = rl_lap = rl_bl1 = 0; nbl = collections.Counter(); linkviol = 0; linktot = 0; difsetter = 0; reuse = 0
    for row in rows:
        steps, g = row[2], row[3]
        used = set()
        for k, s in enumerate(steps):
            if k > g:
                tot += 1
                bl = s['blockers']; nbl[len(bl)] += 1
                laps = {i: round(s['R'] * row[1][i] / 8) for i in bl}
                if s['setter'] == min(bl): rl_low += 1
                if s['setter'] == max(bl): rl_high += 1
                if laps[s['setter']] == max(laps.values()): rl_lap += 1
            key = (s['setter'], s['lap'])
            if key in used: reuse += 1
            used.add(key)
            if k + 1 < len(steps):
                a, b = s, steps[k+1]; linktot += 1
                ra, rb = row[1][a['setter']], row[1][b['setter']]
                if a['setter'] == b['setter']: difsetter += 1
                elif rb > ra: linkviol += (b['lap'] <= a['lap'])
                else: linkviol += (b['lap'] > a['lap'])
    P('   phase-2 moves examined %d; setter = lowest-rank blocker in %d; = highest-rank blocker in %d; = blocker of largest lap in %d; blocker-count distribution %s' % (tot, rl_low, rl_high, rl_lap, sorted(nbl.items())))
    P('   LINK RULE over all consecutive move pairs (phase 1 and 2) of these members: %d pairs; consecutive equal setters %d; link-rule violations %d; (reading,lap) setters used twice in one path: %d' % (linktot, difsetter, linkviol, reuse))
def bounds(rows, out, label):
    P = lambda *a: print(*a, file=out, flush=True)
    def B1(r, X):
        return sum(fl((X*r[y]-1)/8) - fl((9*r[y]-1)/8) for y in range(1, 7))
    def B2(r, X):
        zs = []
        for y in range(1, 7):
            j = 1
            while True:
                en, ex = F(8*j-1)/r[y], F(8*j+1)/r[y]
                if en >= X: break
                if 9 < ex <= X: zs.append((ex, en, y, j))
                j += 1
        zs.sort(); best = {}
        for k, (ex, en, y, j) in enumerate(zs):
            b = 1 if en < 9 < ex else 0
            for k2 in range(k):
                ex2, en2, y2, j2 = zs[k2]
                if ex2 < ex and en < ex2 and best[k2] > 0 and y2 != y: b = max(b, best[k2] + 1)
            best[k] = b
        return max(best.values()) if best else 0
    mx = collections.Counter(); viol = 0; sl1 = collections.Counter(); sl2 = collections.Counter(); sl12 = collections.Counter()
    maxB1 = maxB2 = maxB1_12 = maxB2_12 = 0; viol12 = 0
    for row in rows:
        r, R, n2 = row[1], row[4], len(row[6])
        b1, b2 = B1(r, R), B2(r, R)
        b1x, b2x = B1(r, F(12)), B2(r, F(12))
        if not (n2 <= b2 <= b1): viol += 1
        if not (n2 <= b2x <= b1x): viol12 += 1
        sl1[b1 - n2] += 1; sl2[b2 - n2] += 1; sl12[b2x - n2] += 1
        maxB1, maxB2, maxB1_12, maxB2_12 = max(maxB1, b1), max(maxB2, b2), max(maxB1_12, b1x), max(maxB2_12, b2x)
    P('-- %s phase-2 move count N2 vs per-arrangement bounds (exact): B1 = sum over ranks 2..7 of #zones with exit in (9,X]; B2 = longest chain of zones (exit increasing, next zone contains the previous exit, consecutive readings differ, first zone contains 9) with exits in (9,X]' % label)
    P('   X = landing R*: violations of N2 <= B2 <= B1: %d of %d; max B1 %d, max B2 %d, max N2 %d; slack B2-N2 distribution %s; slack B1-N2 %s' % (viol, len(rows), maxB1, maxB2, max(len(r[6]) for r in rows), sorted(sl2.items()), sorted(sl1.items())))
    P('   X = 12 (uses landing < 12, observed): violations %d; max B1 %d, max B2 %d; slack B2-N2 distribution %s' % (viol12, maxB1_12, maxB2_12, sorted(sl12.items())))
if __name__ == '__main__':
    out = open('ph2_task1_v1.out', 'w')
    P = lambda *a: print(*a, file=out, flush=True)
    t = pickle.load(open('terminals7_J1.pkl', 'rb'))
    mem1 = load('cell_members7_J1.pkl')
    rows1 = analyse(mem1, 'J=1 (rho_7<=9), all outcome regions', out)
    rows1T = [row for row in rows1 if t[row[0]][-1] == 'T']
    P('   of which members of leaf regions: %d; of stop regions: %d' % (len(rows1T), len(rows1) - len(rows1T)))
    determinacy(rows1, out, 'J=1 all regions')
    catalogue(rows1, out, 'J=1 all regions', tsv='ph2_words_J1_v1.tsv')
    bounds(rows1, out, 'J=1 all regions')
    # stabilisation by window of rho_7
    P('-- J=1 new phase-2 words by window of rho_7 (cumulative, ascending rho_7 windows of width 1; members sorted by window):')
    seen = set()
    for lo in range(1, 9):
        ws = set(row[6] for row in rows1 if lo < row[1][6] <= lo+1); new = ws - seen; seen |= ws
        P('   rho_7 in (%d,%d]: members %d; words %d; new words %d; cumulative %d' % (lo, lo+1, sum(1 for row in rows1 if lo < row[1][6] <= lo+1), len(ws), len(new), len(seen)))
    # J=2 leaf-only
    mem2 = load('cell_members_J2.pkl')
    rows2 = analyse(mem2, 'J=2 (rho_7<=17), LEAF REGIONS ONLY (cell_members_J2.pkl; the stop regions of J=2 are not on disk)', out)
    determinacy(rows2, out, 'J=2 leaf-only')
    catalogue(rows2, out, 'J=2 leaf-only', tsv='ph2_words_J2leaf_v1.tsv')
    bounds(rows2, out, 'J=2 leaf-only')
    W1 = set(row[6] for row in rows1); W1T = set(row[6] for row in rows1T); W2 = set(row[6] for row in rows2)
    P('-- word-set comparison: J=1 all %d, J=1 leaf-only %d, J=2 leaf-only %d; J=2 leaf words not among J=1 all-region words: %d; not among J=1 leaf-only words: %d; J=1 all words not among J=2 leaf words: %d' % (len(W1), len(W1T), len(W2), len(W2 - W1), len(W2 - W1T), len(W1 - W2)))
    seen = set(W1)
    P('-- J=2 leaf-only: words new relative to J=1 all-region words, by window of rho_7:')
    for lo in range(9, 17, 2):
        ws = set(row[6] for row in rows2 if lo < row[1][6] <= lo+2); new = ws - seen; seen |= ws
        P('   rho_7 in (%d,%d]: members %d; words %d; new %d; cumulative incl. J=1 %d' % (lo, lo+2, sum(1 for row in rows2 if lo < row[1][6] <= lo+2), len(ws), len(new), len(seen)))
    P('   (J=2 members with rho_7 <= 9: %d)' % sum(1 for row in rows2 if row[1][6] <= 9))
    out.close()
