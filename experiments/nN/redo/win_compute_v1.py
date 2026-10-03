# usage: win_compute_v1.py DATASET [start end]   DATASET in J1, taxo, lat1, lat3, lat5, lat7
# writes win_rec_<DATASET>_<start>_v1.pkl : list of (label, readings, windows) ; and .out with exact-check tallies
import sys, pickle, random, itertools, time
exec(open('win_lib_v1.py').read())
ds = sys.argv[1]; s = int(sys.argv[2]) if len(sys.argv) > 2 else 0; e = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
items = []
if ds == 'J1':
    for idx, rh in pickle.load(open('cell_members7_J1.pkl', 'rb')): items.append((('J1', idx), rh))
elif ds == 'taxo':
    for k, t in enumerate(pickle.load(open('taxo_sample_v1.pkl', 'rb'))): items.append((('taxo', t[0], k), t[1]))
else:
    m = int(ds[3:]); rnd = random.Random(7000 + m)
    if m == 1:
        for c in itertools.combinations(range(2, 17), 6): items.append((('lat1', c), [F(1)] + [F(x) for x in c]))
    elif m == 3:
        for c in itertools.combinations(range(4, 22), 6): items.append((('lat3', c), [F(1)] + [F(x, 3) for x in c]))
    else:
        seen = set()
        while len(seen) < 4000:
            c = tuple(sorted(rnd.sample(range(m + 1, 9 * m + 1), 6)))
            if c not in seen: seen.add(c)
        for c in sorted(seen): items.append((('lat%d' % m, c), [F(1)] + [F(x, m) for x in c]))
items = items[s:e]
rec = []; bad = Counter(); t0 = time.time()
for lab, rh in items:
    rh = norm(rh); L = 23
    ws = windows(rh, L)
    if not verify(rh, ws, L): bad['verify'] += 1
    steps, R = path(rh)
    if not ws or ws[0][0] != R: bad['firstR'] += 1
    if lab[0] != 'taxo' and ds in ('J1',):
        o = outcome(rh)
        if o['R'] != R or ws[0][1] - ws[0][0] != o['width']: bad['outcome_width'] += 1
    if ds.startswith('lat'):
        m = int(ds[3:]); Lm = 8 * m - 1
        wm = windows(rh, Lm)
        if not verify(rh, wm, Lm): bad['verify_m'] += 1
        sym = sorted((8 * m - hi, 8 * m - lo) for lo, hi in wm)
        if sym != wm: bad['symmetry'] += 1
        rec.append((lab, rh, ws, wm))
    else: rec.append((lab, rh, ws))
pickle.dump(rec, open('win_rec_%s_%d_v1.pkl' % (ds, s), 'wb'))
print(ds, s, e, 'members', len(rec), 'failures', dict(bad), 'sec', round(time.time() - t0))
