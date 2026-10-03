# tmpl_r2_v1 -- R2 sets (exact) for every distinct crosser.  usage: tmpl_r2_v1.py START END   (index into the sorted distinct-crosser list)
# Per crosser: the exact open-interval set of rho_7 > rho_6 for which every window of K6 lies in one open zone of reading 7;
# checks: (i) member's own rho_7 lies in it (exact), (ii) midpoint of the top component and of the component containing rho_7 give outcome()['R']>7.
import sys, pickle, glob, time, signal
exec(open('tmpl_lib_v1.py').read())
signal.alarm(570); t0 = time.time()
cr = {}
for f in sorted(glob.glob('tmpl_rec_*_v1.pkl')):
    d = pickle.load(open(f, 'rb'))
    for n, rh, tid in d['cross']: cr.setdefault(rh, d['tlist'][tid])
X24 = (F(1),F(2752864293769,970238379379),F(3691147638604,961559468885),F(4851775667488,988103849833),F(5240560485773,830842598345),F(2806730537001,400961505286),F(474233610200591258564537783,19451412054102649094869700))
keys = sorted(set(cr) | {X24}, key=lambda r: (r[6], r))
a, b = int(sys.argv[1]), int(sys.argv[2]); out = []; bad = []
for rh in keys[a:b]:
    iv, unb = r2_set(list(rh))
    own = None if unb else [k for k, (lo, hi) in enumerate(iv) if lo < rh[6] < hi]
    if unb or not own: bad.append((rh, 'own rho_7 not in R2' if not unb else 'unbounded'))
    chk = []
    if not unb and iv:
        for k in sorted(set([len(iv) - 1] + (own or []))):
            m = (iv[k][0] + iv[k][1]) / 2
            chk.append(outcome(list(rh[:6]) + [m])['R'] > 7)
    if not all(chk): bad.append((rh, 'midpoint check failed'))
    out.append((rh, iv, unb, own))
pickle.dump(dict(a=a, b=min(b, len(keys)), n=len(keys), out=out, bad=bad), open('tmpl_r2_%d_v1.pkl' % a, 'wb'))
print('r2', a, min(b, len(keys)), 'of', len(keys), 'bad', len(bad), 'sec', round(time.time() - t0))
