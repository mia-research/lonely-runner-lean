# tmpl_collect_v1 -- templates + gate flag for a slice of a member list.  usage: tmpl_collect_v1.py SRC start end
# SRC in J1, J2 (cell_members7_J1/J2.pkl, items (region index, readings)), seeds (stress_seeds_v1.pkl keys)
# Exact: gate flag from in_zone7 on the windows (Lemma 2); every gate crosser re-checked with outcome()['R']>7;
# every 50th non-crosser re-checked with outcome()['R']<=7.  Records: crossers keep readings; non-crossers keep (idx, template id, rho_7).
import sys, pickle, time, signal
exec(open('tmpl_lib_v1.py').read())
src, s0, s1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
t0 = time.time(); signal.alarm(560)
if src == 'seeds': data = [(i, k) for i, k in enumerate(pickle.load(open('stress_seeds_v1.pkl', 'rb')))]
else: data = [(it[0], tuple(it[1])) for it in pickle.load(open('cell_members7_%s.pkl' % src, 'rb'))]
tids = {}; tlist = []; cross = []; non = []; bad = []; nchk = 0; nchk_non = 0
for n in range(s0, min(s1, len(data))):
    idx, rh = data[n]
    T, W = template(rh); g = gate(rh, W)
    if T not in tids: tids[T] = len(tlist); tlist.append(T)
    if g:
        R = outcome(list(rh))['R']; nchk += 1
        if not R > 7: bad.append((n, 'gate but landing<=7'))
        cross.append((n, rh, tids[T]))
    else:
        if n % 50 == 0:
            R = outcome(list(rh))['R']; nchk_non += 1
            if R > 7: bad.append((n, 'no gate but landing>7'))
        non.append((n, tids[T], rh[6]))
pickle.dump(dict(src=src, s0=s0, s1=min(s1, len(data)), tlist=tlist, cross=cross, non=non, bad=bad), open('tmpl_rec_%s_%d_v1.pkl' % (src, s0), 'wb'))
print(src, s0, min(s1, len(data)), 'members', min(s1, len(data)) - s0, 'crossers', len(cross), 'noncross', len(non), 'templates', len(tlist),
      'outcome-checked crossers', nchk, 'non-crossers', nchk_non, 'violations', len(bad), 'sec', round(time.time() - t0))
