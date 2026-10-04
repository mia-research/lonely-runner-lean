# adj_bfs_v1 -- breadth-first search over fine cells of gate crossers.  usage: adj_bfs_v1.py MODE SECONDS [MAXCELLS]
# MODE = unb (no bound on rho_7) or box (rows: rho_7 <= 25 rho_1 added to every cell).  State in adj_state_MODE_v1.pkl (resumable).
import sys, os, pickle, time
from collections import Counter, deque
exec(open('adj_lib_v1.py').read())
MODE = sys.argv[1]; SECS = float(sys.argv[2]); MAXC = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
BOX = 25 if MODE == 'box' else None
SF = 'adj_state_%s_v1.pkl' % MODE
T115 = pickle.load(open('adj_t115_v1.pkl', 'rb'))
T0 = time.time(); DEAD = T0 + SECS
if os.path.exists(SF):
    S = pickle.load(open(SF, 'rb'))
else:
    S = dict(seen={}, queue=deque(), loss=Counter(), lossexamples={}, facetclass=Counter(), unresolved=[], degenerate=[], tmplseen={}, outside=[],
             edges=[], strata={}, hull=Counter(), hullpairs=[], selfloops=0, start=[], checks=0, checkfail=0, order_cross=[], boxwall=0, expanded=0, elapsed=0.0, runs=0, startsig=[])
    reps = pickle.load(open('adj_reps_v1.pkl' if MODE in ('unb', 'box') else 'adj_start_%s_v1.pkl' % MODE, 'rb'))
    for lab, rh, ts in reps:
        x = norm(list(rh))
        if BOX is not None and x[6] > BOX: continue
        ok, st, R = crosses2(x); assert ok, lab
        sg = sig_of(x, BOX)[0]
        S['startsig'].append((lab, sg))
        if sg not in S['seen']:
            S['seen'][sg] = None; S['queue'].append((sg, x, lab))
S['runs'] += 1
def note_template(x, tag):
    T, W = template(x)
    if T not in S['tmplseen']:
        S['tmplseen'][T] = (tag, x)
        if T not in T115:
            ok, st, R = crosses2(x)
            S['outside'].append((tag, x, T, R, x[6]))
    return T
n_this = 0
while S['queue'] and time.time() < DEAD and n_this < MAXC:
    sg, x, lab = S['queue'].popleft(); n_this += 1
    o = expand(x, BOX, DEAD)
    S['expanded'] += 1
    rec = dict(status=o['status'], n_rows=o['n_rows'], n_dist=o['n_dist'], nmoves=o['nmoves'], R=o['R'], entry=x, lab=lab, tc=o.get('tc'))
    S['seen'][sg] = rec
    if o['status'] != 'ok':
        S['degenerate'].append((sg, x, o['status'], o.get('tc'))); continue
    c = o['center']; rec['center'] = c; rec['fmax'] = o['fmax']; rec['nfacets'] = len(o['facets']); rec['thin'] = o['thin']
    okc, stc, Rc = crosses2(c); assert okc
    if S['checks'] < 60 or S['expanded'] % 25 == 0:
        S['checks'] += 1
        if sig_of(c, BOX)[0] != sg: S['checkfail'] += 1
    rec['tmpl'] = {id_: 1 for id_ in ()}
    tset = set()
    tset.add(note_template(x, ('entry', sg))); tset.add(note_template(c, ('center', sg)))
    rec['ntmpl'] = len(tset)
    rec['tmplset'] = tset
    tags = o['tags']; rec['codim'] = o['codim']; rec['tc'] = o['tc']
    def visit(y, cls, key, extra=None):
        ok, st, R = crosses2(y)
        if not ok:
            why = 'noreading1move' if not any(s['setter'] == 0 for s in st) else 'landing<=7'
            S['loss'][(cls, key)] += 1
            S['lossexamples'].setdefault((cls, key), (sg, extra, y, why))
            S['edges'].append((sg, key, None, cls)); return
        sy = sig_of(y, BOX)[0]
        if cls == 'order': S['order_cross'].append((sg, sy))
        S['edges'].append((sg, key, sy, cls))
        tset.add(note_template(y, ('nbr', sg, key)))
        if sy == sg: S['selfloops'] += 1
        elif sy not in S['seen']:
            S['seen'][sy] = None; S['queue'].append((sy, y, 'from ' + sg[:6]))
    for f in o['facets']:
        cls = row_class(tags, f['idx']); S['facetclass'][cls] += 1
        if cls == 'box':
            S['boxwall'] += 1; continue
        if f['y'] is None:
            S['unresolved'].append((sg, f['key'], f['why'], f['t'], cls)); continue
        visit(f['y'], cls, f['key'], describe(tags, f['idx']))
        if cls != 'order':
            p = f['p']; okp, stp, Rp = crosses2(p)
            if okp:
                sp = sig_of(p, BOX)[0]
                if sp != sg and sp not in S['strata'] and sp not in S['seen']:
                    S['strata'][sp] = (p, sg, f['key'], len(stp), Rp)
                    note_template(p, ('facetpoint', sg, f['key']))
    for h in o['hullcross']:
        cls = 'hull'; key = ('hull', h['eq'][0], h['sgn'])
        S['hull'][h['sgn']] += 1
        if h['y'] is None: S['unresolved'].append((sg, key, 'hull-unstable', 0, cls)); continue
        visit(h['y'], cls, key, 'off-hull crossing of ' + str(h['eq'][0]))
    rec['ntmpl'] = len(tset)
    if n_this % 100 == 0:
        S['elapsed'] += time.time() - T0; T0 = time.time()
        pickle.dump(S, open(SF + '.tmp', 'wb')); os.replace(SF + '.tmp', SF)
S['elapsed'] += time.time() - T0
pickle.dump(S, open(SF + '.tmp', 'wb')); os.replace(SF + '.tmp', SF)
ex = [r for r in S['seen'].values() if r is not None]
print('MODE', MODE, 'run', S['runs'], 'expanded this run', n_this, 'total expanded', S['expanded'], 'cells seen', len(S['seen']), 'queue', len(S['queue']),
      'elapsed total %.0f s' % S['elapsed'])
print('degenerate/unexpanded', len(S['degenerate']), 'unresolved facets', len(S['unresolved']), 'selfloops', S['selfloops'], 'center-sig checks', S['checks'], 'fail', S['checkfail'])
print('templates seen', len(S['tmplseen']), 'outside 115:', len(S['outside']), 'losses', sum(S['loss'].values()), 'edges', len(S['edges']))
