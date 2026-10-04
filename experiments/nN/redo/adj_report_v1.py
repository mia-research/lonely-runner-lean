# adj_report_v1 -- tables from adj_state_MODE_v1.pkl (exact re-checks of everything stated as a fact)
import pickle, sys
from collections import Counter, defaultdict
exec(open('adj_lib_v1.py').read())
from ceil_lib_v1 import maxrho, tight
mode = sys.argv[1]; BOX = 25 if mode == 'box' else None
S = pickle.load(open('adj_state_%s_v1.pkl' % mode, 'rb'))
T115 = pickle.load(open('adj_t115_v1.pkl', 'rb'))
seen = S['seen']; ex = {sg: r for sg, r in seen.items() if r is not None}
okc = {sg: r for sg, r in ex.items() if r['status'] == 'ok'}
print('=== A. counts (mode %s)' % mode)
print('gate-crossing fine cells reached (distinct exact signatures):', len(seen))
print('  expanded:', len(ex), ' status ok:', len(okc), ' not ok:', len(ex) - len(okc), ' frontier (reached, not expanded):', len(S['queue']))
print('  expanded cells by codimension of the cell (0 = full-dimensional):', dict(Counter(r['codim'] for r in okc.values())))
print('  start cells (121 reps incl. duplicates by cell):', len(S['startsig']), 'distinct cells', len(set(s for l, s in S['startsig'])))
print('  facet centre signature checks (centre re-evaluated with path/cell_rows, same signature):', S['checks'], 'failures', S['checkfail'])
print('  self-loops (facet crossing returns same signature):', S['selfloops'], ' order-row crossings landing in a crosser:', len(S['order_cross']), ' box-wall facets:', S['boxwall'])
print('  unresolved facets (thin/exactfail/unstable):', len(S['unresolved']), Counter(u[2] for u in S['unresolved']))
print('  edges recorded:', len(S['edges']), ' to crossers:', sum(1 for e in S['edges'] if e[2] is not None), ' crossing-losing:', sum(1 for e in S['edges'] if e[2] is None))
print('  hull (off-hull) single-equality crossings from lower-dimensional cells:', dict(S['hull']))
print('  moves per cell (expanded):', sorted(Counter(r['nmoves'] for r in okc.values()).items()))
strata = {sg: v for sg, v in S['strata'].items() if sg not in seen}
print('  facet points (on a facet, exact) that are gate crossers of a different, unexpanded cell:', len(strata))
print('=== B. templates')
ts = S['tmplseen']; src = Counter(); srcout = Counter()
for T, (tag, x) in ts.items(): src[tag[0]] += 1
print('distinct K6 templates among evaluated crosser points:', len(ts), ' of the 115:', sum(1 for T in ts if T in T115), ' outside:', len(ts) - sum(1 for T in ts if T in T115), ' of the 115 not met:', len(T115 - set(ts)))
print('  first-source tags of templates seen:', dict(src))
print('  outside list (exact re-check: outcome landing, gate by windows, R2 contains rho_7, tie flag):')
for tag, x, T, R, r7 in S['outside']:
    o = outcome(list(x)); W = windows(x); g = gate(x, W); r2, unb = r2_set(x)
    in_r2 = any(lo < x[6] < hi for lo, hi in (r2 or []))
    sg = tag[1]; cd = seen[sg].get('codim') if seen.get(sg) else None
    tie = any(p for l, r, p in T) or any(len(l) > 1 or (len(r) > 1 and not (len(r) == 2 and ('R7',) in r)) for l, r, p in T)
    print('   ', tag[0], 'cell codim', cd, '| template', tstr(T), '| landing', R, '= %.6f' % float(R), '| outcome R>7', o['R'] > 7, '| gate', g, '| rho_7 in R2', in_r2, '| rho_7 = %.6f' % float(x[6]), '| tie/zero-width window:', tie)
    print('       exact arrangement:', [str(v) for v in x])
print('=== C. attained / limit values of rho_2..rho_7 over reached cells')
cells_all = list(okc.items())
for k in range(2, 8):
    cand = sorted(cells_all, key=lambda kv: -(kv[1]['fmax'][k] or 0))[:4]
    best = None
    for sg, r in cand:
        x = r['entry']; rows, tags, steps, R = cell_of(norm(list(x)), BOX)
        res = maxrho(rows, k)
        if res is None: print('  rho%d: exact certificate failed for cell %s' % (k, sg[:8])); continue
        X, lam = res; val = X[k - 1]
        if best is None or val > best[0]: best = (val, sg, X, lam, rows, r)
    val, sg, X, lam, rows, r = best
    vx = norm(list(X)); okv, stv, Rv = crosses2(vx)
    c = r['center']; delta = F(1, 2 ** 30)
    q = [X[0]] + [X[m] + delta * (c[m] - X[m]) for m in range(1, 7)]
    okq, stq, Rq = crosses2(q); sq = sig_of(q, BOX)[0]
    print('  rho%d: max of closure over reached expanded cells = %s = %.9f (exact LP, Farkas certified); the vertex arrangement is itself a gate crosser: %s;' % (k, val, float(val), okv))
    print('        exact arrangement in that cell with rho_%d = %s (= %.9f, below the limit by %s): gate %s, same signature %s' % (k, q[k - 1], float(q[k - 1]), val - q[k - 1], okq, sq == sg))
    if k == 7: print('        arrangement:', [str(v) for v in q]); print('        vertex:', [str(v) for v in X])
    print('        evaluated exact crosser points (centres + entry points of all reached cells): largest rho_%d = %.9f' % (k, max(float(r2['center'][k - 1]) for r2 in okc.values())))
print('=== D. crossing-losing facet crossings by causing row')
tot = Counter(); los = Counter(); toc = Counter()
for e in S['edges']:
    tot[e[3]] += 1
    if e[2] is None: los[e[3]] += 1
    else: toc[e[3]] += 1
print('  by row kind (facet crossings recorded): kind | all | stays a crosser | loses the crossing')
for k in sorted(tot): print('   ', k, '|', tot[k], '|', toc[k], '|', los[k])
byk = Counter(); ex_ = {}
for (cls, key), n in S['loss'].items(): byk[(cls, key)] += n
print('  distinct causing rows (hyperplanes):', len(byk), ' total losing crossings', sum(byk.values()))
print('  top 40 causing rows (count | kind | row a.rho >= 0 | meaning in the first cell met):')
for (cls, key), n in byk.most_common(40):
    e = S['lossexamples'][(cls, key)]
    ks = key if cls != 'hull' else key[1]
    print('   ', n, '|', cls, '|', eq_string(ks) if cls != 'hull' else 'hull', '|', e[1])
pickle.dump(dict(byk=byk), open('adj_loss_%s_v1.pkl' % mode, 'wb'))
print('=== D2. causing rows decoded as zone-endpoint coincidences from the UNNORMALISED row of the first cell where each occurs: a row has coefficient 8L+1 (exit of lap L) or 8L-1 (entry of lap L) on one reading; the zone endpoint of reading u has numerator |coefficient of the other reading|')
def endp(m):
    if m % 8 == 1: return ('exit', (m - 1) // 8)
    if m % 8 == 7: return ('entry', (m + 1) // 8)
    return ('?', m)
def decode_raw(a):
    nz = [(i, v) for i, v in enumerate(a) if v != 0]
    if len(nz) != 2: return None
    (u, cu), (v, cv) = nz
    eu = endp(abs(cv)); ev = endp(abs(cu))
    return ('%s(%d,%d)' % (eu[0], u + 1, eu[1]), '%s(%d,%d)' % (ev[0], v + 1, ev[1]), eu[0], ev[0])
types = Counter(); typ_rows = defaultdict(Counter); nodec = 0; cache = {}
for (cls, key), n in byk.items():
    if cls == 'hull': continue
    sg = S['lossexamples'][(cls, key)][0]
    if sg not in cache:
        rows, tags, steps, R = cell_of(norm(list(seen[sg]['entry'])), BOX); cache[sg] = (rows, groups_of(rows))
    rows, Dg = cache[sg]
    ds = set()
    if key in Dg:
        for i in Dg[key]:
            d = decode_raw(rows[i])
            if d is not None: ds.add(d)
    else:
        d = decode_raw(key)           # key reduced modulo a lower-dimensional cell's hull: decode the reduced row itself
        if d is not None: ds.add(d)
    if not ds: nodec += n; continue
    ds = sorted(ds); d = ds[0]
    t = '='.join(sorted([d[2], d[3]])); types[t] += n; typ_rows[t][(d[0], d[1], len(ds))] += n
print('  losing crossings by coincidence type (first decode of the group):', dict(types), ' undecoded:', nodec)
for t in typ_rows:
    print('  %s : %d distinct coincidences; top 30 (count, coincidence, number of distinct state-level decodes of the same hyperplane):' % (t, len(typ_rows[t])))
    for (a, b, nd), n in typ_rows[t].most_common(30): print('     %5d  %s = %s   [%d]' % (n, a, b, nd))
