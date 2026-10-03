# tmpl_analyse_v1 -- catalogue of K6 templates of gate crossers (exact); reads tmpl_rec_*_v1.pkl and tmpl_r2_*_v1.pkl
import pickle, glob, random, sys, signal
from collections import Counter, defaultdict
exec(open('tmpl_lib_v1.py').read())
signal.alarm(560)
def dec(x, k=5):
    x = F(x); n = x.numerator * 10**k // x.denominator; return '%d.%0*d' % (n // 10**k, k, n % 10**k)
seedsrc = {k: v[0] for k, v in pickle.load(open('stress_seeds_v1.pkl', 'rb')).items()}
X24 = (F(1),F(2752864293769,970238379379),F(3691147638604,961559468885),F(4851775667488,988103849833),F(5240560485773,830842598345),F(2806730537001,400961505286),F(474233610200591258564537783,19451412054102649094869700))
cr = {}            # readings -> (template, set of sources)
non = []           # (template, rho_7, source)
for f in sorted(glob.glob('tmpl_rec_*_v1.pkl')):
    d = pickle.load(open(f, 'rb')); tl = d['tlist']; s = d['src']
    for n, rh, tid in d['cross']:
        lab_ = (s if s != 'seeds' else 'seeds:' + seedsrc[rh])
        cr.setdefault(rh, [tl[tid], set()])[1].add(lab_)
    for n, tid, r7 in d['non']: non.append((tl[tid], r7, s))
T24, W24 = template(X24); assert gate(X24, W24)
cr.setdefault(X24, [T24, set()])[1].add('X24')
print('== 1. counts per source (distinct reading tuples that are gate crossers; gate = Lemma 2, every one re-checked with outcome()[R] > 7)')
srcs = Counter()
for rh, (T, ss) in cr.items():
    for s in ss: srcs[s] += 1
for s, c in sorted(srcs.items()): print('  ', s, c)
print('   distinct crosser reading tuples (union):', len(cr), '; overlapping several sources:', sum(1 for v in cr.values() if len(v[1]) > 1))
print('   member crossers (J1 + J2 member lists):', srcs['J1'], '+', srcs['J2'], '; non-crossers available:', len(non))
tc = Counter(v[0] for v in cr.values())
print('   DISTINCT crosser templates:', len(tc), '; templates with one reading tuple:', sum(1 for c in tc.values() if c == 1), '; max multiplicity', max(tc.values()))
print('   windows per crosser template (number of templates):', sorted(Counter(len(T) for T in tc).items()))
print('   windows per crosser reading tuple (number of tuples):', sorted(Counter(len(v[0]) for v in cr.values()).items()))
print('   templates with a one-point window:', sum(1 for T in tc if any(w[2] for w in T)), '; with a tied label (>1 label at an end):', sum(1 for T in tc if any(len(w[0]) > 1 or len(w[1]) > 1 for w in T)))
# per source
for s in sorted(srcs):
    ts = Counter(v[0] for v in cr.values() if s in v[1]); print('   source', s, 'tuples', srcs[s], 'distinct templates', len(ts))
print('   multiplicity distribution (multiplicity: number of templates):', sorted(Counter(tc.values()).items())[:25], '...')
print('   10 most frequent templates:')
for T, c in tc.most_common(10): print('     %6d  %s' % (c, tstr(T)))
print('\n== 2. finiteness test: first-seen templates')
order = sorted(cr, key=lambda r: (r[6], r))
seen = set(); cum = []; 
for i, rh in enumerate(order, 1):
    seen.add(cr[rh][0]); cum.append(len(seen))
print('  by increasing rho_7: after n crossers -> distinct templates:', [(n, cum[n - 1]) for n in (500, 1000, 2000, 4000, 6000, 8000, 10000, 12000, 14000, 16000, len(order))])
bands = [(7, 8), (8, 9), (9, 10), (10, 11), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17), (17, 100)]
seen = set(); print('  templates first seen, by rho_7 band (band: crossers in band, new templates):')
for lo, hi in bands:
    mem = [rh for rh in order if lo <= rh[6] < hi]; new = 0
    for rh in mem:
        if cr[rh][0] not in seen: seen.add(cr[rh][0]); new += 1
    print('     [%d,%d): crossers %d, new templates %d' % (lo, hi, len(mem), new))
print('  by source order J1 -> J2 -> seeds -> X24 (new templates):')
seen = set()
for s in ('J1', 'J2', 'seeds', 'X24'):
    mem = [v[0] for v in cr.values() if any(x == s or x.startswith(s) for x in v[1])]; ts = set(mem)
    print('     %s: tuples %d, templates %d, new relative to earlier %d, templates already seen %d' % (s, len(mem), len(ts), len(ts - seen), len(ts & seen))); seen |= ts
for sd in (1, 2, 3):
    rnd = random.Random(sd); o = list(cr); rnd.shuffle(o); seen = set(); c = {}
    for i, rh in enumerate(o, 1):
        seen.add(cr[rh][0]); c[i] = len(seen)
    N = len(o); print('  random order seed %d: distinct templates after n crossers:' % sd, [(n, c[n]) for n in (500, 1000, 2000, 4000, 8000, 12000, N - 1000, N)])
    print('     new templates in the last 1000 / 100 crossers of this order:', c[N] - c[N - 1000], '/', c[N] - c[N - 100])
# 2b. templates seen once but whose... leave-one-out: templates with a single tuple
print('  templates with exactly one reading tuple (a leave-one-out count: removing it loses a template):', sum(1 for c in tc.values() if c == 1))
print('\n== 2c. maxima over the crossers (distinct tuples)')
mx = [max(rh[k] for rh in cr) for k in range(1, 7)]
print('  max rho_2..rho_6:', [(k + 2, dec(m, 6)) for k, m in enumerate(mx)], '; max rho_7', dec(max(rh[6] for rh in cr), 6), '; min rho_7', dec(min(rh[6] for rh in cr), 6))
print('  min rho_2..rho_6:', [(k + 2, dec(min(rh[k] for rh in cr), 6)) for k in range(1, 6)])
Lx = Counter(); Le = Counter(); mj = [0, 0]
for T in tc:
    for L, Rr, p in T:
        for t in L:
            if t[0] == 'x': Lx[(t[1], t[2])] += 1; mj[0] = max(mj[0], t[2])
        for t in Rr:
            if t[0] == 'e': Le[(t[1], t[2])] += 1; mj[1] = max(mj[1], t[2])
print('  max lap j in an exit label:', mj[0], '; in an entry label:', mj[1])
print('  exit labels (rank, lap) -> templates containing:', sorted(Lx.items()))
print('  entry labels (rank, lap) -> templates containing:', sorted(Le.items()))
print('  max lap by rank, exits:', sorted({(y, max(j for (yy, j) in Lx if yy == y)) for (y, j) in Lx}), 'entries:', sorted({(y, max(j for (yy, j) in Le if yy == y)) for (y, j) in Le}))
# 3. R2
print('\n== 3. R2 sets')
r2 = {}; badall = []
for f in sorted(glob.glob('tmpl_r2_*_v1.pkl')):
    d = pickle.load(open(f, 'rb')); badall += d['bad']
    for rh, iv, unb, own in d['out']: r2[rh] = (iv, unb, own)
assert set(r2) == set(cr), (len(r2), len(cr))
print('  R2 computed for', len(r2), 'tuples; failures of the exact checks (own rho_7 in R2; path() on midpoints):', len(badall), '; unbounded:', sum(1 for v in r2.values() if v[1]))
sup = {rh: v[0][-1][1] for rh, v in r2.items()}
print('  R2 components per tuple (number of components: tuples):', sorted(Counter(len(v[0]) for v in r2.values()).items()))
print('  tuples whose own rho_7 is in the TOP component:', sum(1 for rh, v in r2.items() if v[2] and len(v[0]) - 1 in v[2]), 'of', len(r2))
print('  sup R2 (max rho_7 with the six readings fixed): overall max', dec(max(sup.values()), 8), 'at', max(sup, key=sup.get)[6] == X24[6] and 'X24' or 'other', '; overall min', dec(min(sup.values()), 6))
print('  gap sup - own rho_7: min', dec(min(sup[r] - r[6] for r in cr), 8), 'max', dec(max(sup[r] - r[6] for r in cr), 6))
byT = defaultdict(list)
for rh in cr: byT[cr[rh][0]].append(sup[rh])
print('  distribution of per-template maximum of sup R2 (integer band: number of templates):', sorted(Counter(int(max(v)) for v in byT.values()).items()))
print('  distribution of the per-tuple sup (integer band: tuples):', sorted(Counter(int(v) for v in sup.values()).items()))
sp = sorted(((max(v) - min(v), T) for T, v in byT.items() if len(v) >= 2), key=lambda x: -x[0])
print('  templates with >= 2 tuples:', len(sp), '; spread (max sup - min sup) within template: largest', [dec(s, 4) for s, _ in sp[:5]], 'median', dec(sp[len(sp) // 2][0], 4), 'smallest', dec(sp[-1][0], 6))
print('  within-template ranges, 12 most frequent templates (n, min sup, max sup):')
for T, c in tc.most_common(12): print('     %5d  [%s, %s]  %s' % (c, dec(min(byT[T]), 5), dec(max(byT[T]), 5), tstr(T)))
print('  templates whose members\' sup lie in different integer bands:', sum(1 for v in byT.values() if int(min(v)) != int(max(v))), 'of', len(byT))
# sup attained at: (window k, j) -> sup = (8j+1)/b ; b right end label
att = Counter(); attbig = Counter()
for rh, (iv, unb, own) in r2.items():
    T, W = template(list(rh)); hi = iv[-1][1]; found = None
    for k, (a, b) in enumerate(W):
        x = hi * b - 1
        if x.denominator == 1 and x.numerator % 8 == 0 and x.numerator > 0:
            found = (k, x.numerator // 8, T[k][1]); break
    if found is None: att['none'] += 1; continue
    k, j, rl = found; key = (lab(rl), j); att[key] += 1
    if rh[6] > F(164, 10): attbig[key] += 1
    # exact identity: hi == (8j+1)/b where b the right end of window k
print('  top upper end of R2 equals (8j+1)/b for window k with right-end label; (label, j): tuples', att.most_common(15), '; unidentified', att.get('none', 0))
print('  same, crossers with rho_7 > 16.4:', attbig.most_common(10))
# 4. extremes
print('\n== 4. largest and smallest crossers')
big = [rh for rh in order if rh[6] > F(164, 10)]
print('  crossers with rho_7 > 16.4:', len(big), '; distinct templates among them:', len({cr[r][0] for r in big}))
for T, c in Counter(cr[r][0] for r in big).most_common(12): print('     %5d  %s' % (c, tstr(T)))
print('  top 12 by rho_7:')
for rh in order[::-1][:12]: print('     rho_7=%s rho_6=%s rho_5=%s  sup=%s  %s  src=%s' % (dec(rh[6]), dec(rh[5]), dec(rh[4]), dec(sup[rh], 6), tstr(cr[rh][0]), sorted(cr[rh][1])))
print('  X24: rho_7', dec(X24[6], 8), 'template', tstr(T24), 'sup R2', dec(sup[X24], 10), 'R2 components', [(dec(a, 8), dec(b, 8)) for a, b in r2[X24][0]])
small = order[:12]
print('  12 smallest rho_7:')
for rh in small: print('     rho_7=%s rho_6=%s  sup=%s  %s' % (dec(rh[6], 6), dec(rh[5], 6), dec(sup[rh], 6), tstr(cr[rh][0])))
sm = [rh for rh in order if rh[6] < 8]
print('  crossers with rho_7 < 8:', len(sm), ', templates among them:', len({cr[r][0] for r in sm}))
def maxlap(T): return max([t[2] for L, Rr, p in T for t in L + Rr if t[0] in 'xe'] or [0])
def lapset(T): return sorted({(t[0], t[1], t[2]) for L, Rr, p in T for t in L + Rr if t[0] in 'xe'})
print('  (max lap in template, number of crossers) for rho_7 < 8 :', sorted(Counter(maxlap(cr[r][0]) for r in sm).items()))
print('  (max lap in template, number of crossers) for rho_7 > 16.4:', sorted(Counter(maxlap(cr[r][0]) for r in big).items()))
print('  (max lap, crossers) all:', sorted(Counter(maxlap(v[0]) for v in cr.values()).items()))
print('  windows count (n_6) for rho_7 < 8 :', sorted(Counter(len(cr[r][0]) for r in sm).items()), '; > 16.4:', sorted(Counter(len(cr[r][0]) for r in big).items()))
print('  (max lap in template, number of crossers) by rho_7 band:')
for lo, hi in bands:
    mem = [r for r in order if lo <= r[6] < hi]
    if mem: print('     [%d,%d): max-lap counts %s ; windows counts %s' % (lo, hi, sorted(Counter(maxlap(cr[r][0]) for r in mem).items()), sorted(Counter(len(cr[r][0]) for r in mem).items())))
print('  rank of the zone entry bounding the LAST window (label of right end of the last window), count of crossers, by rho_7 band:')
for lo, hi in bands:
    mem = [r for r in order if lo <= r[6] < hi]
    if mem: print('     [%d,%d): %s' % (lo, hi, Counter(lab(cr[r][0][-1][1]) for r in mem).most_common(6)))
print('  rank-and-lap of the zone exit bounding the left end of the LAST window:')
for lo, hi in bands:
    mem = [r for r in order if lo <= r[6] < hi]
    if mem: print('     [%d,%d): %s' % (lo, hi, Counter(lab(cr[r][0][-1][0]) for r in mem).most_common(6)))
# 5. non-crossers
print('\n== 5. crosser templates against non-crossers')
nt = Counter(T for T, r7, s in non)
print('  non-crosser members:', len(non), '; distinct templates:', len(nt))
print('  crosser templates also occurring among ALL non-crosser members:', len(set(tc) & set(nt)), '; crosser-only (not reached by the non-crosser members J1+J2):', len(set(tc) - set(nt)))
print('  tuples with a crosser-only template:', sum(c for T, c in tc.items() if T not in nt))
for sd in (20261004, 1, 2):
    rnd = random.Random(sd); samp = rnd.sample(non, len(cr)); st = Counter(T for T, r7, s in samp)
    print('  equal-size non-crosser sample (%d, seed %d): distinct templates %d; shared with crosser templates %d; crosser-only %d; sample-only %d' % (len(samp), sd, len(st), len(set(st) & set(tc)), len(set(tc) - set(st)), len(set(st) - set(tc))))
sh = sorted(set(tc) & set(nt), key=lambda T: -tc[T])[:8]
print('  shared templates, crosser tuples vs non-crosser members (top 8 by crosser multiplicity):')
for T in sh: print('     crossers %d, non-crossers %d  %s' % (tc[T], nt[T], tstr(T)))
co = sorted(set(tc) - set(nt), key=lambda T: -tc[T])[:8]
print('  crosser-only templates (top 8 by multiplicity):')
for T in co: print('     crossers %d  %s' % (tc[T], tstr(T)))
print('  non-crosser templates by number of windows (templates): ', sorted(Counter(len(T) for T in nt).items())[:14], '; maximum windows', max(len(T) for T in nt))
print('  crosser templates: max windows', max(len(T) for T in tc))
print('  non-crossers: fraction-free count with <=6 windows:', sum(1 for T, r7, s in non if len(T) <= 6), 'of', len(non), '; non-crosser templates with <= 6 windows', sum(1 for T in nt if len(T) <= 6))
pickle.dump(dict(tc=tc, nt=nt), open('tmpl_counts_v1.pkl', 'wb'))
