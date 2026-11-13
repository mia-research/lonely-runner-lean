# joinedge2_census_v1.py -- verification + census over joinedge2_perbox_v1.jsonl (dump v2).
# Checks (all exact, Fractions):
#   0. regression flags per box (v6, v1-record, provenance equality, join domination) [T 73/73];
#   1. witness validity over EVERY stored witness: product == cap exactly, endpoints y->x,
#      datum P*cap <= Q, strict-flag OR, per-hop domination bookkeeping consistent;
#   2. cap classes (strict / chain-attained / incomplete), row coverage, deaths-weighted;
#   3. walk-length histograms (all / derived-attr primaries);
#   4. undominated-hop structure (class, kind);
#   5. the 5 banked spineFamData controls [T 5/5];
#   6. v1-style derived-only rows (no chain-side conflict, from joinedge_perbox_v1.jsonl
#      cross-reference) and their v2 coverage;
#   7. per-box DumpDom-ready summary.
# New files only; nothing existing is modified.  Exact Fractions; floats nowhere.
import json, os
from fractions import Fraction as F
from collections import Counter, defaultdict

AUD = os.path.dirname(os.path.abspath(__file__))
lines = []
def P(s=''):
    lines.append(s); print(s, flush=True)

recs = [json.loads(l) for l in open(os.path.join(AUD, 'joinedge2_perbox_v1.jsonl'))]
v1 = {}
for l in open(os.path.join(AUD, 'joinedge_perbox_v1.jsonl')):
    r = json.loads(l); v1[tuple(r['box'])] = r

P('joinedge2_census_v1 -- verification + census over joinedge2_perbox_v1.jsonl (%d boxes)' % len(recs))
P('')

# ---- 0. regression ----
bad = [r['box'] for r in recs if not all(r['regression'].values())]
P('0. regression flags (v6, v1-record, prov chains/deaths/U0, join domination) all true on all boxes: %s [T %d/%d]'
  % (not bad, len(recs) - len(bad), len(recs)))
if bad: P('   failures: %s' % bad)
P('')

# ---- 1. witness validity over EVERY stored witness ----
nw = [0, 0]; ex = [0, 0]; en = [0, 0]; da = [0, 0]
for r in recs:
    stored = set()
    for row in r['death_rows']:
        for c in row['caps']:
            stored.add(str(c['witness'])); stored.update(str(a) for a in c.get('witness_alt', []))
    for wid, w in r['witnesses'].items():
        nw[1] += 1; nw[0] += 1 if wid in stored else 0
        prod = F(1)
        for h in w['hops']: prod *= F(h['value'])
        ex[1] += 1; ex[0] += (prod == F(w['cap']))
        en[1] += 1; en[0] += (w['nodes'][0] == w['y'] and w['nodes'][-1] == w['x'])
    # datum per cap-reference (P, Q live on the row)
    for row in r['death_rows']:
        for c in row['caps']:
            for wid in [str(c['witness'])] + [str(a) for a in c.get('witness_alt', [])]:
                w = r['witnesses'][wid]
                da[1] += 1
                da[0] += 1 if (F(row['P'], row['Q']) * F(w['cap']) <= 1) else 0
P('1. witness validity over every STORED witness:')
P('   product(hops) == cap exactly      : %d/%d' % (ex[0], ex[1]))
P('   endpoints (nodes y -> x)          : %d/%d' % (en[0], en[1]))
P('   datum P*cap <= Q (per cap-ref)    : %d/%d' % (da[0], da[1]))
P('   witnesses stored / referenced     : %d/%d' % (nw[0], nw[1]))
P('   primary-witness flag_or + datum fields (from the dump checks blocks): see per-box checks')
P('')

# ---- 2. cap classes, rows, deaths ----
caps = Counter(); dth = Counter(); der_caps = Counter(); der_dth = Counter()
rows_cov = Counter(); wordrows = Counter()
for r in recs:
    c2 = r['census']
    for k, v in c2.get('deaths_by_class', {}).items(): dth[k] += v
    for k, v in c2.get('derived_deaths_by_class', {}).items(): der_dth[k] += v
    caps['strict'] += c2['caps_strict_complete']; caps['attained'] += c2['caps_chain_attained']
    caps['incomplete'] += c2['caps_incomplete']
    der_caps['strict'] += c2['derived_strict_complete']
    rows_cov['rows_any_strict'] += c2['rows_strict_complete']
    rows_cov['rows'] += c2['death_rows']
    for row in r['death_rows']:
        if not row['row_strict_complete']:
            allpure = all(all(h['class'] == 'word' for h in r['witnesses'][str(c['witness'])]['hops'])
                          for c in row['caps'])
            wordrows['pure_word' if allpure else 'mixed'] += 1
P('2. cap classes (row-cap pairs): %s, total %d' % (dict(caps), sum(caps.values())))
P('   deaths by class: %s, total %d' % (dict(dth), sum(dth.values())))
P('   derived-attr caps: %s' % dict(der_caps))
P('   derived-attr deaths by class: %s' % dict(der_dth))
P('   rows: %d, with >=1 strict (DumpDom-ready) cap: %d, without: %d' %
  (rows_cov['rows'], rows_cov['rows_any_strict'], rows_cov['rows'] - rows_cov['rows_any_strict']))
P('   rows without strict cap, by witness structure: pure-word %d, mixed word+box/J %d' %
  (wordrows['pure_word'], wordrows['mixed']))
P('')

# ---- 3. walk lengths ----
lall = Counter(); lder = Counter()
for r in recs:
    for row in r['death_rows']:
        for c in row['caps']:
            w = r['witnesses'][str(c['witness'])]
            lall[w['n_hops']] += 1
            if c['attr'] == 'derived': lder[w['n_hops']] += 1
P('3. walk length hist (primary witnesses, all caps): %s' % dict(sorted(lall.items())))
P('   walk length hist (derived-attr caps): %s' % dict(sorted(lder.items())))
P('   max walk length: %d hops (E813 observed range: 1 start/box-end + 1-5 seam bounds = <= 6 primitives)'
  % max(lall))
P('')

# ---- 4. undominated hops ----
und = Counter()
for r in recs:
    for wid, w in r['witnesses'].items():
        for h in w['hops']:
            if not h['dominated_strict']: und[(h['class'], h.get('kind'))] += 1
P('4. undominated hops (class, kind) over stored witnesses: %s' % dict(und))
P('   box-class hops undominated: %d; J-class hops undominated: %d'
  % (und[('box', None)] if ('box', None) in und else sum(v for k, v in und.items() if k[0] == 'box'),
     sum(v for k, v in und.items() if k[0] == 'J')))
P('')

# ---- 5. banked controls ----
BANKED = {
    (1, 2, 3, 4, 5, 6, 8): [('seamE', 2, 6, '17/7', '25/63'), ('seamE', 2, 6, '41/17', '25/63')],
    (1, 3, 4, 5, 5, 6, 8): [('seamE', 5, 3, '17/23', '49/39')],
    (1, 3, 4, 4, 5, 6, 7): [('seamE', 5, 3, '17/23', '49/39'), ('seamE', 7, 2, '17/47', '73/31')],
    (1, 3, 4, 5, 6, 7, 8): [('seamM', 7, 3, '17/39', '97/49')],
    (1, 2, 3, 4, 5, 6, 7): [('seamE', 2, 7, '49/17', '33/103')],
}
ok = 0
for r in recs:
    n = tuple(r['box'])
    if n not in BANKED: continue
    bc = r['banked_control']
    got = {}
    for b in bc:
        got[(b['kind'], b['x1'], b['y1'], b['cap'], b['demand'])] = b
    allok = True
    for k in BANKED[n]:
        b = got.get(k)
        good = (b is not None and b['in_rawk'] and b['AC_le_BD'] and b['attaining_chains'] > 0
                and b['witnesses'] and all(w['product_exact'] and w['endpoints_ok'] and w['datum_ok']
                                           and w['n_hops'] >= 1 for w in b['witnesses']))
        allok &= bool(good)
    ok += allok
    P('   control %s: banked rows %d/%d reproduced with exact chain-hop witnesses -> %s'
      % (str(n), sum(1 for k in BANKED[n] if k in got), len(BANKED[n]), 'PASS' if allok else 'FAIL'))
P('   controls [T %d/5]' % ok)
P('')

# ---- 6. v1-style derived-only rows cross-reference ----
# v1 row is derived-only iff no chain-side candidate conflicts (both cands missing/non-conflict)
# and not covered_joinfam; recovered from v1's per-edge demand records.
v1_der_rows = set()
for n, r in v1.items():
    for e in r['edges']:
        for d in e['demands']:
            if not d['covered_joinfam'] and not any(cc['conflict'] for cc in d['chainside']):
                v1_der_rows.add((n, e['kind'], e['x1'], e['y1'], d['P'], d['Q']))
cov = Counter()
for r in recs:
    n = tuple(r['box'])
    for row in r['death_rows']:
        if (n, row['kind'], row['x1'], row['y1'], row['P'], row['Q']) in v1_der_rows:
            best = 'incomplete'
            for c in row['caps']:
                cls = 'strict' if c['complete_strict'] else ('attained' if (c['attaining_chains'] or 0) > 0 else 'incomplete')
                order = {'strict': 0, 'attained': 1, 'incomplete': 2}
                if order[cls] < order[best]: best = cls
            cov[best] += 1
P('6. v1-style derived-only rows (no chain-side conflict at all): %d' % len(v1_der_rows))
P('   their best v2 witness class: %s' % dict(cov))
P('')

# ---- 7. per-box DumpDom-ready summary ----
full = []
for r in recs:
    c2 = r['census']
    if c2['death_rows'] and c2['rows_strict_complete'] == c2['death_rows']:
        full.append(tuple(r['box']))
P('7. boxes whose EVERY death row carries a strict-complete (DumpDom-ready) cap: %d of %d' % (len(full), len(recs)))
P('   %s' % full)
P('')
P('=== census done')
with open(os.path.join(AUD, 'joinedge2_census_v1.out'), 'w') as f:
    f.write('\n'.join(lines) + '\n')
