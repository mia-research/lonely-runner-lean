# joinedge_census_v1.py -- census over joinedge_perbox_v1.jsonl for the SpineTotal one-sided lift.
#
# Reads the per-box dump and computes, per box and globally, the JoinFam-representability census
# under four cap/demand representation policies:
#   STRICT   : reduced demand (A, B) with A = 1,7 and B = 1,7 mod 8 (comb ratio form), cap C = 1,7
#              as stored, conflict A*C <= B*D  -- the banked spineFamData style (task criterion).
#   LEANMIN  : reduced demand with A = 1,7 mod 8 only (the letter of Fresh.FilterAssembly.JoinFam),
#              cap C = 1,7 as stored, conflict.
#   COMBUNRED: the UNREDUCED comb pair (P, Q) (the artifact's own raw word-edge form; P, Q are
#              8m+-1 comb/window numerators by construction), cap C = 1,7 as stored, conflict.
#   NUM      : unreduced comb demand, cap value odd (so some integer representation kC has
#              kC = 1 mod 8 -- Lean-consumable, but the numerator is no longer a comb tooth),
#              conflict.
# Residual classes beyond every policy:
#   derived-only deaths: the dying (edge, demand) has NO chain-side (J/box) conflict at all --
#     the kill is a word+box+J composed cycle (E813 item 7 / E814 item 4 product form needed);
#   even-numerator caps: the chain-side cap value's reduced numerator is even -- no integer
#     representation can carry an 8m+-1 numerator (hard composition-needed).
# Also verifies the [T 5/5] control annotations and the v6 regression flags.  Exact arithmetic.
import json, os
from fractions import Fraction as F
from collections import Counter, defaultdict

AUD = os.path.dirname(os.path.abspath(__file__))
PM1 = (1, 7)
def pm1(x): return x % 8 in PM1

recs = [json.loads(l) for l in open(os.path.join(AUD, 'joinedge_perbox_v1.jsonl'))]
one = [r for r in recs if r['role'] == 'one_sided']
ctrl = [r for r in recs if r['role'] == 'two_sided_control']

lines = []
def P(s=''):
    lines.append(s); print(s, flush=True)

P('joinedge_census_v1 -- census over joinedge_perbox_v1.jsonl (%d boxes: %d one-sided + %d two-sided controls)'
  % (len(recs), len(one), len(ctrl)))
P('')

# ---- 0. regression and control checks ----
v6ok = all(r['matches_v6_out'] for r in recs)
P('v6 regression: per-box deaths/completions match j2_cycle_v6.out on all %d boxes: %s [T %d/%d]'
  % (len(recs), v6ok, sum(1 for r in recs if r['matches_v6_out']), len(recs)))
ctrl_ok = []
for r in ctrl:
    t = r.get('twosided_v12', {})
    ok = t.get('control_ok', False)
    ctrl_ok.append(ok)
    P('control %s: banked rows found %s, counts match %s, lean form ok %s -> [T] %s'
      % (tuple(r['box']), t.get('banked_rows_found'), t.get('banked_counts_match'),
         all(z['joinfam_valid'] for z in t.get('lean_form', [])), 'PASS' if ok else 'FAIL'))
P('controls [T %d/%d]' % (sum(ctrl_ok), len(ctrl_ok)))
P('')

# ---- 1. structural check: every unreduced demand pair is comb-form ----
noncomb_dem = Counter()
tot_dem = 0
for r in one:
    for e in r['edges']:
        for d in e['demands']:
            tot_dem += 1
            if not (pm1(d['P']) and pm1(d['Q'])):
                noncomb_dem[(d['P'], d['Q'])] += 1
P('structural check: all %d per-box demand records have unreduced (P, Q) both 8m+-1 (comb/window form): %s'
  % (tot_dem, not noncomb_dem))
if noncomb_dem: P('  exceptions: %s' % dict(list(noncomb_dem.items())[:10]))
P('')

# ---- 2. per-box policies ----
def box_census(r):
    f = r['family']
    tot = f['deaths_total']
    per = {p: 0 for p in ('STRICT', 'LEANMIN', 'COMBUNRED', 'NUM')}
    der_only = f['uncovered_derived_only']
    even_cap = 0
    odd345 = 0
    for e in r['edges']:
        for d in e['demands']:
            A, B, PQok = d['A'], d['B'], pm1(d['P']) and pm1(d['Q'])
            strict_dem = pm1(A) and pm1(B)
            lean_dem = pm1(A)
            cands = d['chainside']
            conf = [c for c in cands if c['conflict']]
            best = None
            for c in conf:
                # strictness priority: pm1-as-stored > odd > even
                cls = 0 if pm1(c['C']) else (1 if c['C'] % 2 == 1 else 2)
                if best is None or cls < best[0]: best = (cls, c)
            if best is None:
                continue  # derived-only (counted in der_only)
            cls, c = best
            if cls == 2: even_cap += d['deaths']
            elif cls == 1: odd345 += d['deaths']
            if cls == 0:
                if strict_dem: per['STRICT'] += d['deaths']
                if lean_dem: per['LEANMIN'] += d['deaths']
                if PQok: per['COMBUNRED'] += d['deaths']
            if cls <= 1:
                # NUM policy: the cap value is odd, so kC = 1 mod 8 has a solution -- the datum
                # (kC, kD) represents the same bound and passes JoinFam's congruence
                per['NUM'] += d['deaths']
    return tot, per, der_only, even_cap, odd345

P('=== per-box census (68 one-sided boxes) ===')
P('%-22s %9s %7s %7s %7s %7s %9s %9s %9s' % ('box', 'deaths', 'STRICT', 'LEANMIN', 'COMBUNR', 'NUM', 'der-only', 'even-cap', 'odd3/5'))
agg = {p: 0 for p in ('STRICT', 'LEANMIN', 'COMBUNRED', 'NUM')}
tot_all = der_all = even_all = odd_all = 0
ready = {p: [] for p in ('STRICT', 'LEANMIN', 'COMBUNRED', 'NUM')}
for r in one:
    tot, per, der_only, even_cap, odd345 = box_census(r)
    tot_all += tot; der_all += der_only; even_all += even_cap; odd_all += odd345
    for p in agg: agg[p] += per[p]
    if der_only == 0 and even_cap == 0:
        if odd345 == 0:
            for p in ('STRICT', 'LEANMIN', 'COMBUNRED'): ready[p].append(tuple(r['box']))
        ready['NUM'].append(tuple(r['box']))
    P('%-22s %9d %7d %7d %7d %7d %9d %9d %9d' %
      (str(tuple(r['box'])), tot, per['STRICT'], per['LEANMIN'], per['COMBUNRED'], per['NUM'],
       der_only, even_cap, odd345))
P('')
P('=== totals over the 68 one-sided boxes ===')
P('deaths total                 : %d' % tot_all)
P('covered STRICT (comb ratio, cap 8m+-1 as stored) : %d (%.3f)' % (agg['STRICT'], agg['STRICT'] / tot_all))
P('covered LEANMIN (A 8m+-1, cap 8m+-1 as stored)   : %d (%.3f)' % (agg['LEANMIN'], agg['LEANMIN'] / tot_all))
P('covered COMBUNRED (unreduced comb demand)        : %d (%.3f)' % (agg['COMBUNRED'], agg['COMBUNRED'] / tot_all))
P('covered NUM (cap odd, rescalable to 8m+-1)       : %d (%.3f)' % (agg['NUM'], agg['NUM'] / tot_all))
P('residual derived-only (no chain-side conflict)   : %d (%.3f)' % (der_all, der_all / tot_all))
P('residual even-numerator chain-side caps          : %d (%.3f)' % (even_all, even_all / tot_all))
P('residual odd 3/5-mod-8 caps (rescalable, not teeth): %d (%.3f)' % (odd_all, odd_all / tot_all))
P('')
for p in ready:
    P('boxes fully covered under %s (and no derived-only/even-cap residual): %d %s' % (p, len(ready[p]), ready[p] if len(ready[p]) <= 20 else ''))
P('')

# ---- 3. the non-8m+-1 inventories ----
capcl = Counter(); demcl = Counter(); even_caps = Counter(); odd35_caps = set(); nonpm1_dem = Counter()
for r in one:
    for b in r['jside_bounds']:
        v = F(b[2]); C = v.numerator
        capcl['pm1' if pm1(C) else ('odd' if C % 2 else 'even')] += 1
        if C % 2 and not pm1(C): odd35_caps.add(b[2])
        if not C % 2: even_caps[b[2]] += 1
    for e in r['edges']:
        for d in e['demands']:
            if not (pm1(d['A']) and pm1(d['B'])):
                demcl['reduced_noncomb'] += 1
                nonpm1_dem['%d/%d' % (d['P'], d['Q'])] += 1
            else: demcl['reduced_comb'] += 1
P('=== inventories over the 68 boxes ===')
P('J-side bounds by reduced-numerator class: %s' % dict(capcl))
P('odd 3/5-mod-8 J caps (rescalable, non-tooth numerators), distinct: %d, e.g. %s' %
  (len(odd35_caps), sorted(odd35_caps)[:8]))
P('even-numerator J caps (never 8m+-1 representable), distinct: %d, e.g. %s' %
  (len(even_caps), sorted(even_caps, key=lambda z: -even_caps[z])[:8]))
P('demand records by reduced form: %s' % dict(demcl))
P('demands whose REDUCED form breaks the comb ratio (unreduced pair is comb-form), distinct: %d, e.g. %s' %
  (len(nonpm1_dem), sorted(nonpm1_dem, key=lambda z: -nonpm1_dem[z])[:10]))
P('')

# ---- 4. verdict (data-driven) ----
P('=== verdict ===')
for p in ('STRICT', 'LEANMIN', 'COMBUNRED', 'NUM'):
    P('fully-covered boxes under %-9s: %d of 68%s' % (p, len(ready[p]), (' ' + str(ready[p])) if 0 < len(ready[p]) <= 15 else ''))
if not ready['STRICT']:
    P('The one-sided SpineTotal lift consumes NO box as-is under the strict comb-ratio datum:')
    P('every one of the 68 boxes has deaths needing either (a) composed caps (derived-only kills:')
    P('%d deaths with NO chain-side conflict, E813 item 7 / E814 item 4 product form) or' % der_all)
    P('(b) a chain-side cap value that cannot carry an 8m+-1 numerator as stored (%d even-numerator' % even_all)
    P('deaths, never representable; %d odd-3/5-mod-8 deaths, rescalable but non-tooth numerators).' % odd_all)
P('representation relaxation ladder: STRICT %d -> LEANMIN %d -> COMBUNRED %d -> NUM %d (of 68 boxes fully covered)'
  % (len(ready['STRICT']), len(ready['LEANMIN']), len(ready['COMBUNRED']), len(ready['NUM'])))

with open(os.path.join(AUD, 'joinedge_census_v1.out'), 'w') as f:
    f.write('\n'.join(lines) + '\n')
print('written joinedge_census_v1.out', flush=True)
