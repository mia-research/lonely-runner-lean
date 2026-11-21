# chambjoin_verify_v1.py -- data side of bridge gamma (the class-match / join emission):
# the THREE-WAY key verification (probe dump class keys <-> datasheet chds_k atoms <->
# emitted join instances) plus the per-class representative checks that back the emitted
# Lean instances:
#   (V1) probe dump results <-> chambds_instances_v1.json: multiset of class records
#        (skel, kL, kR, a, b, n_cases) matches, so the datasheet's chds_idx atom edges are
#        exactly the dump's class-key edges (and the idx order -- the dump's rows sorted by
#        -n_cases, stable -- is re-derived below and validated by the kind re-derivation).
#   (V2) the sweep JSONL (v3_chamber_open_v2_sweep.jsonl, streamed to the dump's cutoff
#        with the probe's complete-line rule) <-> the dump: per-key case counts match
#        exactly (re-derives the dedupe), key sets match.
#   (V3) per class, on the representative recorded case (first per key, mirroring the
#        dump's retention):
#        (a) rho is a nondecreasing 5-tuple and lies in the skeleton's closed cell-box
#            per position (the InBox assertion of the emitted InClass);
#        (b) the certifying readings are pinned: rho_L = (8kL+1)/a and rho_R = (8kR-1)/b
#            occur exactly in rho (the race-certificate L/R readings);
#        (c) the EXACT JOIN: (a, b) is a K6 component of rho -- the data-side verification
#            of the emitted `mem` decide (k6_components / feasible_set COPIED VERBATIM
#            from conjT3_enum_v1.py == v3_chamber_open_probe_v1_enum.py);
#        (d) the atom's semantic content: feasible_set(a, b, 25, 50) = [] (the component
#            is column-dead over [25,50) -- the datasheet's S2 atom);
#        (e) the S2 kind re-derivation at the FIXED (a,b) matches the datasheet's kind
#            (D1: 9a <= 7b; D2: (8J+1) <= 25b with J = largest nonempty band).
# Per-position cell_of vs skeleton cell is ALSO reported (boundary values 7/9/15/17 sit in
# the sweep grid of an adjacent cell, where cell_of names the neighbouring cell; the
# closed-box bounds are the honest InBox predicate and are checked exactly).
#
# Output (NEW files only; nothing existing is modified):
#   chambjoin_classes_v1.json  the emission manifest (per class: key fields, representative
#                              rho literals, cell-box bounds, checks, kind, verdict)
#   chambjoin_verify_v1.out    the verification log
# Run: python3 -I chambjoin_verify_v1.py
import json, sys, time
from fractions import Fraction as F
from collections import Counter

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
DUMPF = DIR + 'v3_chamber_open_probe_v1_dump.json'
JSONL = DIR + 'v3_chamber_open_v2_sweep.jsonl'
DSJSON = DIR + 'chambds_instances_v1.json'
OUTF = DIR + 'chambjoin_verify_v1.out'
MANIFEST = DIR + 'chambjoin_classes_v1.json'
sys.path.insert(0, DIR)

CELLBOUNDS = {'P': (F(1), F(7)), 'S1': (F(7), F(9)), 'G1': (F(9), F(15)),
              'S2': (F(15), F(17)), 'E': (F(17), F(17))}

def cell_of(x):                      # COPIED VERBATIM from conjT3_enum_v1.py
    if x <= F(7): return 'P'
    if x < F(9): return 'S1'
    if x <= F(15): return 'G1'
    if x < F(17): return 'S2'
    return 'E'

def k6_components(rho_small):        # COPIED VERBATIM from conjT3_enum_v1.py
    ivs = []
    for r in rho_small:
        for a, b, j in zones_of(r):
            a2, b2 = max(a, F(1)), min(b, F(7))
            if a2 < b2: ivs.append((a2, b2))
    ivs.sort(); merged = []
    for a, b in ivs:
        if merged and a <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], b)
        else: merged.append([a, b])
    comps, cur = [], F(1)
    for a, b in merged:
        if a > cur: comps.append((cur, a))
        cur = max(cur, b)
    if cur < F(7): comps.append((cur, F(7)))
    return comps

def feasible_set(a, b, rlo, rhi, jmax=1200):   # COPIED VERBATIM from conjT3_enum_v1.py
    ivs = []; j = 1
    while True:
        lo, hi = F(8*j-1, a), F(8*j+1, b)
        if lo >= rhi: break
        if hi > rlo and hi > lo: ivs.append((max(lo, rlo), min(hi, rhi)))
        j += 1
        if j > jmax: break
    ivs.sort(); merged = []
    for lo, hi in ivs:
        if lo >= hi: continue
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    return merged

from taillemma_lib_v1 import zones_of   # import-safe (definitions only; as in the enum)

def main():
    t0 = time.time()
    log = []
    def P(*a):
        s = ' '.join(str(x) for x in a)
        print(s, flush=True); log.append(s)

    # ---- inputs ----
    d = json.load(open(DUMPF))
    rows = d['results']
    cutoff = d['cutoff']['cutoff_lines']
    ds = json.load(open(DSJSON))
    ds_ins = ds['instances']
    P('# chambjoin_verify_v1 -- gamma class-match verification')
    P('# dump: %d classes | datasheet json: %d instances | cutoff lines: %d'
      % (len(rows), len(ds_ins), cutoff))

    # the datasheet json stores skel as a JOINED STRING (e.g. "PPG1G1S2"); the dump
    # stores a list of cells.  Split the string back into cells.
    def split_skel(s):
        out, i = [], 0
        while i < len(s):
            if s[i] in 'SG':
                out.append(s[i:i+2]); i += 2
            else:
                out.append(s[i]); i += 1
        return out

    # ---- V1: dump <-> datasheet (multiset of (skel, kL, kR, a, b, n_cases)) ----
    ds_recs = Counter((x['skel'], int(x['kL']), int(x['kR']), x['a'], x['b'],
                       x['n_cases']) for x in ds_ins)
    dump_recs = Counter((''.join(r['skel']), int(r['kL']), int(r['kR']), r['a'], r['b'],
                         r['n_cases']) for r in rows)
    v1_only_ds = ds_recs - dump_recs
    v1_only_dump = dump_recs - ds_recs
    P('# V1 dump<->datasheet: matched class records %d | datasheet-only %d | dump-only %d'
      % (sum(ds_recs.values()) - sum(v1_only_ds.values()),
         sum(v1_only_ds.values()), sum(v1_only_dump.values())))
    if v1_only_ds:
        P('# V1 MISMATCH datasheet-only (first 5):', list(v1_only_ds.items())[:5])
    if v1_only_dump:
        P('# V1 MISMATCH dump-only (first 5):', list(v1_only_dump.items())[:5])

    # ---- V2: stream the sweep JSONL to the dump cutoff; per-key counts + representatives --
    stream_counts = Counter()
    repr_case = {}
    n_lines = n_open = 0
    with open(JSONL) as f:
        for line in f:
            n_lines += 1
            if n_lines > cutoff: break
            if not line.endswith('}\n'): break   # partial trailing line (append-only file)
            try: dd = json.loads(line)
            except Exception: break
            if dd.get('type') != 'open': continue
            n_open += 1
            c = dd['case']
            key = (''.join(c['skel']), int(c['L'][1]), int(c['R'][1]),
                   cell_of(F(c['L'][0])), cell_of(F(c['R'][0])), c['a'], c['b'])
            stream_counts[key] += 1
            if key not in repr_case: repr_case[key] = c
    P('# V2 stream: lines consumed %d (cutoff %d) | open cases %d | distinct keys %d'
      % (min(n_lines, cutoff), cutoff, n_open, len(stream_counts)))
    # full-key check (skel, kL, kR, cL, cR, a, b) counts vs the dump's n_cases
    dump_key_counts = {( ''.join(r['skel']), int(r['kL']), int(r['kR']), r['cL'], r['cR'],
                         r['a'], r['b']): r['n_cases'] for r in rows}
    v2_bad = []
    n_count_ok = 0
    for r in rows:
        key = (''.join(r['skel']), int(r['kL']), int(r['kR']), r['cL'], r['cR'],
               r['a'], r['b'])
        sc = stream_counts.get(key)
        if sc is None:
            v2_bad.append((key, 'missing', r['n_cases']))
        elif sc != r['n_cases']:
            v2_bad.append((key, 'count', r['n_cases'], sc))
        else:
            n_count_ok += 1
    extra_keys = [k for k in stream_counts if k not in dump_key_counts]
    P('# V2 stream<->dump: per-key counts exact for %d/%d classes | bad %d | stream-only keys %d'
      % (n_count_ok, len(rows), len(v2_bad), len(extra_keys)))
    if v2_bad:
        P('# V2 MISMATCH examples:', v2_bad[:5])
    if extra_keys:
        P('# V2 stream-only key examples:', extra_keys[:5])

    # ---- V3: per-class representative checks (idx order = dump rows sorted by -n_cases,
    # stable -- the datasheet's idx assignment) ----
    manifest = []
    n_ok = Counter()
    v3_fail = []
    order = sorted(range(len(rows)), key=lambda i: (-rows[i]['n_cases'], i))
    for i, ri in enumerate(order):
        r = rows[ri]
        skel = r['skel']
        key = (''.join(skel), int(r['kL']), int(r['kR']), r['cL'], r['cR'],
               r['a'], r['b'])
        c = repr_case.get(key)
        ent = dict(idx=i, src=ri, skel=''.join(skel), kL=int(r['kL']), kR=int(r['kR']),
                   cL=r['cL'], cR=r['cR'], a=r['a'], b=r['b'],
                   n_cases=r['n_cases'], verdict=r['verdict'],
                   refined=str(r.get('refined', 'skipped')).split('(')[0])
        if c is None:
            ent['checks'] = 'NO-REPRESENTATIVE'
            v3_fail.append((key, 'no-repr'))
            manifest.append(ent); continue
        rho = [F(x) for x in c['rho']]
        a, b = F(r['a']), F(r['b'])
        kL, kR = int(r['kL']), int(r['kR'])
        ok_box = all(CELLBOUNDS[skel[j]][0] <= rho[j] <= CELLBOUNDS[skel[j]][1]
                     for j in range(5))
        ok_sorted = all(rho[j] <= rho[j+1] for j in range(4))
        cellpos = [cell_of(rho[j]) == skel[j] for j in range(5)]
        rhoL, rhoR = F(8*kL+1)/a, F(8*kR-1)/b
        ok_pinL = rhoL in rho
        ok_pinR = rhoR in rho
        comps = k6_components(rho)
        ok_join = (a, b) in comps
        fs = feasible_set(a, b, F(25), F(50))
        ok_dead = (len(fs) == 0)
        # S2 kind re-derivation (chambds_classes_v1.py formulas, verbatim arithmetic)
        if a == 1 or b == 7:
            kind_re = 'BOUNDARY'
        elif 9*a <= 7*b:
            kind_re = 'D1'
        else:
            j = 1; J = 0
            while F(8*j-1)*b < F(8*j+1)*a:
                J = j; j += 1
                if J > 200000: break
            kind_re = 'D2' if F(8*J+1) <= 25*b else 'OWED'
        ok_kind = (kind_re == ds_ins[i]['kind']) if i < len(ds_ins) else False
        ok_all = (ok_box and ok_sorted and ok_pinL and ok_pinR and ok_join
                  and ok_dead and ok_kind)
        ent['rho'] = [str(x) for x in rho]
        ent['boxLo'] = [str(CELLBOUNDS[cc][0]) for cc in skel]
        ent['boxHi'] = [str(CELLBOUNDS[cc][1]) for cc in skel]
        ent['kind'] = ds_ins[i]['kind'] if i < len(ds_ins) else kind_re
        ent['Jm'] = ds_ins[i].get('Jm', '') if i < len(ds_ins) else ''
        ent['checks'] = dict(box=ok_box, sorted=ok_sorted, join=ok_join, dead=ok_dead,
                             pinL=ok_pinL, pinR=ok_pinR, kind=ok_kind,
                             cellpos=sum(cellpos), a_is_start=(a == 1),
                             b_is_end=(b == 7))
        if ok_all: n_ok['all'] += 1
        if ok_box: n_ok['box'] += 1
        if ok_join: n_ok['join'] += 1
        if ok_dead: n_ok['dead'] += 1
        if ok_kind: n_ok['kind'] += 1
        if ok_pinL and ok_pinR: n_ok['pin'] += 1
        if not ok_all: v3_fail.append((key, ent['checks']))
        manifest.append(ent)
    P('# V3 representative checks over %d classes:' % len(manifest))
    P('#   closed cell-box per position (InBox):  %d/%d' % (n_ok['box'], len(manifest)))
    P('#   EXACT K6 join (a,b) in k6_components:  %d/%d' % (n_ok['join'], len(manifest)))
    P('#   component dead over [25,50) (atom):    %d/%d' % (n_ok['dead'], len(manifest)))
    P('#   L/R readings pinned by (a,b,kL,kR):    %d/%d' % (n_ok['pin'], len(manifest)))
    P('#   S2 kind re-derivation == datasheet:    %d/%d' % (n_ok['kind'], len(manifest)))
    P('#   ALL CHECKS PASS:                       %d/%d' % (n_ok['all'], len(manifest)))
    if v3_fail:
        P('# V3 FAILURES (first 10):')
        for ff in v3_fail[:10]:
            P('#   %s' % json.dumps(ff, default=str))
    # verdict x kind cross-tab on the manifest
    vt = Counter((m['verdict'], m.get('kind', '?')) for m in manifest)
    P('# manifest verdict x kind cross-tab:')
    for (v, k), n in sorted(vt.items()):
        P('#   %-18s %-13s %d' % (v, k, n))
    # representative tuple multiplicities: classes whose representative has repeated
    # readings (the emission's Fin 5 -> Q literal still fine; report honestly)
    n_dup = sum(1 for m in manifest if isinstance(m.get('rho'), list)
                and len(set(m['rho'])) < 5)
    P('# representatives with repeated readings: %d' % n_dup)

    json.dump(dict(n_classes=len(manifest), classes=manifest), open(MANIFEST, 'w'))
    P('# manifest: %s' % MANIFEST)
    P('# elapsed %.1fs' % (time.time() - t0))
    open(OUTF, 'w').write('\n'.join(log) + '\n')

if __name__ == '__main__':
    main()
