# m4fix_inventory.py -- Review-order item 4: parse m4comp_uclosure_ckpt_v2.jsonl and produce
# the field match/mismatch inventory vs Fresh.UClosureKill.Fixpoint's four fields
# (states / table / rank / aex) plus the seed and iteration count the C3 route needs.
# Read-only; writes m4fix_inventory.out.
import json, os, collections, itertools

HERE = os.path.dirname(os.path.abspath(__file__))
CKPT = os.path.join(HERE, 'm4comp_uclosure_ckpt_v2.jsonl')

fields = collections.Counter()
per_key = collections.Counter()
killed_aA = []          # (t, nstates, ceil) for killed aA boxes -- the 10,211
nstate_hist = collections.Counter()
maxline = 0; total_bytes = 0; nlines = 0

with open(CKPT) as f:
    for line in f:
        line = line.strip()
        if not line: continue
        nlines += 1; total_bytes += len(line) + 1
        maxline = max(maxline, len(line))
        d = json.loads(line)
        fields[tuple(sorted(d.keys()))] += 1
        per_key[(d['key'], d['killed'])] += 1
        if d['key'] == 'aA' and d['killed'] is True:
            killed_aA.append((tuple(d['t']), d['nstates'], d['ceil']))
            nstate_hist[d['nstates']] += 1

# smallest killed aA boxes: minimal nstates, then minimal box tuple
killed_aA.sort(key=lambda r: (r[1], sum(r[0]), r[0]))
smallest = killed_aA[:5]

out = []
out.append('=== m4fix_inventory: checkpoint v2 field census vs Fixpoint ===')
out.append('lines: %d   bytes: %d   max line: %d   avg line: %.1f' %
           (nlines, total_bytes, maxline, total_bytes / nlines))
out.append('')
out.append('field shapes (every line): %s' % dict(fields))
out.append('per (key, killed): %s' % {str(k): v for k, v in sorted(per_key.items())})
out.append('')
kaA = per_key[('aA', True)]
out.append('aA killed boxes: %d   (the C3 bank target count)' % kaA)
out.append('aA nstates histogram (killed): %s' %
           ' '.join('%d:%d' % (k, nstate_hist[k]) for k in sorted(nstate_hist)))
tot_states = sum(k * v for k, v in nstate_hist.items())
out.append('total states over killed aA boxes: %d   mean/box: %.2f' %
           (tot_states, tot_states / kaA))
out.append('')
out.append('5 smallest killed aA boxes (nstates, box):')
for t, ns, c in smallest:
    out.append('  t=%s nstates=%d ceil=%s' % (list(t), ns, c))
out.append('')
out.append("""--- match/mismatch table: checkpoint fields vs Fixpoint fields ---

Fixpoint field          checkpoint carries?   note
states : Finset(Fin6x15)  NO (count only)     checkpoint has nstates = len(st) at kill;
                                              the key SET (a, Aex) pairs is not recorded
table : key -> UTable     NO                  the per-key merged 7x7 (Fraction,bool|None)
                                              tables are not recorded at all
rank : key -> Fin 7       DERIVABLE           rank k = rowOf k.1 = k.1 + 1 (canonical);
                                              but needs the key set first
aex  : key -> Q           DERIVABLE           aex k = envB k.2 = B0 = key.2 exactly (the
                                              aA key stores Aex = B0 = key.2; max-merge
                                              over equal B0s), needs the key set first
seed (opening record)     NO                  the opening st dict (keys + Us tables + P1)
                                              before the fold is not recorded
iteration count T         NO                  the convergence round (<=600 loop) is not
                                              recorded; boxAdmit needs T >= 112
verdict killed            YES (bool)          the only per-box datum beyond the box tuple
ceil                      YES (string)        frontier ceiling, unused by Fixpoint
nstates                   YES (int)           |states| only, -1 when not killed
""")
out.append('VERDICT: the checkpoint is a verdict-summary format. A bank emission needs a')
out.append('re-dump of the generator with recording. Minimum fields to record per box:')
out.append('  1. final st: list of {a, Aex, U (7x7 of null|[num,str,bool]), P}')
out.append('  2. opening st (pre-fold seed record, same shape)')
out.append('  3. convergence round count T (and killed flag)')
out.append('See m4fix_recompute.py for the recording re-run on the smallest box.')

with open(os.path.join(HERE, 'm4fix_inventory.out'), 'w') as f:
    f.write('\n'.join(out) + '\n')
print('\n'.join(out))
