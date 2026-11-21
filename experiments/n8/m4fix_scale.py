# m4fix_scale.py -- Review-order item 4: the C3 fixpoint bank's scale projection.
# Anchors: the measured worked instance (1-state record, Fresh/M4FixBankC3.lean) and the
# checkpoint census (m4fix_inventory.out).  Writes m4fix_scale.out.
import json, os

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = '/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh/M4FixBankC3.lean'

src = open(LEAN).read()
nlines = src.count('\n')
nbytes = len(src)

# measured section boundaries: the per-box record block = from the tab def through the
# m4fixChildMem theorem (everything a per-box emission needs); the reusable part (header,
# bridges, unsat lemma, composition) is emitted ONCE for the whole bank.
tab_start = src.index('def m4fixTab_1_1_1_5_7_12')
mem_end = src.index('/-- The child key\'s table is trivial')
perbox_lines = src[tab_start:mem_end].count('\n')
perbox_bytes = mem_end - tab_start

ckpt = json.load(open(os.path.join(HERE, 'm4fix_recompute_1_1_1_5_7_12.json')))
work_states = len(ckpt['final'])

nstates_hist = {1: 249, 2: 409, 3: 470, 4: 482, 5: 643, 6: 663, 7: 678, 8: 600, 9: 508,
                10: 397, 11: 362, 12: 324, 13: 350, 14: 292, 15: 322, 16: 290, 17: 299,
                18: 267, 19: 240, 20: 278, 21: 207, 22: 189, 23: 216, 24: 183, 25: 160,
                26: 143, 27: 91, 28: 105, 29: 85, 30: 74, 31: 77, 32: 71, 33: 49, 34: 52,
                35: 53, 36: 47, 37: 31, 38: 50, 39: 44, 40: 25, 41: 18, 42: 25, 43: 23,
                44: 13, 45: 13, 46: 10, 47: 11, 48: 5, 49: 3, 50: 2, 51: 5, 52: 2, 53: 4,
                58: 2}
tot_boxes = sum(nstates_hist.values())          # 10,211
tot_states = sum(k * v for k, v in nstates_hist.items())
mean_states = tot_states / tot_boxes

# per-box scaling: fixed scaffold (~30 lines: record def, canon, projection haves) +
# per-state (7 table rows + ~2 cell-haves + ~8 bridge/proof lines ~ 17 lines, ~700 bytes)
scaffold_lines, per_state_lines = 30, 17
scaffold_bytes, per_state_bytes = 1200, 700

est_lines = [scaffold_lines + n * per_state_lines for n in nstates_hist]
est_bytes = [scaffold_bytes + n * per_state_bytes for n in nstates_hist]
tot_est_lines = sum(c * l for c, l in zip(nstates_hist.values(), est_lines))
tot_est_bytes = sum(c * b for c, b in zip(nstates_hist.values(), est_bytes))
mean_lines = tot_est_lines / tot_boxes
mean_bytes = tot_est_bytes / tot_boxes

BATCH = 500  # boxes per batch file (MechDataBatch pattern)
batch_lines = mean_lines * BATCH

out = []
out.append('=== m4fix_scale: the C3 fixpoint bank\'s scale projection ===')
out.append('')
out.append('measured anchors')
out.append('  worked instance file Fresh/M4FixBankC3.lean: %d lines, %d bytes' % (nlines, nbytes))
out.append('    per-box record block (tab..ChildMem) at nstates=1: %d lines, %d bytes'
           % (perbox_lines, perbox_bytes))
out.append('    compile (fresh, import of Mathlib+UClosureKill included): 6.2 s wall, 4.7 s user')
out.append('  checkpoint census: %d killed aA boxes, %d states total, mean %.2f states/box'
           % (tot_boxes, tot_states, mean_states))
out.append('  recompute-with-recording dump (1 state, full JSON): 6,386 bytes')
out.append('')
out.append('per-box emission model (fixed scaffold %d lines/%d B + %d lines/%d B per state)'
           % (scaffold_lines, scaffold_bytes, per_state_lines, per_state_bytes))
out.append('  mean per box: %.0f lines, %.1f KB   (worked box measured: %d lines, %.1f KB)'
           % (mean_lines, mean_bytes / 1024, perbox_lines, perbox_bytes / 1024))
out.append('')
out.append('bank totals over the 10,211 C3-killed boxes')
out.append('  lines: %d   bytes: %.1f MB' % (tot_est_lines, tot_est_bytes / 1e6))
out.append('  (bracket: [%d, %d] lines for per-state 12-22 lines)'
           % (round(tot_est_lines * 12 / per_state_lines), round(tot_est_lines * 22 / per_state_lines)))
out.append('')
out.append('batching plan (MechDataBatch emission pattern, one file per %d boxes)' % BATCH)
out.append('  %d batch files, each ~%.0f K lines (~%.1f MB)' %
           ((tot_boxes + BATCH - 1) // BATCH, batch_lines / 1e3, batch_lines * mean_bytes / mean_lines / 1e6))
out.append('  per-batch compile: the ~5 s fixed import cost + record elaboration; the')
out.append('  per-record marginal cost is the m4fixData evaluation (uExitOK x states with')
out.append('  the decide-bridges) -- the 1-state worked instance compiles in 6.2 s total,')
out.append('  so the per-record elaboration is well under a second at this size; the')
out.append('  dominant bank cost is elaborating ~%.0f M lines of literals, estimated' % (tot_est_lines / 1e6))
out.append('  1-4 h wall across %d batch files (parallelizable per batch, sequential per' % ((tot_boxes + BATCH - 1) // BATCH))
out.append('  the task\'s sequential-compile rule).')
out.append('')
out.append('BLOCKER (see Fresh/M4FixBankC3.lean header): the bank cannot reach')
out.append('M4BoxNoCarvePinned through boxAdmit_of_kill as stated -- c3fix_unsat proves the')
out.append('hypothesis tuple (hcanon, hopen, hseedfine, hclose) empty for every seed and T.')
out.append('A recording re-dump of m4comp_uclosure_sweep_v2.py/merged_kill must add:')
out.append('  1. the final st (per key: a, Aex, U as 7x7 null|[num,str,bool], P),')
out.append('  2. the opening record (pre-fold seed),')
out.append('  3. the convergence round count,')
out.append('AND UClosureKill.lean needs the three named repairs (in-box hseedfine,')
out.append('first-birth child tables, per-box seed + T presentation) before the emission')

with open(os.path.join(HERE, 'm4fix_scale.out'), 'w') as f:
    f.write('\n'.join(out) + '\n')
print('\n'.join(out))
