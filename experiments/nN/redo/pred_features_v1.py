# (d) features of long paths, and (a)-(c) checks re-run on the 20,000-arrangement survey.
import pickle, sys
from collections import Counter, defaultdict
from statistics import mean
exec(open('pred_step_rules_v1.py').read().split('\nif __name__ ==')[0])
tot, allf, allex = pickle.load(open('pred_step_rules_v1.pkl', 'rb'))
rows = pickle.load(open('outcome_survey_v2.pkl', 'rb'))
S = Counter(); sf = []
for r in rows:
    xs = norm([F(x) for x in r['rho']])
    c, e, ft = analyze(xs); S.update(c); ft['fam'] = 'survey:' + r['fam']; ft['rho'] = tuple(xs); sf.append(ft)
print("SURVEY 20,000 arrangements: steps", S['steps'])
VIOL = ['A1_viol','A1b_viol','A2_viol','A2c_viol','A2d_viol','pair_viol','fail_char_viol','LR_viol','link_viol_slower','link_viol_faster','returned_lap_viol','lap_decrease_viol','ratio_test_viol','setter_still_blocks_viol','markov_viol','landing_viol','closure_zone_viol','closure_reading_viol','closure_over']
for k in VIOL: print("  %-28s %d" % (k, S[k]))
for k in ['lowest_rank_agrees','lowest_rank_fails','A2_ties','link_new_slower','link_new_faster','link_slower_lap_same','link_slower_lap_lower','returned','carried','closure_readings','readings_in_closure_not_blocker','readings_not_in_closure','blocker_readings','setter_readings']: print("  %-28s %d" % (k, S[k]))
print("  survey moves:", sorted((int(k.split('=')[1]), v) for k, v in S.items() if k.startswith('moves=')))
print("\nMAIN 50,000 sample, moves distribution:", sorted((int(k.split('=')[1]), v) for k, v in tot.items() if k.startswith('moves=')))
def stats(fs, label):
    if not fs: print("  %-28s (none)" % label); return
    print("  %-28s N=%6d strip0 %.2f nstrip %.2f first_strip %.2f distinct %.2f repeats %.2f maxlap %.1f Rend/R0 %.1f" % (label, len(fs), mean(f['strip0'] for f in fs), mean(f['nstrip'] for f in fs), mean(f['first_strip'] for f in fs), mean(f['distinct'] for f in fs), mean(f['repeats'] for f in fs), mean(f['maxlap'] for f in fs), mean(float(f['Rend'] / f['R0']) for f in fs)))
for name, fs0 in (("MAIN", allf), ("SURVEY", sf)):
    print("\n== (d) features,", name)
    fams = sorted(set(f['fam'] for f in fs0))
    for fam in fams:
        fs = [f for f in fs0 if f['fam'] == fam]
        print(" family", fam, " moves dist", sorted(Counter(min(f['n'], 8) for f in fs).items()))
        stats([f for f in fs if f['n'] >= 6], "  >=6 moves"); stats([f for f in fs if 3 <= f['n'] <= 5], "  3-5 moves"); stats([f for f in fs if 1 <= f['n'] <= 2], "  1-2 moves")
    L = [f for f in fs0 if f['n'] >= 6]
    print(" ALL >=6 moves: N=%d" % len(L))
    print("  distinct setters:", sorted(Counter(f['distinct'] for f in L).items()))
    print("  repeats (moves - distinct setters):", sorted(Counter(f['repeats'] for f in L).items()))
    print("  strip0 (blockers at R0):", sorted(Counter(f['strip0'] for f in L).items()))
    print("  first_strip readings in (7,9):", sorted(Counter(f['first_strip'] for f in L).items()))
    print("  nstrip (readings in any strip):", sorted(Counter(f['nstrip'] for f in L).items()))
    up = dn = same = 0; lapup = Counter()
    for f in L:
        for a, b in zip(f['setters'], f['setters'][1:]):
            if b > a: up += 1
            elif b < a: dn += 1
            else: same += 1
    print("  consecutive setters: faster %d, slower %d, same reading %d" % (up, dn, same))
    print("  rank of setters over all steps of >=6-move paths:", sorted(Counter(x for f in L for x in f['setters']).items()))
    print("  lap of setters (cap 12):", sorted(Counter(min(x, 12) for f in L for x in f['laps']).items()))
    nL = [f for f in fs0 if f['n'] < 6]
    print("  rank of setters over all steps of <6-move paths:", sorted(Counter(x for f in nL for x in f['setters']).items()))
    # long-path prevalence by nstrip
    byn = defaultdict(lambda: [0, 0])
    for f in fs0: byn[f['nstrip']][0] += 1; byn[f['nstrip']][1] += f['n'] >= 6
    print("  P(>=6 moves | nstrip):", {k: "%d/%d" % (v[1], v[0]) for k, v in sorted(byn.items())})
    byd = defaultdict(lambda: [0, 0])
    for f in fs0: byd[f['first_strip']][0] += 1; byd[f['first_strip']][1] += f['n'] >= 6
    print("  P(>=6 moves | #readings in (7,9)):", {k: "%d/%d" % (v[1], v[0]) for k, v in sorted(byd.items())})
    # moves vs strip0 : max moves ever with strip0 = 1 ?
    bys = defaultdict(Counter)
    for f in fs0: bys[f['strip0']][min(f['n'], 8)] += 1
    print("  moves by strip0 (blockers at R0):", {k: sorted(v.items()) for k, v in sorted(bys.items())})
    # zero strip => zero moves
    print("  strip0 == 0 and n > 0:", sum(1 for f in fs0 if f['strip0'] == 0 and f['n'] > 0), "; nstrip == 0 and n > 0:", sum(1 for f in fs0 if f['nstrip'] == 0 and f['n'] > 0), "; nstrip>0 and n == 0:", sum(1 for f in fs0 if f['nstrip'] > 0 and f['n'] == 0))
# inert readings by rank, on the main sample (never setter, never blocker)
inert_s = Counter(); inert_b = Counter(); tot_r = 0
for f in allf + sf:
    xs = [F(x) for x in f['rho']]; steps, _ = path(xs)
    st = set(s['setter'] for s in steps); bl = set(y for s in steps for y in s['blockers'])
    for y in range(7):
        tot_r += 1
        if y not in st: inert_s[y + 1] += 1
        if y not in bl: inert_b[y + 1] += 1
print("\ninert (never setter) by rank:", sorted(inert_s.items()), " readings per rank:", tot_r // 7)
print("inert (never blocker) by rank:", sorted(inert_b.items()))
