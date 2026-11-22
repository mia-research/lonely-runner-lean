# widthpass_v1 -- the width-data pass over the 7,797 chamber classes:
# per class, width(A,B) vs 2/25 splits width-closed (Lean-bankable via colDead50_of_width
# immediately) from race-needed (the intersection lemma's shrunken scope). Exact Fractions.
# Also: the S = 50 pass (width >= 1/25 kills [50,inf)) for the column extension.
# Input: the chamber classes from the probe dump (v3_chamber_open_v2_sweep.jsonl, the
# deduped (skel, kL, kR, cellL, cellR, a, b) keys) + the datasheet atoms chds_k.
import json, sys
from fractions import Fraction as F

def main():
    dump = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/v3_chamber_open_v2_sweep.jsonl'
    classes = {}
    for line in open(dump):
        d = json.loads(line)
        if d.get('type') != 'open': continue
        c = d['case']
        key = (tuple(c['skel']), c['L'][1], c['R'][1], c['L'][0], c['R'][0], c['a'], c['b'])
        classes[key] = classes.get(key, 0) + 1
    print(f'classes: {len(classes)}')

    width_closed = []   # (key, width) with width >= 2/25
    race_needed = []    # (key, width) with width < 2/25
    ext50 = []          # width >= 1/25 (the [50,inf) extension classes)
    for key, cnt in classes.items():
        skel, kL, kR, cellL, cellR, astr, bstr = key
        a = F(astr); b = F(bstr)
        w = b - a
        if w >= F(2, 25):
            width_closed.append((key, w))
        elif w >= F(1, 25):
            ext50.append((key, w))
        else:
            race_needed.append((key, w))

    def stats(lst, label, thr):
        if not lst:
            print(f'{label}: 0 classes'); return
        widths = [w for (_, w) in lst]
        ws = sorted(widths)
        n = len(widths)
        print(f'{label}: {n} classes | width range [{ws[0]}, {ws[-1]}] | median {ws[n//2]} | total cases {sum(cnt for key, cnt in classes.items() if key in dict(lst))}')
    print()
    print(f'WIDTH-CLOSED (w >= 2/25, Lean-bankable via colDead50_of_width): {len(width_closed)} classes')
    print(f'  [50,inf) extension also applies (w >= 1/25): {sum(1 for _, w in width_closed)}')
    print(f'EXT-50 (1/25 <= w < 2/25, [50,inf)-only): {len(ext50)} classes')
    print(f'RACE-NEEDED (w < 1/25): {len(race_needed)} classes')
    if race_needed:
        rw = sorted(F(bstr) - F(astr) for (key, w) in
                    [(k, None) for k in race_needed] for k in [k] for (kk, cnt) in classes.items() if kk == k for w in [F(k[6]) - F(k[5])])
        rws = sorted(F(k[6]) - F(k[5]) for k in race_needed)
        print(f'  race-needed width range: [{rws[0]}, {rws[-1]}]')
    # per-skeleton breakdown of race-needed
    sk_race = {}
    for key in race_needed:
        sk = key[0]
        sk_race[sk] = sk_race.get(sk, 0) + 1
    print(f'race-needed by skeleton: {len(sk_race)} skeletons')

    json.dump(dict(width_closed=[[list(k[0]), k[1], k[2], k[3], k[4], k[5], k[6], str(w)] for (k, w) in width_closed],
                   ext50=[[list(k[0]), k[1], k[2], k[3], k[4], k[5], k[6], str(w)] for (k, w) in ext50],
                   race_needed=[[list(k[0]), k[1], k[2], k[3], k[4], k[5], k[6], str(w)] for (k, w) in race_needed]),
              open('/Users/trentpalelei/Desktop/Math Ex/experiments/n8/widthpass_v1.json', 'w'), indent=1)
    print('-> widthpass_v1.json')

if __name__ == '__main__':
    main()
