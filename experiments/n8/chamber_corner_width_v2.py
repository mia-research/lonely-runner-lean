# chamber_corner_width_v2 -- the corner-width pass over the STABILITY-WINDOW boxes.
# v1 (chamber_corner_width_v1) used the FULL skeleton letter cells and got 0/7797 -- the
# honest chamber box is chamber_test's stability window (v3_chamber_open_v2.chamber_test):
#   rL in [max(cellL_lo, (8kL-1)/a), min(cellL_hi, (8kL+1)/a)],
#   rR in [max(cellR_lo, (8kR-1)/b), min(cellR_hi, (8kR+1)/b)],
# the region where the tuple's certifying component IS (a_t, b_t) =
# ((8kL+1)/rL, (8kR-1)/rR) with the SAME boundary zones (no middle-zone intrusion is a
# further chamber condition -- the width fact here is the box-minimum of the interval
# width; membership of the interval as a component is the tuple-side hypothesis consumed
# by Fresh.WidthCover.tuple_dead_of_width_box).
# width is increasing in rL, decreasing in rR, so its box minimum is at the corner
# (rL_lo, rR_hi).  Corner fact per class: (8kR-1)/rR_hi - (8kL+1)/rL_lo >= 2/25
# (the [25,50) column death via Fresh.WidthCert.colDead_of_width), or >= 1/25 (the
# [50,inf) extension via colDead_of_width_50).
# Cells: the sub-cell instrument's tight windows (the letter cell bounds intersected with
# the zone-edge windows) -- cell letter from conjT3_enum_v1.cell_of, CELLBOUNDS as in v1.
# Exact Fractions.  Output: cornerwidth_v2.json + .out summary.
from fractions import Fraction as F
import json, sys

CELLBOUNDS = {'P': (F(1),F(7)), 'S1': (F(7),F(9)), 'G1': (F(9),F(15)), 'S2': (F(15),F(17)), 'E': (F(17),F(17))}
def cell_of(x):
    if x <= F(7): return 'P'
    if x < F(9): return 'S1'
    if x <= F(15): return 'G1'
    if x < F(17): return 'S2'
    return 'E'

def main():
    dump = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/v3_chamber_open_v2_sweep.jsonl'
    classes = {}
    for line in open(dump):
        d = json.loads(line)
        if d.get('type') != 'open': continue
        c = d['case']
        key = (tuple(c['skel']), c['L'][1], c['R'][1], cell_of(F(c['L'][0])),
               cell_of(F(c['R'][0])), c['a'], c['b'])
        classes[key] = classes.get(key, 0) + 1
    print('classes', len(classes))

    closed25 = closed50 = neither = degen = 0
    rows = []
    for key, cnt in classes.items():
        skel, kL, kR, cL, cR, astr, bstr = key
        a, b = F(astr), F(bstr)
        cL_lo, cL_hi = CELLBOUNDS[cL]; cR_lo, cR_hi = CELLBOUNDS[cR]
        rL_lo = max(cL_lo, F(8*kL-1)/a); rL_hi = min(cL_hi, F(8*kL+1)/a)
        rR_lo = max(cR_lo, F(8*kR-1)/b); rR_hi = min(cR_hi, F(8*kR+1)/b)
        if rL_lo > rL_hi or rR_lo > rR_hi:
            degen += 1; continue
        wmin = F(8*kR-1)/rR_hi - F(8*kL+1)/rL_lo   # corner (rL_lo, rR_hi): the box minimum
        wmax = F(8*kR-1)/rR_lo - F(8*kL+1)/rL_hi
        if wmin >= F(2,25): closed25 += 1
        elif wmin >= F(1,25): closed50 += 1
        else: neither += 1
        rows.append([list(skel), kL, kR, cL, cR, astr, bstr, str(wmin), str(wmax), cnt])
    rows.sort(key=lambda r: F(r[7]))
    print('window-corner width >= 2/25 (box closed on [25,50) via colDead_of_width):', closed25)
    print('window-corner width in [1/25, 2/25) ([50,inf) extension only):', closed50)
    print('window-corner width < 1/25:', neither)
    print('degenerate windows:', degen)
    ws = [F(r[7]) for r in rows]
    print('wmin range:', ws[0], '..', ws[-1])
    print('smallest 10 window-corner widths:')
    for r in rows[:10]:
        print('  ', r[:7], 'wmin', r[7], float(F(r[7])), 'cases', r[9])
    json.dump(dict(closed25=closed25, closed50=closed50, neither=neither, degen=degen,
                   rows=rows), open('cornerwidth_v2.json', 'w'))
    print('-> cornerwidth_v2.json')

if __name__ == '__main__':
    main()
