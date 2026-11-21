# m4rung2_batch1_select.py -- batch-1 box selection for the M4 certificate-transcription
# scaling run: the banked residual boxes (Fresh.MechDataBatch.m4res_<box>) whose DFS
# verdict is fire=true (kind closed) in BOTH checkpoint artifacts, ranked by certificate
# TREE SIZE (node count) ascending, skipping the six already-transcribed boxes
# (rung 1: 1,4,6,7,10,16,16; batch 0: the five smallest).  Prints the next K with node
# counts, plus the tail of done ones for calibration.  python3 -I.
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
MECH = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh',
                                     'MechDataBatch.lean'))

DONE = {(1, 4, 6, 7, 10, 16, 16),   # rung 1
        (1, 1, 4, 5, 7, 9, 11), (1, 2, 2, 4, 5, 7, 9), (1, 2, 2, 4, 6, 7, 10),
        (1, 2, 2, 4, 6, 7, 9), (1, 2, 3, 6, 8, 10, 15)}   # batch 0


def main():
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 25
    src = open(MECH).read()
    banked = []
    for m in re.finditer(r'^def m4res_((?:\d+_){6}\d+) : M4Res :=', src, re.M):
        banked.append(tuple(int(x) for x in m.group(1).split('_')))
    ck2 = {}
    for l in open(os.path.join(HERE, 'm4comp_cert_ckpt_v1.jsonl')):
        r = json.loads(l)
        ck2[tuple(r['t'])] = r
    ck1 = set()
    for l in open(os.path.join(HERE, 'j2_admit_cert2_checkpoint.jsonl')):
        r = json.loads(l)
        if r.get('fire') is True:
            ck1.add(tuple(r['t']))
    elig = []
    for b in banked:
        t = b[1:]
        r = ck2.get(t)
        if r is None or tuple(r['t']) not in ck1 or r.get('fire') is not True:
            continue
        elig.append((r['nodes'], r['leaves'], r['maxdepth'], b))
    elig.sort()
    print('banked=%d eligible(fire+both ckpts)=%d' % (len(banked), len(elig)))
    done_rows = [(n, l, d, b) for (n, l, d, b) in elig if b in DONE]
    print('done boxes present among eligible: %d/6 -> %s' % (
        len(done_rows), [(b, n) for (n, l, d, b) in done_rows]))
    sel = [(n, l, d, b) for (n, l, d, b) in elig if b not in DONE][:k]
    print('== batch 1 selection (next %d by tree size ascending) ==' % len(sel))
    for i, (n, l, d, b) in enumerate(sel):
        print('%2d. (%d,%d,%d,%d,%d,%d,%d)  nodes=%d leaves=%d maxdepth=%d' % (
            (i + 1), *b, n, l, d))
    with open(os.path.join(HERE, 'm4rung2_batch1_selection.json'), 'w') as f:
        json.dump(dict(selection=[list(b) for (n, l, d, b) in sel],
                       nodes=[n for (n, l, d, b) in sel]), f, indent=1)


if __name__ == '__main__':
    main()
