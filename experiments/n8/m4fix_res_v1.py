# m4fix_res_v1 -- construct M4Res records for C3-killed boxes from the m4comp checkpoint.
# The C3 boxes lack banked m4res_<box> records (E923's named gap). The m4comp checkpoint
# carries the full tree data (nodes, leaves, maxdepth, kind, fire, nstart, last_zones).
# This script constructs the m4res records from that data, enabling the mass-run driver
# to process C3 boxes through the existing recon->generate->compile pipeline.
import json, os, sys

HERE = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8'
CKPT = os.path.join(HERE, 'm4comp_uclosure_ckpt_v2.jsonl')
J2CKPT = os.path.join(HERE, 'j2_admit_cert2_checkpoint.jsonl')
OUT = os.path.join(HERE, 'm4fix_res_v1.jsonl')

def main():
    # the C3-killed boxes from the uclosure checkpoint
    c3_boxes = {}
    for line in open(CKPT):
        d = json.loads(line)
        if d.get('key') == 'aA' and d.get('killed'):
            t = tuple(d['t'])
            box = (1,) + t
            c3_boxes[box] = d
    print(f'C3-killed boxes: {len(c3_boxes)}')

    # cross-reference with the j2 M4 checkpoint (which has the DFS certifier's tree data)
    j2_data = {}
    for line in open(J2CKPT):
        d = json.loads(line)
        t = tuple(d['t'])
        box = (1,) + t
        if box in c3_boxes:
            j2_data[box] = d
    print(f'C3 boxes in j2 M4 checkpoint: {len(j2_data)}')

    # construct the m4res records
    records = []
    for box, c3d in sorted(c3_boxes.items()):
        j2 = j2_data.get(box)
        if j2 is None: continue
        rec = {
            'box': list(box),
            't': list(c3d['t']),
            'key': c3d['key'],
            'killed': c3d['killed'],
            'nstates': c3d['nstates'],
            'ceil': str(c3d.get('ceil', '')),
            # from the j2 M4 checkpoint (the DFS certifier's data):
            'nodes': j2['nodes'],
            'leaves': j2['leaves'],
            'maxdepth': j2['maxdepth'],
            'fire': j2['fire'],
            'kind': j2['kind'],
            'nstart': j2['nstart'],
            'reach_leaves': j2.get('reach_leaves', 0),
            'deadend_leaves': j2.get('deadend_leaves', 0),
            'start_infeas': j2.get('start_infeas', 0),
            'lf_min': str(j2.get('lf_min', '')),
            'lf_max': str(j2.get('lf_max', '')),
            'lf_med': str(j2.get('lf_med', '')),
            'last_zones': j2.get('last_zones', []),
        }
        records.append(rec)

    with open(OUT, 'w') as f:
        for rec in records:
            f.write(json.dumps(rec) + '\n')
    print(f'wrote {len(records)} m4res records -> {OUT}')
    
    # summary
    nodes = sorted(r['nodes'] for r in records)
    reach = sum(r['reach_leaves'] for r in records)
    deadend = sum(r['deadend_leaves'] for r in records)
    print(f'tree size: nodes {nodes[0]}-{nodes[-1]}, total reach leaves: {reach}, total deadend: {deadend}')
    zero_reach = sum(1 for r in records if r['reach_leaves'] == 0)
    print(f'boxes with 0 reach leaves (no OWED(b)): {zero_reach}/{len(records)}')

if __name__ == '__main__':
    main()
