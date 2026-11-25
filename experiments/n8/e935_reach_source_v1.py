"""e935_reach_source_v1 -- E925 item 6: why m4fix_res_v1.jsonl says reach_leaves = 0 for all 10,211
C3 boxes while m4comp_cert_ckpt_v1.jsonl says > 0 for 9,765.  Checks, exactly:
 (a) which fields the j2 checkpoint (m4fix_res_v1.py's source) records at all;
 (b) in m4comp_cert_ckpt_v1.jsonl, per C3 box: leaves == reach + deadend + start_infeas, and nodes==1 boxes
     by leaf kind (a 1-node forest is one dfs call; if that call prunes, it IS a reach leaf);
 (c) for every compiled C3 Lean box (Fresh/M4FixRung2_<box>.lean), the count of prune-leaf (DfsPruneDomZone)
     hypotheses/instances against ckpt2's reach_leaves."""
import json, os, re, glob
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh')
res = [json.loads(l) for l in open(os.path.join(HERE, 'm4fix_res_v1.jsonl'))]
T = {tuple(r['t']) for r in res}
keys = Counter(); j2 = {}
for l in open(os.path.join(HERE, 'j2_admit_cert2_checkpoint.jsonl')):
    l = l.strip()
    if not l: continue
    try: r = json.loads(l)
    except Exception: continue
    keys[tuple(sorted(r))] += 1
    if 'fire' in r: j2[tuple(r['t'])] = r
print('(a) j2 checkpoint key sets:', dict(keys))
print('(a) j2 lines carrying reach_leaves:', sum(v for k, v in keys.items() if 'reach_leaves' in k))
print('(a) res records with reach_leaves == 0:', sum(r['reach_leaves'] == 0 for r in res), '/', len(res))
ck = {}
for l in open(os.path.join(HERE, 'm4comp_cert_ckpt_v1.jsonl')):
    r = json.loads(l); ck[tuple(r['t'])] = r
c = Counter(); n1 = Counter(); nod = Counter()
for t in T:
    k = ck[t]
    c['found'] += 1
    c['leaves == reach+deadend+start_infeas'] += (k['leaves'] == k['reach_leaves'] + k['deadend_leaves'] + k['start_infeas'])
    c['nodes agree j2'] += (k['nodes'] == j2[t]['nodes'])
    c['leaves agree j2'] += (k['leaves'] == j2[t]['leaves'])
    c['reach > 0'] += (k['reach_leaves'] > 0)
    c['deadend > 0'] += (k['deadend_leaves'] > 0)
    nod['1' if k['nodes'] == 1 else '2-1000' if k['nodes'] <= 1000 else '>1000'] += 1
    if k['nodes'] == 1:
        n1[(k['reach_leaves'], k['deadend_leaves'], k['start_infeas'])] += 1
print('(b)', dict(c))
print('(b) nodes buckets:', dict(nod))
print('(b) nodes==1 boxes by (reach, deadend, start_infeas):', dict(n1))
print('(b) nodes==1 boxes with leaves==0:', sum(1 for t in T if ck[t]['nodes'] == 1 and ck[t]['leaves'] == 0))
cc = Counter(); bad = []
for f in sorted(glob.glob(os.path.join(FRESH, 'M4FixRung2_*.lean'))):
    box = tuple(int(x) for x in os.path.basename(f)[len('M4FixRung2_'):-5].split('_'))
    if box[1:] not in T and box not in T:
        cc['not a C3 box'] += 1; continue
    t = box[1:] if box[1:] in T else box
    src = open(f).read()
    n = len(re.findall(r'DfsPruneDomZone', src))
    cc['files'] += 1
    cc['reach>0 in ckpt2'] += (ck[t]['reach_leaves'] > 0)
    cc['mentions DfsPruneDomZone'] += (n > 0)
    if ck[t]['reach_leaves'] > 0 and n == 0: bad.append(t)
print('(c)', dict(cc), 'reach>0 but no DfsPruneDomZone:', len(bad), bad[:5])
# (d) object-level: per compiled C3 file, the reach-prune hypotheses of the box's `_cert` theorem
#     (`hpruneZone_<i> : DfsPruneDomZone ...`) against ckpt2's reach_leaves, and the OWED stubs.
dd = Counter(); mism = []
for f in sorted(glob.glob(os.path.join(FRESH, 'M4FixRung2_*.lean'))):
    name = os.path.basename(f)[len('M4FixRung2_'):-5]
    box = tuple(int(x) for x in name.split('_'))
    t = box[1:] if box[1:] in T else box if box in T else None
    if t is None: continue
    src = open(f).read()
    m = re.search(r'theorem m4fix_%s_cert(.*?):\s*\n\s*M4CertSound' % name, src, re.S)
    nh = len(re.findall(r'hpruneZone_\d+\s*:\s*DfsPruneDomZone', m.group(1))) if m else -1
    nstub = len(re.findall(r'-- STANDING: OWED\ntheorem m4fix_%s_pruneDom_\d+' % name, src))
    dd['files'] += 1
    dd['cert found'] += (m is not None)
    dd['cert prune hyps == ckpt2 reach'] += (nh == ck[t]['reach_leaves'])
    dd['OWED pruneDom stubs == ckpt2 reach'] += (nstub == ck[t]['reach_leaves'])
    dd['sum ckpt2 reach'] += ck[t]['reach_leaves']; dd['sum cert prune hyps'] += max(nh, 0)
    if nh != ck[t]['reach_leaves']: mism.append((name, nh, ck[t]['reach_leaves']))
print('(d)', dict(dd), 'mismatches:', len(mism), mism[:5])
print('(d) C3 population total reach leaves (ckpt2):', sum(ck[t]['reach_leaves'] for t in T))
# (e) E923-b's mechanism read `nstates = 1` as a 1-node tree.  nstates is the C3 closure's field; nodes is the DFS's.
ns = Counter((r['nstates'], 'nodes=1' if ck[tuple(r['t'])]['nodes'] == 1 else 'nodes>1') for r in res)
print('(e) (C3 nstates, DFS nodes) pairs:', dict(ns))
# (f) the boxes with reach_leaves = 0 in ckpt2: their leaf kinds and tree sizes.
z = [t for t in T if ck[t]['reach_leaves'] == 0]
zk = Counter(('deadend>0' if ck[t]['deadend_leaves'] else 'deadend=0', 'start_infeas>0' if ck[t]['start_infeas'] else 'start_infeas=0', ck[t]['kind']) for t in z)
print('(f) reach=0 boxes:', len(z), dict(zk))
print('(f) reach=0 boxes, nodes min/max:', min(ck[t]['nodes'] for t in z), max(ck[t]['nodes'] for t in z), ' leaves == deadend + start_infeas:', sum(ck[t]['leaves'] == ck[t]['deadend_leaves'] + ck[t]['start_infeas'] for t in z))
