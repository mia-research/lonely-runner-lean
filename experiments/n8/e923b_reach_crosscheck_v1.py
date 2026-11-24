#!/usr/bin/env python3
"""e923b_reach_crosscheck_v1 -- E923-b says all 10,211 C3 boxes have reach_leaves = 0 in the
constructed records (m4fix_res_v1.jsonl).  Cross-check each record's box against the M4 DFS
checkpoint m4comp_cert_ckpt_v1.jsonl (key: the 6-tuple t; m4fix may carry 1::t).  Count, per
box: reach_leaves in each file, and whether nodes agree."""
import json, collections
ck = {}
for l in open('m4comp_cert_ckpt_v1.jsonl'):
    r = json.loads(l); ck[tuple(r['t'])] = r
fx = [json.loads(l) for l in open('m4fix_res_v1.jsonl')]
print("m4fix records:", len(fx), "keys:", sorted(fx[0].keys())[:20])
c = collections.Counter()
for r in fx:
    t = r.get('t') or r.get('box') or r.get('n')
    t = tuple(t[1:]) if len(t) == 7 else tuple(t)
    k = ck.get(t)
    if k is None: c['not_in_ckpt'] += 1; continue
    c['found'] += 1
    c['fix_reach0'] += (r.get('reach_leaves') == 0)
    c['ckpt_reach_pos'] += (k['reach_leaves'] > 0)
    c['nodes_agree'] += (r.get('nodes') == k['nodes'])
    c['both: fix0 & ckpt>0'] += (r.get('reach_leaves') == 0 and k['reach_leaves'] > 0)
print(dict(c))
