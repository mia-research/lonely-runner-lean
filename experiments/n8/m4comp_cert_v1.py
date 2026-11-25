# m4comp_cert_v1.py -- Task 1: instrumented re-run of the M4 certificate DFS over the 12,540 boxes.
# Verbatim search logic (m4comp_lib_v1.cert_search_dbg == j2_admit_cert_v2.cert_search; leaf counts
# already verified to match the checkpoint exactly on samples + the two deep boxes + 73 controls).
# Per box we aggregate: leaves by type, leaf-depth histogram, leaf frontier (max state sup at the
# pruning reachability) histogram, last-zone (rank, exit-numerator) multiset at leaves, per-reading
# tightened-range pinch of the shallowest leaves.  For a stratified sample of 240 boxes we also keep
# the full per-leaf records.  Exact Fractions throughout.  Output: m4comp_cert_ckpt_v1.jsonl (per
# box), m4comp_cert_sample_v1.jsonl (per leaf, sample boxes), m4comp_cert_v1.out (summary).
import sys, os, json, time, statistics
from fractions import Fraction as F
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from m4comp_lib_v1 import cert_search_dbg, mk, add, tranges, ranges, starts, gate_a, closure_trace

def load(p, key):
    d = {}
    for l in open(os.path.join(HERE, p)):
        l = l.strip()
        if not l: continue
        try: r = json.loads(l)
        except: continue
        if key(r): d[tuple(r['t'])] = r
    return d

def job(args):
    t, rich = args
    col = {}
    t0 = time.time()
    r = cert_search_dbg(t, budget=400000, collect=col)
    lf = col.get('leaf_frontiers', [])
    ld = col.get('leaf_depth', [])
    ll = col.get('leaf_last', [])
    nst = col.get('leaf_nst', [])
    dd = col.get('leaf_deadend_depth', [])
    rec = dict(t=list(t), fire=r['fire'], kind=r['kind'], leaves=r['leaves'],
               maxdepth=r['maxdepth'], nodes=r['nodes'], nstart=r['nstart'],
               reach_leaves=len(lf), deadend_leaves=len(dd),
               start_infeas=col.get('start_infeas', 0),
               lf_min=str(min(lf)) if lf else None, lf_max=str(max(lf)) if lf else None,
               lf_med=str(statistics.median(lf)) if lf else None,
               ld_min=min(ld) if ld else None, ld_max=max(ld) if ld else None,
               ld_med=statistics.median(ld) if ld else None,
               dd_min=min(dd) if dd else None, dd_max=max(dd) if dd else None,
               last_zones=sorted(set(ll)), d=round(time.time() - t0, 2))
    if rich:
        rec['leaf_frontiers'] = [str(x) for x in lf]
        rec['leaf_depth'] = ld
        rec['leaf_last'] = ll
        rec['leaf_nst'] = nst
        rec['leaf_deadend_depth'] = dd
    return rec

def main():
    allt_ok = False
    m4 = load('j2_admit_cert2_checkpoint.jsonl', lambda r: 'fire' in r)
    deep = {}
    import itertools
    allt = list(itertools.combinations_with_replacement(range(1, 18), 6))
    g1 = load('j2_g1sweep_checkpoint.jsonl', lambda r: 's1' in r)
    M4 = [t for t in allt if g1.get(t, {}).get('s1') == 'none' and m4.get(t, {}).get('fire') is True]
    assert len(M4) == 12540
    # stratified sample of 240 for rich per-leaf records: by n2 bucket
    import random
    random.seed(7)
    byn2 = {}
    for t in M4: byn2.setdefault(t[0], []).append(t)
    sample = []
    for k in sorted(byn2):
        v = sorted(byn2[k])
        take = max(4, min(len(v), 30))
        sample += random.sample(v, take)
    richset = set(sample)
    CKPT = os.path.join(HERE, 'm4comp_cert_ckpt_v1.jsonl')
    SCKPT = os.path.join(HERE, 'm4comp_cert_sample_v1.jsonl')
    done = {}
    if os.path.exists(CKPT):
        for l in open(CKPT):
            l = l.strip()
            if not l: continue
            try: d = json.loads(l)
            except: continue
            done[tuple(d['t'])] = d
    queue = [(t, t in richset) for t in M4 if t not in done]
    print('instrumented DFS over %d boxes (%d rich), %d queued' % (len(M4), len(richset), len(queue)), flush=True)
    t0 = time.time()
    fo = open(CKPT, 'a', buffering=1)
    fs = open(SCKPT, 'a', buffering=1)
    n = 0
    with Pool(10) as p:
        for rec in p.imap_unordered(job, queue, chunksize=4):
            fo.write(json.dumps(rec) + '\n')
            if rec['t'] in [list(s) for s in richset] and 'leaf_frontiers' in rec:
                fs.write(json.dumps(rec) + '\n')
            done[tuple(rec['t'])] = rec
            n += 1
            if n % 250 == 0:
                print('[%6d/%6d %.0fs] last %s leaves=%s depth=%s' % (
                    n, len(queue), time.time() - t0, tuple(rec['t']), rec['leaves'], rec['maxdepth']), flush=True)
    print('done %d in %.0fs' % (n, time.time() - t0), flush=True)

if __name__ == '__main__':
    main()
