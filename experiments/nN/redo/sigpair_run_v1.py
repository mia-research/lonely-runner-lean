# sigpair_run_v1 -- resumable chunk runner: python3 sigpair_run_v1.py J [seconds]
# Processes tree cells of window J with 2 worker processes until the deadline, appending finished cells to sigpair_res_J{J}_v1.jsonl-like pickle shards.
import sys, pickle, time, os, json
from multiprocessing import Pool
sys.path.insert(0, '.')
J = int(sys.argv[1]); LIMIT = float(sys.argv[2]) if len(sys.argv) > 2 else 500
OUT = f'sigpair_res_J{J}_v1.jsonl'
from sigpair_cell_v1 import *
T = pickle.load(open(f'terminals5_J{J}.pkl', 'rb'))

def work(i):
    p, lo, hi, box, w = T[i]
    t0 = time.time()
    try:
        r = decide_cell(p, box, J)
    except Exception as e:
        r = {'error': repr(e), 'path': tuple(p), 'opener': p[-1][0]}
    r['i'] = i; r['sec'] = time.time() - t0
    return r

def enc(r):
    r = dict(r)
    for k in ('status', 't', 'ttie', 'xtb', 'cert'):
        if k in r: r[k] = {str(a): b for a, b in r[k].items()}
    r['path'] = [list(x) for x in r['path']]
    return json.dumps(r)

if __name__ == '__main__':
    done = set()
    if os.path.exists(OUT):
        for line in open(OUT):
            try: done.add(json.loads(line)['i'])
            except Exception: pass
    todo = [i for i in range(len(T)) if i not in done]
    print('J', J, 'done', len(done), 'todo', len(todo), flush=True)
    t0 = time.time(); n = 0
    with Pool(int(os.environ.get('WORKERS', '2'))) as pool, open(OUT, 'a') as f:
        it = pool.imap(work, todo, chunksize=8)
        # imap blocks; use a watchdog by checking time after every result; remaining tasks are abandoned at the deadline
        for r in it:
            f.write(enc(r) + '\n'); n += 1
            if n % 200 == 0: f.flush()
            if time.time() - t0 > LIMIT: break
        f.flush(); pool.terminate()
    print('finished this run:', n, 'in', round(time.time() - t0), 's', flush=True)
