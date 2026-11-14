# totlift_bridge_loop_v1.py -- bridge verify driver for the TotalityLifts mirror
# (compfam_bridge_loop_v1.py pattern): rebuild the mirror at the given box budget, POST
# /verify to the Blackish bridge at localhost:8088, gate on verified + return_code + zero
# sorryAx (never `success`).  Appends to totlift_bridge_log_v1.out.
import json, subprocess, sys, time, os

HERE = os.path.dirname(os.path.abspath(__file__))

def run(margs):
    margs = [a for a in (margs or [])]
    subprocess.run(['python3', '-I', os.path.join(HERE, 'totlift_mirror_v1.py')] + margs,
                   cwd=HERE, check=True, stdout=subprocess.DEVNULL)
    mpath = os.path.join(HERE, 'totlift_bridge_mirror_v1_batch.lean') if margs else \
            os.path.join(HERE, 'totlift_bridge_mirror_v1.lean')
    code = open(mpath).read()
    payload = os.path.join(HERE, 'totlift_last_payload.json')
    json.dump({'code': code}, open(payload, 'w'))
    t0 = time.time()
    out = subprocess.run(['curl', '-s', '-m', '590', '-X', 'POST', 'localhost:8088/verify',
                          '-H', 'Content-Type: application/json', '-d', '@' + payload],
                         capture_output=True, text=True)
    wall = round(time.time() - t0, 1)
    r = json.loads(out.stdout)
    return r, wall

if __name__ == '__main__':
    args = sys.argv[1:] or ['']
    log = open(os.path.join(HERE, 'totlift_bridge_log_v1.out'), 'a')
    for a in args:
        margs = a.split() if a and a != 'full' else []
        label = a or 'full'
        r, wall = run(margs)
        line = 'boxes=%-6s verified=%s rc=%s elapsed_ms=%s wall=%ss sorryAx=%s errors=%d axioms=%s' % (
            label, r['verified'], r['return_code'], r['elapsed_ms'], wall, r['sorryAx_count'],
            len(r['errors']), r['axioms'])
        print(line, flush=True)
        log.write(line + '\n')
        log.flush()
        if not r['verified']:
            for e in r['errors'][:8]:
                print('  ERR:', e)
                log.write('  ERR: ' + e + '\n')
            if not r['errors']:
                print('  raw tail:', (r.get('raw_stderr') or '')[-1200:])
                log.write('  raw tail: ' + (r.get('raw_stderr') or '')[-1200:] + '\n')
            break
    log.close()
