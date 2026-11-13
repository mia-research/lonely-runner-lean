# compfam_bridge_loop_v1.py -- batch verify driver: regenerate at n boxes, build the mirror,
# POST /verify, gate on verified (never success).  Writes compfam_bridge_log_v1.out.
import json, subprocess, sys, time, os
HERE = os.path.dirname(os.path.abspath(__file__))

def run(n):
    subprocess.run(['python3', '-I', 'compfam_gen_v1.py', str(n)], cwd=HERE, check=True,
                   stdout=subprocess.DEVNULL)
    subprocess.run(['python3', '-I', 'compfam_mirror_v1.py'], cwd=HERE, check=True,
                   stdout=subprocess.DEVNULL)
    code = open(os.path.join(HERE, 'compfam_bridge_mirror.lean')).read()
    payload = os.path.join(HERE, 'compfam_last_payload.json')
    json.dump({'code': code}, open(payload, 'w'))
    t0 = time.time()
    out = subprocess.run(['curl', '-s', '-m', '290', '-X', 'POST', 'localhost:8088/verify',
                          '-H', 'Content-Type: application/json', '-d', '@' + payload],
                         capture_output=True, text=True)
    wall = round(time.time() - t0, 1)
    r = json.loads(out.stdout)
    return n, r, wall

if __name__ == '__main__':
    sizes = [int(x) for x in sys.argv[1:]] or [12]
    log = open(os.path.join(HERE, 'compfam_bridge_log_v1.out'), 'a')
    for n in sizes:
        n, r, wall = run(n)
        line = 'n=%-3d verified=%s rc=%s elapsed_ms=%s wall=%ss sorryAx=%s errors=%d axioms=%s' % (
            n, r['verified'], r['return_code'], r['elapsed_ms'], wall, r['sorryAx_count'],
            len(r['errors']), r['axioms'])
        print(line, flush=True)
        log.write(line + '\n')
        log.flush()
        if not r['verified']:
            for e in r['errors'][:6]:
                print('  ERR:', e)
                log.write('  ERR: ' + e + '\n')
            if not r['errors']:
                print('  raw tail:', (r['raw_stdout'] or '')[-800:])
                log.write('  raw tail: ' + (r['raw_stdout'] or '')[-800:] + '\n')
            break
    log.close()
