# mechbatch_bridge_loop_v1.py -- verify each mechbatch payload via the verification bridge.
# Fail-closed: stop on first unverified payload or non-standard axiom profile.
import json, glob, urllib.request, sys, time

PAYLOADS = sorted(glob.glob('mechbatch_bridge_payload_*.lean'))
STD = {'propext', 'Classical.choice', 'Quot.sound'}
log = open('mechbatch_bridge_log_v1.out', 'w')
ok = 0
for p in PAYLOADS:
    code = open(p).read()
    t0 = time.time()
    req = urllib.request.Request('http://localhost:8088/verify',
                                 json.dumps({'code': code}).encode(),
                                 {'Content-Type': 'application/json'})
    try:
        r = json.load(urllib.request.urlopen(req, timeout=900))
    except Exception as e:
        print(p, 'HTTP-FAIL', e, file=log, flush=True)
        print(p, 'HTTP-FAIL', e)
        sys.exit(1)
    bad_ax = [a for a in (r.get('axioms') or [])
              if not set(a['axioms']) <= STD]
    good = r['verified'] and r['sorryAx_count'] == 0 and not bad_ax
    line = '%-46s %s elapsed=%.1fs decls=%d sorryAx=%d bad_ax=%d' % (
        p.split('/')[-1], 'PASS' if good else 'FAIL', time.time() - t0,
        len(r.get('axioms') or []), r['sorryAx_count'], len(bad_ax))
    print(line, file=log, flush=True)
    print(line, flush=True)
    if not good:
        print('stderr head:', (r.get('raw_stderr') or '')[:800], file=log, flush=True)
        sys.exit(1)
    ok += 1
print('ALL PAYLOADS PASS:', ok, '/', len(PAYLOADS), file=log, flush=True)
print('ALL PAYLOADS PASS:', ok, '/', len(PAYLOADS))
