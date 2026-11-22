# massrun_fine_driver_v2.py -- fine-ladder mass-run driver (200 boxes, delta-derived
# from the proven m4rung2_batch1_driver.py: same recon -> generate -> ONE lean compile
# at a time -> axiom scan recipe, same honest-partial TSV banking, restart-safe on PASS).
# DELTA: a per-box reachutc dump step (reachutc_dump_v1.py, gate: 'reachutc <box>
# [T n/n]' + exit 0) inserted after recon and before gen -- m4rung2_gen_v1.py asserts
# reachutc_<box>.json exists (the crashed v1 run GEN-FAILed all boxes without it).
# Boxes/order/nodes from massrun_fine_selection.json (tree-size ascending).
# Results append to massrun_fine_results.tsv after EVERY box.  python3 -I.
import json, os, re, resource, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh'))
REPO = os.path.normpath(os.path.join(FRESH, '..', 'LonelyRunner'))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TSV = os.path.join(HERE, 'massrun_fine_results.tsv')


def lean_path():
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=REPO,
                        capture_output=True, text=True, check=True).stdout.strip()
    keep = [p for p in lp.split(':') if p and p != os.path.join(REPO, '.lake/build/lib/lean')]
    return os.path.join(FRESH, 'build') + ':' + ':'.join(keep)


def axscan(log, nprints):
    txt = open(log).read()
    errs = [l for l in txt.splitlines() if ': error:' in l]
    sorry = ('sorryAx' in txt or 'declaration uses \'sorry\'' in txt)
    sets = []
    for m in re.finditer(r"depends on axioms: \[(.*?)\]", txt, re.S):
        sets.append({a.strip() for a in m.group(1).split(',') if a.strip()})
    bad = sorted({tuple(sorted(s)) for s in sets if not s <= ALLOWED})
    ok = (not errs) and (not sorry) and len(sets) == nprints and not bad
    return ok, len(sets), [list(b) for b in bad], len(errs), sorry


def main():
    deadline_min = None
    for a in sys.argv[1:]:
        if a.startswith('--deadline-min'):
            deadline_min = float(a.split('=')[1])
    sel = json.load(open(os.path.join(HERE, 'massrun_fine_selection.json')))
    boxes = [tuple(b) for b in sel['selection']]
    nodes_of = {tuple(b): n for b, n in zip(sel['selection'], sel.get('nodes', []))}
    done = set()
    if os.path.exists(TSV):
        for l in open(TSV):
            f = l.rstrip('\n').split('\t')
            if len(f) > 5 and f[5] == 'PASS':
                done.add(tuple(int(x) for x in f[0].split(',')))
    todo = [b for b in boxes if b not in done]
    print('boxes given=%d done(PASS)=%d todo=%d' % (len(boxes), len(done), len(todo)),
          flush=True)
    LP = lean_path()
    t0 = time.time()
    for b in todo:
        if deadline_min is not None and (time.time() - t0) / 60 > deadline_min:
            print('DEADLINE reached, stopping before %s' % (b,), flush=True)
            break
        box = '_'.join(str(x) for x in b)
        nodes = nodes_of.get(b, '?')
        row = [','.join(str(x) for x in b), str(nodes)]
        # ---- recon (builds the [T 32/32]-verified tree mirror) ----
        t1 = time.time()
        rlog = os.path.join(HERE, 'm4rung2_recon_%s.out' % box)
        try:
            with open(rlog, 'w') as f:
                r = subprocess.run([sys.executable, '-I', 'm4rung2_recon_v1.py',
                                    ','.join(str(x) for x in b)], cwd=HERE,
                                   stdout=f, stderr=subprocess.STDOUT, timeout=3000)
        except subprocess.TimeoutExpired:
            row += ['-', '-', '-', '-', 'FAIL', 'recon wall-timeout (3000s cap)']
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s RECON-TIMEOUT' % box, flush=True)
            continue
        rt = time.time() - t1
        rtxt = open(rlog).read()
        m = re.search(r'recon \[T (\d+)/(\d+)\]', rtxt)
        tok = r.returncode == 0 and m and m.group(1) == m.group(2)
        row.append('%s [T %s/%s]' % ('%.1fs' % rt, m.group(1) if m else '?',
                                     m.group(2) if m else '?'))
        if not tok:
            row += ['-', '-', '-', 'FAIL', 'recon not [T n/n]: %s' % (
                [l for l in rtxt.splitlines() if '[F]' in l][:3] or rtxt[-300:],)]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s RECON-FAIL' % box, flush=True)
            continue
        # ---- reachutc dump pass 1 (provision: per-leaf verdicts from the mirror;
        #      the lean-stub readiness check CANNOT pass yet -- no Lean file exists
        #      before gen -- so pass-1 gates on: exit 0, tally line, dump written,
        #      and every [F] line being a lean.* readiness check) ----
        t1 = time.time()
        ulog = os.path.join(HERE, 'reachutc_dump_%s.out' % box)
        ujson = os.path.join(HERE, 'reachutc_%s.json' % box)
        if os.path.exists(ujson):
            os.remove(ujson)
        try:
            with open(ulog, 'w') as f:
                u = subprocess.run([sys.executable, '-I', 'reachutc_dump_v1.py',
                                    ','.join(str(x) for x in b)], cwd=HERE,
                                   stdout=f, stderr=subprocess.STDOUT, timeout=3000)
        except subprocess.TimeoutExpired:
            row += ['-', '-', '-', 'FAIL', 'utc wall-timeout (3000s cap)']
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s UTC-TIMEOUT' % box, flush=True)
            continue
        ut = time.time() - t1
        utxt = open(ulog).read()
        m = re.search(r'reachutc \S+ \[T (\d+)/(\d+)\]', utxt)
        flines = [l for l in utxt.splitlines() if l.startswith('[F] ')]
        uok = (u.returncode == 0 and m and os.path.exists(ujson)
               and all(l.startswith('[F] lean.') for l in flines))
        row.append('%s [T %s/%s%s]' % ('%.1fs' % ut, m.group(1) if m else '?',
                                       m.group(2) if m else '?',
                                       '+lean-pending' if (m and flines) else ''))
        if not uok:
            row += ['-', '-', 'FAIL', 'utc not n/n (lean-pending): %s' % (
                [l for l in utxt.splitlines() if '[F]' in l or 'Error' in l][:3] or utxt[-300:])]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s UTC-FAIL %s' % (box, flines[:2]), flush=True)
            continue
        # ---- generate ----
        t1 = time.time()
        g = subprocess.run([sys.executable, '-I', 'm4rung2_gen_v1.py',
                            ','.join(str(x) for x in b)], cwd=HERE,
                           capture_output=True, text=True, timeout=1200)
        gt = time.time() - t1
        src = os.path.join(FRESH, 'Fresh', 'M4CertRung2_%s.lean' % box)
        if g.returncode != 0 or not os.path.exists(src):
            row += ['%.1fs' % gt, '-', 'FAIL', 'generator abort: %s' % g.stderr.strip()[-400:]]
            with open(TSV, 'a') as f:
                f.write('\t'.join(row) + '\n'); f.flush()
            print('%s GEN-FAIL %s' % (box, g.stderr.strip()[-200:].replace('\n', ' | ')),
                  flush=True)
            continue
        nprints = open(src).read().count('#print axioms')
        row.append('%.1fs' % gt)
        # ---- compile (ONE at a time); CPU time via getrusage children delta ----
        t1 = time.time()
        ru0 = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
        clog = os.path.join(HERE, 'm4rung2_compile_%s.log' % box)
        env = dict(os.environ, LEAN_PATH=LP)
        with open(clog, 'w') as f:
            try:
                c = subprocess.run(['lean', 'Fresh/M4CertRung2_%s.lean' % box, '-R', '.',
                                    '-o', 'build/Fresh/M4CertRung2_%s.olean' % box],
                                   cwd=FRESH, env=env, stdout=f, stderr=subprocess.STDOUT,
                                   timeout=3000)
            except subprocess.TimeoutExpired:
                row += ['>3000s', 'FAIL', 'compile wall-timeout (3000s safety cap)']
                with open(TSV, 'a') as f:
                    f.write('\t'.join(row) + '\n'); f.flush()
                print('%s COMPILE-TIMEOUT' % box, flush=True)
                continue
        ct = time.time() - t1
        cpu = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime - ru0
        row.append('%.0fs wall/%.0fs cpu' % (ct, cpu))
        # ---- reachutc dump pass 2 (verify: the compiled Lean file now exists, so the
        #      lean-stub check is live; strict [T n/n] gate -- this is the OWED (b)
        #      per-leaf verification of the transcribed stubs) ----
        t1 = time.time()
        with open(ulog, 'w') as f:
            try:
                u2 = subprocess.run([sys.executable, '-I', 'reachutc_dump_v1.py',
                                     ','.join(str(x) for x in b)], cwd=HERE,
                                    stdout=f, stderr=subprocess.STDOUT, timeout=3000)
            except subprocess.TimeoutExpired:
                u2, utxt2 = None, 'TIMEOUT'
        if u2 is None:
            utxt2 = 'utc2 wall-timeout (3000s cap)'
        else:
            utxt2 = open(ulog).read()
        ut2 = time.time() - t1
        m2 = re.search(r'reachutc \S+ \[T (\d+)/(\d+)\]', utxt2)
        u2ok = (u2 is not None and u2.returncode == 0 and m2
                and m2.group(1) == m2.group(2))
        row.append('%s [T %s/%s]' % ('%.0fs' % ut2, m2.group(1) if m2 else '?',
                                     m2.group(2) if m2 else '?'))
        # ---- axiom scan ----
        if c.returncode != 0:
            errclass = 'exit %d; ' % c.returncode + '; '.join(
                [l.strip()[:160] for l in open(clog) if ': error:' in l][:3])
            row += ['FAIL', errclass]
        elif not u2ok:
            row += ['FAIL', 'utc2 not [T n/n]: %s' % (
                [l for l in utxt2.splitlines() if '[F]' in l][:3] or utxt2[-200:])]
        else:
            ok, nd, bad, nerr, sorr = axscan(clog, nprints)
            if ok:
                note = '%d/%d axioms all in {propext, Classical.choice, Quot.sound}' % (nd, nprints)
                if ct > 600:
                    note += ' -- SLOW WALL (contention; cpu=%ds)' % cpu
                row += ['PASS', note]
            else:
                row += ['FAIL', 'axscan: sets=%d/%d bad=%s errs=%d sorry=%s'
                        % (nd, nprints, bad, nerr, sorr)]
        with open(TSV, 'a') as f:
            f.write('\t'.join(row) + '\n'); f.flush()
        print('%s %s (nodes=%s compile=%s)' % (box, row[5], nodes, row[4]), flush=True)


if __name__ == '__main__':
    main()
