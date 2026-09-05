#!/usr/bin/env python3
"""Exhaustive full 2^32 integer-seed sweep for glibc rand() and Python MT,
subprocess-parallel (multiprocessing hangs here). Subsumes the earlier
time-window + small-int ranges. Writes best run per (prng,model) to results file."""
import subprocess, os, sys, time, tempfile, glob

HERE = os.path.dirname(os.path.abspath(__file__))
WORKER = os.path.join(HERE, 'prng_fingerprint_v1.py')
NCORE = 10
FULL = 2**32
OUTDIR = tempfile.mkdtemp(prefix='prng_full32_')
RESULT = os.path.join(HERE, 'full32_results.txt')

JOBS = [('glibc', 'bits'), ('glibc', 'mod'), ('MT', 'randrange'), ('MT', 'topbit')]
SLICES = 40   # per job

def build():
    tasks = []
    step = FULL // SLICES
    for prng, model in JOBS:
        for i, s in enumerate(range(0, FULL, step)):
            e = min(s + step, FULL)
            out = os.path.join(OUTDIR, f"{prng}_{model}_{i}.txt")
            tasks.append((prng, model, s, e, out))
    return tasks

def main():
    tasks = build()
    # glibc jobs first (fast), MT last: sort so cheap ones drain early for quick partial signal
    tasks.sort(key=lambda t: 0 if t[0] == 'glibc' else 1)
    running = []; todo = list(reversed(tasks)); done = 0; total = len(tasks); t0 = time.time()
    print(f"Full 2^32 sweep: {total} chunks, {NCORE} cores, outdir {OUTDIR}", flush=True)
    while todo or running:
        while todo and len(running) < NCORE:
            prng, model, s, e, out = todo.pop()
            p = subprocess.Popen([sys.executable, WORKER, 'worker', prng, model, str(s), str(e), out])
            running.append((p, (prng, model)))
        time.sleep(0.5)
        still = []
        for p, task in running:
            if p.poll() is None: still.append((p, task))
            else: done += 1
        if len(still) != len(running):
            print(f"  {done}/{total} chunks, {time.time()-t0:.0f}s", flush=True)
        running = still
    # aggregate
    best = {}
    for f in glob.glob(os.path.join(OUTDIR, '*.txt')):
        line = open(f).read().strip()
        if not line: continue
        prng, model, lo, hi, run, seed = line.split('\t'); run = int(run)
        k = (prng, model)
        if k not in best or run > best[k][0]: best[k] = (run, seed)
    HIT = 70
    with open(RESULT, 'w') as r:
        r.write(f"FULL 2^32 SWEEP — elapsed {time.time()-t0:.0f}s — hit-run={HIT}\n")
        for (prng, model), (run, seed) in sorted(best.items(), key=lambda x: -x[1][0]):
            flag = "  <<< HIT!" if run >= HIT-3 else ""
            r.write(f"  {prng:6s} {model:9s}: best run {run:2d}/{HIT} (seed {seed}){flag}\n")
        verdict = "HIT FOUND: "+str([k for k,v in best.items() if v[0]>=HIT-3]) if any(v[0]>=HIT-3 for v in best.values()) else "NO HIT — full 2^32 space RULED OUT for glibc + MT."
        r.write("VERDICT: "+verdict+"\n")
    print(open(RESULT).read(), flush=True)

if __name__ == '__main__':
    main()
