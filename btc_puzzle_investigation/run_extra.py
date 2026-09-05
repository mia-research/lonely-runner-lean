#!/usr/bin/env python3
"""Driver for prng_extra.py (PHP mt_rand + Randstorm RC4). Subprocess-parallel.
Sweeps time-window 2013-2018 + small-int 0-20M (pure-Python impls too slow for
full 2^32). Aggregates best run per (prng,model)."""
import subprocess, os, sys, time, tempfile, glob

HERE = os.path.dirname(os.path.abspath(__file__))
WORKER = os.path.join(HERE, 'prng_extra.py')
NCORE = 10
OUTDIR = tempfile.mkdtemp(prefix='prng_extra_')
RESULT = os.path.join(HERE, 'extra_results.txt')

RANGES = [("TIME", 1356998400, 1514764800), ("SMALLINT", 0, 20_000_000)]  # 2013-2018 + 0-20M
JOBS = [('PHP', 'bits'), ('PHP', 'words'), ('RC4', 'stream')]
SLICES = 20

def build():
    tasks = []
    for rlabel, lo, hi in RANGES:
        step = max(1, (hi - lo) // SLICES)
        for prng, model in JOBS:
            for i, s in enumerate(range(lo, hi, step)):
                e = min(s + step, hi)
                out = os.path.join(OUTDIR, f"{rlabel}_{prng}_{model}_{i}.txt")
                tasks.append((prng, model, s, e, out, rlabel))
    return tasks

def main():
    tasks = build()
    running = []; todo = list(tasks); done = 0; total = len(tasks); t0 = time.time()
    print(f"Extra sweep: {total} chunks, {NCORE} cores, outdir {OUTDIR}", flush=True)
    while todo or running:
        while todo and len(running) < NCORE:
            prng, model, s, e, out, rlabel = todo.pop()
            p = subprocess.Popen([sys.executable, WORKER, 'worker', prng, model, str(s), str(e), out])
            running.append((p, None))
        time.sleep(0.5)
        still = [(p, t) for p, t in running if p.poll() is None]
        if len(still) != len(running):
            done += len(running) - len(still)
            print(f"  {done}/{total} chunks, {time.time()-t0:.0f}s", flush=True)
        running = still
    best = {}
    for f in glob.glob(os.path.join(OUTDIR, '*.txt')):
        rlabel = os.path.basename(f).split('_')[0]
        line = open(f).read().strip()
        if not line: continue
        prng, model, lo, hi, run, seed = line.split('\t'); run = int(run)
        k = (rlabel, prng, model)
        if k not in best or run > best[k][0]: best[k] = (run, seed)
    HIT = 70
    with open(RESULT, 'w') as r:
        r.write(f"PHP + RANDSTORM(RC4) SWEEP — elapsed {time.time()-t0:.0f}s — hit-run={HIT}\n")
        for (rlabel, prng, model), (run, seed) in sorted(best.items(), key=lambda x: -x[1][0]):
            flag = "  <<< HIT!" if run >= HIT-3 else ""
            r.write(f"  {rlabel:9s} {prng:4s} {model:6s}: best run {run:2d}/{HIT} (seed {seed}){flag}\n")
        hit = any(v[0] >= HIT-3 for v in best.values())
        r.write("VERDICT: " + ("HIT FOUND" if hit else
                 "NO HIT — PHP mt_rand + Randstorm RC4 (time+small-int seeds) RULED OUT.") + "\n")
    print(open(RESULT).read(), flush=True)

if __name__ == '__main__':
    main()
