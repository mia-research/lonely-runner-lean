#!/usr/bin/env python3
"""Driver for prng_fingerprint_v1.py: launch worker subprocesses (NOT multiprocessing,
which hangs here), 10 at a time, over sliced seed ranges; aggregate best run per
(prng,model). Prints a decisive rule-out table."""
import subprocess, os, sys, time, tempfile, glob

HERE = os.path.dirname(os.path.abspath(__file__))
WORKER = os.path.join(HERE, 'prng_fingerprint_v1.py')
NCORE = 10
OUTDIR = tempfile.mkdtemp(prefix='prng_sweep_')

# (label, lo, hi) seed ranges
RANGES = [
    ("TIME 2013-2018", 1356998400, 1514764800),   # Unix seconds, 5-yr window
    ("SMALLINT 0-20M", 0, 20_000_000),
]
JOBS = {  # prng -> models
    'MT':    ['randrange', 'topbit', 'reject'],
    'glibc': ['bits', 'mod'],
    'V8':    ['floor', 'bits'],
}
SLICES_PER_JOB = 10   # split each (prng,model,range) into this many sub-ranges

def build_tasks():
    tasks = []
    for rlabel, lo, hi in RANGES:
        step = max(1, (hi - lo) // SLICES_PER_JOB)
        for prng, models in JOBS.items():
            for model in models:
                for i, s in enumerate(range(lo, hi, step)):
                    e = min(s + step, hi)
                    out = os.path.join(OUTDIR, f"{rlabel.split()[0]}_{prng}_{model}_{i}.txt")
                    tasks.append((prng, model, s, e, out, rlabel))
    return tasks

def run(tasks):
    running = []   # (Popen, task)
    todo = list(tasks); done = 0; total = len(tasks); t0 = time.time()
    while todo or running:
        while todo and len(running) < NCORE:
            prng, model, s, e, out, rlabel = todo.pop()
            p = subprocess.Popen([sys.executable, WORKER, 'worker', prng, model,
                                  str(s), str(e), out])
            running.append((p, (prng, model, s, e, out, rlabel)))
        time.sleep(0.3)
        still = []
        for p, task in running:
            if p.poll() is None: still.append((p, task))
            else: done += 1
        if len(still) != len(running):
            sys.stderr.write(f"\r  {done}/{total} chunks done, {time.time()-t0:.0f}s ")
            sys.stderr.flush()
        running = still
    sys.stderr.write("\n")

def aggregate():
    best = {}   # (rlabel,prng,model) -> (run, seed)
    for f in glob.glob(os.path.join(OUTDIR, '*.txt')):
        rlabel = os.path.basename(f).split('_')[0]
        with open(f) as fh:
            line = fh.read().strip()
        if not line: continue
        prng, model, lo, hi, run, seed = line.split('\t')
        run = int(run); key = (rlabel, prng, model)
        if key not in best or run > best[key][0]:
            best[key] = (run, seed)
    return best

if __name__ == '__main__':
    tasks = build_tasks()
    print(f"Launching {len(tasks)} worker chunks across {NCORE} cores. Output dir: {OUTDIR}")
    t = time.time()
    run(tasks)
    best = aggregate()
    HIT = 70   # contiguous solved keys #1..#70
    print(f"\n=== SWEEP RESULT (elapsed {time.time()-t:.0f}s) — hit-run = {HIT}, "
          f"coincidence floor ~4-7 ===")
    for rlabel in sorted(set(k[0] for k in best)):
        print(f"\n[{rlabel}]")
        rows = [(k[1], k[2], v[0], v[1]) for k, v in best.items() if k[0] == rlabel]
        for prng, model, run, seed in sorted(rows, key=lambda x: -x[2]):
            flag = "   <<< HIT — PRNG IDENTIFIED!" if run >= HIT - 3 else ""
            print(f"   {prng:6s} {model:9s}: best run {run:2d}/{HIT}  (seed {seed}){flag}")
    hits = [k for k, v in best.items() if v[0] >= HIT - 3]
    print("\nVERDICT:", "HIT(S) FOUND: " + str(hits) if hits else
          "NO HIT — every candidate stayed at the coincidence floor; "
          "all swept (prng,model,seed-space) combinations RULED OUT.")
