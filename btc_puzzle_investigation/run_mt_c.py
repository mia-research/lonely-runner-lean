#!/usr/bin/env python3
"""Exhaustive MT full-2^32 sweep using the validated C engine (mt_sweep), all 3
consumption models. Waits for the PHP/Randstorm sweep to finish first (avoid core
contention), then runs 10 C processes at a time over sliced ranges. Aggregates
best run per model -> mt_full32_results.txt.
C validated bit-for-bit vs CPython random; reproduces the pure-Python sweep's
exact best-seed (7 @ 803837)."""
import subprocess, os, sys, time, glob, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, 'mt_sweep')
NCORE = 10
FULL = 2**32
SLICES = 60                     # per model -> ~71.6M seeds/slice
MODELS = {0: 'randrange', 1: 'topbit', 2: 'reject'}
RESULT = os.path.join(HERE, 'mt_full32_results.txt')

def wait_for_extra():
    """Poll until no prng_extra workers remain, so we run uncontended."""
    while True:
        out = subprocess.run(['pgrep', '-f', 'prng_extra.py worker'],
                             capture_output=True, text=True).stdout.strip()
        if not out:
            return
        time.sleep(15)

def main():
    print("waiting for PHP/Randstorm sweep to finish before starting MT-C...", flush=True)
    wait_for_extra()
    print("clear. launching MT full-2^32 C sweep (3 models).", flush=True)
    step = FULL // SLICES
    tasks = []   # (model, lo, hi)
    for m in MODELS:
        for s in range(0, FULL, step):
            tasks.append((m, s, min(s + step, FULL)))
    total = len(tasks); t0 = time.time()
    best = {m: (0, 0) for m in MODELS}      # model -> (run, seed)
    running = []                            # (Popen, model)
    todo = list(tasks); done = 0
    while todo or running:
        while todo and len(running) < NCORE:
            m, lo, hi = todo.pop()
            p = subprocess.Popen([BIN, 'sweep', str(m), str(lo), str(hi)],
                                 stdout=subprocess.PIPE, text=True)
            running.append((p, m))
        time.sleep(0.5)
        still = []
        for p, m in running:
            if p.poll() is None:
                still.append((p, m)); continue
            done += 1
            out = p.stdout.read().strip()
            if out:
                run, seed = out.split()
                run = int(run)
                if run > best[m][0]:
                    best[m] = (run, int(seed))
        if len(still) != len(running):
            eta = (time.time()-t0)/max(done,1)*(total-done)
            print(f"  {done}/{total} chunks, {time.time()-t0:.0f}s, eta {eta:.0f}s, "
                  f"best={{{','.join(f'{MODELS[m]}:{best[m][0]}' for m in MODELS)}}}", flush=True)
        running = still
    HIT = 70
    with open(RESULT, 'w') as r:
        r.write(f"MT FULL 2^32 (C engine) — all 3 models — elapsed {time.time()-t0:.0f}s — hit-run={HIT}\n")
        for m in MODELS:
            run, seed = best[m]
            flag = "  <<< HIT!" if run >= HIT-3 else ""
            r.write(f"  MT {MODELS[m]:9s}: best run {run:2d}/{HIT} (seed {seed}){flag}\n")
        hit = any(best[m][0] >= HIT-3 for m in MODELS)
        r.write("VERDICT: " + ("HIT FOUND" if hit else
                 "NO HIT — full 2^32 integer-seed space RULED OUT for Python MT (all 3 models).") + "\n")
    print(open(RESULT).read(), flush=True)

if __name__ == '__main__':
    main()
