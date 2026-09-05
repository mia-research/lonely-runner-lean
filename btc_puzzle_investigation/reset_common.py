#!/usr/bin/env python3
"""Shared loaders for the reset threads. Exact integers only (no float in signal path)."""
import csv, os

_CSV = os.path.join(os.path.dirname(__file__), "btc_puzzle_master_exact.csv")

def load_solved():
    """Return dict {puzzle:int -> {'bits':int,'d':int,'X':int or None,'Y':int or None}}
    for every SOLVED puzzle that has a private key."""
    out = {}
    with open(_CSV) as f:
        for r in csv.DictReader(f):
            if r["status"].strip().upper() != "SOLVED":
                continue
            pd = r["priv_dec"].strip()
            if not pd:
                continue
            pz = int(r["puzzle"])
            X = int(r["X_hex"], 16) if r["X_hex"].strip() else None
            Y = int(r["Y_hex"], 16) if r["Y_hex"].strip() else None
            out[pz] = {"bits": int(r["bits"]), "d": int(pd), "X": X, "Y": Y}
    return out

def contiguous_run(solved, start=1):
    """Longest run of consecutive puzzle indices present, starting at `start`."""
    run = []
    i = start
    while i in solved:
        run.append(i)
        i += 1
    return run

def low_bits(d, nbits):
    """The low `nbits` bits of key d (i.e. d with its forced top bit removed).
    For puzzle N, d in [2^(N-1), 2^N), nbits = N-1, and this returns bits 0..N-2."""
    return d & ((1 << nbits) - 1)

if __name__ == "__main__":
    s = load_solved()
    run = contiguous_run(s, 1)
    print(f"solved-with-key: {len(s)} puzzles; indices {sorted(s)}")
    print(f"contiguous run from 1: {run[0]}..{run[-1]}  (len {len(run)})")
    total_low = sum(p - 1 for p in run)          # bits of generator output if sequential
    print(f"generator bits embedded in the contiguous run (sum of N-1): {total_low}")
    # sanity: top bit really is set and value in range
    bad = [p for p in s if not (2**(s[p]['bits']-1) <= s[p]['d'] < 2**s[p]['bits'])]
    print(f"range-check failures: {bad}")
