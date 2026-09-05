# Bitcoin Puzzle #135 — Team Kangaroo Pool

*One document to read, run, and share. Supersedes the internal handoff notes.*

We built a **shared, distributed Pollard-kangaroo search** pointed at the real,
unsolved Puzzle #135. Anyone on the team can contribute fallow compute; everyone's
work merges into **one** search instead of N private ones.

**Be honest with yourselves up front:** at any compute the team can realistically
muster, this never actually finds the key. It's a shared *Andromeda shot* — a group
lottery ticket that's genuinely bought and genuinely searching, not a progress bar.
The value is a real, correct, improvable thing we own together. See
[The honest ceiling](#the-honest-ceiling).

---

## The target

| | |
|---|---|
| Puzzle | #135 (unsolved, ~13.5 BTC) |
| Public key | `02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16` |
| Address | `16RGFo6hjq9ym6Pj7N5H7L1NR1rVPJyw2v` |
| Private key range | `2^134 … 2^135` (verified on-curve) |

The public key is exposed, which is the only reason a √-speedup attack is even possible.

---

## Why this design — the three rungs

**1. Brute force → hopeless at any speed.** The key is one of 2¹³⁴ ≈ 2.2×10⁴⁰ values.
Faster hardware only multiplies the *check rate* by a constant, and no constant beats an
exponent:

| compute | time to search 2¹³⁴ | vs age of universe |
|---|---|---|
| a quadrillion keys/s (10¹⁵) | 6.9×10¹⁷ yr | 50 million × |
| the entire Bitcoin network (10²¹) | 6.9×10¹¹ yr | 50 × |

*(`python3 why_speed_cannot_win.py` prints this.)* This is why a "faster engine" is the
wrong lever — it optimizes the one term that provably can't win.

**2. Kangaroo → the real method.** Pollard's kangaroo uses the exposed public key to find
`d` in a known interval in **~2·√W ≈ 2⁶⁷·⁵ ≈ 3×10²⁰** group operations — a square-root
speedup. That's finite. It's how #120 / #125 / #130 actually fell. On a 1,000-GPU cluster
(~10¹² ops/s) that's on the order of **years**, not never. *(`python3 puzzle_kangaroo.py`
prints the honest cost; `--demo` solves a small interval live to prove the machinery.)*

**3. Pool → everyone's kangaroos combine.** Ten people running kangaroo independently are
ten slow searches. Pointed at one **shared distinguished-point (DP) table**, they are one
~10× search. That's this tool.

The only lever left after this is a *smaller exponent* — a genuine structural leak in the
keys. We hunted that separately and found nothing: the keys behave like uniform-random
integers. So kangaroo-at-scale is the honest state of the art.

---

## Quick start

Pure Python, standard library only. No installs. Python 3.8+.

### 1 — One person hosts the server (a laptop/VM that stays up)

```
python3 puzzle_kangaroo_pool.py serve --puzzle 135 --dp-bits 24 --db pool135.db --port 8080
```

- `--puzzle 135` loads the real on-curve pubkey + interval.
- The DB is persistent and crash-safe (SQLite WAL) — restart any time; the frozen
  problem and every distinguished point survive.
- Note the host's reachable address (e.g. `http://192.168.1.50:8080`) and share it.

### 2 — Everyone else contributes compute

```
python3 puzzle_kangaroo_pool.py work --server http://<host>:8080 --name you
```

Add `--sleep 5` to pause 5 s between batches (gentler on a shared machine). The worker
pulls the problem, walks herds, submits the DPs it finds, and stops automatically if the
pool is ever solved.

### 3 — Anyone checks standings

```
python3 puzzle_kangaroo_pool.py board --server http://<host>:8080
```

…or just open `http://<host>:8080/` in a browser (same scoreboard).

---

## Prove it works before you trust it

```
python3 puzzle_kangaroo_pool.py demo --clients 4 --width-bits 24
```

Hides a key in a small interval, runs 4 clients against one shared table, and recovers it
**exactly** — the same machinery as the real pool, at a size that finishes in seconds.
Verified: it solves and reports the winner.

Integrity gate (keeps the math exact-integer; only display throughput may be float):
```
bash check_no_float.sh puzzle_kangaroo_pool.py
```
Must print `OK`.

---

## How it works (and why it's safe)

Two herds do pseudorandom jumps where **the jump size depends only on the current point**,
so once any two kangaroos land on the same point they merge forever:

```
tame point = val·G          (val = absolute exponent)
wild point = Q + val·G      (val = accumulated distance from the target Q)
same point, opposite herds  ⇒  d = tame_val − wild_val
```

The server keeps a shared table of distinguished points (points whose x-coordinate ends in
`dp_bits` zero bits). When a tame DP and a wild DP collide, it recovers `d`.

**Self-verifying — bad nodes can't hurt it.** A solve is accepted **only when `d·G == Q`**
(the recovered key actually reproduces the target public key). A forged or buggy DP yields a
`d` that fails this check and is dropped. Malformed submissions are skipped, never fatal.
The worst a bad contributor can do is waste table space — it can **never** fake a win or
corrupt a real one.

**Why anyone's worker merges correctly:** every node computes the *identical* jump function
(same `scan_herd`, same curve arithmetic). Any worker built to the contract below will
combine with the pool.

---

## Tuning

- **`--dp-bits`** (rarity of distinguished points; ~1 DP per `2^dp_bits` jumps).
  - Lower → more DPs → bigger table, finer detection. Higher → fewer DPs → tiny table.
  - Rough guide: pick it so *(expected total team jumps) / 2^dp_bits* ≈ 10⁵–10⁶ rows.
  - **`24` is a sane start** (~16M jumps per DP). The interval-derived default (62) is far
    too sparse for a pool — always override it.
  - **Honest caveat:** `dp_bits` governs table size and detection granularity, *not the
    odds*. It is not a lever on "our chances."
- **`--k`** (number of jump sizes; mean jump ~`2^k/k`). Default is fine; leave it unless tuning.

---

## Files

| file | what it is |
|---|---|
| `puzzle_kangaroo_pool.py` | **The pool.** `serve` / `work` / `board` / `demo`. http.server + sqlite3 + urllib. |
| `puzzle_kangaroo_distributed.py` | Curve + worker (`scan_herd`) the pool reuses, so every node's jumps merge. Also a `--demo` coordinator with pluggable `local`/`mock`/`lambda` backends. |
| `puzzle_kangaroo.py` | Single-process reference + honest `#135` cost report. `--demo` solves a small interval. |
| `puzzle135_bruteforce_toy.py` | The naive brute-forcer — the "why it's hopeless" teaching piece. `--demo` finds a small key. |
| `why_speed_cannot_win.py` | Prints the compute-vs-universe table. |
| `check_no_float.sh` | Integrity gate (exact-integer signal path). |

### Worker contract (for anyone writing a faster worker)

```
request  {"pubkey":"02..","a":"0x..","b":"0x..","K":int,"dp_bits":int,
          "herd":"tame"|"wild","start":"0x..","jumps":int}
response {"dps": [["0x<x>","0x<y>","0x<val>"], ...]}
```

Match `scan_herd`'s jump function exactly and your worker's DPs will merge with everyone's.

---

## The honest ceiling

#135 is **~2⁶⁷·⁵ group operations no matter how many people plug in.** Everything we can add
— more nodes, a compiled/GPU worker (the real 10⁴–10⁶× lever), continuous herds (~10×),
the negation map (~1.4×) — changes the *constant* and *who can participate*, never the
*exponent*. Expected result: nil — a shared one. That's the point. The ticket is bought,
it's real, and it's ours.

### What's next (optional, "fun page")

- **Faster workers** behind the same contract: a native/GPU kangaroo (libsecp256k1, batched
  inversions). Pure Python is ~8,000 jumps/s and the GIL means one `work` process = one core
  — scale by running many processes/machines, or drop in a fast worker. *This is the only
  change that moves jumps/s.*
- Algorithmic constant-factor wins (van Oorschot–Wiener continuous herds, negation map).
- A cumulative "jumps ever / DPs ever" counter and a polished intranet scoreboard.
