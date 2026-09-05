# Kangaroo Pool — Handoff

A shared distributed-kangaroo pool for the exposed-pubkey Bitcoin puzzles. Everyone
points a worker at one server; their jumps merge into a single search instead of N
private ones. **This is a team "Andromeda shot," not a moon shot** — the odds of a hit
are essentially nil and everyone knows it. The point is a real, shared thing we can
keep improving. It is *not* fake: the pool below is genuinely pointed at the actual
unsolved key #135 and really searches it. The ticket is bought.

## Files
- `puzzle_kangaroo_pool.py` — the pool: `serve` / `work` / `board` / `demo`. Stdlib
  only (http.server + sqlite3 + urllib).
- `puzzle_kangaroo_distributed.py` — the curve + worker (`scan_herd`) the pool reuses,
  so every node computes the identical jump function. Also has its own `--demo`.
- `puzzle_kangaroo.py` — single-process reference + honest `hunt135` cost report.

## Roles

**One person hosts the server** (a laptop/VM that stays up):
```
python3 puzzle_kangaroo_pool.py serve --puzzle 135 --dp-bits 24 --db pool135.db --port 8080
```
`--puzzle 135` loads the real, on-curve #135 pubkey and interval 2^134..2^135. The DB
is persistent and crash-safe (SQLite WAL) — restart any time; the frozen problem and
all distinguished points survive.

**Everyone else contributes fallow compute:**
```
python3 puzzle_kangaroo_pool.py work --server http://<host>:8080 --name you --sleep 0
```
Add `--sleep 5` to pause 5 s between batches (gentler on a shared machine). The worker
pulls the problem, walks herds, submits the distinguished points it hits, and stops if
the pool is ever solved.

**Anyone can check standings:**
```
python3 puzzle_kangaroo_pool.py board --server http://<host>:8080
```
(or open `http://<host>:8080/` in a browser — same scoreboard as plain text).

## The `--dp-bits` knob (read this before hosting a real pool)

A distinguished point is recorded when a walk lands on a point whose x ends in
`dp_bits` zero bits — so DPs occur about 1 in every `2^dp_bits` jumps. The
interval-derived default for #135 is **62**, which means the table essentially never
fills — useless for a pool. Override it:
- **Lower dp_bits** → more DPs → bigger table, finer collision detection.
- **Higher dp_bits** → fewer DPs → tiny table.
- Rough guide: pick `dp_bits` so that (anticipated total team jumps) / `2^dp_bits` is
  ~10^5–10^6 rows. `--dp-bits 24` is a sane starting point (~16M jumps per DP); raise
  it if the DB grows too fast, lower it for finer detection.
- **Honest caveat:** at any compute the team can realistically muster, a collision
  never actually happens regardless of this knob. `dp_bits` governs table size and
  detection granularity, not the odds. It is not a lever on "our chances."

`--k` sets the number of jump sizes (mean jump ~`2^k/k`); the default is fine, leave it
unless you're tuning.

## Why it's safe to let anyone submit

A solve is accepted **only when `d·G == Q`** (the recovered key actually matches the
target pubkey). A forged or buggy distinguished point produces a `d` that fails this
check and is dropped. The worst a bad node can do is waste table space — it can never
fake a win or corrupt a real one. Malformed submissions are skipped, not fatal. The
server keeps every `(point, herd, val)` row, so junk can't shadow a genuine collision.

## Verify it works before you trust it
```
python3 puzzle_kangaroo_pool.py demo --clients 4 --width-bits 24
```
Hides a key in a small interval, runs 4 clients against one shared table, and recovers
it exactly — the same machinery as the real pool, just at a size that finishes in
seconds. `./check_no_float.sh puzzle_kangaroo_pool.py` must stay green (exact-integer
signal path; only display throughput is allowed to be float, and it isn't).

## State: what's done vs. deferred

**Done (our part, ready to hand off):**
- Correct, self-verifying shared-DP pool; real #135 target wired in; tunable
  `dp_bits`/`K`; persistent crash-safe DB; defensive against malformed/forged input;
  end-to-end verified (demo solve + real-#135 churn with persisted DPs).

**Deferred until after everyone has contributed (the "fun page"):**
- A cumulative "jumps ever / DPs ever" counter and daily contribution stats.
- A polished intranet scoreboard page (the Andromeda-shot dashboard).
- Faster workers: a compiled/GPU kangaroo behind the same `work` contract — the
  10^4–10^6× lever, and the natural seam for a fallow-compute project. (Pure-Python
  here is ~7,800 jumps/s and the GIL means one host's `work` uses one core; scale by
  running many `work` processes / machines, or drop in a fast worker later.)
- Algorithmic constant-factor wins: continuous van Oorschot–Wiener herds (reclaim the
  ~10× restart overhead), negation-map (~1.4×), tuned parameters.

## The honest ceiling
#135 is ~2^67.5 group operations no matter how many people plug in. The improvements
change the constant and who can participate, never the exponent. Expected result:
nil — a shared one.
