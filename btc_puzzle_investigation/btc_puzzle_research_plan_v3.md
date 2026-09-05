# BTC Puzzle — Research Plan v3 (new tests from the big-menu triage)

Date: 2026-07-08. Supersedes selection logic in v1/v2 (does not retract their
nulls). Governed by `CLAUDE.md` (NO FLOATING POINT in the signal path) and the
signal-vs-noise scaling discipline in `power_scaling.py`.

## 0. The selection rule (why most of the menu is NOT a test)

The no-float rule exists because **a null on the wrong instrument is
uninformative** — you cannot tell "no signal" from "signal destroyed before the
test ran." Extend that same discipline to *experiment selection*:

> Run a test only if BOTH of its possible outcomes teach us something.

For any idea that reduces to "extract information about `d` from the algebraic
structure of the curve faster than √W," the only outcomes are (a) NULL — which we
already know, because that is exactly the 40-year-hardened ECDLP wall — or
(b) "broke ECDLP," which will not happen on a laptop. A null there is as
uninformative as a float-smeared null. **Do not spend cycles confirming we can't
break ECDLP.** Spend them where both outcomes move us.

That single rule sorts the entire menu into three buckets.

---

## Bucket 1 — Reduces to ECDLP. Null is uninformative. DO NOT run as a break.

Each collapses to the discrete log; the reduction is the disposition.

| Idea | Why it is ECDLP in disguise |
|---|---|
| **Ladder bit-structure leakage** (double-and-add trajectory of `Q=dG`) | Reading a bit of `d` off the trajectory *without already knowing `d`* **is** the discrete log — the trajectory is a deterministic function of `d`, and inverting it is the problem itself. Confirmed by literature: every real ladder leak is a **side-channel** (timing/power/EM) → EHNP → lattice (LadderLeak, EHNP-trace work). We have no side channel — the keys are just published points. The "pure-mathematical break of secp256k1" preprints (academia.edu "MSN Trace", keyhunters) are unverified, no reproduced batch recovery — not a frontier. |
| **Sum-product as a constructive attack** | The Bourgain–Konyagin bounds are *upper bounds on structure*, used to **prove** kangaroo behaves near-ideal-random. "Inverting them to constructive" would be a new theorem, not an experiment — nothing to run. (Its one *empirical* shadow is a diagnostic, not an attack → Test 3.) |
| **Isogeny (SIDH/Castryck–Decru)** | Castryck–Decru broke the **isogeny-graph** problem (walk recovery). secp256k1 ECDLP is not that problem; there is no isogeny-graph secret here. Different problem family, no transfer. |
| **Genus theory / class number** | secp256k1 is prime-order, huge CM discriminant, nothing-up-my-sleeve. No small-degree relations to exploit. The user already flagged this as a long shot; nothing testable. |
| **Quantum-walk-as-classical** | The speedup needs the quantum walk. The *classical* question ("is the ladder/Cayley graph glued-tree-like?") is answerable, but the answer is known a priori: the Cayley graph of a large prime cyclic group with generic generators is an **expander**, not glued-tree-structured. Cost to confirm is nonzero; payoff is only "confirmed unstructured." Skip unless idle. |
| **Coppersmith / lattice on the interval** | Coppersmith needs the unknown remainder **small vs the modulus** (O(log) unknown bits). Kangaroo's interval for #135 has ~2^134 unknown bits — the *whole* secret. Coppersmith yields nothing until you already know almost all bits. **BUT** it is exactly the right *back-end* — see Test 1: if the generator leaks partial known bits or a cross-key relation, Coppersmith/LLL is how you cash it. It is not a standalone test; it is the exploitation stage for a positive Bucket-3 finding. |

---

## Bucket 2 — Measures OUR OWN system. Both outcomes informative. DESIGN THESE.

None beats √W. All are honestly bounded, cheap, and run on the working
`puzzle_kangaroo_pool.py` demo sizes (2^32–2^40).

### Test 2 (priority-2) — DP-table percolation / density threshold
- **Question.** Does the DP table's effective collision probability rise
  *smoothly* with distinguished-point density ρ (classical birthday model), or is
  there a **sharp critical ρ_c** (percolation-like knee) as jumps accumulate?
- **Setup.** Instrument `puzzle_kangaroo_pool.py` at solvable widths. Define
  ρ = (#DPs) / (√W · 2^{−dp_bits}). Log, as walks accumulate, the empirical
  time-to-first-collision and p_eff(ρ). Sweep `dp_bits` across a range and fit
  the p_eff(ρ) curve.
- **Exactness.** Collision detection is already integer-exact (point equality) —
  keep it that way. The only floats are in *reporting* the fitted curve; never in
  deciding a collision.
- **Pre-registered outcomes.** Sharp knee at some ρ_c ⇒ retune `dp_bits` to sit
  just past the boundary — a real constant-factor win on live runs. Smooth ⇒
  current birthday model validated; still a useful confirmation for the team
  guide's tuning section.

### Test 3 (priority-3) — DP-coordinate uniformity (the ONLY empirical sum-product check)
- **Question.** At *our* scale, does the group operation on secp256k1 produce
  X-coordinates measurably non-uniform — the one place sum-product "structure
  limits" become concretely checkable?
- **Setup.** Dump all visited X coords (or DP `X[0]` bytes) from a real run. Test
  uniformity of `X mod m` for m ∈ {7, 251, 256, 2^k} and of consecutive-jump
  increments, against a **matched null** = same count of genuinely random curve
  points `r·G`.
- **Exactness.** Verdict by **exact permutation / rank statistic** (chi-square as
  a ranked statistic vs the matched null), never a float threshold — reuse the
  `mi_bits` + permutation-null machinery from `leak_test_exact.py` /
  `power_scaling.py`.
- **Pre-registered outcomes.** Deviation ⇒ genuinely novel, escalate. Uniform ⇒
  kangaroo's core assumption confirmed empirically at this scale (publishable
  sanity result). Feed it through `power_scaling.py` so a noise-floor blip is
  classified by its N-scaling, not a single p-value.

### Lower priority (cheap, design-only for now)
- **2C — MCMC mixing of jump selection** (`i = X[0] % K`). Is uniform jump-index
  selection mixing optimally over the interval, or is there a constant-factor
  gain from conditioning jump size on a cheap local statistic (Hamming weight of
  `X[0]`, distance-to-nearest-known-DP)? Bounded: cannot beat √W; at most a tuned
  constant. Test = A/B two selection rules at fixed width, compare jump-count
  distributions. Run only after Test 2 (same instrumentation).
- **2D — near / multi-collision information.** Do 3-way near-coincidences in the
  DP table carry partial bits? Literature says this is mostly a constant-factor
  optimization, not a structural break. Lowest priority; fold into Test 2's
  instrumented run rather than a separate build.

---

## Bucket 3 — Attacks the GENERATION, not the curve. The genuinely open one. DESIGN FIRST.

This is the only avenue that does **not** fight ECDLP. Precedented (Sony PS3
nonce reuse, Randstorm, biased-nonce lattice attacks). It targets human/RNG
choices in how keys #1–160 were made.

**What is already nulled (do not repeat):** weak-seed hypothesis
(name/date/hash × MT19937/glibc × 4 consumption models) → NULL; single-key MT
fingerprint → NULL; `prng_new_families` pass-1 → NULL. Memory: *"keys have
exactly N bits, not nested prefixes."* So *known-seed, single-key* recovery is
closed.

**The un-run variant (Test 1, priority-1): cross-key STATE-continuity with an
UNKNOWN seed.** Prior work guessed the seed. This test never guesses it —
it recovers PRNG *state* from the concatenated outputs themselves (the
LadderLeak/state-recovery flavor) and tests continuity *across* keys.

### Test 1 — Cross-key generator state-recovery (CONFIRMS, not FINDS)
- **Data.** Solved keys #1–134: exact `d_i`, each with offset
  `o_i = d_i − 2^{i−1} ∈ [0, 2^{i−1})`. All integer.
- **Model family.** Hypothesize keys emitted *sequentially from one continuous
  stream*. Enumerate consumption models: (a) rejection-uniform in the interval;
  (b) `o_i = draw() mod 2^{i−1}`; (c) fixed 256-bit draw then mask/shift. For MT
  each model fixes how the 32-bit words map to `o_i`.
- **Recovery (the new move).** For MT19937: untemper the reconstructed 32-bit
  words across the *whole sequence* (~134 keys × ⌈bits/32⌉ words — potentially
  ≥ 624 words = full state) and solve for internal state **without the seed**.
  For LCG/xorshift families: LLL over integer relations among consecutive `o_i`
  to detect a low-degree recurrence mod 2^t on the top-t bits.
- **Verdict (held-out, integer-exact, per the CONFIRMS-not-FINDS memory).**
  Fit state on keys #1..m, then check whether the recovered generator reproduces
  the KNOWN keys #(m+1)..134 it was **not** fit on — by exact integer equality.
  No float anywhere: this is untempering + modular linear algebra.
- **Pre-registered outcomes.** Held-out keys reproduced ⇒ regenerate #135
  directly — game over, and Coppersmith/LLL (Bucket 1 #6) becomes the back-end if
  only partial bits recover. NULL ⇒ bounded conditional negative: *"under
  consumption models {a,b,c} and generator families {MT19937, LCG(glibc/PCG),
  xorshift}, the #1–134 sequence is not one continuous stream"* — never
  "impossible."
- **Controls.** Same pipeline on (i) a real MT19937 stream sliced into the same
  interval structure (must succeed — validates the recovery), and (ii) 134
  independent `secrets.randbelow` offsets (must NULL — bounds false-positive
  rate).

---

## Order of work
1. **Test 1** (cross-key state-recovery) — highest value, doesn't fight ECDLP,
   integer-only, self-verifying via held-out. Build `xkey_state_recovery.py`.
2. **Test 2** (DP percolation) — instrument existing pool; real tuning payoff.
3. **Test 3** (DP uniformity) — reuse `leak_test_exact` + `power_scaling`.
4. Bucket 2C/2D — fold into Test 2's instrumented run.
5. Bucket 1 — parked with reductions above; Coppersmith held as Test-1 back-end.

Every script routes through `check_no_float.sh` before any result is reported.
