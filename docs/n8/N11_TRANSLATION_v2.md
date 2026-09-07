# Does the n=11 architecture translate to n=8 — v2

2026-09-07. **Supersedes `N11_TRANSLATION_v1.md`.** Two changes, both against v1:
its §4 named the Coupling Principle as the untranslated component — **that is wrong,
and §2 below retracts it with the source quotes**; and its §2 located the collapse in
the complementary-pair count, which is right but is **not** where the n=11 proof's
engine sits — §3 shows the engine is primality-free and does translate. v1 also wrote
from the recorded architecture only; v2 is written against `eleven_lonely_runners_v33.md`
itself and against a built n=8 instantiation (`experiments/n8/pacemaker_n8_v{1,2}.py`).

Companion: `TIGHT_INSTANCES_v1.md`, which carries the extremal boundary and the
separate finding that v33's **target statement** is false at n=8.

## 1. What v1 got right and is kept

`[PROVED]` The complementary-pair count is tight at a prime and broken at `n = 8`:
`φ(11) = 10` unit witnesses against 10 speeds; `φ(8) = 4` against 7. The four unit
witnesses `m/8` form two pairs `{1,7}` and `{3,5}`, owned by runners `(1,7)` and
`(3,5)`, because `(ℤ/8)ˣ` has exponent 2 and `j ↦ j⁻¹` is the identity. The pair
pigeonhole does not run at `n = 8`. Unchanged from v1 §2.

`[PROVED]` The witness ladder of v1 §3, and its identification with Rosenfeld's
Lemma 4. Unchanged, and `TIGHT_INSTANCES_v1.md` §1 sharpens it: levels `q ≤ 7` are
**strict**, level `q = 8` is **tight**, so the ladder splits `n = 8` into a one-line
case that contains every tight instance and a residual case that contains none.

## 2. Retraction — the Coupling Principle DOES translate  `[PROVED]`

`N11_TRANSLATION_v1.md` §4, verbatim:

> "| Coupling Principle (bad intervals move together under the free parameter) |
> **not translated.** At n=11 the free parameter is a real speed `a₂`; at n=8 with
> integer speeds there is no continuous parameter. … The n=8 analogue is
> unidentified. **This is the gap.** |"

Its premise — that `n = 8` must be attacked with integer speeds — is not the n=11
method's frame. Three quotes settle it:

- `eleven_lonely_runners_v33.md:41-43` — *"**Theorem 1.1 (Main Theorem).** For any ten
  distinct positive **real** speeds $e_1<\cdots<e_{10}$…"*
- `:149-150` — *"normalise by setting $a_i := \frac{10e_i}{e_{10}},\ a_{10}=10$"*
- `:277-283`, Lemma 4.1, proved in one sentence — *"Immediate from the endpoint
  formula."*

The free parameters are the **real normalised speeds**, not integers, and the
Coupling Principle is the endpoint formula `B_{j,k}(a_j) = [(nk+n-1)/(n a_j),
(nk+n+1)/(n a_j)]` — no primality, no integrality, no `n = 11`. At `n = 8` the same
formula gives the same rigid motion in `1/a_j` for the five free speeds
`a_2,…,a_6`. **It transfers verbatim.** v1's "this is the gap" was an artefact of
having adopted the Rosenfeld integer frame; it is withdrawn.

## 3. The engine that carries the n=11 proof is primality-free  `[PROVED]`

The n=11 proof does not turn on the pair table as such. It turns on **one unclaimed
slot**: `v33:325-327` — *"Slot $I_9$ is not covered by any pair's AP-limit witness
labels"* — and `:811-812` — *"The algebraic structure of the prime modulus 11 …
forces the unclaimed slot $I_9$"*. Everything downstream (PSM, Chain A, Chain B,
Universal Blocking, the static core, shift invariance) is `ℚ`-interval arithmetic.

The corollary that `I_{n-2}` is unclaimed needs no primality. Slot `I_s` carries
witness label `m = s+1`; runner `j` claims it iff `jm ≡ ±1 (mod n)`. At
`s = n-2`, `m = n-1 ≡ -1`, so `-j ≡ ±1`, so `j ∈ {1, n-1}` — and both are excluded,
runner 1 opening the window and runner `n-1` being the pacemaker. **One line, every
`n`.** At `n = 8` this is slot `I_6 = [49/56, 55/56]`, empty when `a_1 = 1` and
opening exactly when `a_1 < 1` — the same large-ratio trigger as `I_9` at `n = 11`.

So the correct statement of the collapse is narrower than v1's: **the pair table
collapses; the unclaimed-slot engine does not.**

## 4. The n=8 architecture, built  `[PROVED — exact rational arithmetic]`

`experiments/n8/pacemaker_n8_v1.py`. Translation of v33 §2 term for term:
`a_i = 7e_i/e_7`, `a_7 = 7`; `B_{j,k} = [(8k+7)/(8a_j), (8k+9)/(8a_j)]`;
`I_s = [(8s+1)/56, (8s+7)/56]`, `s = 1,…,6`; `W_ref = [1/(8a_1), 7/(8a_1)]`.
The counts are the general-`n` counts — `n-2` slots against `n-3` free runners,
surplus exactly 1, at every `n` (9 v 8 at `n = 11`; 6 v 5 at `n = 8`).

AP-limit ownership at `n = 8`, every figure exact and in units of `1/56`:

| slot | witness | covering chain | tight touch |
|---|---|---|---|
| `I_1 [9,15]` | `2/8` | `r6[9,10.5] r5[9.8,12.6] r4[12.25,15]` | **none** |
| `I_2 [17,23]` | `3/8` | `r3[17,21] r5[21,23]` | **`3/8`, pair (3,5)** |
| `I_3 [25,31]` | `4/8` | `r2[24.5,31.5]` alone | **none** |
| `I_4 [33,39]` | `5/8` | `r5[33,35] r3[35,39]` | **`5/8`, pair (3,5)** |
| `I_5 [41,47]` | `6/8` | `r4[41,43.75] r5[43.4,46.2] r6[45.5,47]` | **none** |
| `I_6 [49,55]` | `7/8` | — | empty at `a_1 = 1` |

The three even-label slots are unclaimed for a **different** reason from `I_6`: their
witness `m/8` has `gcd(m,8) > 1`, so no runner sits at a boundary there — and they are
covered by chains with strictly positive overlap, i.e. with slack. That is the
`n = 8`-specific feature, and it is a **surplus**, not a loss: at `n = 11` all eight
interior slots are covered with a single touching point each and the configuration is
critically braced, whereas at `n = 8` runners 2, 4 and 6 are over-provisioned relative
to the pacemaker slots.

## 5. A flag on v33 Lemma 5.1, not a refutation

`v33:373-376` — *"When $a_j\ge j+1$, runner $j$'s zeroth bad interval
$B_{j,0}=[10/(11a_j),12/(11a_j)]$ lies entirely to the right of its primary slot
$I_{j-1}$… The four cases $j=2,3,4,5$ expose the boundaries $12/110,\ 23/110,\
34/110,\ 45/110$"*. Against its own `Theorem 4.2` table at `:314-320`, which assigns
pair `(2,9)` the slots `I_4, I_5` — not `I_1`.

The arithmetic: at the in-range value `a_2 = 2`, `B_{2,0} = [10/22, 12/22] =
[50/110, 60/110]`, which already lies entirely to the right of `I_1 = [12/110,
21/110]`. So the mechanism as written does not separate `a_2 ≥ 3` from `a_2 = 2`.
Under Theorem 4.2, `B_{2,0}` straddles `I_4 = [45,54]/110` and `I_5 = [56,65]/110`.

**Scope of this flag.** Appendices A.1–A.8 carry the actual enumeration and have
**not** been read; the summary paragraph may be mis-indexed while the lemma stands.
Recorded because the `n = 8` translation cannot build a sign-class decomposition on
Lemma 5.1 until the intended indexing is fixed — and because
`TIGHT_INSTANCES_v1.md` §5 shows the naive `n = 8` analogue of the lemma is **false**.

## 6. Where the route now stands

| n=11 component | status at n=8 |
|---|---|
| Coupling Principle | **transfers verbatim** (§2 — v1 said otherwise) |
| unclaimed slot `I_{n-2}` | **transfers, primality-free** (§3) |
| Complementary Pairs table | **fails** — 4 witnesses, 7 speeds, `(ℤ/8)ˣ` exponent 2 (§1) |
| Sign-range containment (`a_j ∈ (j-1,j+1)`) | **false in the naive global form** — two counterexamples (`TIGHT_INSTANCES_v1.md` §5) |
| target `GF(I_s) > 0` | **false at n=8** — two off-hyperplane witnesses (`TIGHT_INSTANCES_v1.md` §4) |

The two failures in the bottom rows share one cause and one repair: both are broken
by tight instances, every tight instance sits outside the residual case, and the
residual case is where a measure argument is available. The next object is therefore
**not** a replacement for complementary pairs. It is: *does `inf{M(T) : T residual}`
exceed `1/8`* — and if so, the v33 architecture runs on the residual case unmodified.

## 7. Ledger

Decided cells: 2 of 135 (unchanged — nothing here touches the Rosenfeld sector count).
Retracted: v1 §4's Coupling-Principle gap. Established: the engine transfers, the pair
table does not, the target functional must change, and the split that makes all three
consistent. Owed: the residual-infimum question, and Appendices A.1–A.8 of v33.
