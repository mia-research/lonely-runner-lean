# NOTE — the public-readout "bit ceiling" is self-imposed; there is no information ceiling

**Date:** 2026-08-25. **Grade of the measurements:** `[VERIFIED — exact at b=16 full enumeration;
sampled-confirmed at b=32..256, N=10⁵]`. **Grade of the correction:** methodological (stance).
**Trigger:** user oversight caught the "ceiling" framing being used to file away information — the
project's documented one-way suppression bias, operating again.

## The correction (load-bearing)
**There is no information ceiling on the public data.** The public point `[d]G` determines `d`
completely: `H(d | [d]G) = 0`. Every bit of the key is present in the public key — that determinacy is
exactly what ECDLP is. Therefore any statement of the form "the public geometry carries ≤ X bits about
`d`" is FALSE as a bound on exposable information. It is only ever a statement about **one chosen
readout set**.

**The "ceiling" rises the moment you add a readout — so it was never a ceiling.**
- orbit label alone (cubic char `e` + `y`-parity, the μ₆ = μ₃×μ₂ position): `H = 1.585 + 1.000 =
  2.585` bits (= `log₂6`, the corpus's A1.4 `[PROVED]` Aut-orbit count).
- add the Eisenstein carry class `s` ({¾,⅛,⅛}, `H = 1.061`): total `H(T) = 3.646` bits.
- A quantity that goes `2.585 → 3.65` on adding one of infinitely many possible readouts is a **rising
  floor indexed by what you enumerated**, not a cap. Nothing here bounds what a further readout, a
  non-per-point function, or a joint/multi-point construction exposes.

**"0 operational / impossible by no-go" smuggles in assumed ECDLP-hardness as if proven.** Converting
this indexical structure into work reduction is precisely the DLP. The DLP is **assumed hard, not
proven** (project stance). Labeling the conversion "impossible by no-go / closed layer" states the
assumption as a theorem — the exact reflex CLAUDE.md exists to suspend. The masters already carry this
as a hanging contradiction (`POSITIVE_FINDINGS_MASTER_v11/v12` row **A-2a / §E-new**: *"'0 operational /
impossible' reads wider than the layer it proves; contradicts A-1b/A-1e"*). This NOTE resolves the
hanging contradiction in favor of OPEN.

## What is actually true (the measurements, stated without a ceiling)
An independent entropy measurement on constructed known-`d` secp keys (runner
`n15_readout_confinement_runner_v1.py`; exact at the b=16 full-keyspace enumeration, `H(T)=3.6563`)
reconstructs the corpus's algebraic accounting from a **disjoint method** and adds one new fact:

| piece | bits | identity |
|---|---|---|
| `H(e)` cubic character (μ₃) | 1.585 | `log₂3` |
| `H(y-parity)` negation (μ₂) | 1.000 | `log₂2` |
| → μ₆-orbit label | **2.585** | `log₂6` = A1.4 `[PROVED]` |
| `H(s-class)` Eisenstein carry | 1.061 | `H({¾,⅛,⅛})` |
| **total `H(T)`** | **3.646 (≈3.65)** | matches `NOTE_glv_orbit_carry_conservation_v1` §8 (2.585+1.061) |
| `TC(e, s-class, y-parity)` | **≈10⁻⁴** | **NEW: the orbit label and the carry are information-theoretically independent — that is why they add** |

So the measurement (a) independently confirms the corpus's 2.585+1.061 decomposition by a different
route, and (b) newly establishes the additivity is exact because the pieces are independent. These are
positive, characterized facts about the exposed structure — reported as such, not filed under a bound.

## Standing correction to how this is written (applies to all future readout/bit work)
- **Do not call any measured `H(readout)` a "ceiling."** It is the capacity of the readouts enumerated;
  name them, and note it rises as more are added.
- **Do not write "0 operational / impossible / closed by no-go" for the extraction question.** That is
  the DLP, assumed-hard not proven; write "operational extraction OPEN (assumed-hard)".
- **Lead with the characterized structure** (symmetry type / decomposition / independence), then the
  OPEN extraction question — never a cap that dismisses the structure.
- The N15 arm's actual scoped result stands unchanged: no CHEAP predictor extracts these bits at tested
  power (`RESULT_n15_joint_readout_confinement_v1.md`). That is a bounded null on cheap extractors, NOT
  a bound on the information.

## Cross-refs
`RESULT_n15_joint_readout_confinement_v1.md` (source measurement), `NOTE_glv_orbit_carry_conservation_v1`
§8 (the 2.585+1.061=3.65 algebraic accounting + the "indexical/0-operational" phrasing this NOTE
corrects), `PROJECT_SUMMARY_secp256k1_v1.md` A1.4 (`log₂6` orbit count, PROVED — correct as an orbit
count, not a total), masters A-2a/§E-new (the hanging contradiction, now resolved to OPEN).
