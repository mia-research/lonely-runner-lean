
# LBE v2 Formulation: Deficit-Frequency Fingerprinting + Phase Accumulation

## Deliverable

A complete pre-registration document (`PREREG_localized_bit_extraction_v2.md`) with two experiment arms, ready for the experiment-designer gate.

## Session steps

### 1. Review and digest existing infrastructure
- Read `PREREG_localized_bit_extraction_v1.md` and `RESULT_localized_bit_extraction_v1.md` for the v1 template, null structure, and deviations
- Read `RESULT_row_budget_lowtail_v3.md` for the deficit-frequency set machinery
- Read `RESULT_subrayleigh_deficit_arithmetic_scatter_v2.md` for the current N7 state
- Read the relevant M19/M20 results for existing bounds

### 2. Design Arm A: Deficit-frequency fingerprinting
**Core conjecture**: The identity of which frequency rows $(b,c)$ are in the character's low tail is not fully random — it carries residual information about the scalar $d$ beyond what the group-automorphism null preserves.

**Readout $B$**: For each point $P_d$, compute a "deficit-aligned fingerprint" — a vector of single-point phase values evaluated at the deficit-carrying frequency set (the $(b,c)$ where the character's $|U(a,b,c)|$ is most suppressed relative to matched nulls). The frequency set is precomputed from the public curve (not from $d$), so $B$ is a function of $(x_d, y_d)$ evaluated at a fixed public frequency set.

**Target $\tau$**: mu_6-orbit rank of $d$ (multiplicatively adapted — this was the v1 mismatch). Also $d \bmod 3$ and $d \bmod 7$ as secondary targets.

**Null**: Group-automorphism relabel $F(P_{t \cdot d}) \leftrightarrow \tau(d)$, preserving all geometric structure and the exact frequency set.

**Power**: Quantify from the 8% excess × $p^2$ rows. At $p \sim 10^5$, the frequency set has $\sim 10^{10}$ rows — even a per-row signal of $10^{-5}$ could be detectable with coherent accumulation.

**Key technical challenges**:
- The frequency set must be computed without knowing $d$ — it comes from the public character sum structure
- The single-point phase $e_p(b x_d + c y_d)$ is provably uniform by Weil — the signal must live in the **joint pattern** across frequencies, not in any single frequency
- Must avoid the residue-vs-component tautology (Retraction #24)

### 3. Design Arm B: Non-unitary phase-moment accumulation
**Core conjecture**: Coherent phase accumulation over the deficit-carrying frequencies breaks the Weil noise floor, because the deficit is an $\ell^1$ phenomenon (below the $\ell^2$ surface pinned by Parseval).

**Readout $B$**: Coherent accumulation $S_d = \arg\max_\phi |\sum_{(b,c) \in D} e_p(b x_d + c y_d) \cdot e^{i\phi}|$ where $D$ is the deficit-frequency set and $\phi$ sweeps over alignment angles. This is the maximum coherent sum — the best possible phase alignment of the single-point contributions at the deficit frequencies.

**Target $\tau$**: Same as Arm A (mu_6-orbit rank, $d \bmod 3$, $d \bmod 7$).

**Null**: Same group-automorphism relabel.

**Key advantage over Arm A**: This is explicitly non-unitary — it doesn't project onto any Fourier basis. The deficit is an $\ell^1$ effect; coherent accumulation is the natural $\ell^1$ readout.

### 4. Design controls and firing criteria
- Forced-null control (readout of a constant function — must give $z = 0$)
- Power plant: inject a known mixing fraction $\epsilon$ into the target and verify the statistic detects it above $\epsilon_{\min}$
- Firing criterion: Holm-Bonferroni over the joint (Arm A + Arm B) cell set at FWER 0.01
- Falsification cells: pre-committed null arms that must fire
- Replication: 4/5 primes criterion from v1

### 5. Address symmetry-mismatched null trap
- Verify by construction that every readout's invariances are preserved by the null
- x-based readouts are even in $d$ — either (a) use only y-based or joint readouts, or (b) match on $\{d, n-d\}$ orbits explicitly
- Document the invariance-preserving argument in the PREREG

### 6. Write the PREREG
- Follow the v1 template structure
- Include all mandatory components: readout, target, null, power, falsification
- Pre-commit the verdict table (A1–A7 style from the Semaev PREREG)
- Run the experiment-designer gate before any data collection

### 7. Implement the harness (if PREREG passes gate)
- Build on `lbe_harness_v1.py` / `lbe_run_v1.py` where possible
- New components: deficit-frequency set computation, coherent phase accumulation
- Test at small primes first ($p \leq 1000$) before scaling

## Key files to read/create
- **Read**: `PREREG_localized_bit_extraction_v1.md`, `RESULT_localized_bit_extraction_v1.md`, `RESULT_row_budget_lowtail_v3.md`, `RESULT_subrayleigh_deficit_arithmetic_scatter_v2.md`, M19/M20 result files
- **Create**: `PREREG_localized_bit_extraction_v2.md`
- **Create (after gate)**: `lbe_harness_v2.py`, `lbe_run_v2.py`

## Risks and caveats
- The Weil bound is a hard floor for single-frequency readouts — the design banks on multi-frequency coherent accumulation breaking this floor, which is unproven
- Detection floor at $p \sim 10^5$ is $e_{\min} \sim 0.02$; any effect that decays like $1/\sqrt{p}$ is undetectable at secp scale
- This is the direction "most vulnerable to symmetry-mismatched nulls manufacturing false positives" — the null design is load-bearing
