# CT.1 Gap Analysis — 2026-04-14

## Status
CT.1 (Companion-Residue Exposure Mechanism / Chain-Transfer Control) is the single
remaining analytical gap blocking Lemma 5.2 (the dropped-unit bridge) for general prime n.

## What is CT.1?

**Setup:** prime n, |E_non| = n-2 runners all unit mod n, one missing unit class d ∉ R_non.
Target: r_d = -d^{-1} mod n. Base fibre b_0 = L/n fully covered (assumption for hard case).
Lemma 5.1b gives: some residue r* has multiplicity exactly 1 at b_0 (sole cover e*).

**CT.1 asserts:** The thin-burden chain starting at r* terminates with a safe fibre
(some fibre b ∈ B_div where some residue is uncovered). Empirically: depth ≤ 1 always.

## What's Proved vs. Open

### PROVED (sub-case 1): Floor-0 argument for small speeds

If E_non ⊂ {1,...,n-1} (all retained speeds < n), then at b_0 = L/n:
- All runners have floor state 0 (since e < n → floor(e/n) = 0)  
- bad(e, 0, n) = {0, -e^{-1}} for each unit runner e
- Since e ≢ d mod n (d ∉ R_non): -e^{-1} ≢ r_d
- Also: 0 ≢ r_d (since r_d ∈ {1,...,n-1})
- **Therefore: r_d ∉ bad(e, 0, n) for ANY e ∈ E_non → r_d uncovered at b_0 → x_0 ≥ 1.**

This is a complete, clean proof for E_non ⊂ {1,...,n-1}. No CT.1 needed.

### PROVED: Lemma 5.1b (base-fibre thinness)
If b_0 fully covered (prime n, |E_non| ≤ n-2): some r* has mult-1.
Proof: total incidence I_0 = 2|E_non| ≤ 2(n-2) < 2n; can't have all mults ≥ 2.

### PROVED: Shift symmetry
For any runner f: bad(f, b_last) = bad(f, b_0) + 1 (mod n), where b_last = (n-1)L/n.
Proof: floor at b_last = f - q_f - 1, and (q(n-1)+ρ-1) ≡ -(q+1) mod n, so
LOW at b_last = -(-(q+1)) · ρ^{-1} = (q+1)ρ^{-1} = 1 - (-q·ρ^{-1}) = 1 + LOW(b_0) mod n. ✓

### OPEN: CT.1 for large-speed case

When some e ∈ E_non has e ≥ n (so q_e ≥ 1 at b_0): some large-speed runner can cover
r_d at b_0 via its non-zero floor state. Lemma 5.1b applies (thin r* exists), but
the full proof that r* is eventually exposed requires CT.1.

## Three Routes for CT.1

### Route (A): Coincident floor-reset counting
After depth-1 transfer, depth-2 requires a NEW runner to gain r_c at exactly the same
fibre b_2 where the transfer runner drops r_c. This requires two SIMULTANEOUS floor-reset
events at b_2 with specific residue conditions. Should be rare/impossible for generic speeds.
Status: **Not yet formalized. Main obstacle: showing the specific arithmetic of LRC speeds
prevents the coincidence.**

### Route (B): Missing unit forces eventual exposure
The missing d ∉ R_non means: at floor states ≡ 0 mod n, r_d has NO coverage (proved above).
Within B_div, floor state 0 appears (for small-speed runners) or is "effectively absent"
for large-speed runners. The key: d-coverage is always "borrowed" from non-d residue classes,
and this borrowed coverage has a structural gap.
Status: **Partial. Proved for small-speed case. Large-speed case unresolved.**

### Route (C): Terminal floor-state analysis
The shift symmetry (bad at b_last = bad at b_0 + 1) shows the thin set evolves.
Under full obstruction T(b) = 4 thin residues everywhere. T(b_last) = T(b_0) + 1.
The thin set must "travel" by +1 from start to end. Could this be exploited?
Status: **Shift symmetry is proved but no contradiction extracted yet.**

## Most Promising Path Forward

**Combination approach for prime n:**

For sub-case "all speeds < n": floor-0 argument (complete).

For sub-case "all speeds in (n, 2n)": at b_0, runners have floor state exactly 1.
Coverage of r_d as HIGH at floor 1 requires ρ = 2d. Coverage as LOW requires ρ = d
(IMPOSSIBLE since d ∉ R_non). So if no runner has ρ = 2d: r_d uncovered at b_0 → done.
If runner with ρ = 2d exists: r_d covered at b_0. But then at the start of B_div,
specifically in [L/n, L/(n+2d)), runner (n+2d) hasn't yet reached floor 1 → r_d may
be uncovered in [L/(n+2d), 2L/(n+2d)).

This sub-case analysis seems doable but requires careful work through floor-state
arithmetic for each speed range.

## On Architecture Elegance

Current structure: Lemma 5.1b (static, 3-line proof) + CT.1 (dynamic, hard).

Possible unified formulation: **"Direct Coverage Exhaustion Theorem"**
- For any E with d ∉ R_non: coverage of r_d in B_div by any runner has BOUNDED duration.
- If the coverage intervals of all runners can't tile all of B_div simultaneously: safe fibre.
- This subsumes 5.1b + CT.1 into one statement, but the proof splits the same way.

The floor-0 sub-case is genuinely separable and cleaner. The thin-burden chain handles
the remainder. I don't see a way to merge them into a single mechanism that is simpler
than the two-step approach — the two steps address genuinely different proof obstacles.

## Model Performance Notes

- DeepSeek r1:14b: times out on multi-step proof attempts (>120s). Short verification ok.
- Gemma4:26b: very slow on this hardware (>120s for any response). Not useful for proofs.
- Qwen3.5:4b: useful for quick verification, format checks, simple math. 
- Recommendation: CT.1 requires human-level insight. Local models not adequate for this.
