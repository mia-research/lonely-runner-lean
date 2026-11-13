# N8_AUDIT92_RESULT — the 92 three-cell-missed controls: fully certified, two shared lemmas

Companion note to `N8_ONE_FAST_REJECTION.md` (2026-11-13; the delegated task from that note's "remaining obligation"). Artifacts: `experiments/n8/onefast_audit/audit92_mechanisms.py/.out`, `audit92_families.py/.out`, `audit92_pinchreach.py/.out`, `audit92_population.jsonl`. Exact Fractions throughout; nothing existing modified.

## Headline

**All 92 controls certify — mechanism census [T 92/92], the residual class is empty:** pinch theorem 5/92, j=0 pair 21/92, width handoff 64/92, higher-j 2/92, uncertified 0/92. Controls: 0 false fires on any common-rejection verdict; the 73 chain boxes probed (embeddings as six-slow cores with d = t₆, plus offsets) — every probe wide or exactly sound.

## The two shared lemmas (both corollaries of `clear_of_integer_gap`, already Lean)

**Lemma SF (seam-flank pair; covers 90/92, including all 5 pinch cases).** Cells [a,b], [c,e], a ≤ b < c ≤ e, where the **seam** is one slow reading ρ's blocked zone: b = (8M−1)/(8ρ), c = (8M+1)/(8ρ) — the gap is exactly 1/(4ρ). Rate: 1/4 ≤ d(e−a) and d ≤ 3ρ (equivalent to d(c−b) ≤ 3/4 by the seam identity). Retention: per-reading band inequalities keep both cells clear. Sub-shape **SS (scissors)**: a and e are another reading σ's single clear-zone edges (8L+1)/(8σ), (8L+7)/(8σ) — the rate hypotheses collapse to the **ratio band σ/3 ≤ d ≤ 3ρ** plus the two containment inequalities (8L+1)ρ ≤ (8M−1)σ, (8M+1)σ ≤ (8L+7)ρ. SS covers 57/92 and legitimately co-certifies 149/238 pair-controls and 2,196 wide controls (co-certification, not contradiction — both certificates exact, same loneliness conclusion).

**Lemma LS (lap-shift; the 2 residuals).** b, c are consecutive clear-zone entries of ONE reading (c − b = 1/ρ), d(e−a) ≥ 5/4, d ≤ 7ρ/4; a tie-seam singleton left cell is allowed (b = ρ₅'s lap-1 exit = ρ₁₁'s lap-4 entry, exactly 3/8); certified at j = 1. These 2 controls have NO j=0 pair — forced by their exact j-censuses (min j = 1), so the residual is closed by classification, not left open.

## Family table (canonical certifying pairs)

- **P, 5**: [1/8,1/8] (reading-1 lap-0 entry tied with reading-7 lap-0 exit) + [9/56,7/40]; ρᵢ = 7 = w; pair covers d ∈ [5,21], wide at 35/2 → all d ≥ 5.
- **S (seam+scissors), 37**: e.g. (1,3,4,5,7,8) d = 129/16: a = 25/56 (σ=7, L=3), b = 15/32, c = 17/32 (ρ=4, M=2), e = 31/56; band [7/3, 12]; handoff cell [25/56,15/32] → wide at 56/5 → all d ≥ 7/3.
- **M (seam+mixed), 34**: e.g. (1,2,3,5,7,8) d = 129/16: a = 9/56, b = 7/40, c = 9/40 (ρ=5, M=1), e = 15/64 (σ=8 lap-1); d ≤ 15, d(e−a) = 4257/7168 ≥ 1/4.
- **X (plain j=0, four distinct readings), 12**: e.g. (1,2,5,6,7,8) d = 129/16: A = [9/40,15/64] (ρ=5, σ=8), B = [17/56,5/16] (ρ=7, σ=6).
- **H (lap-shift), 2**: (1,4,5,6,7,11) d = 14 and (1,4,6,7,10,11) d = 14.

Population note (feature, not a gap): all 92 come from the 462 integer cores (0/500 grid cores; 24 distinct cores, top (1,2,5,6,7,8)×6).

## Structural read

The recurring shape is a **ratio band between a blocked-zone reading and a clear-zone reading** (σ/3 ≤ d ≤ 3ρ) with two containment inequalities — the same two-reading band structure as the pinch theorem's d ≤ 3w and the E812 one-ratio conflict. One mechanism at another scale, consistent with E838's identification.
