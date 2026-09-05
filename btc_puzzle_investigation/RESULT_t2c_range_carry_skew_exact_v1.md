# RESULT — the T2c range→carry skew is now EXACT: full law $P_k$, $k=127\ldots146$, with the public interval map (deterministic, no sampling)

**Date 2026-08-21. Grade: `[VERIFIED — exact integer counts; decidable artifact]`** for the
$P_k$ table and interval maps; the carry sign-law lemma is `[PROVED — 3-line, from $|a|,|b|<n$]`.
Deterministic first pass per `ROADMAP_REDIRECT_v3` (no prereg needed; **no leakage/advantage claim
is made** — that would need `experiment-designer`). Script: `t2c_range_carry_skew_exact_v1.py`
(exact `int`/`Fraction` only; log `.log`). Extends `REVIEW_eis_carry_framing_suppression_v1.md`
(sampled 40k) and `RESULT_eis_carry_2d_dlp_reduction_v1.md` (ε_LBE = overflow bit of the GLV halves).

## Object

$P_k = \Pr[\varepsilon_{LBE}=1 \mid d \text{ uniform in } [2^{k-1}, 2^k)]$, where $(a,b)=\mathrm{glv}(d)$
is the balanced Babai decomposition on $L=\{(x,y): x+\lambda y \equiv 0 \ (\mathrm{mod}\ n)\}$ and
$\varepsilon_{LBE} = [(a \bmod n)+(b \bmod n) \ge n]$ — the carry bit the ARSENAL tools 3/5/7 consume.
The range is PUBLIC (puzzle keys live in exactly such ranges).

## The exact mechanism (proved + machine-verified)

**Lemma (carry sign-law).** For secp, $|a|,|b| \le 2\cdot 2^{128} \ll n$, so
$$\varepsilon_{LBE} = \begin{cases} 0 & a\ge 0,\ b\ge 0\\ 1 & a<0,\ b<0\\ [a+b\ge 0] & \text{mixed signs.}\end{cases}$$
*Proof:* $a \bmod n = a + n[a<0]$ etc.; $a+b+2n \ge n$ always, $a+b \ge n$ never. Verified 0/200,000
mismatches against the direct definition over the full range.

**Piecewise structure.** Between Babai rounding boundaries ($c_1(d)=d\,\mathrm{GB2}_y/\mathrm{GDET}$ or
$c_2$ at half-integers — two arithmetic families of rationals, spacing $\approx 2^{128}$), the correction
$(m_1,m_2)$ is constant, so $a(d)=d-m_1$ (slope 1) and $b=-m_2$ (constant). Hence $\varepsilon$ is
constant on $d$-intervals cut only by the rounding boundaries and the two integers $m_1$ ($a=0$) and
$m_1+m_2$ ($a+b=0$). The counter enumerates these cuts exactly (Fractions) and sums integer counts;
every elementary run is endpoint-verified by direct $\varepsilon$ calls.

**Validation.** (V1) exact counter == full enumeration on 3 small ranges (10k+5k+3k, 0 diff);
(V2) fresh 200k samples match the exact values at $k\in\{129,135,140\}$ to $0.08$–$0.20\,\sigma$;
(V3) local `glv`/`eps` identical to `t2c_range_glv_structure_v1` on 500 random $d$.

## Results — the exact law $P_k$

| $k$ | $P_k$ | $P_k-\tfrac12$ | | $k$ | $P_k$ | $P_k-\tfrac12$ |
|---|---|---|---|---|---|---|
| 127 | **0** | $-\tfrac12$ | | 134 | 0.50169 | +0.0017 |
| 128 | **0.87849** | +0.3785 | | 135 | 0.51142 | +0.0114 |
| 129 | **0.81044** | +0.3104 | | 136 | 0.49821 | −0.0018 |
| 130 | **0.29080** | −0.2092 | | 137 | 0.49439 | −0.0056 |
| 131 | 0.64432 | +0.1443 | | 138 | 0.50182 | +0.0018 |
| 132 | 0.38135 | −0.1186 | | 139 | 0.50071 | +0.0007 |
| 133 | 0.49063 | −0.0094 | | 140 | 0.50043 | +0.0004 |
| | | | | 142 | 0.50041 | +0.0004 |
| | | | | 145 | 0.5000012 | +1.2e−6 |
| | | | | 146 | 0.4999936 | −6.4e−6 |

Sampled predecessors confirmed (129: 0.809→0.81044 exact; 135: 0.511→0.51142). New structure the
sampling missed: $P_{128}=0.878$ is the **maximum** skew (stronger than 129); $P_{130}$ lands
**below** ½; the approach to ½ is **oscillatory**, not monotone (130−, 131+, 132−, then alternating),
roughly halving per $k$ beyond 134 — a Kronecker-discrepancy signature of the line $(d,0) \bmod L$
equidistributing in the fundamental domain.

**The public interval map (stronger than a marginal bias).** At $k=129$ the range splits into exactly
four runs (fractions of the range, exact): $\varepsilon=1$ on $[0, 0.0812) \cup [0.2708, 1)$ and
$\varepsilon=0$ on $[0.0812, 0.2708)$ — i.e. the FUNCTION $d\mapsto\varepsilon_{LBE}(d)$ is publicly
determined (not merely biased) on 81.04% of that key range. Same structure at $k=128$ (87.85%) and
$k=130$ (29.08% + interval map). This is the T2c dichotomy's answer at these $k$: neither "constant on
the strip" nor merely "varies" — it is **constant on a public partition of the strip** into 3–4 runs.
(Conditionality kept straight: the partition tells you $\varepsilon$ *given* a sub-range for $d$; the
sub-range of the actual key is not public.)

## Honest leverage read (stated straight, both directions)

- **Structure, not nothing:** a public range → public exact carry partition is a genuine, exact,
  scale-free range→carry coupling — the REVIEW's "third, live regime," now exact, with the full
  $k$-curve and the $\sqrt n$-transition shape ($P\equiv 0$ for $k\le 127$; jumps to 0.878 at 128;
  oscillates to ½ by ~145).
- **Applicability, split by target class** (solved set = the 82-key csv, max #130; every 5th puzzle
  from 135 up is exposed-pubkey/kangaroo-runnable, the rest address-only — `KNOWN_FACTS` §10):
  - Exposed-pubkey live targets $k\in\{135,140,145,\ldots\}$: exact skews $+0.011$, $+0.0004$,
    $+10^{-6}$ — at $k\ge 140$ the prior carries $\lesssim 10^{-6}$ bits; even a FREE oracle for the
    actual key's $\varepsilon$ would cut the search range to $\max(P_k,1-P_k) = 0.511$ of it
    (~0.03 bits at #135). **No exponent movement.**
  - The strong-skew window $k\in[128,132]$ DOES contain unsolved keys (#131: $P=0.644$,
    #132: $P=0.381$) — but they are **address-only** (hash barrier: no public point exists to
    evaluate anything against), so the partition has nothing to compose with there either. It WOULD
    matter if a #131/132-class key ever gained a public point, or if any future channel observes
    $\varepsilon$ (the biased prior is then worth $1-H(P_k) \approx 0.056$ bits at #131).
- **What would change this:** a public point for a key in $[2^{127}, 2^{133})$, or an arsenal tool
  whose cost is super-linear in the *entropy* of $\varepsilon$ rather than in range width. Neither
  exists today (tools 3/5/7 consume one bit; the map above supplies it exactly only at $k\lesssim132$).

## Provenance / scope

Deterministic map of a public constraint through a public map; no $d$ sampled secretly, no leakage
null (per roadmap). The $P_k$ are exact integer counts conditional on (i) the sign-law lemma [proved],
(ii) Babai coordinate-rounding boundaries being the only discontinuities [structural; endpoint-verified
on every run; V1-enumerated]. Not a closure of T2c: the **joint/multi-point (N15)** and
**√6-composition** questions remain open (the latter now with a precise object: compose the public
partition at $k\in[128,132]$ — or the $k=135$ bias — with the endomorphism kangaroo).
