# Transport Completeness for n = p^k: Structural Invariant
## v1 — Session B (2026-03-10)

**Purpose:** Capture the structural invariant that separates dangerous fibres from
safe ones for n = p^k, k ≥ 3. One definition, one theorem, one proof obligation.

---

## 1. Transport-Complete Floor States

Let n = p^k (p odd prime, k ≥ 2), E_fix = all φ(n) unit runners (U-FORCE).
For b ∈ B_div, define the floor-state vector τ(b) = (t_e)_{e unit}, t_e = ⌊b/e⌋.

**Definition TC.** τ(b) is *transport-complete* if ∪_{e∈E_fix} bad(e, t_e, n) = Z_{p^k}.

A fibre b is safe iff τ(b) is NOT transport-complete.

---

## 2. P-Alignment: The Necessary Condition

**Lemma TC-1 (P-alignment necessity).**
If τ(b) is transport-complete, then for each non-unit residue r = jp
(j = 1,...,p^{k-1}-1), some runner in E_fix covers jp.
By Lemma CO-1: unit runner e_u covers non-unit residue jp only when
p | t_{e_u} or p | (t_{e_u}+1), i.e., t_{e_u} ≡ 0 or p-1 (mod p).

**Define:** E_aln(b) = {e unit : t_e ≡ 0 or p-1 (mod p)} — the p-aligned runners at b.

TC requires: for each jp, some e_u ∈ E_aln(b) has bad(e_u, t_{e_u}, n) ∋ jp.
This is a MATCHING condition: E_aln(b) must cover all p^{k-1}-1 non-unit residues.

---

## 3. Affine Coset Synchrony: The Conjectured Characterisation

Write each unit as e = αp + β with α = ⌊e/p⌋ ∈ {0,...,p^{k-1}-1}, β ∈ {1,...,p-1}.

**Definition ACS.** The floor state τ(b) has *affine coset synchrony* if t_e depends
only on α = ⌊e/p⌋ (not on β = e mod p): for all pairs e,e' with ⌊e/p⌋ = ⌊e'/p⌋,
t_e = t_{e'}.

Equivalently: ACS holds at b iff ⌊b/(αp+β)⌋ = ⌊b/(αp+β')⌋ for all α and all β,β'.

**When ACS holds:** ACS in coset α holds for b ∈ [α(αp+p-1), (α+1)(αp+1)).
Width = 2α+1. These intervals for different α are DISJOINT (different magnitude ranges).
So only one coset can be ACS-active at any b. FULL ACS (all cosets) requires b < 2,
which is outside B_div. Full ACS never holds in B_div. [Key correction to the
"s=1 period is globally ACS" picture; see §5.]

---

## 4. The Correct Structural Theorem (Conjectured)

The user's insight is correct in spirit but the right invariant is not global ACS.
The correct statement is:

**Conjecture TC-2 (Sparsity of transport-complete fibres).**
For n = p^k under U-FORCE B3b:

    |{b ∈ B_div : τ(b) is transport-complete}| ≤ C · L/p

for some constant C = C(k) depending only on k (not on p or j-values).

Since |B_div| ≈ (n-2)L/n ≈ L and φ(n) = p^{k-1}(p-1):
safe fibres ≥ |B_div| - C·L/p ≥ L(1 - C/p) >> p^{k-1}(p-1) = φ(n)
for all sufficiently large p. Tier 2 closes.

**Why this should hold:** TC requires E_aln(b) to cover all p^{k-1}-1 non-unit
residues. The p-aligned fraction of unit runners is ≈ 2/p (floors ≡ 0 or p-1 mod p).
With φ(n) = p^{k-1}(p-1) runners, typically 2p^{k-2}(p-1) ≈ 2p^{k-2}p are p-aligned.
For these to cover all p^{k-1}-1 non-unit residues via the bad-set matching, the
floors must satisfy CRT conditions — restricting b to a sub-lattice of density ≤ 1/p.

---

## 5. Correction: The F_p×-Orbit Structure (Session B, Verified Empirically)

**The "unique s=1 dangerous period" hypothesis is FALSE.**
Numerical check (p=3,5,7): at b = sM (M = L/p), floor of unit e = αp+β is
    q_e(s) = αs + ⌊βs/p⌋.
Coverage at s=0 is NOT transport-complete. Coverage at every s ∈ {1,...,p-1}
IS transport-complete. Verified for p = 3, 5, 7.

**The actual structure is an F_p×-orbit:**
    Cov(s) = s · Cov(1)  (mod p²)
where Cov(s) = ∪_e bad(e, q_e(s), p²) is the coverage at b = sM.

So all (p-1) non-zero chamber-entry states are dangerous, related by scaling.
The "unique dangerous period" was a model artefact. The true dangerous set is
a full multiplicative orbit of size p-1.

**Drop-pair dependence:** Which full periods [sM,(s+1)M) are "fully unsafe"
(TC for every fibre in the period, not just the entry) depends on which two
non-unit runners are dropped. Empirically (p=5): dropping {p,2p} makes
s∈{1,3} fully unsafe; dropping {p,4p} makes s=2 fully unsafe.

**What this kills:** The proof route "s=1 is the unique dangerous period;
all other p-1 periods are safe" is dead. Dangerous geometry is richer.

**What survives:** Modes A/B/C are correct. The correct new question is:
    how quickly does TC decay as b moves away from a chamber entry sM?

---

## 6. Revised Proof Obligation

**Dangerous fibres = TC fibres.** We know:
- At each chamber entry b = sM (s = 1,...,p-1): τ(b) is TC.
- After b moves away from sM: TC may decay. Rate of decay = unknown.

**The PERSISTENCE THEOREM (to prove):**
For each s ∈ {1,...,p-1}, there exist at most P(p,k) consecutive TC fibres
starting from b = sM, where P(p,k) << |B_div|/φ(n).

**Why persistence must be bounded:** As b increases from sM by δ, some runner e
with gcd(e, L/sM) = ... has its floor increase from q_e(s) to q_e(s)+1. This
changes bad(e, ·, p^k) — potentially exposing a residue. The first floor change
occurs at b = e·(q_e(s)+1). If this change breaks TC: P = e·(q_e(s)+1) - sM.
For the smallest unit runner e_min = 1: q_1(s) = s (floor of b=sM at speed 1
is sM), and e_min·(s+1) - sM = (s+1) - sM = 1 - M(s-1). For M >> 1: this is
negative — meaning the first floor change of e_min is already BEFORE sM (it
last changed at sM - (sM mod 1) = sM). So e_min = 1 always has its floor
AT sM. Its floor changes at EVERY integer. So at b = sM+1: q_1 = sM+1 ≠ sM.
This immediately changes bad(e=1, ·, p^k) = {-q_1, -(q_1+1)} mod p^k.

**Concrete consequence:** If the change bad(1, sM, p^k) → bad(1, sM+1, p^k)
exposes some residue, TC breaks at b = sM+1. TC-fibres-per-entry = 1.
Total TC fibres ≤ (p-1) entries × 1 = p-1 << φ(n) = p^{k-1}(p-1). Done.

**What needs checking:** Is bad(1, sM, p^k) ∪ rest ≠ bad(1, sM+1, p^k) ∪ rest?
Specifically: does the residue -sM - 1 (mod p^k) that bad(e=1) stops covering
at b = sM+1 get covered by some other runner?

**Next file:** `lrc_persistence_decay_v1.md` — check whether TC breaks at b=sM+1
for n = p^3, then extract the general persistence bound.
