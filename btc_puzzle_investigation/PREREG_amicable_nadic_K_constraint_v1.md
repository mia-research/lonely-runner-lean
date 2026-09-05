# PRE-REGISTRATION — Amicable-pair n-adic K-constraint leakage test (v1)

**Status of this document:** written BEFORE any leakage data. It is a spec, not a result.
**Verdict slot:** **REJECTED AT ITEM 1 — CIRCULAR.** The proposed feature cannot be computed
from public data; evaluating it requires a residue of the secret. Items 2–6 are recorded in the
degenerate form they collapse to, so the same design is not re-proposed.

Grade of every claim below: the circularity verdict is **PROVED** (exact-arithmetic witness,
information-theoretic). The "amicable structure is a real anomalous oracle" statement is
**VERIFIED-scope** (holds on the searched small-prime family). No claim here is an empirical null.

---

## 0. Fixed setup (given, not in question)

- Global CM curve E/Q: `y^2 = x^3 + b` (j=0, CM by Z[omega]).
- Amicable pair (p, n): `#E(F_p) = n` and `#E(F_n) = p`, both prime, p != n.
- Secret DLP on the NON-anomalous side E/F_p: public base point G, public target `Q = [d]G`,
  secret `d in [0, ord_p(G))`. Recover d (or a p-adic digit of d).
- SSSA machinery + the identity `psi([N]Q~) = d*psi([N]P~) + N*psi(K)` are given and validated.
- Established fact (1): N=p (anomalous) => K-term gains valuation => d recovered exactly,
  lift-invariant. This is the live firing control (an anomalous curve solves DLPs it can see).
- Established fact (2): N=n (unit) => K-term corrupts the leading digit; recovery is
  lift-dependent. K (the kernel-of-reduction ambiguity) is unpinned by the p-adic boundary alone.

## 0a. SCOPE (every number below inherits this)

- Curve family: `y^2 = x^3 + b`, b in [1,59]; both primes p,n up to ~600.
- Canonical instance for all worked checks: **b=3, p=199 (#E=211=n), n=211 (#E=199=p)**,
  global rational base point **G=(1,2)** (on E/Q, reduces to non-identity mod both p and n).
- Precision: exact Z/m arithmetic, no floats in any signal path.
- Amicable pairs available at this scale (search, exact point count): >30, e.g.
  b=2 (13,19),(139,163),(541,571); b=3 (199,211),(463,487); b=7 (67,79); b=45 (7,13).
  Amicable pairs are plentiful — the design is NOT starved for trials.

---

## 1. CIRCULARITY / DISJOINTNESS CHECK  (make-or-break; run FIRST)

**Question.** To evaluate the proposed n-adic consistency constraint on the shared CM lift, must
one transport the specific target point Q (equivalently, know d, or the secret's n-orbit residue)
across to the n-adic side?

**Trace.**
1. The constraint that would pin the p-adic ambiguity K_p can only bite on Q if it relates the
   p-adic lift of Q to an n-adic avatar of *the same point* Q. The p-adic K_p (kernel of reduction
   mod p) and the n-adic K_n (kernel of reduction mod n) are a priori INDEPENDENT objects; they are
   coupled only through a shared GLOBAL lift `Q~ in E(Q)` reducing to Q mod p. Absent such a global
   lift, there is no wire from the n-adic side to K_p at all.
2. So the feature needs one of:
   (a) a global rational point `R in E(Q)` with `R = Q mod p` — then reduce R mod n; or
   (b) the n-avatar `Q mod n` directly.
3. **(b) requires the secret.** `Q mod n = [d](G mod n)`. With prime orders,
   `ord_p(G) = n` and `ord_n(G) = p`, which are COPRIME. The public p-side reveals only
   `d mod ord_p(G) = d mod n`. The n-avatar depends on `d mod ord_n(G) = d mod p`. By CRT these are
   independent: **the public p-side data leaves d mod p completely free.** The n-avatar is not a
   function of public data; it is (a component of) the secret.
4. **(a) does not rescue it.** A random Q of order n is not in the reduction image of low-height
   E(Q) generically; if some global R happens to reduce to Q mod p, R is NOT `[d]G` globally
   (d is an arbitrary integer mod n, not the shadow of a global scalar relation), so `log(R mod n)`
   is unrelated to d; and confirming any candidate against d requires d — the small-curve
   "validate against known d" leak. Route (a) is a red herring, not a public feature.

**Decidable witness (exact integers, `scratchpad/circularity_witness.py`, run 2026-08-13):**
On b=3,p=199,n=211,G=(1,2): secrets d1=137 and d2=348 satisfy `d1 = d2 mod 211` (=> IDENTICAL
public target `[d]G mod p = (34,30)` for both) but `d1 != d2 mod 199` (=> DIFFERENT n-avatars
`(145,201)` vs `(191,134)`). One public state, ord_n(G)=199 equally-consistent n-avatars.

**VERDICT: CIRCULAR.** The feature (Q's n-adic avatar, hence any n-adic K_p constraint that bites
on Q) is not computable from public data {E, p, n, global model, G, Q mod p}. It requires d mod p,
which the public p-side does not contain. **Stop.** Items 2–6 below are recorded only in the
degenerate form the circularity forces, to prevent re-proposal.

**Why the amicable structure looked like a lever (positive framing, so it is not re-chased):**
It IS real — the companion E/F_n is genuinely anomalous, an SSSA oracle that solves ANY DLP
*presented on the n-side* exactly. The gap is solely the input port: presenting Q on the n-side is
`Q mod n = [d](G mod n)`, i.e. applying the secret. Amicability supplies an oracle with no public
wire to its input. It buys 0 bits on the transport problem, not because the oracle is weak but
because the wire is the secret.

---

## 2. STATISTIC S  (degenerate form)

Intended: `S = digit_0( psi([n]Q~_n) / psi([n]P~_n) )` computed on the anomalous n-side after
transporting Q, claimed `= d mod p`. **As written, S is not evaluable from public data** — its
input `Q~_n` is `Q mod n = [d](G mod n)`, undefined without d mod p (Item 1). There is no
one-statistic, aimed-at-a-subspace replacement, because the missing quantity is not hidden in a
subspace we failed to project onto; it is information-theoretically absent (CRT-independent of all
public p-side observables). Under the correct null, S is uniform over ord_n(G) values.

## 3. MATCHED CONTROL (null)  — cannot be constructed

A valid matched null randomizes K over its legal coset while preserving curve/reduction/±/orbit
symmetry. Here there is nothing to randomize: the coupling the null must destroy (n-adic pinning of
K_p) does not exist as a public object. The "signal" and its matched null are identical uniform
distributions over the ord_n(G) legal n-avatars. A null that equals the alternative is not a test.

## 4. FIRING PLANT — fires, and its firing localizes the defect

Plant: feed the instrument the TRUE n-avatar `Q mod n` (computed WITH d) and run anomalous SSSA on
the n-side. Pass threshold: recover d mod p exactly, 8/8 trials. This **fires** (it is fact (1) on
the companion). But firing here proves the OPPOSITE of what the design needs: the instrument is
alive *only when handed the secret-dependent input*. The plant is the proof of circularity, not a
green light. (Witness: same script; anomalous recovery on the n-side is exact once the n-avatar is
supplied.)

## 5. POWER  — zero, by construction

Effect detectable from PUBLIC data: **0 digits of d**, detection probability `1/ord_n(G) = 1/199`
on the canonical instance = chance. No number of amicable pairs raises this: each pair adds an
independent unconstrained d mod p. This is not a low-power bound to be improved with more n; it is
an information-theoretic 0 (CRT independence). A design with chance-level power is uninformative —
full stop (per the "cubic-moment null with f=1.0" precedent).

## 6. FALSIFICATION + PRE-COMMITTED OUTCOME TABLE

Falsification of the CIRCULARITY verdict (what would reopen the design): exhibit a procedure taking
only {E, p, n, global model, G, Q mod p} that outputs `Q mod n` correctly for strictly more than
`1/ord_n(G)` of secrets sharing the same public p-side state. The Item-1 witness shows this is
impossible at the canonical instance (identical public state, distinct n-avatars); the same
collision construction generalizes to every amicable pair (orders coprime => CRT independence).

Pre-committed conclusions (fixed before any run):
- Public feature depends on d mod p  => **CIRCULAR / not a leakage test.**  [ACTUAL OUTCOME]
- Public feature independent of Q's n-avatar => proceed to run Items 2–5.  [did not occur]
- Public feature recovers a d-digit at rate > 1/ord_n(G) on matched null => real cross-rep lever.
  [precluded by CRT independence; would require refuting the Item-1 witness]

**Decision rule (fixed):** the CRT-independence witness (ord_p(G) coprime to ord_n(G),
public state fixes only d mod ord_p(G)) is the sole gate. It is met => STRUCTURAL NULL by
circularity, not an empirical null; the avenue is closed by an exact argument, not by exhaustion.

## 7. EXACTNESS

All arithmetic Z/m exact; no float in any signal path. Witness script uses only integer EC
arithmetic and modular inverses. No float carve-out needed.

## 8. WHAT A REAL (NON-CIRCULAR) VERSION WOULD REQUIRE

For completeness, so a future proposal is not misfiled as "same idea":
a non-circular use of the amicable oracle needs a PUBLIC map sending the p-side target to a correct
n-side point without applying d. That requires either (i) a public global lift R in E(Q) with
R = [d]G globally (not merely R = Q mod p) — which is a global scalar relation, generically absent
and not public; or (ii) some public homomorphism coupling `d mod n` to `d mod p` — which does not
exist (CRT). Either would be a genuinely different object; neither is the present hypothesis.
