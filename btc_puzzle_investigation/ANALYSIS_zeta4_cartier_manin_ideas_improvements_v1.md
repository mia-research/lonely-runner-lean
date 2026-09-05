# Three ideas in `test-isotypic-projection-audit.py` — assessed at the IDEA level, with improvements

**Date 2026-08-18.** User asked: look at the **ideas** (not the method/application) and see where we
can improve. Grounded (not asserted) against the ledgers + one exact check
(`cartier_manin_idea_check_v1.py`). Two of the three ideas are real and improvable; one is our closed
circular claim (N17) — but its honest decomposition points at the same live channel the other two do.
**The through-line: the artifact's real content is the `ζ₄` biquadratic channel and a Cartier–Manin
proof; its keyspace tally is the circular part.**

---

## Idea 1 — split the cotangent space by the JOINT `(ζ₄, ζ₃)` action  → **sound, aligns, improvable**
The construction (Kummer cover `C: w⁴=x³+7`, `Jac(C) ~ E × A_new`, differentials `ω₁=dx/w²`,
`ω₂=dx/w³`, `ω₃=x·dx/w³`, split by the non-equivariant `ζ₄:(x,w)↦(x,iw)` and GLV `ζ₃:(x,w)↦(βx,w)`)
is **our object** — N14 (isotypic trace), the N1 **2+2 splitting**, the M23 tower `Q⊂Q(ω)⊂L`. The
distinct eigenvalue *pairs* `ω₁=(−1,β)`, `ω₂=(i,β)`, `ω₃=(i,β²)` do give 1-dim eigenspaces, isolating
the Frobenius eigenvalues `α₁,α₂` on `A_new`.

**Where it improves.** The valuable, non-obvious content is **isolating the *individual* eigenvalue
`α₁` (absolute), not merely the ratio `α₂/α₁ = ζ₃` (relative).** The ratio is exactly what is circular
in any keyspace readout (relative orbit position — see Idea 3); the individual eigenvalue is what would
be *absolute*. So the improvement is to ask precisely: **does the `ζ₄` (biquadratic, `F_{p²}`) channel
deliver an absolute per-point quantity that the `ζ₃` (GLV) channel cannot?** That is the live question,
and it is exactly **Brick E** (the degree of `c(d)=dlog_{A_new}(φ([d]G))`) and **Brick C** (phase on
the weight-1 eigenspace). *(Caveat, from `feedback_verify_root_system_against_defining_polynomial`:
verify the specific eigenvalue assignments against the defining polynomial before building on them — a
prior `ζ₁₂`-vs-primitive-cube-root paste error cost two files.)*

---

## Idea 2 — Cartier–Manin vanishing ⇒ `A_new` supersingular for all `p≡3 mod 4`  → **the gem**
**Checked exactly** (`cartier_manin_idea_check_v1.py`):
- **(A)** the Hasse–Witt method is sound and reproduces the artifact's own number: coeff of `x^{p-1}`
  in `(x³+7)^{(p-1)/2}` `= t_E mod p` at **8/8 primes**, incl. **`=13=t_E` at `p=43`** (the artifact's
  `C(ω₁)=13`), and `=0` exactly at `p≡2 mod 3` (correctly flags supersingular `E`).
- **(B)** the `A_new` mechanism holds: for every tested `p≡3 mod 4`, `deg[x^a·(x³+7)^{(p-3)/4}] =
  3(p-3)/4+a < p-1`, so the `x^{p-1}` coefficient **vanishes (both `a=0,1`) at 8/8 primes** — a genuine
  **scale-free** degree argument.

**Why this matters to us.** We already hold `A_new` supersingular at `p≡3 mod4` — but via **two other**
routes (the `ζ₄`-twist `π ζ₄ π⁻¹=ζ₄⁻¹`, §XI.19; the character-sum/Stickelberger reduction, v9
`c2_law_symbolic_proof`). The Cartier–Manin degree argument is an **independent third route** — exactly
the *independent adversarial re-derivation of N2's external inputs* that N2 still **owes** (open-items
#2/#11). And by the roadmap-v3 banner refinement it is a **form-level** claim (a proof, no measured
input) — **admissible toward secp**, unlike a measured null.

**Where it improves / must be nailed.**
1. **Method detail (the one real gap):** confirm the vanishing coefficient in (B) *is* the actual
   `A_new` Cartier–Manin entry for the `w⁴`-cover differentials `dx/w³, x·dx/w³` (the superelliptic
   Cartier operator on `w^m=f`), not just *a* low-degree coefficient. The `(p-3)/4` power is right for a
   quartic cover at `p≡3 mod4`; the operator bookkeeping is the piece to make rigorous.
2. **`superspecial` vs `supersingular` — decide, don't conflate.** Hasse–Witt `≡ 0` gives
   **superspecial** (a-number `= g`), *strictly stronger* than supersingular (Newton slopes ½). The
   artifact says superspecial; our ledger records supersingular. If the operator computation is right,
   this is an **upgrade** of N2, not just a re-derivation — but superspecial-for-all-`p≡3 mod4` is a
   strong uniform statement and needs the bookkeeping in (1) before we claim it.

**Disposition:** folds into **Brick E** as the concrete **N2-discharge (and possible upgrade)** route.
`[PROVED — structural, pending the (1) operator-identity check]`.

---

## Idea 3 — "read `d mod 6` from public data → 6× (2.585-bit) keyspace cut"  → **our N17 circular null**
This is the closed claim (**N17**, powered null, net 0 bits). The **script proves the circularity in
its own code**: line 54 `val_pos = (d*pow(lam,j,n))%n` and line 59 `d0 = orbit[0]` compute the orbit
representative `d0` **from the secret `d`**; the "non-circular extraction" then feeds `d0` into
`d_pred_mod3`. The load-bearing input is the secret. (Matches `ANALYSIS_public_gate_glv_carry_circularity`
§2: `d = λ^j d₀` is a relation between two unknowns.)

**The honest decomposition (improvement, non-suppressing).** Split the claimed `6× = 2.585 bits`:
- **`mod 2` — the negation parity `s=[y>p/2]`:** *genuinely public* (`y` is public; resolves `d` vs
  `n−d`), a real **2×**. **But it is BASELINE** — the `±1` automorphism, already inside the ~128-bit
  GLV/Wiener–Zuccherato estimate.
- **`mod 3` — the GLV orbit label `j` (`ζ₃`):** **circular** — relative position in `{d,λd,λ²d}`, needs
  `d₀`.
- **Net NEW non-circular reduction = 0.** The `2.585` conflates 1 baseline bit with `log₂3` circular
  bits. (Not a `√6`-vs-`6` error: the `6×` keyspace tally would be valid *if* `d mod 6` were knowable —
  it is the *knowability* that fails, and only the baseline `mod-2` bit is public.)

**Where it improves.** The one place a genuinely *non-circular* bit could come from is **Idea 1's `ζ₄`
absolute channel** (an absolute eigenvalue, not the relative `ζ₃` ratio). So Idea 3's value is **not**
its tally — it is that, stripped to the honest core, it points back at the same `ζ₄`/`A_new` question as
Ideas 1–2 and Brick E. Drop the `d mod 6` reduction claim; keep the pointer.

---

## Net — what to carry
1. **Idea 2 → Brick E:** adopt the Cartier–Manin degree argument as the **independent re-derivation
   (and candidate upgrade to superspecial) of N2**, pending the single operator-identity check. This is
   the most valuable item — a scale-free proof, banner-admissible.
2. **Idea 1 → Bricks C/E:** the real lever is the **individual/absolute** `ζ₄` eigenvalue vs the
   relative `ζ₃` ratio; verify eigenvalue assignments against the defining polynomial first.
3. **Idea 3:** record as N17-consistent (circular by its own code); keep only the honest `2+3`
   decomposition and its pointer to the `ζ₄` channel. No keyspace claim.

*Evidence: `cartier_manin_idea_check_v1.py`. Related: N2 (open-items #2/#11), N14, N17, §XI.19,
`ROADMAP_REDIRECT_v3.md` Bricks C/E.*
