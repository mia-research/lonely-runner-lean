# NOTE: cross-`j` Aut-contrast — relevance decision (retire as a mechanism discriminator)

**Date:** 2026-08-01
**Item C.1** of the 2026-08-01 plan. Reconciles `NEXT_SESSION_PROMPT_2026-08-01_v2.md` §B against the current mechanism picture.
**Register:** purist reasoning note (no lens).

---

## The question §B asks

`PREREG_jclass_120deg_discriminator_v2.md` asks whether the $\zeta_3$ lock is present on curves whose $\mathrm{Aut}(E)$ lacks $\mu_3$ — framed as a **necessary condition** for any mechanism that routes the $\zeta_3$ through the curve's automorphism / CM structure. The arms ($j=0$, $j=1728$, secp) died three times (prime-order obstruction, supersingularity, the $b_1=0$ premise only at $p\equiv3\bmod4$); §B specified a revival (drop prime-order, measure $b_1$, F-EMPTY-first). The question here: does reviving it still discriminate the *surviving* mechanism, or only the dead one?

## The Aut-routed mechanism is already refuted by existing data

The Aut-routed mechanism ("$\zeta_3$ comes from $\mu_3\subset\mathrm{Aut}(E)$") is a claim that the $120°$ lock **requires** $\mu_3\subset\mathrm{Aut}(E)$. That necessary condition is falsified by the secp256k1 data already in hand:

- secp256k1 has $j=0$ over $\mathbb{C}$ but, more to the point, the lock is verified on the **j=0 / $\mu_6$ curve** structure at 22 primes / 3585 cells (now `[PROVED-exact conjoined]`, `RESULT_120deg_conjoined_certificate_v1.md`). 
- Wait — secp256k1 *is* $j=0$ ($y^2=x^3+7$, CM by $\mathbb{Z}[\omega]$, $\omega=e^{2\pi i/3}$). So $\mu_3\subset\mathrm{Aut}(E_{\overline{\mathbb{Q}}})$ holds for secp. The cross-j contrast is therefore not "Aut has $\mu_3$ vs not" on secp; it is "$j=1728$ curves ($\mu_4$ Aut, no $\mu_3$) vs $j=0$ curves ($\mu_6$ Aut, has $\mu_3$)."

**Correction of the framing.** The cross-j test is genuinely a test of "$\zeta_3$-lock requires $\mu_3\subset\mathrm{Aut}$": $j=1728$ (Aut $=\mu_4$, no order-3 automorphism) is the negative-Aut-$\mu_3$ arm; $j=0$ is the positive arm. The existing secp data is on the *positive* arm only, so it does not by itself refute the Aut-routed mechanism. **The cross-j contrast is not redundant with existing data.** This reverses the "already refuted" claim I made in the planning phase.

## What the surviving mechanism predicts

The surviving mechanism (the geometric monodromy on the twist-parameter family, verified $SU(2)$ on the connected-component trace at 49833 cells) is a statement about the **$a$-family** — the sheaf $H^1_c(E, L_{\chi_2(y)}\otimes L_{\chi_a})$ as $a$ varies. Whether $SU(2)$-trace monodromy holds is, in principle, **$j$-dependent** (different $j$ gives a different curve, different sheaf, different monodromy) — but the conjectural picture is that it is a feature of the rigid-CM / twist construction, not of the specific $j$. So:

- If the lock **is** $j$-independent, the cross-j contrast confirms a structural (monodromy-theoretic) origin and refutes any Aut-routed origin (the $j=1728$ arm locks without $\mu_3\subset\mathrm{Aut}$).
- If the lock is **$j$-dependent** (present at $j=0$, absent at $j=1728$), that is evidence *for* an Aut-routed contribution and a genuinely new finding — but note the $+1$/$-1$ branch-dependence just established (item B) shows the arithmetic-level objects are already branch-sensitive; $j$-dependence would be a second, independent sensitivity.

So the cross-j contrast **does** discriminate, against the Aut-routed hypothesis, and **also** measures $j$-independence as an orthogonal structural fact. It is **not** vacated by item B (B is about arithmetic Galois group vs branch; cross-j is about the lock vs $j$). **Neither retire nor leave dangling — proceed as the orthogonal j-independence measurement in C.2.**

## The interpretation has shifted, though

The planning-phase dichotomy ("retire vs keep") was a false fork (correctly flagged). The serial resolution:

1. **As a mechanism discriminator:** keep. The Aut-routed hypothesis is *live* (not refuted by secp data, since secp is $j=0$ = positive arm), and cross-j is the right test. The earlier "already refuted by existing data" was wrong.
2. **As an orthogonal $j$-independence fact:** also keep — $j$-independence of the $120°$ lock is a structural claim worth one short `--check` run regardless of the mechanism question.

**Gate discipline (standing):** pursue only the `--check` mode (pre-gate legal). `--arms` is gate-blocked (the experiment-designer gate, failed 3×); **do not bypass it silently.** If `--check` surfaces something worth an `--arms` verdict, STOP and surface the gate decision explicitly. Apply the v2 standing repairs to any run (C-NEG $n\geq20$; readout-parity $\times$ index-set-parity check before each probe; precompute the pool difference table; never pipe through `tail`; OOS before naming).

## What this means for the spine

- The confidence-table row "$G_{\text{geom}}$ connected-component trace $= SU(2)$" is verified on $j=0$ only. A cross-j `--check` that reproduces the lock at $j=1728$ would extend the $SU(2)$-trace claim's empirical base across $j$; a failure would localize it to $j=0$ and reopen the Aut-routed mechanism. Either is a contribution; neither is predicted by the current record.
- This is consistent with item B: the *arithmetic* Galois object is branch-dependent; whether the *geometric* monodromy (the $SU(2)$-trace object) is $j$-dependent is a separate, open, and now-actionable question.

## Decision

**Do not retire cross-j.** Proceed to C.2 (the `--check` j-independence run) when time allows, after A2. Treat the planning-phase "retire" option as withdrawn — the Aut-routed mechanism is not refuted by secp data alone, and cross-j is the discriminating test.
