# Audit — the nine flagged counting/pigeonhole claims in the n=11 lineage

2026-09-07. Triggered by a corpus survey that flagged nine counting arguments
asserted without proof. Each was read at source and triaged by **whether it
reaches a live document**: the frozen preprint `lrc_n11_ap_paper_v30.md`
(Zenodo, 2026-03-27) or the current journal draft
`eleven_lonely_runners_v33.md`.

## Headline

**None of the nine reaches either live document.** Three sit in dead working
files, three died before `v30`, and three belong to the general-`n` programme
that is on hold. Most importantly, the central one — the "9 slots, 8 runners"
pigeonhole — was **replaced in `v33` by a correct algebraic fact**, which I
verified.

## The repair in v33, verified

The working files argued: *"The 9 slots are partitioned among 8 runners, so by
pigeonhole, at least one runner must cover ≥ 2 slots as its primary."* That step
assumes every slot has a primary owner and that ownership partitions — neither
established.

`v33` does not use it. It uses complementary pairs instead:

> Because `11` is prime, runners `j` and `11−j` share the same two labels: they
> form a *complementary pair*. The four pairs — `(2,9)`, `(3,8)`, `(4,7)`,
> `(5,6)` — together own eight primary slots `I₁,…,I₈`, two per pair. Slot `I₉`
> is left unclaimed: no pair's label corresponds to it.

**Verified exactly.** With labels `m_j^± ≡ ±j⁻¹ (mod 11)`:

| pair | labels |
|---|---|
| (2,9) | {5,6} |
| (3,8) | {4,7} |
| (4,7) | {3,8} |
| (5,6) | {2,9} |

Union `= {2,…,9}`; unowned `= {1,10}`. With the slot indexing `I_s ↔ m = s+1`
(from `lrc_n11_closing_conditions_v1.md`), owned labels give exactly `I₁…I₈`,
label 10 gives `I₉` (unclaimed), and label 1 is not a slot. The claim holds.

`v33` also scopes the notion explicitly — *"It does not mean the pair covers the
slot under all perturbed configurations; that is exactly what the gap obstruction
lemmas in Section 5 resolve."* — so it does not overclaim.

## Triage

### Dead working files — not in v30 or v33

| # | Site | Finding |
|---|---|---|
| D1 | `lrc_n11_structural_mechanism_v1.md:127` | Overdetermination Lemma. Labelled "Proof **sketch**" yet closed with `□`. Two soft steps: *"Generically this system has no solution"* (9 equations in 8 unknowns can still be consistent), and the pigeonhole above. Self-flagged in the next line and listed as a to-do in the same file — but **the `□` should not be there**. |
| D2 | `lrc_n11_to_nall_bridge_v1.md:39` | *"9 conditions, 8 unknowns → generically no joint solution."* Called "the master argument". Same soft step, no proof. |
| D3 | `lrc_n11_baton_pass_v1.md:182` | **Dangling reference.** Cites *"the counting argument in §6 of `lrc_n11_closing_conditions_v1.md`"* for the formal proof. That file's §6 is "Summary Status" — there is no counting argument there. The cited proof does not exist. |

### Died before the frozen preprint — checked absent from v30 and v33

| # | Site | Finding |
|---|---|---|
| D4 | `lrc_n11_ap_paper_v13.md:940` | *"each runner actively blocks at most `⌈8·2/11⌉ = 2` … **in expectation**"* then used as a worst-case bound. Absent from v30/v33. |
| D5 | `lrc_n11_ap_paper_v3.md:428` | Honest self-flag: *"This is exactly tight … No mechanism supplied."* Absent from v30/v33. |
| D6 | `lrc_n11_ap_paper_v6.md:235`, `v18.md:244` | The one proved member of the family, but only under a small-perturbation hypothesis. Absent from v30/v33. |

### General-`n` programme — on hold, still live *there*

| # | Site | Finding |
|---|---|---|
| D7 | `lrc_proof_allN_v11_8.md` (Conj. 5.2-H), `lrc_v11_9_theorem_5_2_sr_draft_v2.md` (Conj. 5.2-SR-H) | "The union of blocked sets is not everything." Empirically verified (34/34), **analytically open**, and the manuscript's abstract already declares the Main Theorem conditional. This is the real open item — and see below. |
| D8 | `lrc_proof_v10_9.md:368` | CT.1 Case B marked open; *"depth ≤ 1 empirically"*. Superseded lineage (v10 → v11_8). |
| D9 | `lrc_proof_v10_9.md:346` | The **theorem is correct** — I checked the counting: `∑_r (m_b(r)−1) = 2(n−2) − n = n−4` over `n` residues forces ≥ 4 residues at multiplicity 1. But the proof text leaves an abandoned false start in place: *"forces at least `2n − 4 − (2·(n−1)) = −2`... more precisely:"*. Editorial defect inside a proof; the mathematics is sound. |

## The one that matters

**D7 is the same obstruction as Rosenfeld's Lemma 6.** Established separately in
`docs/n8/WHY_13_AND_19_v2.md` §4: `lrc_n11_paper_v4.tex`'s safe-point count
`x₀(E)` is Rosenfeld's uncovered-time count with `k+1 = 11`, `p = lcm(E)`; and
`lrc_v11_9_srh_analysis_session_2026_05_28b.md` records the union bound
`2(n−2) > n` failing, in the same shape.

So the general-`n` programme and the n=8 work are blocked on **one** obstruction,
not two. That is the argument for attacking it in the n=8 setting, where `p` is a
free parameter.

## Recommended actions

1. **Nothing blocks v30 or v33 from this family.** No correction is owed to the
   preprint on these grounds.
2. Remove the `□` from D1 and the "master argument" framing from D2, or demote
   both to explicitly conjectural — they are cited as settled by later working
   files even though they are not.
3. Fix or delete the dangling §6 reference in D3.
4. Clean the abandoned computation in D9's proof if that lineage is ever revived.
5. D7 stays open and is now the shared target with n=8.

## Scope of this audit

Nine specific claims, read at source. This is **not** a general audit of the n=11
lineage: it says nothing about `v33`'s own §5 gap obstruction lemmas, its
seven-region exhaustiveness argument, or the separate issues that keep the
preprint from submission. Those were not examined here.
