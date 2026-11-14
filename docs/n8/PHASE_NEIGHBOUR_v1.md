# Native lifted-phase neighbour lemma

Rules: 1–4, 8–18. New source `Fresh/PhaseNeighbour.lean`; root uniform block and catalogue files remain untouched.

- [L] `phase_separation X hgap i j hij` derives a closed1/8 gap between any strictly ordered lifted labels. `Fin.monotone_iff_le_succ` applied to `X_i−i/8` carries the original adjacent inequalities; no finite enumeration or imported density argument is used.
- [L] `phase_neighbour V X N T hphase hgap hspan k hk1 hk6` proves `IsolatedAt V k T` for1≤k≤6, withhphase `∀i,V_i*T=X_i+N_i`, integer lap functionN, adjacent lifted gaps≥1/8 andspan `X_7−X_0≤1`.
- [L] The opposite endpoint's neighbour retains the closed7/8 bound. Every signed physical reading is rewritten with explicit integer lapN_i−N_k; reflected readings use that lap minus1. All seven readings remain present.
- [L] `internal_isolation` adds onlyT>0 and yields `Isolation V k`. Physical positivity/injectivity may be retained by consuming arrangement classes; no arbitrary representation or existence of such a lift is asserted here.
- [T21976/21976] Root `phase_neighbour_map_v1` source was read before proof. It preserves original histories; all16482 internal-subject controls clear at the same carried reference, while624 old reference failures occur only at outer labels. These control counts are not proof premises.
- [L] All three endpoints compile warning-free with exactly `[propext, Classical.choice, Quot.sound]`; source scanner finds no sorry/native_decide/axiom/admit/unsafe declarations.
- [OBS] Endpoint subjects0/7 are deliberately outside this lemma. The hypotheses do not impose a1/8 lower bound on the phase gap fromX_7 back toX_0 across the full turn, so no global-isolation claim follows.
