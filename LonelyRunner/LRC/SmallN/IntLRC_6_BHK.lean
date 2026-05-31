import LonelyRunner.LRC.SmallN.IntLRC_6_BHK_Cases

/-!
# BHK 2001 — Six Lonely Runners (umbrella module)

Re-export shim. The substance lives in four sibling modules; this file
exists so `IntLRC_6.lean` keeps its existing import.

| Module | Contents |
|---|---|
| `IntLRC_6_BHK_Defs` | `bhkB`, `bhkBunion`, `unsafeOf`, bridge lemmas, structural facts |
| `IntLRC_6_BHK_Lemma4` | Lemma 4 (45-block bound), Corollary 5 |
| `IntLRC_6_BHK_MainLemma` | Main Lemma, Corollary 6 |
| `IntLRC_6_BHK_Cases` | §§5–8 case branches, `bhk_theorem_2`, `intLRC_six_hard` |

Source: Bohman, Holzman, Kleitman, *Six Lonely Runners*, EJC 8 (2001) R3.
-/
