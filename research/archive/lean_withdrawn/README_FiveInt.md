# `FiveInt.lean` — withdrawn 2026-09-21

Withdrawn by the owner's decision the day it was written. It is kept, not deleted, per the
project's archive rule.

**Why it was wrong.** It proved order five by importing `intLRC_five` — an *analytical* proof
already in this tree, by a different method. Three faults:

1. **It mixes two Leans.** The `intLRC_*` line is the analytical small-`n` programme
   (BHK / Bienia / Barajas–Serra). The cascade framework is a separate development. Results
   from one must not be wired into the other; they are kept apart deliberately.
2. **It proved nothing new.** `intLRC_five` already closes order five for integer speeds.
   The file re-expressed it in the framework's objects and added no mathematics.
3. **It broke real speeds.** The framework is real-valued throughout (`MANUSCRIPT_v19` §1.1;
   `LRC.SpecN.doors_agree` carries no rationality hypothesis). `intLRC` is integer-only, so the
   import introduced a restriction the framework does not have, and produced an apparent
   "real-speeds gap" that was an artefact of the import. The gcd-clearing, sorting and padding
   in the file are likewise shape-fixes for `intLRC`'s signature, and are antithetical to the
   boundary-set method, which takes an arbitrary positive real difference set.

Nothing imported it. Removing it changes no other result.

See `docs/nN/N5_CORRECTIONS_AND_LAP_TRUNCATION_v1.md` §1.3.
