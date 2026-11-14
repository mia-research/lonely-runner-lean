# Global clock investigation, 2026-10-20

The objective is to understand how the **same six disparities** constrain all
blocked-band resets over a full period. This investigation does not settle
primitive one-multiple existence or n=8. No new divisibility family is claimed.

## Exact coordinates and the common-period constraint

Let `x>0`, `32|x`, and let every positive base disparity d satisfy `8∤d`.
Every exceptional-clear time in one period has the coordinates

```
t = (k+s)/x,       k=0,...,x−1,       1/8≤s≤7/8.
```

For one base disparity put `g=gcd(d,x)`, `a=d/g`, `m=x/g`.
Then `gcd(a,m)=1`, a is odd, and `8|m`. Indeed all factors of two in d
occur in g, with exponent at most two, while x has exponent at least five.
The base phase is `a*(k+s)/m`.

**[P] Global row clock.** Write `m=8h`. A base boundary occurs when

```
a*k + a*s = 8h*q ± h.
```

Thus `a*s` is integral. Conversely, if `a*s=j` is integral, invert a modulo m:
both signs have solutions in k. The change times are **exactly `s=j/a`**.
They are fixed by the actual disparity. Resets in different windows cannot be
chosen separately.

**[L]** `exit_clock_iff` and `entry_clock_iff` prove this equivalence for the
normalized coprime integers a,8h. `packet_quarter_separation` proves the linked
integer congruences below. The normalization from arbitrary d,x is justified
above, but that gcd/power-of-two bridge is not formalized in these new files.

At `s=j/a`, the outgoing and incoming positions satisfy

```
a*k_out+j ≡  h (mod m),
a*k_in +j ≡ −h (mod m).
```

Each residue occurs g times among the x positions. The row therefore exchanges
two packets of g positions. The packet separation is `m/4` or `3m/4`, with
orientation determined by `a mod 4`. At the exact boundary both packets are
clear for this row; one packet was blocked before the event, the other is
blocked after it. Since m is divisible by eight, the exchange preserves the
parity of k. Repeated base laps are retained in this description.

**[L] Clock coincidences.** If two reduced clocks a,b tick together, their
common phase belongs to the gcd(a,b) clock (`common_tick_gcd`). If their gcd is
one, they cannot tick together for `0<s<1` (`coprime_ticks_separate`). This
restricts simultaneous events; it does not prohibit strict handovers between
events. For example, coprime clocks 47 and67 can tick successively.

## Global counts and what they do not force

**[P; PROVISIONAL: counting tool] Exact count for a physical row.** The map
`k↦a*k mod m` permutes the m residues, each repeated g times over x positions.
After translating by a*s, these are equally spaced points modulo m. The open
blocked arc has length `m/4` and integer endpoints before translation. It
contains `m/4` coset points if a*s is not integral, and `m/4−1` if a*s is
integral: in the latter case both endpoints are excluded. Therefore

```
number blocked by d at phase s = x/4 − g * indicator(a*s is integral).
```

This supports the blocked-position count for one supplied disparity. At every
sample `s=j/8`, `j=1,...,7`, a*s is not integral, since a is odd. In particular,
each row blocks exactly x/4 of the x exceptional openings.

**[P + L; PROVISIONAL: counting tool]** If six rows block every opening, total
multiplicity is `3x/2`. Let N1 count singly blocked positions. Multiplicities
give `3x/2≥N1+2(x−N1)`, hence `N1≥x/2`. At clock events the total is lower, so
the same conditional lower bound holds whenever every position remains blocked.
The generic counting implication is formalized in `many_singletons` and
`six_quarter_rows_singletons`. **The arbitrary-disparity quarter-count formula
is proved in the elementary argument above, not yet in Lean**. The Lean
application has an explicit row-count premise. Concrete row counts in the hard
example are kernel checked independently.

**[P; PROVISIONAL: covering]** To sustain total failure, every outgoing packet
must still be blocked by another disparity at its exact exit. An incoming row
at its own boundary cannot protect it, because boundaries are clear. A genuine
handover therefore needs strict overlap. `later_blocker_entered` [L] proves that
a blocker initially clear and later blocked must have entered its open band
between those phases. This supports the interval overlap in a supplied handover;
it does not establish that an unprotected exit must occur.

## A useful candidate that fails

The deterministic greedy-cover population contains 19,058 distinct primitive
six-row inputs: 4,113 at x=32 and14,945 at x=64, with `d<4x`. All exceptional
openings are blocked. Every input has a successful one-step displacement from
some singly blocked opening. This suggested a short-rescue candidate.

An adversarial coordinate search refutes it at the sixth prescribed starting
cover, after17,616 examined distinct neighbors. The primitive counterexample is

```
D={2,47,66,81,130,134},   x=32.
```

**[L]** All32 exceptional openings are blocked, each row blocks exactly8, and
18 openings have exactly one blocker. None of those18 succeeds by clearing its
sole blocker within the current exceptional clear interval. Eight have slow
blocker2 whose exit is beyond the interval; the other ten hand over to another
base blocker. These statements quantify all32 openings; the outcome is not a
conclusion from the adversarial score alone.

**[L + OBS, exact]** This input is nevertheless lonely. The relevant phase path
is

| Time | Phase s | Base blockers |
|---|---|---|
| `17/256` | `1/8` | 47,134 |
| `25/376` | `6/47` | 134 |
| `73/1072` | `12/67` | none |

Both exits lie strictly inside the same exceptional clear interval
`[17/256,23/256]`. Row47 clears first, creating a singleton *inside* the
interval. The reduced clock67 of row134 then ticks without replacement.
The witness `73/1072` is kernel verified for all seven disparities. The exact
cascade from its usual initial instant reaches it in two moves; from `17/256`
the cascade clears the two blockers together in one move. No necessity of two
cascade moves from every exceptional opening is claimed.

The stronger candidate allowing a single cascade move from *any* opening,
including multiply blocked openings, survived the separately recorded bounded
coordinate searches at x32 and64. This is not a theorem, and those searches do
not establish local or global optimality. It is not used in any proof here.

## Equal sampled masks do not determine the handovers

**[L]** Compare the hard base with

```
D'={2,47,66,81,126,122}.
```

The replacement pairs are `130↦256−130=126`, `134↦256−134=122`.
For all32 indices k and all seven eighth phases `s=j/8`, the corresponding
rows have identical blocked/clear masks. This follows because their phases at
these times sum to `8k+j`, an integer. `twin_sample_masks` kernel checks the
entire finite claim.

But at the singleton opening `41/256`, both inputs have only blocker81.
Its next opening is `35/216`. For D', that time is lonely; for D, row130 is
blocked there. Both assertions are kernel verified. The full diagnostic finds
three directly rescued singleton openings for D', none for D.

Their clocks changed: the reduced frequencies65,67 became63,61. A fixed-phase
mask reduction retains the sampled clearance tests, but loses these continuous
handovers. This does not invalidate any existing fixed-grid certificate, which
returns an actual sampled witness. It prevents using that same quotient as a
complete representation of the dynamics between samples.

## Verification and present limit

* New Lean sources: `OrderEightGlobalClocksN.lean` (eight general theorems) and
  `OrderEightGlobalClockExamplesN.lean` (twelve example/soundness theorems).
* `python3 scripts/check_order_eight_global_clocks.py` from the nested repository:
  PASS,20 standard-axiom reports,6 transitive dependency exclusions,434 stable
  fingerprints. The arbitrary normalization/count bridge remains outside these
  formal statements, as recorded explicitly in the manifest.
* `global_phase_clocks_v1.py` reconstructs the entire lonely set from every
  event and every intervening phase chamber for six named inputs, including
  boundary-only touches. All results agree with independently merged Fraction
  cells and the deterministic cascade. This completeness check reindexes the
  existing opening/cell description; it is not a new existence proof.
* `global_singleton_adversary_v1.py`, `global_one_jump_adversary_v1.py` and their
  JSON outputs record the specified searches. They are diagnostics with no
  universal inference. All arithmetic is integral or exact Fraction arithmetic.

**Still unresolved:** whether the six linked arithmetic clocks can protect
every outgoing packet throughout the exceptional clear phase interval. Counts
alone do not exclude it; the singleton-at-opening candidate is false. The
remaining proof needs the actual packet positions and their common-clock
constraints, including newly created singleton positions and repeated laps.
No theorem excluding every globally compatible failed period has been proved.

Earlier sources/gates are unchanged. Nothing is committed or pushed.
