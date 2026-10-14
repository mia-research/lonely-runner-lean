# Direct incoming-window transfer — 2026-10-05

The user requested an attempt to prove that conversion to the AP/grid ideal
transfers isolation back to arbitrary arrangements, rather than introducing
another classification obligation.

`IncomingWindowN.rational_window_time` constructs a rational positive witness
for any feasible natural-lap window of positive rational readings. It selects
the maximum lower endpoint. A rational pinch time is therefore not an extra
input that must be discovered or certified.

`IncomingWindowN.replacement_of_incoming` takes an old natural lap vector q
that is feasible both at d-delta*v and at rational d, with positive readings
and delta>0. It derives reflected labels p and epsilon>0 giving positive-time
clear windows at every d+h*v for 0<=h<=epsilon. The direction v may be real,
and simultaneous boundary constraints are allowed. Earlier-feasibility
inequalities and the rational witness time are discharged internally using
the existing window and reflection theorems. No successful future replacement
or simple-pinch condition is supplied.

Targeted build passed. Both declarations audited with only propext,
Classical.choice and Quot.sound. No full Spec gate, commit or push this turn.

This is a local consequence of existing reflection, not the universal
conversion theorem. It still takes the old window's feasibility at the
current arrangement. An arbitrary sequence of replacements is not thereby
proved to cover its limiting arrangement; the existing finite-label endpoint
theorem handles that when its finite-family hypothesis is supplied. No new
assumption of universal isolation or finite catalogue has been introduced.
