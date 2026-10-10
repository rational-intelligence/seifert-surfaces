# Weak Weyl task-pin compatibility modifications

Source: qinz1yang/differential-geometry at
777299070a5529e96345e0033979706fd00c7e62. Target: Lean 4.35.0-rc3 and
Mathlib 3f6737de4761ec7bf368491fe9faccc991ebd6ca.

The task-pin indicator/restricted-measure API requires NullMeasurableSet.
Existing MeasurableSet hypotheses supply the proof consequence
MeasurableSet.nullMeasurableSet. Exact argument insertions, lines and source
hashes are recorded in port_modifications.json and port_deltas/.
The previously reviewed DeGiorgi compatibility modules and two accepted v2
proof-field bodies are preserved in the approved baseline. The new
zeroExtendWitness and extendOfCompactSupport proof-field conversions are exactly
F-Reviewer approved and root-frozen as versioned v2 supplements. Original v1
snapshots remain preserved. The same review approves 21 compiler-name metadata
bindings without changing source code or task IDs.
No mathematical helper, hypothesis or data formula is introduced.
Original licenses, NOTICE, citations and modification logs remain exact.
