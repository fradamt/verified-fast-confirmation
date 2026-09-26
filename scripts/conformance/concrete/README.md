# Concrete FFG differential mode

`run_differential.py` sends one JSON fixture list to the pinned Gloas minimal
pyspec and to `FFGDifferential.lean`. It compares the retained state after each
call. It compares the failing guard class when a call is rejected. Validation
runs the comparison when the pinned `.venv/bin/python` is present.

The fixture uses one fixed committee schedule: committee 0 is `[0, 1]`, and
committee 1 is `[2, 3]`. It replaces Python committee reads with this schedule.
This is the fixed-schedule scope in `FixedCommitteeSchedule`. The result does
not test RANDAO committee selection. An unmodified Python committee read can
give a different assignment.

The fixture uses one block-validity oracle mode. It accepts the structural
indexed check and omits BLS verification. It sets base rewards to zero and
erases actual-balance writes. These choices do not supply FFG state. Slot tests
use deterministic state and header root labels in place of SSZ hashing. The
same label rule is used for the Python source call and the Lean input. The
15 other epoch steps use identity frames, as required by the fixed registry
scope. The comparison does not claim equality of full Python states or hash
roots outside this oracle mode.

The fixture set covers epochs 0 and 1, the slot-16 boundary, PJF target
support, empty-balance floors, all four finalization rules and their order,
one, two and many skipped boundaries, root-ring wraparound, current and
previous target votes, repeated and overlapping participation, wrong target
with accepted source, invalid source, committee bits, wire payload status,
same-slot and skipped-slot payload checks, and the inclusion edge. The
runner also compares a fabricated current-epoch vote at an epoch start. Both
implementations reject its unavailable root.

The fixture also tests a concrete state transition with accepted and rejected
blocks, including the block header, deposits, a slashed proposer, the genesis
stub, a skipped slot, and the opaque oracle result. The block test keeps the
Python header, attestation, and operation order. It replaces cryptography and
the other block operations with the same documented oracle mode.

One separate Lean check rejects a state whose participation array is shorter
than its validator registry. Python can construct such a state, but it is
outside the well-formed fixed-scope domain. The Python/Lean differential count
excludes that structural check.

The pinned `anchor_semantics_probe.py` separately tests the a1
checkpoint-sync negative trace. The differential runner does not test network
delivery, BLS authenticity, or SSZ hashing outside the stated oracle mode.
