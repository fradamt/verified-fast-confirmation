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
structural checks in `state_transition` reject malformed array lengths before
processing. A malformed Python SSZ container is outside the differential
input domain because its constructor rejects that container.

This runner tests the FFG projection. It does not test the a1 checkpoint-sync
negative trace, network delivery, BLS authenticity, or the full Gloas block
oracle. Those checks remain separate from this transcription comparison.
