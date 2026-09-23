module
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.Execution.Trajectory.StoreDynamicsInputs

@[expose] public section

/-!
# Spec / Proof / EdgeDynamics

Derives relay and vote-class updates for one execution trajectory edge.

This module contains `blockRoots_subset_of_relay`, `equiv_subset_of_relay`, `EdgeInputResidual` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — relay containments (`hsub`, `hequiv`) -/

/-- **`hsub` — block-root containment from `block_relay`.** Every root known at the
confirming anchor `(vc, nc)` is known at the endpoint `(w, m)`, provided the endpoint is at
least one slot past the anchor (`slot_at nc + 1 ≤ slot_at (m + 1)`). This is the block
propagation deadline `Synchrony.block_relay` for each root, packaged as a set containment;
it feeds both `is_ancestor` transports so they carry no raw containment premise. -/
theorem blockRoots_subset_of_relay (hsync : NextSlotSynchronyPremises cfg ext E)
    {vc w : ValidatorIndex} {nc m : ℕ}
    (hvc : vc ∈ E.honest) (hw : w ∈ E.honest)
    (hHnc : E.WithinHorizon cfg nc) (hHm : E.WithinHorizon cfg m)
    (hslot : E.slot_at cfg nc + 1 ≤ E.slot_at cfg (m + 1)) :
    (E.store cfg ext vc nc).block_roots ⊆ (E.store cfg ext w m).block_roots :=
  fun r hr => hsync.block_relay vc hvc nc r hHnc hr w hw m hHm hslot


/-- **`hequiv` — equivocator containment from `attester_slashing_relay`.** Every equivocator
known at the confirming anchor `(vc, nc)` is known at the endpoint `(w, m)`, under the
one-slot ordering `slot_at nc + 1 ≤ slot_at m`. This supplies
`ForkEdgeInput`'s `hequiv` field. -/
theorem equiv_subset_of_relay (hsync : NextSlotSynchronyPremises cfg ext E)
    {vc w : ValidatorIndex} {nc m : ℕ}
    (hvc : vc ∈ E.honest) (hw : w ∈ E.honest)
    (hHnc : E.WithinHorizon cfg nc) (hHm : E.WithinHorizon cfg m)
    (hslot : E.slot_at cfg nc + 1 ≤ E.slot_at cfg m) :
    (E.store cfg ext vc nc).equivocating_indices ⊆
      (E.store cfg ext w m).equivocating_indices :=
  fun i hi => hsync.attester_slashing_relay vc hvc nc i hHnc hi w hw m hHm hslot

/-! ## Section 2 — the `is_ancestor` transports (`htS`, `htA`)

The forward transport is `EngineTransport.is_ancestor_transport` (walk from `r` toward
`b`'s slot); the reverse transport (needed for `AncestorOrVoteless`'s `b ⪯ r` orientation)
is the same `BlockAgreement.is_ancestor_congr` with the walk from `b` toward `r`'s slot.
Both consume only the block relay containment (Section 1) and the per-root `WalkKnown`
domain conditions. -/










end Execution

end FastConfirmation.Spec

end
