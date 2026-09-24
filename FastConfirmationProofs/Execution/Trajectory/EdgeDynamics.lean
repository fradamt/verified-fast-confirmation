module
public import FastConfirmationProofs.Execution.Delivery.VoteDeadlineOrigin
public import FastConfirmationProofs.Handlers.HandlerStepFacts
public import FastConfirmationProofs.Execution.Trajectory.StoreDynamicsInputs

@[expose] public section

/-!
# Spec / Proof / EdgeDynamics

Derives relay and vote-class updates for one execution trajectory edge.

This module contains `equiv_subset_of_relay`, `EdgeInputResidual` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-! ## Section 1 — relay containments (`hsub`, `hequiv`) -/

/-- **`hequiv` — equivocator containment from `attester_slashing_relay`.** Every equivocator
known at the confirming anchor `(vc, nc)` is known at the endpoint `(w, m)`, under the
one-slot ordering `slot_at nc + 1 ≤ slot_at m`. This supplies
`ForkEdgeInput`'s `hequiv` field. -/
theorem equiv_subset_of_relay (hsync : NextSlotSynchronyPremises cfg ext E)
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    {vc w : ValidatorIndex} {nc m : ℕ}
    (hvc : vc ∈ E.honest) (hw : w ∈ E.honest)
    (hHnc : E.WithinHorizon cfg nc) (hHm : E.WithinHorizon cfg m)
    (hdue : nc ≤ E.slot_start cfg (E.slot_at cfg nc) +
      get_attestation_due_ms cfg / 1000)
    (hslot : E.slot_at cfg nc + 1 ≤ E.slot_at cfg m) :
    (E.store cfg ext vc nc).equivocating_indices ⊆
      (E.store cfg ext w m).equivocating_indices := by
  obtain ⟨hnext, hlt⟩ := E.past_slot_deadline_target_gate cfg hdiv hgenTime
    (Nat.lt_of_succ_le hslot)
  exact fun i hi => hsync.attester_slashing_relay vc hvc nc i hHnc hi hdue
    w hw m hHm hnext hlt

/-! ## Section 2 — the `is_ancestor` transports (`htS`, `htA`)

The forward transport is `EngineTransport.is_ancestor_transport` (walk from `r` toward
`b`'s slot); the reverse transport (needed for `AncestorOrVoteless`'s `b ⪯ r` orientation)
is the same `BlockAgreement.is_ancestor_congr` with the walk from `b` toward `r`'s slot.
Both consume only the block relay containment (Section 1) and the per-root `WalkKnown`
domain conditions. -/










end Execution

end FastConfirmation.Spec

end
