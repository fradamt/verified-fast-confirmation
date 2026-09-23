module
public import FastConfirmationProofs.FFG.State.PathLocalFinalizedTransport
public import FastConfirmationProofs.Checkpoints.ResetCheckpointClassification
public import FastConfirmationProofs.FFG.CurrentTarget.CurrentTargetWalkKnownness
public import FastConfirmationProofs.Execution.History.HistoricalCheckpointInclusionBranches

public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Historical finalized placement on the retained source tip

The endpoint filter needs its exact finalized checkpoint equation on the
same retained tip which carries source recency.  Global finalized origins do
not themselves identify that tip: their installer can be an unrelated known
block.  This module closes the historically lagging case without making that
invalid identification.

If the endpoint finalized epoch is no later than the query finalized epoch,
accepted global provenance and exact certificate accountability give an
epoch-indexed prefix from `endpoint.F` to `query.F`.  The query's executable
filter witness first realizes `query.F` on the selected result.  Paired causal
walks transport that exact computation to the endpoint selected result, and
checkpoint composition realizes the older `endpoint.F` there.  The retained
source tip is a descendant of the selected result, so one final boundary walk
finishes the executable check.

No ordinary `RootDescends` fact is substituted for an exact checkpoint
prefix.  No global installer is merged with the retained source carrier, and
the statements assume no source visibility, AU for a finalized checkpoint at
the retained tip, filter result, `SafeFrom`, justification interface,
selected-margin bundle, or safety conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable {E : Execution Root}

namespace ExactPrefixAcceptedFFGSemantics


end ExactPrefixAcceptedFFGSemantics

/-! ## Honest target carried by an accepted finalization -/

/-- A concrete honest vote which targeted an accepted finalized checkpoint
before the store containing its certificate carrier.

This is the useful inner result of the older reset-root-delivery argument.
It retains the voter's actual executable head and target-boundary walk rather
than concluding only that the finalized root was relayed somewhere. -/
structure AcceptedHonestFinalizedTargetAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (w : ValidatorIndex) (m : Nat) (finalized : Checkpoint Root) where
  validator : ValidatorIndex
  vote_slot : Slot
  second : Nat
  index : CommitteeIndex
  validator_honest : validator ∈ E.honest
  second_within : E.WithinHorizon cfg second
  second_slot : E.slot_at cfg second = vote_slot
  post_anchor : E.slot_at cfg 0 ≤ vote_slot
  before_endpoint : vote_slot < E.slot_at cfg m
  anchor_epoch_lt : B.anchor.epoch < finalized.epoch
  target_eq :
    (honest_attestation cfg ext
      (E.store cfg ext validator second) vote_slot index validator
    ).data.target = finalized
  target_walk : WalkKnown (E.store cfg ext validator second)
    (compute_start_slot_at_epoch cfg finalized.epoch)
    (get_head cfg (E.store cfg ext validator second)).root




namespace AcceptedRetainedPhaseSourceCarrierAt




end AcceptedRetainedPhaseSourceCarrierAt

end Execution


end FastConfirmation.Spec

end
