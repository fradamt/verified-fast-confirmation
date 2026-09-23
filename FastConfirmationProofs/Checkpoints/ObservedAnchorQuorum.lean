module
public import FastConfirmationProofs.Checkpoints.AnchorChainSafety
public import FastConfirmationProofs.FFG.Certificates.CertExtract
public import FastConfirmationProofs.Checkpoints.SlotClock

@[expose] public section

/-!
# Spec / Proof / Nucleus

The honest-quorum, vote-time, and cross-store transport nucleus for the
observed-anchor covering route.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)


namespace Execution

variable (E : Execution Root)






/-- **The missing current-epoch E5 bridge.** This is the exact equal branch of
the endpoint-epoch trichotomy needed by the observed-anchor producer. The
confirmation-side `glc` is anchored at the rotated observed/greatest-unrealized
checkpoint, and the endpoint carries a justified checkpoint in the confirmation
epoch; the required result is `AnchorCovSupply`'s covering disjunction.

This is deliberately exposed as a predicate, not asserted as a theorem. It is
the current-epoch FFG/LMD interplay condition:
the spec gates current-epoch confirmations on
`will_current_target_be_justified` precisely so this holds; formal derivation
requires the cross-validator target-agreement export whose non-circularity
constraint `Statements/Premises/Live.lean` documents. Concretely,
`HonestVotesSupportTarget` quantifies over same-slot and future target-epoch
votes, whereas the available shell IH covers only strictly earlier endpoint
stores, and `justified_requires_targets` carries no processed-by-endpoint time
conjunct. The committed `observed_justified` export supplies only `JustifiedIn`
for the rotated checkpoint, so deriving this bridge without the missing export
would be circular. -/
def CurrentEpochCoveringBridge (E : Execution Root) : Prop :=
  ∀ v ∈ E.honest, ∀ n : ℕ,
    get_current_slot cfg (E.store cfg ext v (n + 1)) >
        get_current_slot cfg (E.store cfg ext v n) →
    is_one_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n).store
        (get_current_balance_source (E.fcrStoreAtCall cfg ext v n))
        (get_latest_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n)) = true →
    ∀ w ∈ E.honest, ∀ m : ℕ, n + 1 ≤ m →
      E.WithinHorizon cfg m →
      E.slot_at cfg (n + 1) + 1 ≤ E.slot_at cfg (m + 1) →
      E.ConfirmedWithAnchor cfg ext
        (get_latest_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n))
        (E.fcrStoreAtCall cfg ext v n).current_epoch_observed_justified_checkpoint.root
        v (n + 1) →
      (E.store cfg ext w m).justified_checkpoint.epoch =
        compute_epoch_at_slot cfg (E.slot_at cfg (n + 1)) →
      is_ancestor (E.store cfg ext w m)
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n)))
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root) = true ∨
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root (E.store cfg ext w m).justified_checkpoint.root)
          (get_node_for_root (get_latest_confirmed cfg ext (E.fcrStoreAtCall cfg ext v n))) = true


end Execution

end FastConfirmation.Spec

end
