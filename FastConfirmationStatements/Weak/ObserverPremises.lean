module
public import FastConfirmationModel.Weak.ObserverState
public import FastConfirmationStatements.Premises.SelectedMargin

@[expose] public section

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution
variable (E : Execution Root)

/-- The three indexed-attestation laws on the observer's own keyed states. -/
structure ObserverIndexedAttestationValidity (E : Execution Root) (obs : ValidatorIndex) : Prop where
  honest_attestation_valid : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ∀ v ∈ E.honest, a.attesting_indices = [v] → v ∈ E.committee a.data.slot →
    (∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data) →
      ext.is_valid_indexed_attestation state a = true
  valid_attestation_honest : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  valid_attestation_committee : ∀ (state : BeaconState Root) (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state →
    ext.is_valid_indexed_attestation state a = true →
    ∀ i ∈ a.attesting_indices, i ∈ E.committee a.data.slot

/-- The two store-level coherence facts an arbitrary (not necessarily honest)
observer's own store must still satisfy for the confirmed-margin machinery to
run: committee readback (feeding `PrefixCommitteeAgreement`, in place of
`BeaconExternalsPremises.committees_agree v hv …`) and justified-root knownness
(in place of `SelectedMarginDomain.justified_root_known v hv …`). Both are
facts about the observer's own trajectory, not about the observer's honesty;
an implementation that always computes committees from its own head state and
always keeps its own justified root in its block map satisfies them whether
or not the observer is Byzantine. -/
structure ObserverCoherence (obs : ValidatorIndex) : Prop where
  validity : E.ObserverIndexedAttestationValidity cfg ext obs
  committees_agree : ∀ n : ℕ, E.WithinHorizon cfg n → ∀ s : Slot,
    E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s
  justified_root_known : ∀ n : ℕ, E.WithinHorizon cfg n →
    (E.store cfg ext obs n).justified_checkpoint.root ∈
      (E.store cfg ext obs n).block_roots

/-- The **internal** assumption bundle the margin machinery runs on: the usual
`SelectedMarginAssumptions` and the observer's own store coherence. The
observer `obs` is completely arbitrary — it **may** be honest; the model simply
grants it nothing. (Non-honesty was never used by any proof, so it is not a
field: carrying it would only narrow the statements.)

This record is *not* the premise surface of the weak development's top-level
statements: `coherence.justified_root_known` is a derived fact, never a
caller-supplied one. Callers hand in `WeakObserverPremises` below, whose
observer-store fields are `validity` and `committees_agree`, and every statement carrying
the accepted-FFG package (`B`, `hT`, `hanchor`, `hboundary`) — the folds, the
closed call theorems, and the finalized-base corollaries — builds this bundle
internally with `WeakObserverPremises.toMarginAssumptions`. Only the
`hmargin`/`hfilter`-carrying one-shot floor forms
(`weak_safeFrom_find_latest_confirmed_descendant`, `…_discharged` and their
endpoint forms), which carry no `B` at all and so have nothing to derive
`justified_root_known` from, still take this bundle directly. -/
structure WeakObserverMarginPremises (obs : ValidatorIndex) : Prop where
  base : SelectedMarginAssumptions cfg ext E
  validity : E.ObserverIndexedAttestationValidity cfg ext obs
  coherence : E.ObserverCoherence cfg ext obs

/-- **The observer premise surface of the weak development.** Everything a
caller must supply about the observer `obs`, and nothing that is derivable:

* `base` — the ordinary (observer-independent) `SelectedMarginAssumptions`;
* `genesis` — the committed-anchor initialization required by the accepted trajectory;
* `validity` — the indexed-attestation laws on keyed observer-run states;
* `committees_agree` — the observer reads back the scheduled committees from its own store.

The observer `obs` is arbitrary and **may** be honest: the weak development's
point is that nothing is assumed *in the observer's favour* (no delivery, no
honest behaviour), not that the observer is dishonest. Non-honesty was never
used by any proof, so it is not a field — carrying it would only narrow every
weak statement.

`ObserverCoherence.justified_root_known` is deliberately absent: it is a
fact about any node's trajectory
(`ObserverCoherence.justified_root_known_of_acceptedGlobalTrajectory`), and
every top-level weak statement carries the accepted-FFG/trajectory premises
that prove it, so it is derived rather than assumed. -/
structure WeakObserverPremises (obs : ValidatorIndex) : Prop where
  base : SelectedMarginAssumptions cfg ext E
  genesis : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
    anchorState.slot = anchorBlock.message.slot ∧
    ext.AnchorCommitsToState anchorBlock.message anchorState ∧
    anchorBlock.message.parent_root ≠ anchorBlock.root
  validity : E.ObserverIndexedAttestationValidity cfg ext obs
  committees_agree : ∀ n : ℕ, E.WithinHorizon cfg n → ∀ s : Slot,
    E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s

end Execution
end FastConfirmation.Spec

end
