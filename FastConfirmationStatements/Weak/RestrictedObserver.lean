module
public import FastConfirmationStatements.Weak.ObserverLocalFFG
public import FastConfirmationStatements.Weak.CompletedCall
public import FastConfirmationModel.Weak.Execution

/-! Restricted weak observer premises and their local input boundary.

This design module does not change the existing weak headlines. Shared records
read `withoutObserver`; local input contracts read the actual observer. The
Internal companion proves schedule independence for a non-honest observer.
No justification-interface laws are assumed.
-/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-- The shared execution view erases the observer's input schedule. For the
non-honest observer used below, erasing it from the honest set has no effect.
Votes, committees, genesis, and the verification horizon are unchanged. -/
def withoutObserver (E : Execution Root) (obs : ValidatorIndex) : Execution Root :=
  { E with honest := E.honest.erase obs
           schedule := fun v n => if v = obs then [] else E.schedule v n }

/-- Exact change domain for the independence oracle. All execution data other
than the observer schedule are fixed, including the observer's signed votes. -/
structure SameOutsideObserver (E E' : Execution Root) (obs : ValidatorIndex) : Prop where
  horizon : E.verification_horizon = E'.verification_horizon
  genesis : E.genesis_store = E'.genesis_store
  honest : E.honest = E'.honest
  committee : E.committee = E'.committee
  vote : E.vote = E'.vote
  schedule : ∀ v, v ≠ obs → E.schedule v = E'.schedule v

variable (cfg : Config) (ext : Externals Root)

/-- Shared weak contracts on the execution without the observer. This reuses
main's records, including its horizon vote lookahead. For `obs ∉ E.honest`,
the economic bound uses exactly `E.honest`. FFG semantics here cover the
restricted accepted-root domain. -/
structure WeakRestrictedNetworkPremises (E : Execution Root) where
  base : SelectedMarginAssumptions cfg ext E
  delivery_lookahead : HorizonVoteDeliveryLookahead cfg E
  semantics : CausalPrefixFFGInterpretation cfg ext E
  anchor_eq : semantics.anchor = E.genesis_store.justified_checkpoint
  anchor_boundary : E.TrustedAnchorBoundaryAligned
    (cfg := cfg) (anchor := semantics.anchor)
  finalization_delay : E.RealizedFinalizationDelay cfg ext semantics
  paper_a32 : semantics.state.PaperA32Inclusion cfg ext
  checkpoint_projection : EpochCheckpointClosure semantics.anchor
    (E.AcceptedRoot cfg ext) semantics.state.C
  exact_link_validity : semantics.state.ExactLinkValidity
  completed_calls : E.WeakCompletedFCRCallSupplement cfg ext
  epoch_ends_fit : EpochEndsFitUint64 cfg
  genesis : ∃ (state : BeaconState Root) (block : SignedBeaconBlock Root),
    E.genesis_store = get_forkchoice_store cfg state block ∧
    state.slot = block.message.slot ∧
    ext.AnchorCommitsToState block.message state ∧
    block.message.parent_root ≠ block.root

/-- Shared records evaluated after observer erasure. -/
abbrev WeakObserverRestrictedCore (E : Execution Root) (obs : ValidatorIndex) :=
  WeakRestrictedNetworkPremises cfg ext (E.withoutObserver obs)

/-- Input authenticity and coherence at the actual observer. No clause requires
receipt of a message. Missing messages make the event clauses vacuous. The
vote-head clause checks the fixed signed output against the new local input
run when the observer is honest; it is not automatically schedule invariant.

The three block clauses restore precisely the observer part of execution
well-formedness. The first includes agreement between two observer inputs.
`validity` concerns keyed observer states, not guaranteed target arrival. -/
structure ObserverInputAuthenticity (E : Execution Root) (obs : ValidatorIndex) : Prop where
  validity : E.ObserverIndexedAttestationValidity cfg ext obs
  committees_agree : ∀ n, E.WithinHorizon cfg n → ∀ s,
    E.SlotWithinHorizon cfg s →
    get_slot_committee cfg ext (E.store cfg ext obs n) s = E.committee s
  no_forgery : ∀ n (a : Attestation Root) fb,
    Event.attestation a fb ∈ E.schedule obs n →
    ∀ v ∈ E.honest, v ∈ a.attesting_indices →
      ∃ m a', m ≤ n ∧ E.vote v a.data.slot = some (m, a') ∧ a.data = a'.data
  block_labels : ∀ n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule obs n →
    ∀ w k (b' : SignedBeaconBlock Root), Event.block b' ∈ E.schedule w k →
      b.root = b'.root → b.message = b'.message
  genesis_blocks : ∀ n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule obs n → b.root ∈ E.genesis_store.block_roots →
      b.message = E.genesis_store.blocks b.root
  anchor_parent : ∀ r ∈ E.genesis_store.block_roots,
    ∀ n (b : SignedBeaconBlock Root), Event.block b ∈ E.schedule obs n →
      b.root ≠ (E.genesis_store.blocks r).parent_root
  process_slots_validity : ∀ state slot (a : Attestation Root),
    E.ObserverValidationState cfg ext obs state → state.slot < slot →
    ext.is_valid_indexed_attestation (ext.process_slots state slot) a =
      ext.is_valid_indexed_attestation state a
  votes_head : obs ∈ E.honest → ∀ s, obs ∈ E.committee s →
    E.SlotWithinHorizon cfg s → E.slot_at cfg 0 ≤ s →
    ∃ n index, E.WithinHorizon cfg n ∧ E.slot_at cfg n = s ∧
      E.vote obs s =
        some (n, honest_attestation cfg ext (E.store cfg ext obs n) s index obs)

/-- The observer input laws, with the explicitly listed local FFG refinement. -/
structure ObserverLocalInputs (E : Execution Root) (obs : ValidatorIndex) : Prop
    extends E.ObserverInputAuthenticity cfg ext obs where
  ffg : Nonempty (E.ObserverLocalFFG cfg ext obs)

/-- Restricted surface for a non-honest observer. The caller supplies
`obs ∉ E.honest` separately. The core FFG domain excludes observer-only
accepted blocks, which the local input record covers through its content
certificate extension. -/
structure WeakObserverRestrictedPremises (E : Execution Root) (obs : ValidatorIndex) where
  core : E.WeakObserverRestrictedCore cfg ext obs
  local_inputs : E.ObserverLocalInputs cfg ext obs

end Execution
end FastConfirmation.Spec
end
