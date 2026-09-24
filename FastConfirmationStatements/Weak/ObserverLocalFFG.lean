module
public import FastConfirmationStatements.Weak.ObserverPremises
public import FastConfirmationStatements.Premises.CheckpointLinks

/-! FFG content certificates and coherence for the observer's own inputs.

Content membership is separate from occurrence. No content law requires a
carrier, attestation, or validation state at another node. The local extension
connects the content to exact successful observer calls and prepared states.
-/

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution

/-- The observer's accepted domain, including its trusted initial store. -/
def ObserverAcceptedRoot (E : Execution Root) (obs : ValidatorIndex) (r : Root) : Prop :=
  ∃ store, E.ObserverCausalStore cfg ext obs store ∧ r ∈ store.block_roots

/-- A block-content domain. The certificate laws have no accepted-root or
received-attestation premise. `RootDescends` uses the concrete block labels;
local occurrence and body checks are separate fields of `ObserverLocalFFG`. -/
structure ObserverFFGContent (ext : Externals Root) (E : Execution Root) (anchor : Checkpoint Root) where
  domain : Root → Prop
  blocks : Root → BeaconBlock Root
  included : Root → Attestation Root → Prop
  formed : Root → Checkpoint Root → Prop
  C : Root → Epoch → Checkpoint Root
  GJ : Root → Checkpoint Root
  GU : Root → Checkpoint Root
  GF : Root → Checkpoint Root
  GUF : Root → Checkpoint Root
  checkpoint_epoch : ∀ r e, (C r e).epoch = e
  formed_domain : ∀ {r c}, formed r c → domain r
  formed_certificate : ∀ {r c}, formed r c →
    IncludedCertifiedJustified cfg E included anchor r c
  formed_on_chain : ∀ {r c}, formed r c → E.RootDescends r c.root
  gj_mem : ∀ r, domain r → ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GJ r)
  gu_mem : ∀ r, domain r → ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GU r)
  gf_mem : ∀ r, domain r → ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GF r)
  guf_mem : ∀ r, domain r → ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GUF r)
  gj_anchor_or_before : ∀ r, domain r →
    GJ r = anchor ∨ (GJ r).epoch < compute_epoch_at_slot cfg (blocks r).slot
  gj_max : ∀ {r c}, domain r →
    (∃ carrier, E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch < compute_epoch_at_slot cfg (blocks r).slot → c.epoch ≤ (GJ r).epoch
  gu_max : ∀ {r c}, domain r →
    (∃ carrier, E.RootDescends r carrier ∧ formed carrier c) → c.epoch ≤ (GU r).epoch
  au_epoch_le_block : ∀ {r c}, domain r →
    (∃ carrier, E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch ≤ compute_epoch_at_slot cfg (blocks r).slot
  gf_evidence : ∀ r, domain r → GF r = anchor ∨
    Nonempty (IncludedCertifiedFinalized cfg E included anchor r (GF r))
  guf_evidence : ∀ r, domain r → GUF r = anchor ∨
    Nonempty (IncludedCertifiedFinalized cfg E included anchor r (GUF r))
  gf_epoch_le_gj : ∀ r, domain r → (GF r).epoch ≤ (GJ r).epoch
  guf_epoch_le_gu : ∀ r, domain r → (GUF r).epoch ≤ (GU r).epoch
  gf_epoch_le_guf : ∀ r, domain r → (GF r).epoch ≤ (GUF r).epoch

namespace ObserverFFGContent
variable {cfg ext}
def AU {E : Execution Root} {anchor : Checkpoint Root}
    (S : ObserverFFGContent cfg ext E anchor) (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier, E.RootDescends tip carrier ∧ S.formed carrier c
end ObserverFFGContent

/-- Positive body evidence with a prepared validation state from this observer.
There is no separately scheduled attestation and no honest-store witness. -/
structure ObserverIncludedEvidence (E : Execution Root) (obs : ValidatorIndex)
    (carrier : Root) (body : BeaconBlock Root) (a : Attestation Root) where
  carrier_store : Store Root
  carrier_local : E.ObserverCausalStore cfg ext obs carrier_store
  carrier_known : carrier ∈ carrier_store.block_roots
  carrier_body : carrier_store.blocks carrier = body
  body_member : a ∈ body.attestations
  validation_store : Store Root
  validation_local : E.ObserverCausalStore cfg ext obs validation_store
  target_known : a.data.target.root ∈ validation_store.block_roots
  valid : ext.is_valid_indexed_attestation
    (let base := validation_store.block_states a.data.target.root
     let start := compute_start_slot_at_epoch cfg a.data.target.epoch
     if base.slot < start then ext.process_slots base start else base) a = true
  slot_within_horizon : E.SlotWithinHorizon cfg a.data.slot
  slot_before_carrier : a.data.slot < body.slot
  target_epoch : a.data.target.epoch = compute_epoch_at_slot cfg a.data.slot
  head_descends_target : E.RootDescends a.data.beacon_block_root a.data.target.root
  target_on_chain : E.RootDescends carrier a.data.target.root
  target_descends_source : E.RootDescends a.data.target.root a.data.source.root

/-- Selector equations at the trusted state and successful local `on_block`
post-states. These are refinement laws for the opaque external primitives. -/
structure ObserverFFGSelectorCoherence (E : Execution Root) (obs : ValidatorIndex)
    {anchor : Checkpoint Root} (S : ObserverFFGContent cfg ext E anchor) : Prop where
  genesis_gj : ∀ r ∈ E.genesis_store.block_roots,
    (E.genesis_store.block_states r).current_justified_checkpoint = S.GJ r
  genesis_gf : ∀ r ∈ E.genesis_store.block_roots,
    (E.genesis_store.block_states r).finalized_checkpoint = S.GF r
  genesis_gu : ∀ r ∈ E.genesis_store.block_roots,
    (ext.process_justification_and_finalization
      (E.genesis_store.block_states r)).current_justified_checkpoint = S.GU r
  genesis_guf : ∀ r ∈ E.genesis_store.block_roots,
    (ext.process_justification_and_finalization
      (E.genesis_store.block_states r)).finalized_checkpoint = S.GUF r
  genesis_unrealized_justification : ∀ r ∈ E.genesis_store.block_roots,
    E.genesis_store.unrealized_justifications r = S.GU r
  transition_gj : ∀ t : E.AcceptedBlockTransition cfg ext, t.atPrefix.node = obs →
    (t.postStore.block_states t.signedBlock.root).current_justified_checkpoint =
      S.GJ t.signedBlock.root
  transition_gf : ∀ t : E.AcceptedBlockTransition cfg ext, t.atPrefix.node = obs →
    (t.postStore.block_states t.signedBlock.root).finalized_checkpoint = S.GF t.signedBlock.root
  transition_gu : ∀ t : E.AcceptedBlockTransition cfg ext, t.atPrefix.node = obs →
    (ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)).current_justified_checkpoint =
      S.GU t.signedBlock.root
  transition_guf : ∀ t : E.AcceptedBlockTransition cfg ext, t.atPrefix.node = obs →
    (ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)).finalized_checkpoint = S.GUF t.signedBlock.root

/-- The local FFG extension. All occurrence premises are at the observer.
Certificate existence, selector order, and reflection are local refinement
contracts, not consequences of signature authenticity. The content relation
is fixed once for the whole observer run, including duplicates. -/
structure ObserverLocalFFG (E : Execution Root) (obs : ValidatorIndex) where
  state : ObserverFFGContent cfg ext E E.genesis_store.justified_checkpoint
  domain_local : ∀ r, state.domain r ↔ E.ObserverAcceptedRoot cfg ext obs r
  block_read : ∀ {store}, E.ObserverCausalStore cfg ext obs store →
    ∀ r ∈ store.block_roots, state.blocks r = store.blocks r
  included_evidence : ∀ {r a}, state.included r a →
    ObserverIncludedEvidence cfg ext E obs r (state.blocks r) a
  selectors : ObserverFFGSelectorCoherence cfg ext E obs state
  checkpoint_of_known : ∀ {store}, E.ObserverCausalStore cfg ext obs store →
    ∀ r ∈ store.block_roots, ∀ e, state.C r e = get_checkpoint_for_block cfg store r e
  au_checkpoint_of_known : ∀ {store}, E.ObserverCausalStore cfg ext obs store →
    ∀ r ∈ store.block_roots, ∀ c, state.AU r c →
      c = get_checkpoint_for_block cfg store r c.epoch
  finalization_delay : ∀ t : E.AcceptedBlockTransition cfg ext, t.atPrefix.node = obs →
    let finalized := (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
    finalized = E.genesis_store.justified_checkpoint ∨
      finalized.epoch + 2 ≤ compute_epoch_at_slot cfg t.signedBlock.message.slot
  checkpoint_projection : EpochCheckpointClosure E.genesis_store.justified_checkpoint
    state.domain state.C
  /-- Content exactness is conditional on local domain membership. It does
  not require arbitrary outside descendants to enter the observer store. -/
  exact_link_endpoints : ∀ {carrier source target}, state.domain carrier →
    (L : IncludedSupermajorityLink cfg E state.included carrier source target) →
    IncludedSupermajorityLink.Contributing cfg E.genesis_store.justified_checkpoint L →
    source = state.C carrier source.epoch ∧ target = state.C carrier target.epoch

end Execution
end FastConfirmation.Spec
end
