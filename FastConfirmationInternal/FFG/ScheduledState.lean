module
public import FastConfirmationStatements.Premises.FFGState
public import FastConfirmationInternal.FFG.Certificates

@[expose] public section

/-! Concrete block-local FFG state predicates used by proofs. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
/-- A concrete block message at an execution root.  The block comes either
from the trusted initial store or from an actual scheduled block event. -/
def BlockAt (r : Root) (b : BeaconBlock Root) : Prop :=
  (r ∈ E.genesis_store.block_roots ∧
      b = E.genesis_store.blocks r) ∨
    ∃ (w : ValidatorIndex) (n : ℕ) (sb : SignedBeaconBlock Root),
      Event.block sb ∈ E.schedule w n ∧
      sb.root = r ∧ sb.message = b

/-- Membership in the execution's concrete block universe. -/
def ExecutionRoot (r : Root) : Prop :=
  ∃ b : BeaconBlock Root, E.BlockAt r b


namespace AcceptedBlockAttestationInclusion
end AcceptedBlockAttestationInclusion
end Execution
/-- The causal honest witness for a non-anchor formed checkpoint is itself an
attestation included on the carrier chain, not an unrelated ground vote. -/
def HonestTargetIncludedBeforeCarrier (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (carrier : Root) (c : Checkpoint Root) : Prop :=
  ∃ b : BeaconBlock Root, E.BlockAt carrier b ∧
    ∃ i ∈ E.honest, ∃ (s : Slot) (k : ℕ) (a : Attestation Root),
      s < b.slot ∧
      E.SlotWithinHorizon cfg s ∧
      E.vote i s = some (k, a) ∧
      a.data.slot = s ∧
      a.data.target = c ∧
      AttestationIncludedOnChain E included carrier a

namespace IncludedSupermajorityLink
/-- Forget carrier locality while retaining the exact scheduled attestations.
This is the sound direction from the stronger block-body certificate to the
older global certificate API. -/
def toSupermajorityLink
    {E : Execution Root}
    (I : Execution.BlockAttestationInclusion cfg E)
    {carrier : Root} {source target : Checkpoint Root}
    (L : IncludedSupermajorityLink cfg E I.Included carrier source target) :
    SupermajorityLink cfg E source target where
  signers := L.signers
  source_before_target := L.source_before_target
  target_descends_source := L.target_descends_source
  target_epoch_within := L.target_epoch_within
  target_span_within := L.target_span_within
  signers_in_epoch := L.signers_in_epoch
  signer_attestation := by
    intro i hi
    obtain ⟨a, ⟨containing, _hdesc, hincluded⟩, hia, hsource, htarget⟩ :=
      L.signer_attestation i hi
    obtain ⟨w, n, hreceived⟩ := (I.evidence hincluded).received_from_block
    exact ⟨w, n, a, true, hreceived, hia, hsource, htarget⟩
  supermajority := L.supermajority

end IncludedSupermajorityLink
namespace IncludedCertifiedJustified
/-- Every carrier-local included-attestation certificate induces the existing
global scheduled-attestation certificate. -/
def toCertifiedJustified
    {E : Execution Root}
    (I : Execution.BlockAttestationInclusion cfg E)
    {anchor : Checkpoint Root} {carrier : Root} {c : Checkpoint Root} :
    IncludedCertifiedJustified cfg E I.Included anchor carrier c →
      CertifiedJustified cfg E anchor c
  | .anchor => .anchor
  | .link hsource hlink =>
      .link (toCertifiedJustified I hsource)
        (IncludedSupermajorityLink.toSupermajorityLink (cfg := cfg) I hlink)

end IncludedCertifiedJustified
namespace IncludedCertifiedFinalized
/-- Forget carrier locality to recover the existing finalization certificate
API without inventing any new vote witness. -/
def toCertifiedFinalized
    {E : Execution Root}
    (I : Execution.BlockAttestationInclusion cfg E)
    {anchor : Checkpoint Root} {carrier : Root} {c : Checkpoint Root}
    (F : IncludedCertifiedFinalized cfg E I.Included anchor carrier c) :
    CertifiedFinalized cfg E anchor c where
  justified := IncludedCertifiedJustified.toCertifiedJustified
    (cfg := cfg) I F.justified
  child := F.child
  child_epoch := F.child_epoch
  middle_justified := by
    intro hchild
    obtain ⟨middle, hepoch, hdesc, ⟨hmiddle⟩⟩ := F.middle_justified hchild
    exact ⟨middle, hepoch, hdesc,
      IncludedCertifiedJustified.toCertifiedJustified (cfg := cfg) I hmiddle⟩
  finalizing_link := IncludedSupermajorityLink.toSupermajorityLink
    (cfg := cfg) I F.finalizing_link

end IncludedCertifiedFinalized
/-- Concrete evidence represented by one block-local AU entry.  Certification
is backed by attestations included on the carrier chain; `on_chain` ties the
checkpoint to its carrier; and every non-anchor checkpoint exposes an honest
ground vote strictly before the carrier. -/
structure FormedCheckpointEvidence (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root) (carrier : Root)
    (c : Checkpoint Root) : Prop where
  certified : Nonempty
    (IncludedCertifiedJustified cfg E included anchor carrier c)
  on_chain : E.RootDescends carrier c.root
  causal : c = anchor ∨
    HonestTargetIncludedBeforeCarrier cfg E included carrier c

/-- The block-local FFG state omitted by the
executable `BeaconState`, quantified over every scheduled wire root.

`formed carrier c` means that `carrier` contains sufficient available /
unrealized evidence for `c`.  AU at a tip is defined below by inheriting such
evidence from a carrier on the tip's chain. -/
structure ChainFFGState (E : Execution Root)
    (anchor : Checkpoint Root) where
  /-- Indexed-attestation validity oracle. `FFGTransitionCoherence` identifies it with the execution's
  actual `BeaconFunctionInterface.is_valid_indexed_attestation`. -/
  attestationValidity : BeaconState Root → Attestation Root → Bool

  /-- Actual block-body inclusion, with carrier, validity, committee, horizon,
  and chain-position evidence. -/
  includedAttestations :
    Execution.BlockAttestationInclusion cfg E

  formed : Root → Checkpoint Root → Prop

  /-- Epoch-boundary checkpoint `C(b,e)` and the greatest realized,
  unrealized, and finalized selectors at a block. -/
  C : Root → Epoch → Checkpoint Root
  GJ : Root → Checkpoint Root
  GU : Root → Checkpoint Root
  GF : Root → Checkpoint Root
  /-- Finalized checkpoint obtained by the eager next-boundary pull-up.  This
  is separate from `GF`: `process_justification_and_finalization` can advance
  finality beyond the finalized checkpoint in the block's post-state. -/
  GUF : Root → Checkpoint Root

  checkpoint_epoch : ∀ r e, (C r e).epoch = e

  formed_evidence : ∀ {r : Root} {c : Checkpoint Root},
    formed r c → FormedCheckpointEvidence cfg E
      includedAttestations.Included anchor r c

  gj_mem : ∀ r : Root, E.ExecutionRoot r →
    ∃ carrier : Root,
      E.RootDescends r carrier ∧ formed carrier (GJ r)
  gu_mem : ∀ r : Root, E.ExecutionRoot r →
    ∃ carrier : Root,
      E.RootDescends r carrier ∧ formed carrier (GU r)

  /-- Finalized checkpoints are a subset of the available/unrealized
  justified checkpoints on the same chain (`AF(b) ⊆ AU(b)` in the companion
  model).  This is also the phase0 state-transition invariant that finality
  can advance only to an already justified checkpoint. -/
  gf_mem : ∀ r : Root, E.ExecutionRoot r →
    ∃ carrier : Root,
      E.RootDescends r carrier ∧ formed carrier (GF r)

  /-- The eagerly pulled-up finalized selector obeys the same `AF ⊆ AU`
  invariant. -/
  guf_mem : ∀ r : Root, E.ExecutionRoot r →
    ∃ carrier : Root,
      E.RootDescends r carrier ∧ formed carrier (GUF r)

  /-- A block's realized justified checkpoint is the anchor or strictly
  precedes the block epoch, matching ordinary epoch processing. -/
  gj_anchor_or_before : ∀ {r : Root} {b : BeaconBlock Root},
    E.BlockAt r b →
      GJ r = anchor ∨
        (GJ r).epoch < compute_epoch_at_slot cfg b.slot

  /-- GJ is greatest among AU checkpoints eligible before this block epoch. -/
  gj_max : ∀ {r : Root} {b : BeaconBlock Root}
      {c : Checkpoint Root},
    E.BlockAt r b →
    (∃ carrier : Root,
      E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch < compute_epoch_at_slot cfg b.slot →
    c.epoch ≤ (GJ r).epoch

  /-- GU is greatest among all AU checkpoints at this tip. -/
  gu_max : ∀ {r : Root} {c : Checkpoint Root},
    E.ExecutionRoot r →
    (∃ carrier : Root,
      E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch ≤ (GU r).epoch

  /-- AU never contains a checkpoint from after its carrier tip's block
  epoch (paper Property 1.7). -/
  au_epoch_le_block : ∀ {r : Root} {b : BeaconBlock Root}
      {c : Checkpoint Root},
    E.BlockAt r b →
    (∃ carrier : Root,
      E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch ≤ compute_epoch_at_slot cfg b.slot

  /-- Finalized evidence permits the trusted anchor exception because a
  checkpoint-sync anchor need not have an in-segment finalizing link. -/
  gf_evidence : ∀ r : Root, E.ExecutionRoot r →
    GF r = anchor ∨
      Nonempty (IncludedCertifiedFinalized cfg E
        includedAttestations.Included anchor r (GF r))

  guf_evidence : ∀ r : Root, E.ExecutionRoot r →
    GUF r = anchor ∨
      Nonempty (IncludedCertifiedFinalized cfg E
        includedAttestations.Included anchor r (GUF r))

  gf_epoch_le_gj : ∀ r : Root, E.ExecutionRoot r →
    (GF r).epoch ≤ (GJ r).epoch
  guf_epoch_le_gu : ∀ r : Root, E.ExecutionRoot r →
    (GUF r).epoch ≤ (GU r).epoch
  gf_epoch_le_guf : ∀ r : Root, E.ExecutionRoot r →
    (GF r).epoch ≤ (GUF r).epoch

namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}



/-- Available/unrealized checkpoint evidence inherited along a concrete
execution chain. -/
def AU (S : ChainFFGState cfg E anchor)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier : Root,
    E.RootDescends tip carrier ∧ S.formed carrier c

end ChainFFGState
/-- **Deprecated migration API.** Coherence of the opaque beacon-state
functions with the all-scheduled-root `ChainFFGState`.

The genesis fields identify the values already present in the trusted initial
store.  The transition fields apply to every successful scheduled block
transition, including the eager next-boundary pull-up of its post-state.  This
handler-local form is deliberate: exact equations for reachable stores are
then consequences of execution induction, rather than endpoint assumptions.

The final two fields are the projected block-root-history facts which cannot
be proved from the reduced `BeaconState`: they identify epoch-boundary roots
in reachable honest stores. -/
structure FFGTransitionCoherence
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : ChainFFGState cfg E anchor) : Prop where
  /-- The semantic block-body validity oracle is the same abstract primitive
  used by the executable handlers. -/
  attestation_validity : S.attestationValidity =
    ext.is_valid_indexed_attestation

  genesis_gj : ∀ r ∈ E.genesis_store.block_roots,
    (E.genesis_store.block_states r).current_justified_checkpoint = S.GJ r

  genesis_gf : ∀ r ∈ E.genesis_store.block_roots,
    (E.genesis_store.block_states r).finalized_checkpoint = S.GF r

  genesis_gu : ∀ r ∈ E.genesis_store.block_roots,
    (ext.process_justification_and_finalization
      (E.genesis_store.block_states r)
    ).current_justified_checkpoint = S.GU r

  genesis_guf : ∀ r ∈ E.genesis_store.block_roots,
    (ext.process_justification_and_finalization
      (E.genesis_store.block_states r)
    ).finalized_checkpoint = S.GUF r

  genesis_unrealized_justification :
    ∀ r ∈ E.genesis_store.block_roots,
      E.genesis_store.unrealized_justifications r = S.GU r

  transition_gj : ∀ (pre : BeaconState Root)
      (sb : SignedBeaconBlock Root) (post : BeaconState Root),
    (∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n) →
    ext.state_transition pre sb = some post →
    post.current_justified_checkpoint = S.GJ sb.root

  transition_gf : ∀ (pre : BeaconState Root)
      (sb : SignedBeaconBlock Root) (post : BeaconState Root),
    (∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n) →
    ext.state_transition pre sb = some post →
    post.finalized_checkpoint = S.GF sb.root

  transition_gu : ∀ (pre : BeaconState Root)
      (sb : SignedBeaconBlock Root) (post : BeaconState Root),
    (∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n) →
    ext.state_transition pre sb = some post →
      (ext.process_justification_and_finalization
        post).current_justified_checkpoint = S.GU sb.root

  transition_guf : ∀ (pre : BeaconState Root)
      (sb : SignedBeaconBlock Root) (post : BeaconState Root),
    (∃ (w : ValidatorIndex) (n : ℕ),
      Event.block sb ∈ E.schedule w n) →
    ext.state_transition pre sb = some post →
      (ext.process_justification_and_finalization
        post).finalized_checkpoint = S.GUF sb.root

  checkpoint_of_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    ∀ r ∈ (E.store cfg ext w m).block_roots, ∀ e : Epoch,
      S.C r e =
        get_checkpoint_for_block cfg (E.store cfg ext w m) r e

  au_checkpoint_of_known : ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    ∀ r ∈ (E.store cfg ext w m).block_roots,
      ∀ c : Checkpoint Root,
        S.AU cfg r c →
        c = get_checkpoint_for_block cfg
          (E.store cfg ext w m) r c.epoch

namespace AcceptedBlockFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
def IncludedOnChain (S : AcceptedBlockFFGState cfg ext E anchor)
    (tip : Root) (a : Attestation Root) : Prop :=
  AttestationIncludedOnChain E S.includedAttestations.Included tip a

def HasSlashablePairOnChain
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (tip : Root) (i : ValidatorIndex) : Prop :=
  ∃ a₁ a₂ : Attestation Root,
    S.IncludedOnChain cfg ext tip a₁ ∧
    S.IncludedOnChain cfg ext tip a₂ ∧
    i ∈ a₁.attesting_indices ∧
    i ∈ a₂.attesting_indices ∧
    is_slashable_attestation_data a₁.data a₂.data = true

noncomputable def slashableOnChain
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (tip : Root) : Finset ValidatorIndex := by
  classical
  exact (Finset.range E.registry.length).filter
    (S.HasSlashablePairOnChain cfg ext tip)

end AcceptedBlockFFGState
/-- One accepted semantic state and selector interpretation, chosen before
any compatible-prefix variables.  This smaller bundle is the Gate-A
feasibility surface. -/
structure ExactPrefixAcceptedFFGSelectors (E : Execution Root) where
  anchor : Checkpoint Root
  state : AcceptedBlockFFGState cfg ext E anchor
  coherence : FFGStateReadAgreement cfg ext state

/-- A concrete, time-bounded *candidate producer* for the paper's support
antecedent.  Restricting signers to honest validators is stronger than the
paper's "all received votes except `D_b`" formulation.  In particular, this
object alone does not show that the common `source` is `vs(b',e)` for every
descendant `b'`; that bridge must be proved separately. -/
structure HonestTargetQuorumBefore (E : Execution Root)
    (deadline : Slot) (source target : Checkpoint Root) : Type where
  signers : Finset ValidatorIndex
  signers_honest : signers ⊆ E.honest
  signers_in_epoch : signers ⊆
    E.span_committee (target.epoch * cfg.slots_per_epoch)
      (target.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
  signer_vote : ∀ i ∈ signers,
    ∃ (k : ℕ) (a : Attestation Root),
      E.vote i a.data.slot = some (k, a) ∧
      E.SlotWithinHorizon cfg a.data.slot ∧
      a.data.slot < deadline ∧
      a.data.source = source ∧
      a.data.target = target
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers

namespace CheckpointInclusionView
variable {E : Execution Root}
end CheckpointInclusionView

namespace ChainFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}

end ChainFFGState
namespace AcceptedBlockFFGState
variable {E : Execution Root} {anchor : Checkpoint Root}
/-- Accepted-state paper voting-source selector. -/
abbrev voting_source_at (S : AcceptedBlockFFGState cfg ext E anchor)
    (store : Store Root) (b : Root) (e : Epoch) : Checkpoint Root :=
  if get_block_epoch cfg store b = e then S.realized_justified b else S.unrealized_justified b

/-- Accepted-state specialization of support throughout the next epoch. -/
abbrev SourceTargetSupportThroughoutEpoch
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (b : Root) (e : Epoch) : Prop :=
  FastConfirmation.Spec.SourceTargetSupportThroughoutEpoch cfg ext
    (S.checkpoint_inclusion_view cfg ext) b e

/-- Accepted-state specialization of exact link support. -/
abbrev PaperA32LinkSupportAt
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (w : ValidatorIndex) (m : ℕ) (b' : Root)
    (source target : Checkpoint Root) : Type :=
  SourceTargetLinkSupportAt cfg ext (S.checkpoint_inclusion_view cfg ext)
    w m b' source target

end AcceptedBlockFFGState


end FastConfirmation.Spec

end
