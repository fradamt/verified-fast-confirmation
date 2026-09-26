module
public import FastConfirmationStatements.Premises.FFGCertificates
public import FastConfirmationModel.Execution.ScheduledPrefixes

@[expose] public section

/-!
Defines accepted-block FFG evidence and checkpoint views for the safety and inclusion premises.
The executable transcription retains the ordered FFG attestations in block
bodies but abstracts most of the beacon-state FFG machinery. This file supplies the corresponding
semantic objects while keeping fork-choice safety, filtering, and selected FCR
results outside the model boundary.

`AvailableCheckpoint` names the checkpoints with justification
evidence at a tip: a checkpoint is available at a tip when a carrier block on the
tip's chain has formed evidence for it.

There are three interfaces:

* `AcceptedBlockFFGState` is the block-local projection used by the accepted
  theorem. It ranges over exact accepted event-prefix roots and records
  available-checkpoint evidence on exact accepted event-prefix roots.
  `checkpoint_at_epoch` is the epoch checkpoint selector. The fields
  `realized_justified`, `unrealized_justified`, `realized_finalized`, and
  `unrealized_finalized` are the checkpoint reads of a block;
* `FFGStateAndCheckpointReadAgreement` connects the accepted
  projection to actual successful block-handler transitions; and
* `EventualCheckpointInclusion` is the paper's separate liveness assumption.  Its
  antecedent is the paper's link-specific support condition in every honest
  view throughout epoch `e+1`; its conclusion is exact available-checkpoint inclusion in a
  concrete descendant, not the weaker epoch-only consequence read by
  `get_voting_source`.

`FastConfirmationInternal/FFG/InterpretationFidelity.lean` states the intended interpretation of the
included votes. It is not part of the safety premise.

None of these declarations assumes that a block is canonical, safe, retained
by the filter, or selected by the FCR.  Canonicality appears only as an
antecedent of Assumption 3.2.
-/

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

/-- Canonicity throughout one execution epoch.  This is used only as an
antecedent of the paper's Assumption 3.2. -/
def CanonicalThroughoutEpoch (b : Root) (e : Epoch) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    compute_epoch_at_slot cfg (E.slot_at cfg m) = e →
    b ∈ (E.store cfg ext w m).block_roots ∧
      is_ancestor (E.store cfg ext w m)
        (get_head cfg (E.store cfg ext w m))
        (get_node_for_root b) = true

/-- Evidence for one attestation assigned to a carrier block. The
accepted-carrier extension below ties `carrier_message` to the carrier root.

These are the inclusion facts that the safety proof uses. Body membership,
validity, and the validation-state origin are in
`Execution.IncludedAttestationFidelity`, outside the safety premise. The
fidelity record constrains the external indexed-attestation check. -/
structure IncludedAttestationEvidence
    (carrier : Root) (a : Attestation Root) where
  carrier_message : BeaconBlock Root
  received_from_block : ∃ (w : ValidatorIndex) (n : ℕ),
    Event.attestation a true ∈ E.schedule w n
  slot_within_horizon : E.SlotWithinHorizon cfg a.data.slot
  slot_before_carrier : a.data.slot < carrier_message.slot
  target_epoch : a.data.target.epoch =
    compute_epoch_at_slot cfg a.data.slot
  attesters_in_committee : ∀ i ∈ a.attesting_indices,
    i ∈ E.committee a.data.slot

/-- A supplied inclusion relation for ordinary FFG attestations. -/
structure BlockAttestationInclusion where
  /-- Supplied assignment of an attestation to a carrier block. -/
  Included : Root → Attestation Root → Prop
  evidence : ∀ {carrier : Root} {a : Attestation Root},
    Included carrier a →
      IncludedAttestationEvidence cfg E carrier a

/-! ### Accepted positive inclusion carriers -/

/-- Positive inclusion evidence whose exact carrier block occurs in a causal
execution prefix.  This strengthens the projected evidence with
`BlockKnownInScheduledPrefix`, not merely same-root schedule membership. -/
structure AcceptedBlockAttestationEvidence
    (carrier : Root) (a : Attestation Root)
    extends IncludedAttestationEvidence cfg E carrier a where
  carrier_accepted :
    E.BlockKnownInScheduledPrefix cfg ext carrier carrier_message

/-- A supplied positive inclusion relation with an accepted carrier. -/
structure AcceptedBlockAttestationInclusion where
  /-- Carrier-vote assignment with accepted-carrier evidence. -/
  Included : Root → Attestation Root → Prop
  evidence : ∀ {carrier : Root} {a : Attestation Root},
    Included carrier a →
      AcceptedBlockAttestationEvidence cfg ext E carrier a

namespace AcceptedBlockAttestationInclusion

/-- Forget only the accepted-carrier strengthening.  This projects positive
evidence to the broader scheduled-root relation. -/
def relation
    (I : AcceptedBlockAttestationInclusion cfg ext E) :
    BlockAttestationInclusion cfg E where
  Included := I.Included
  evidence := fun h => (I.evidence h).toIncludedAttestationEvidence

end AcceptedBlockAttestationInclusion

end Execution

/-- An attestation occurs in a block on `tip`'s concrete execution chain. -/
def AttestationIncludedOnChain (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (tip : Root) (a : Attestation Root) : Prop :=
  ∃ carrier : Root, E.RootDescends tip carrier ∧ included carrier a

/-- A source-to-target supermajority whose actual attestations occur in block
bodies on `carrier`'s chain.  Unlike `SupermajorityLink`, this is not merely a
global scheduled-gossip certificate. -/
structure IncludedSupermajorityLink (E : Execution Root)
    (included : Root → Attestation Root → Prop) (carrier : Root)
    (source target : Checkpoint Root) : Type where
  signers : Finset ValidatorIndex
  source_before_target : source.epoch < target.epoch
  target_descends_source : E.RootDescends target.root source.root
  target_epoch_within : target.epoch < E.verification_horizon
  target_span_within :
    E.SlotWithinHorizon cfg (target.epoch * cfg.slots_per_epoch) ∧
    E.SlotWithinHorizon cfg
      (target.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
  signers_in_epoch : signers ⊆
    E.span_committee (target.epoch * cfg.slots_per_epoch)
      (target.epoch * cfg.slots_per_epoch + (cfg.slots_per_epoch - 1))
  signer_attestation : ∀ i ∈ signers,
    ∃ a : Attestation Root,
      AttestationIncludedOnChain E included carrier a ∧
      i ∈ a.attesting_indices ∧
      CheckpointReadsAs a.data.source source ∧
      a.data.target = target
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers

/-- Checkpoint justification generated from the trusted anchor using only
links whose votes are included on the particular carrier chain. -/
inductive IncludedCertifiedJustified (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root) (carrier : Root) :
    Checkpoint Root → Prop
  | anchor : IncludedCertifiedJustified E included anchor carrier anchor
  | link {source target : Checkpoint Root} :
      IncludedCertifiedJustified E included anchor carrier source →
      IncludedSupermajorityLink cfg E included carrier source target →
      IncludedCertifiedJustified E included anchor carrier target

/-- Carrier-local Casper finalization: both justification and the immediately
following finalizing link are backed by attestations included on this chain. -/
structure IncludedCertifiedFinalized (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root) (carrier : Root)
    (c : Checkpoint Root) where
  justified : IncludedCertifiedJustified cfg E included anchor carrier c
  child : Checkpoint Root
  child_epoch : child.epoch = c.epoch + 1
  finalizing_link :
    IncludedSupermajorityLink cfg E included carrier c child

/-- Accepted-prefix version of the causal honest formation witness.  The
exact carrier message, rather than only some same-root scheduled message, is
known in a causal store. -/
def HonestEarlierTargetVoteOnCarrierChain (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (carrier : Root) (c : Checkpoint Root) : Prop :=
  ∃ b : BeaconBlock Root, E.BlockKnownInScheduledPrefix cfg ext carrier b ∧
    ∃ i ∈ E.honest, ∃ (s : Slot) (k : ℕ) (a : Attestation Root),
      s < b.slot ∧
      E.SlotWithinHorizon cfg s ∧
      E.vote i s = some (k, a) ∧
      a.data.slot = s ∧
      a.data.target = c ∧
      AttestationIncludedOnChain E included carrier a

/-- Concrete evidence represented by one accepted block-local AU entry.
Certification and inclusion remain positive, while the non-anchor temporal
carrier is an exact accepted block. -/
structure IncludedCheckpointEvidence (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root) (carrier : Root)
    (c : Checkpoint Root) : Prop where
  certified : Nonempty
    (IncludedCertifiedJustified cfg E included anchor carrier c)
  on_chain : E.RootDescends carrier c.root
  causal : c = anchor ∨
    HonestEarlierTargetVoteOnCarrierChain cfg ext E included carrier c

/-! ## Accepted event-prefix FFG semantics -/

/-- The production block-local FFG state.  Selector functions remain total
for Lean convenience, but all semantic laws are restricted to causal-prefix
accepted roots or exact accepted block carriers.  Every positive inclusion
and formed carrier is accepted.

The maximality laws follow the Python timing.  `realized_justified` of a block
in epoch `E` is the result of the epoch-boundary justification runs before
`E`, so it reflects only evidence in blocks of earlier epochs.
`unrealized_justified` runs the same function on the block state at epoch
`E`.  Both runs return early at epochs up to `GENESIS_EPOCH + 1`, hence the
epoch bound in `realized_justified_max`. -/
structure AcceptedBlockFFGState (E : Execution Root)
    (anchor : Checkpoint Root) where
  includedAttestations :
    Execution.AcceptedBlockAttestationInclusion cfg ext E
  checkpoint_evidence_in_block : Root → Checkpoint Root → Prop
  checkpoint_at_epoch : Root → Epoch → Checkpoint Root
  realized_justified : Root → Checkpoint Root
  unrealized_justified : Root → Checkpoint Root
  realized_finalized : Root → Checkpoint Root
  unrealized_finalized : Root → Checkpoint Root
  checkpoint_epoch : ∀ r e, (checkpoint_at_epoch r e).epoch = e
  formed_carrier_accepted : ∀ {r c}, checkpoint_evidence_in_block r c →
    E.RootKnownInScheduledPrefix cfg ext r
  formed_evidence : ∀ {r : Root} {c : Checkpoint Root},
    checkpoint_evidence_in_block r c → IncludedCheckpointEvidence cfg ext E
      includedAttestations.Included anchor r c
  realized_justified_mem : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ checkpoint_evidence_in_block carrier (realized_justified r)
  unrealized_justified_mem : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ checkpoint_evidence_in_block carrier (unrealized_justified r)
  realized_finalized_mem : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ checkpoint_evidence_in_block carrier (realized_finalized r)
  unrealized_finalized_mem : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ checkpoint_evidence_in_block carrier (unrealized_finalized r)
  realized_justified_anchor_or_before : ∀ {r b}, E.BlockKnownInScheduledPrefix cfg ext r b →
    realized_justified r = anchor ∨ (realized_justified r).epoch < compute_epoch_at_slot cfg b.slot
  realized_justified_max : ∀ {r b seed sb c}, E.BlockKnownInScheduledPrefix cfg ext r b →
    E.BlockKnownInScheduledPrefix cfg ext seed sb → E.RootDescends r seed →
    compute_epoch_at_slot cfg sb.slot < compute_epoch_at_slot cfg b.slot →
    GENESIS_EPOCH + 2 < compute_epoch_at_slot cfg b.slot →
    (∃ carrier, E.RootDescends seed carrier ∧ checkpoint_evidence_in_block carrier c) →
    c.epoch ≤ (realized_justified r).epoch
  realized_justified_realized : ∀ {r b}, E.BlockKnownInScheduledPrefix cfg ext r b →
    realized_justified r = anchor ∨
      GENESIS_EPOCH + 2 < compute_epoch_at_slot cfg b.slot ∧
      ∃ seed sb, E.BlockKnownInScheduledPrefix cfg ext seed sb ∧ E.RootDescends r seed ∧
        compute_epoch_at_slot cfg sb.slot < compute_epoch_at_slot cfg b.slot ∧
        ∃ carrier, E.RootDescends seed carrier ∧
          checkpoint_evidence_in_block carrier (realized_justified r)
  unrealized_justified_max : ∀ {r c}, E.RootKnownInScheduledPrefix cfg ext r →
    (∃ carrier, E.RootDescends r carrier ∧ checkpoint_evidence_in_block carrier c) →
    c.epoch ≤ (unrealized_justified r).epoch
  realized_justified_epoch_le_unrealized : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    (realized_justified r).epoch ≤ (unrealized_justified r).epoch
  unrealized_justified_mono : ∀ {seed tip}, E.RootKnownInScheduledPrefix cfg ext seed →
    E.RootKnownInScheduledPrefix cfg ext tip → E.RootDescends tip seed →
    (unrealized_justified seed).epoch ≤ (unrealized_justified tip).epoch
  unrealized_justified_epoch_le_later_realized : ∀ {seed sb tip tb},
    E.BlockKnownInScheduledPrefix cfg ext seed sb →
    E.BlockKnownInScheduledPrefix cfg ext tip tb → E.RootDescends tip seed →
    compute_epoch_at_slot cfg sb.slot < compute_epoch_at_slot cfg tb.slot →
    (unrealized_justified seed).epoch ≤ (realized_justified tip).epoch
  available_checkpoint_epoch_le_block : ∀ {r b c}, E.BlockKnownInScheduledPrefix cfg ext r b →
    (∃ carrier, E.RootDescends r carrier ∧ checkpoint_evidence_in_block carrier c) →
    c.epoch ≤ compute_epoch_at_slot cfg b.slot
  realized_finalized_evidence : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    realized_finalized r = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
      includedAttestations.Included anchor r (realized_finalized r))
  unrealized_finalized_evidence : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    unrealized_finalized r = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
      includedAttestations.Included anchor r (unrealized_finalized r))
  realized_finalized_epoch_le_realized_justified : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    (realized_finalized r).epoch ≤ (realized_justified r).epoch
  unrealized_finalized_epoch_le_unrealized_justified : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    (unrealized_finalized r).epoch ≤ (unrealized_justified r).epoch
  unrealized_finalized_epoch_le_realized_justified : ∀ r, E.RootKnownInScheduledPrefix cfg ext r →
    (unrealized_finalized r).epoch ≤ (realized_justified r).epoch

namespace AcceptedBlockFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- AU ("available or unrealized") membership: a carrier block on the tip's
chain has checkpoint_evidence_in_block evidence for the checkpoint. -/
def AvailableCheckpoint (S : AcceptedBlockFFGState cfg ext E anchor)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier, E.RootDescends tip carrier ∧ S.checkpoint_evidence_in_block carrier c

end AcceptedBlockFFGState

/-- Accepted-only selector coherence.  Its transition equations quantify
only over actual successful `on_block` calls at exact causal prefixes.  Each
raw state or store read reads as the selector (`CheckpointReadsAs`): it is
equal to it, or both are `GENESIS_EPOCH` checkpoints.  Thus a real genesis
anchor state with the stub `Checkpoint(GENESIS_EPOCH, ZERO_HASH)` reads as
the anchor, and its descendants keep that reading until the first
justification. -/
structure FFGStateReadAgreement
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedBlockFFGState cfg ext E anchor) : Prop where
  genesis_gj : ∀ r ∈ E.genesis_store.block_roots,
    CheckpointReadsAs (E.genesis_store.block_states r).current_justified_checkpoint
      (S.realized_justified r)
  genesis_gf : ∀ r ∈ E.genesis_store.block_roots,
    CheckpointReadsAs (E.genesis_store.block_states r).finalized_checkpoint
      (S.realized_finalized r)
  genesis_gu : ∀ r ∈ E.genesis_store.block_roots,
    CheckpointReadsAs (ext.process_justification_and_finalization
      (E.genesis_store.block_states r)).current_justified_checkpoint
      (S.unrealized_justified r)
  genesis_guf : ∀ r ∈ E.genesis_store.block_roots,
    CheckpointReadsAs (ext.process_justification_and_finalization
      (E.genesis_store.block_states r)).finalized_checkpoint
      (S.unrealized_finalized r)
  genesis_unrealized_justification : ∀ r ∈ E.genesis_store.block_roots,
    CheckpointReadsAs (E.genesis_store.unrealized_justifications r)
      (S.unrealized_justified r)
  transition_gj : ∀ t : E.SuccessfulScheduledBlockImport cfg ext,
    CheckpointReadsAs
      (t.postStore.block_states t.signedBlock.root).current_justified_checkpoint
      (S.realized_justified t.signedBlock.root)
  transition_gf : ∀ t : E.SuccessfulScheduledBlockImport cfg ext,
    CheckpointReadsAs
      (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
      (S.realized_finalized t.signedBlock.root)
  transition_gu : ∀ t : E.SuccessfulScheduledBlockImport cfg ext,
    CheckpointReadsAs (ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)
    ).current_justified_checkpoint (S.unrealized_justified t.signedBlock.root)
  transition_guf : ∀ t : E.SuccessfulScheduledBlockImport cfg ext,
    CheckpointReadsAs (ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)
    ).finalized_checkpoint (S.unrealized_finalized t.signedBlock.root)

/-- Accepted selector coherence plus checkpoint reflection at every exact
causal prefix store. -/
structure FFGStateAndCheckpointReadAgreement
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedBlockFFGState cfg ext E anchor) : Prop
    extends FFGStateReadAgreement cfg ext S where
  checkpoint_of_known : ∀ {store : Store Root},
    E.ScheduledPrefixStore cfg ext store → ∀ r ∈ store.block_roots, ∀ e,
      S.checkpoint_at_epoch r e = get_checkpoint_for_block cfg store r e
  available_checkpoint_checkpoint_of_known : ∀ {store : Store Root},
    E.ScheduledPrefixStore cfg ext store → ∀ r ∈ store.block_roots, ∀ c,
      S.AvailableCheckpoint cfg ext r c →
      c = get_checkpoint_for_block cfg store r c.epoch

/-- The exact-prefix bundle with causal-store checkpoint reflection.
Its accepted inclusion relation has an accepted carrier block. Body
membership and validation origin are in `FFGInterpretationFidelity`, which
is not a safety premise. The bundle does not cover delayed queues or
arbitrary global action traces. -/
structure ScheduledFFGInterpretation (E : Execution Root) where
  anchor : Checkpoint Root
  state : AcceptedBlockFFGState cfg ext E anchor
  coherence : FFGStateAndCheckpointReadAgreement cfg ext state

/-- A wire attestation has reached validator `w`'s execution view by second
`m`.  The schedule is the model's received-message history; validity and
link identity are recorded by the support certificate below. -/
def Execution.AttestationReceivedBy
    (E : Execution Root) (w : ValidatorIndex) (m : ℕ)
    (a : Attestation Root) : Prop :=
  ∃ k ≤ m, ∃ fromBlock : Bool,
    Event.attestation a fromBlock ∈ E.schedule w k

/-- The positive state ingredients used by paper Assumption 3.2.

This is a projection of one already-selected semantic state, not a fresh
state existentially chosen per call.  Included-attestation evidence is kept
losslessly so `D_b` remains the concrete block-local slashing set, and AU is
derived below from the same checkpoint_evidence_in_block-carrier relation as the source state. -/
structure CheckpointInclusionView (E : Execution Root) where
  /-- Carrier domain for the block whose canonicality triggers A.3.2. -/
  BlockAt : Root → BeaconBlock Root → Prop
  includedAttestations :
    Execution.BlockAttestationInclusion cfg E
  formed : Root → Checkpoint Root → Prop
  C : Root → Epoch → Checkpoint Root
  GJ : Root → Checkpoint Root
  GU : Root → Checkpoint Root
  checkpoint_epoch : ∀ r e, (C r e).epoch = e

namespace CheckpointInclusionView

variable {E : Execution Root}

/-- AU ("available or unrealized") membership inherited from a formed carrier
on the tip's chain. -/
def AvailableCheckpoint (V : CheckpointInclusionView cfg E)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier : Root, E.RootDescends tip carrier ∧ V.formed carrier c

/-- The concrete block-body equivocation predicate underlying `D_b`. -/
def HasSlashablePairOnChain (V : CheckpointInclusionView cfg E)
    (tip : Root) (i : ValidatorIndex) : Prop :=
  ∃ a₁ a₂ : Attestation Root,
    AttestationIncludedOnChain E V.includedAttestations.Included tip a₁ ∧
    AttestationIncludedOnChain E V.includedAttestations.Included tip a₂ ∧
    i ∈ a₁.attesting_indices ∧
    i ∈ a₂.attesting_indices ∧
    is_slashable_attestation_data a₁.data a₂.data = true

/-- `D_b`, computed from actual included attestation payloads. -/
noncomputable def slashableOnChain (V : CheckpointInclusionView cfg E)
    (tip : Root) : Finset ValidatorIndex := by
  classical
  exact (Finset.range E.registry.length).filter
    (V.HasSlashablePairOnChain cfg tip)

/-- The paper's source selector `vs(b,e)`, expressed through the block-local
AU selectors and a reachable store's exact block epoch.

Definition 7 only defines this selector when the block epoch is at most `e`.
Callers representing paper statements therefore carry that domain fact
explicitly; this executable helper remains total for internal phase0 lemmas
which already establish the same/current-or-earlier dichotomy. -/
def voting_source_at (V : CheckpointInclusionView cfg E) (store : Store Root)
    (b : Root) (e : Epoch) : Checkpoint Root :=
  if get_block_epoch cfg store b = e then V.GJ b else V.GU b

end CheckpointInclusionView

/-- Lossless positive A.3.2 projection of the accepted-prefix state.  The
ordinary relation forgets only its extra accepted-carrier proof. -/
def AcceptedBlockFFGState.checkpoint_inclusion_view
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedBlockFFGState cfg ext E anchor) :
    CheckpointInclusionView cfg E where
  BlockAt := E.BlockKnownInScheduledPrefix cfg ext
  includedAttestations := S.includedAttestations.relation
  formed := S.checkpoint_evidence_in_block
  C := S.checkpoint_at_epoch
  GJ := S.realized_justified
  GU := S.unrealized_justified
  checkpoint_epoch := S.checkpoint_epoch

/-- The exact link-specific support term in Assumption 3.2 at one honest
view/time/descendant.

`signers` are validators whose received valid FFG attestations name precisely
`source → target`, after removing the block-local slashable set `D_b'`.
The static-validator-set premise used by the public theorem identifies the
paper's `W_t^{b'}` with `E.total_active`; this record deliberately does not
replace a source-specific link by target-only LMD support. -/
structure SourceTargetLinkSupportAt
    {E : Execution Root} (V : CheckpointInclusionView cfg E)
    (w : ValidatorIndex) (m : ℕ) (b' : Root)
    (source target : Checkpoint Root) : Type where
  view_within_horizon : E.WithinHorizon cfg m
  source_before_target : source.epoch < target.epoch
  target_epoch_within : target.epoch < E.verification_horizon
  target_known : target.root ∈ (E.store cfg ext w m).block_roots
  target_state_keyed :
    target ∈ (E.store cfg ext w m).checkpoint_state_keys
  signers : Finset ValidatorIndex
  signers_not_slashable : ∀ i ∈ signers,
    i ∉ V.slashableOnChain cfg b'
  signers_in_registry : signers ⊆ Finset.range E.registry.length
  signer_attestation : ∀ i ∈ signers,
    ∃ a : Attestation Root,
      E.AttestationReceivedBy w m a ∧
      i ∈ a.attesting_indices ∧
      ext.is_valid_indexed_attestation
        ((E.store cfg ext w m).checkpoint_states target) a = true ∧
      E.SlotWithinHorizon cfg a.data.slot ∧
      a.data.slot ≤ E.slot_at cfg m ∧
      compute_epoch_at_slot cfg a.data.slot = target.epoch ∧
      i ∈ E.committee a.data.slot ∧
      CheckpointReadsAs a.data.source source ∧
      a.data.target = target
  supermajority : 2 * E.total_active cfg ≤ 3 * E.weight signers

/-- Assumption 3.2's support premise throughout epoch `e+1`: every honest
view, for every known block `b' ⪰ C(b,e)`, has a two-thirds link from the
fixed paper voting source `vs(b,e)` to the exact target `C(b,e)`, after
excluding `D_b'`.

The quantified descendant indexes the paper's block-local slashable set and
active weight; it does not replace the fixed source by `vs(b',e)`.  The base
block's knownness and `epoch(b) ≤ e` are recorded at each concrete view so
that Definition 7 is never silently read on its undefined future-block
branch.

The paper also asks `st(e+1) ≥ GST`.  The spec execution begins inside the
globally synchronous segment, so that temporal guard is represented by the
ambient `Synchrony`/horizon premises rather than a second clock constant. -/
def SourceTargetSupportThroughoutEpoch
    {E : Execution Root} (V : CheckpointInclusionView cfg E)
    (b : Root) (e : Epoch) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    compute_epoch_at_slot cfg (E.slot_at cfg m) = e + 1 →
    b ∈ (E.store cfg ext w m).block_roots ∧
      get_block_epoch cfg (E.store cfg ext w m) b ≤ e ∧
      ∀ b' ∈ (E.store cfg ext w m).block_roots,
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root b') (get_node_for_root (V.C b e).root) = true →
        Nonempty (SourceTargetLinkSupportAt cfg ext V w m b'
          (V.voting_source_at cfg (E.store cfg ext w m) b e) (V.C b e))

/-- Paper Assumption 3.2, separated from state-transition coherence.

This is the paper's quantifier shape: if `b` is canonical and the exact fixed
`vs(b,e)`-to-`C(b,e)` support condition holds in every honest view throughout
epoch `e+1`, then by `st(e+2)` each honest view contains a pre-boundary
descendant carrying `C(b,e)` in AU.  Target-only support or a free
`A32IncludedAtTip` consequence is intentionally insufficient. -/
structure EventualCheckpointInclusion
    {E : Execution Root} (V : CheckpointInclusionView cfg E) : Prop where
  included : ∀ {b : Root} {bb : BeaconBlock Root} {e : Epoch},
    V.BlockAt b bb →
    compute_epoch_at_slot cfg bb.slot ≤ e →
    E.CanonicalThroughoutEpoch cfg ext b (e + 1) →
    SourceTargetSupportThroughoutEpoch cfg ext V b e →
    ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      compute_start_slot_at_epoch cfg (e + 2) ≤ E.slot_at cfg m →
      ∃ b' ∈ (E.store cfg ext w m).block_roots,
        b ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root b') (get_node_for_root b) = true ∧
        get_block_epoch cfg (E.store cfg ext w m) b' < e + 2 ∧
        V.AvailableCheckpoint cfg b' (V.C b e)

namespace AcceptedBlockFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- Accepted-state specialization of paper Assumption 3.2. -/
abbrev EventualCheckpointInclusion
    (S : AcceptedBlockFFGState cfg ext E anchor) : Prop :=
  FastConfirmation.Spec.EventualCheckpointInclusion cfg ext
    (S.checkpoint_inclusion_view cfg ext)

end AcceptedBlockFFGState

end FastConfirmation.Spec

end
