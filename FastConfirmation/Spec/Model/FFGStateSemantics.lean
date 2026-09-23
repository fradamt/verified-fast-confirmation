module
public import FastConfirmation.Spec.Model.FFGCertificates
public import FastConfirmation.Spec.Model.AcceptedExecution

@[expose] public section

/-!
# Spec / Model / FFGStateSemantics

The executable transcription deliberately omits beacon-block bodies and most
of the beacon-state FFG machinery.  This file supplies the corresponding
semantic objects while keeping fork-choice safety, filtering, and selected FCR
results outside the model boundary.

There are four interfaces:

* `AcceptedChainFFGState` is the block-local projection used by the accepted
  theorem. It ranges over exact accepted event-prefix roots and records
  available/unrealized checkpoint evidence on exact accepted event-prefix
  roots;
* `ChainFFGState` is a broader projection over every scheduled wire root,
  used by generic internal lemmas about checkpoint evidence and the `C`,
  `GJ`, `GU`, and `GF` selectors;
* `AcceptedFFGTransitionCoherence` connects the accepted projection to actual
  successful block-handler transitions; `FFGTransitionCoherence` is the
  corresponding scheduled-root interface; and
* `PaperA32Inclusion` is the paper's separate liveness assumption.  Its
  antecedent is the paper's link-specific support condition in every honest
  view throughout epoch `e+1`; its conclusion is exact AU inclusion in a
  concrete descendant, not the weaker epoch-only consequence read by
  `get_voting_source`.

None of these declarations assumes that a block is canonical, safe, retained
by the filter, or selected by the FCR.  Canonicality appears only as an
antecedent of Assumption 3.2.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

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

/-- Evidence for one attestation in a concrete beacon-block body.

Block bodies are projected out of `BeaconBlock`, so inclusion itself has to
be supplied semantically.  The evidence below restores the constraints that
matter to FFG: the carrier and wire attestation are concrete execution
objects, the attestation passes the supplied indexed-attestation validity
oracle on the ground registry, it is assigned to the exact slot committee,
its source/target roots lie on the carrier chain, and its attested head lies
on the target's chain (it may fork from the carrier after that boundary). -/
structure IncludedAttestationEvidence
    (validity : BeaconState Root → Attestation Root → Bool)
    (carrier : Root) (a : Attestation Root) where
  carrier_message : BeaconBlock Root
  carrier_at : E.BlockAt carrier carrier_message
  received_from_block : ∃ (w : ValidatorIndex) (n : ℕ),
    Event.attestation a true ∈ E.schedule w n
  validation_state : BeaconState Root
  validation_registry : validation_state.validators = E.registry
  valid : validity validation_state a = true
  slot_within_horizon : E.SlotWithinHorizon cfg a.data.slot
  slot_before_carrier : a.data.slot < carrier_message.slot
  target_epoch : a.data.target.epoch =
    compute_epoch_at_slot cfg a.data.slot
  /-- The attested LMD head may fork from the including block after the target
  boundary; validity requires the head to descend the target, not to descend
  the carrier. -/
  head_descends_target :
    E.RootDescends a.data.beacon_block_root a.data.target.root
  target_on_chain : E.RootDescends carrier a.data.target.root
  target_descends_source :
    E.RootDescends a.data.target.root a.data.source.root
  attesters_in_committee : ∀ i ∈ a.attesting_indices,
    i ∈ E.committee a.data.slot
  attesters_in_registry : ∀ i ∈ a.attesting_indices,
    i < E.registry.length

/-- The semantic block-body attestation payload omitted by the executable
`BeaconBlock` projection.  `Included carrier a` means actual inclusion, not
mere gossip receipt; `evidence` makes that primitive relation accountable to
the concrete execution and to a validity oracle. -/
structure IncludedAttestationRelation
    (validity : BeaconState Root → Attestation Root → Bool) where
  Included : Root → Attestation Root → Prop
  evidence : ∀ {carrier : Root} {a : Attestation Root},
    Included carrier a →
      IncludedAttestationEvidence cfg E validity carrier a

/-! ### Accepted positive inclusion carriers -/

/-- Positive inclusion evidence whose exact carrier block occurs in a causal
execution prefix.  This strengthens the projected block-body evidence with
`AcceptedBlockAt`, not merely same-root schedule membership. -/
structure AcceptedIncludedAttestationEvidence
    (validity : BeaconState Root → Attestation Root → Bool)
    (carrier : Root) (a : Attestation Root)
    extends IncludedAttestationEvidence cfg E validity carrier a where
  carrier_accepted :
    E.AcceptedBlockAt cfg ext carrier carrier_message

/-- A positive block-body inclusion relation all of whose exact carrier
messages are accepted in the causal event-prefix domain. -/
structure AcceptedIncludedAttestationRelation
    (validity : BeaconState Root → Attestation Root → Bool) where
  Included : Root → Attestation Root → Prop
  evidence : ∀ {carrier : Root} {a : Attestation Root},
    Included carrier a →
      AcceptedIncludedAttestationEvidence cfg ext E validity carrier a

namespace AcceptedIncludedAttestationRelation

/-- Forget only the accepted-carrier strengthening.  This projects positive
evidence to the broader scheduled-root relation. -/
def relation
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : AcceptedIncludedAttestationRelation cfg ext E validity) :
    IncludedAttestationRelation cfg E validity where
  Included := I.Included
  evidence := fun h => (I.evidence h).toIncludedAttestationEvidence

end AcceptedIncludedAttestationRelation

end Execution

/-- An attestation occurs in a block on `tip`'s concrete execution chain. -/
def AttestationIncludedOnChain (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (tip : Root) (a : Attestation Root) : Prop :=
  ∃ carrier : Root, E.RootDescends tip carrier ∧ included carrier a

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
      a.data.source = source ∧
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

namespace IncludedSupermajorityLink

/-- Forget carrier locality while retaining the exact scheduled attestations.
This is the sound direction from the stronger block-body certificate to the
older global certificate API. -/
def toSupermajorityLink
    {E : Execution Root}
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : Execution.IncludedAttestationRelation cfg E validity)
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
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : Execution.IncludedAttestationRelation cfg E validity)
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
    {validity : BeaconState Root → Attestation Root → Bool}
    (I : Execution.IncludedAttestationRelation cfg E validity)
    {anchor : Checkpoint Root} {carrier : Root} {c : Checkpoint Root}
    (F : IncludedCertifiedFinalized cfg E I.Included anchor carrier c) :
    CertifiedFinalized cfg E anchor c where
  justified := IncludedCertifiedJustified.toCertifiedJustified
    (cfg := cfg) I F.justified
  child := F.child
  child_epoch := F.child_epoch
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

/-- Accepted-prefix version of the causal honest formation witness.  The
exact carrier message, rather than only some same-root scheduled message, is
known in a causal store. -/
def AcceptedHonestTargetIncludedBeforeCarrier (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (carrier : Root) (c : Checkpoint Root) : Prop :=
  ∃ b : BeaconBlock Root, E.AcceptedBlockAt cfg ext carrier b ∧
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
structure AcceptedFormedCheckpointEvidence (E : Execution Root)
    (included : Root → Attestation Root → Prop)
    (anchor : Checkpoint Root) (carrier : Root)
    (c : Checkpoint Root) : Prop where
  certified : Nonempty
    (IncludedCertifiedJustified cfg E included anchor carrier c)
  on_chain : E.RootDescends carrier c.root
  causal : c = anchor ∨
    AcceptedHonestTargetIncludedBeforeCarrier cfg ext E included carrier c

/-! ## Scheduled-root checkpoint state

The declarations through `FFGTransitionCoherence` below constrain every
scheduled block root. The accepted theorem instead uses
`AcceptedChainFFGState` and `AcceptedFFGTransitionCoherence`, which range only
over successful accepted prefixes. There is intentionally no conversion
between the two domains.
-/

/-- The block-local FFG state omitted by the
executable `BeaconState`, quantified over every scheduled wire root.

`formed carrier c` means that `carrier` contains sufficient available /
unrealized evidence for `c`.  AU at a tip is defined below by inheriting such
evidence from a carrier on the tip's chain. -/
structure ChainFFGState (E : Execution Root)
    (anchor : Checkpoint Root) where
  /-- Indexed-attestation validity oracle used by the omitted block-body
  projection.  `FFGTransitionCoherence` identifies it with the execution's
  actual `Externals.is_valid_indexed_attestation`. -/
  attestationValidity : BeaconState Root → Attestation Root → Bool

  /-- Actual block-body inclusion, with carrier, validity, committee, horizon,
  and chain-position evidence. -/
  includedAttestations :
    Execution.IncludedAttestationRelation cfg E attestationValidity

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


/-- Inclusion somewhere on a concrete tip's ancestor chain. -/
def IncludedOnChain (S : ChainFFGState cfg E anchor)
    (tip : Root) (a : Attestation Root) : Prop :=
  AttestationIncludedOnChain E S.includedAttestations.Included tip a

/-- A validator has two slashable FFG attestations in block bodies on the
chain of `tip`.  This is the paper's semantic offense predicate underlying
`D_b`; it deliberately does not read the node-local gossip slashing cache. -/
def HasSlashablePairOnChain (S : ChainFFGState cfg E anchor)
    (tip : Root) (i : ValidatorIndex) : Prop :=
  ∃ a₁ a₂ : Attestation Root,
    S.IncludedOnChain cfg tip a₁ ∧
    S.IncludedOnChain cfg tip a₂ ∧
    i ∈ a₁.attesting_indices ∧
    i ∈ a₂.attesting_indices ∧
    is_slashable_attestation_data a₁.data a₂.data = true

/-- `D_b`, derived rather than supplied: registry validators for which the
actual attestation payload of `chain(b)` contains a slashable pair. -/
noncomputable def slashableOnChain (S : ChainFFGState cfg E anchor)
    (tip : Root) : Finset ValidatorIndex := by
  classical
  exact (Finset.range E.registry.length).filter
    (S.HasSlashablePairOnChain cfg tip)

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

/-! ## Accepted event-prefix FFG semantics -/

/-- The production block-local FFG state.  Selector functions remain total
for Lean convenience, but all semantic laws are restricted to causal-prefix
accepted roots or exact accepted block carriers.  Every positive inclusion
and formed carrier is accepted. -/
structure AcceptedChainFFGState (E : Execution Root)
    (anchor : Checkpoint Root) where
  attestationValidity : BeaconState Root → Attestation Root → Bool
  includedAttestations :
    Execution.AcceptedIncludedAttestationRelation cfg ext E
      attestationValidity
  formed : Root → Checkpoint Root → Prop
  C : Root → Epoch → Checkpoint Root
  GJ : Root → Checkpoint Root
  GU : Root → Checkpoint Root
  GF : Root → Checkpoint Root
  GUF : Root → Checkpoint Root
  checkpoint_epoch : ∀ r e, (C r e).epoch = e
  formed_carrier_accepted : ∀ {r c}, formed r c →
    E.AcceptedRoot cfg ext r
  formed_evidence : ∀ {r : Root} {c : Checkpoint Root},
    formed r c → AcceptedFormedCheckpointEvidence cfg ext E
      includedAttestations.Included anchor r c
  gj_mem : ∀ r, E.AcceptedRoot cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GJ r)
  gu_mem : ∀ r, E.AcceptedRoot cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GU r)
  gf_mem : ∀ r, E.AcceptedRoot cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GF r)
  guf_mem : ∀ r, E.AcceptedRoot cfg ext r →
    ∃ carrier, E.RootDescends r carrier ∧ formed carrier (GUF r)
  gj_anchor_or_before : ∀ {r b}, E.AcceptedBlockAt cfg ext r b →
    GJ r = anchor ∨ (GJ r).epoch < compute_epoch_at_slot cfg b.slot
  gj_max : ∀ {r b c}, E.AcceptedBlockAt cfg ext r b →
    (∃ carrier, E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch < compute_epoch_at_slot cfg b.slot → c.epoch ≤ (GJ r).epoch
  gu_max : ∀ {r c}, E.AcceptedRoot cfg ext r →
    (∃ carrier, E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch ≤ (GU r).epoch
  au_epoch_le_block : ∀ {r b c}, E.AcceptedBlockAt cfg ext r b →
    (∃ carrier, E.RootDescends r carrier ∧ formed carrier c) →
    c.epoch ≤ compute_epoch_at_slot cfg b.slot
  gf_evidence : ∀ r, E.AcceptedRoot cfg ext r →
    GF r = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
      includedAttestations.Included anchor r (GF r))
  guf_evidence : ∀ r, E.AcceptedRoot cfg ext r →
    GUF r = anchor ∨ Nonempty (IncludedCertifiedFinalized cfg E
      includedAttestations.Included anchor r (GUF r))
  gf_epoch_le_gj : ∀ r, E.AcceptedRoot cfg ext r →
    (GF r).epoch ≤ (GJ r).epoch
  guf_epoch_le_gu : ∀ r, E.AcceptedRoot cfg ext r →
    (GUF r).epoch ≤ (GU r).epoch
  gf_epoch_le_guf : ∀ r, E.AcceptedRoot cfg ext r →
    (GF r).epoch ≤ (GUF r).epoch

namespace AcceptedChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}


def IncludedOnChain (S : AcceptedChainFFGState cfg ext E anchor)
    (tip : Root) (a : Attestation Root) : Prop :=
  AttestationIncludedOnChain E S.includedAttestations.Included tip a

def HasSlashablePairOnChain
    (S : AcceptedChainFFGState cfg ext E anchor)
    (tip : Root) (i : ValidatorIndex) : Prop :=
  ∃ a₁ a₂ : Attestation Root,
    S.IncludedOnChain cfg ext tip a₁ ∧
    S.IncludedOnChain cfg ext tip a₂ ∧
    i ∈ a₁.attesting_indices ∧
    i ∈ a₂.attesting_indices ∧
    is_slashable_attestation_data a₁.data a₂.data = true

noncomputable def slashableOnChain
    (S : AcceptedChainFFGState cfg ext E anchor)
    (tip : Root) : Finset ValidatorIndex := by
  classical
  exact (Finset.range E.registry.length).filter
    (S.HasSlashablePairOnChain cfg ext tip)

def AU (S : AcceptedChainFFGState cfg ext E anchor)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier, E.RootDescends tip carrier ∧ S.formed carrier c

end AcceptedChainFFGState

/-- Accepted-only selector coherence.  Its transition equations quantify
only over actual successful `on_block` calls at exact causal prefixes. -/
structure AcceptedFFGSelectorCoherence
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor) : Prop where
  attestation_validity : S.attestationValidity =
    ext.is_valid_indexed_attestation
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
  /-- The genesis store's `unrealized_justifications` map agrees with the
      semantic `GU` selector on every anchor root.

      **DISCLOSURE (`docs/plumbing-spec-citations.md` P-3): together with
      `genesis_gu` this over-constrains the pinned initializer.**
      `get_forkchoice_store` (fork-choice.md:215) stores the *un-pulled*
      value, `unrealized_justifications={anchor_root: justified_checkpoint}`,
      where `justified_checkpoint = Checkpoint(anchor_epoch, anchor_root)`.
      `genesis_gu` separately says
      `pjf(anchor_state).current_justified_checkpoint = GU anchor_root`, i.e.
      the *pulled-up* value.  The two fields together therefore demand
      `pjf(anchor_state).current_justified_checkpoint =
      Checkpoint(anchor_epoch, anchor_root)` — an extra contract on
      `ext.process_justification_and_finalization` AT THE ANCHOR STATE, which
      `get_forkchoice_store` does not establish and which the pinned spec does
      not state anywhere.  It is true of a trusted anchor that is itself a
      justified boundary state (the checkpoint-sync case this development
      already restricts to via `TrustedAnchorBoundaryAligned`), and it is in
      that sense a companion of the trust-boundary premise rather than a
      transcription of the initializer.  Nothing weaker is used: the field is
      read only at the anchor root. -/
  genesis_unrealized_justification : ∀ r ∈ E.genesis_store.block_roots,
    E.genesis_store.unrealized_justifications r = S.GU r
  transition_gj : ∀ t : E.AcceptedBlockTransition cfg ext,
    (t.postStore.block_states t.signedBlock.root).current_justified_checkpoint =
      S.GJ t.signedBlock.root
  transition_gf : ∀ t : E.AcceptedBlockTransition cfg ext,
    (t.postStore.block_states t.signedBlock.root).finalized_checkpoint =
      S.GF t.signedBlock.root
  transition_gu : ∀ t : E.AcceptedBlockTransition cfg ext,
    (ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)
    ).current_justified_checkpoint = S.GU t.signedBlock.root
  transition_guf : ∀ t : E.AcceptedBlockTransition cfg ext,
    (ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)
    ).finalized_checkpoint = S.GUF t.signedBlock.root

/-- Accepted selector coherence plus checkpoint reflection at every exact
causal prefix store. -/
structure AcceptedFFGTransitionCoherence
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor) : Prop
    extends AcceptedFFGSelectorCoherence cfg ext S where
  checkpoint_of_known : ∀ {store : Store Root},
    E.CausalStore cfg ext store → ∀ r ∈ store.block_roots, ∀ e,
      S.C r e = get_checkpoint_for_block cfg store r e
  au_checkpoint_of_known : ∀ {store : Store Root},
    E.CausalStore cfg ext store → ∀ r ∈ store.block_roots, ∀ c,
      S.AU cfg ext r c →
      c = get_checkpoint_for_block cfg store r c.epoch

/-- One accepted semantic state and selector interpretation, chosen before
any compatible-prefix variables.  This smaller bundle is the Gate-A
feasibility surface. -/
structure ExactPrefixAcceptedFFGSelectors (E : Execution Root) where
  anchor : Checkpoint Root
  state : AcceptedChainFFGState cfg ext E anchor
  coherence : AcceptedFFGSelectorCoherence cfg ext state

/-- The production exact-prefix bundle, adding causal-store checkpoint
reflection to the same globally selected semantic state.  It does not claim
coverage of delayed queues or arbitrary global action traces. -/
structure ExactPrefixAcceptedFFGSemantics (E : Execution Root) where
  anchor : Checkpoint Root
  state : AcceptedChainFFGState cfg ext E anchor
  coherence : AcceptedFFGTransitionCoherence cfg ext state

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
derived below from the same formed-carrier relation as the source state. -/
structure PaperA32StateView (E : Execution Root) where
  /-- Carrier domain for the block whose canonicality triggers A.3.2. -/
  BlockAt : Root → BeaconBlock Root → Prop
  attestationValidity : BeaconState Root → Attestation Root → Bool
  includedAttestations :
    Execution.IncludedAttestationRelation cfg E attestationValidity
  formed : Root → Checkpoint Root → Prop
  C : Root → Epoch → Checkpoint Root
  GJ : Root → Checkpoint Root
  GU : Root → Checkpoint Root
  checkpoint_epoch : ∀ r e, (C r e).epoch = e

namespace PaperA32StateView

variable {E : Execution Root}

/-- Available/unrealized evidence inherited from a formed carrier on the
tip's chain. -/
def AU (V : PaperA32StateView cfg E)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier : Root, E.RootDescends tip carrier ∧ V.formed carrier c

/-- The concrete block-body equivocation predicate underlying `D_b`. -/
def HasSlashablePairOnChain (V : PaperA32StateView cfg E)
    (tip : Root) (i : ValidatorIndex) : Prop :=
  ∃ a₁ a₂ : Attestation Root,
    AttestationIncludedOnChain E V.includedAttestations.Included tip a₁ ∧
    AttestationIncludedOnChain E V.includedAttestations.Included tip a₂ ∧
    i ∈ a₁.attesting_indices ∧
    i ∈ a₂.attesting_indices ∧
    is_slashable_attestation_data a₁.data a₂.data = true

/-- `D_b`, computed from actual included attestation payloads. -/
noncomputable def slashableOnChain (V : PaperA32StateView cfg E)
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
def VSAt (V : PaperA32StateView cfg E) (store : Store Root)
    (b : Root) (e : Epoch) : Checkpoint Root :=
  if get_block_epoch cfg store b = e then V.GJ b else V.GU b

end PaperA32StateView

/-- Lossless A.3.2 projection of the migration-only scheduled-root state. -/
def ChainFFGState.paperA32View
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : ChainFFGState cfg E anchor) : PaperA32StateView cfg E where
  BlockAt := E.BlockAt
  attestationValidity := S.attestationValidity
  includedAttestations := S.includedAttestations
  formed := S.formed
  C := S.C
  GJ := S.GJ
  GU := S.GU
  checkpoint_epoch := S.checkpoint_epoch

/-- Lossless positive A.3.2 projection of the accepted-prefix state.  The
ordinary relation forgets only its extra accepted-carrier proof. -/
def AcceptedChainFFGState.paperA32View
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : AcceptedChainFFGState cfg ext E anchor) :
    PaperA32StateView cfg E where
  BlockAt := E.AcceptedBlockAt cfg ext
  attestationValidity := S.attestationValidity
  includedAttestations := S.includedAttestations.relation
  formed := S.formed
  C := S.C
  GJ := S.GJ
  GU := S.GU
  checkpoint_epoch := S.checkpoint_epoch

/-- The exact link-specific support term in Assumption 3.2 at one honest
view/time/descendant.

`signers` are validators whose received valid FFG attestations name precisely
`source → target`, after removing the block-local slashable set `D_b'`.
The static-validator-set premise used by the public theorem identifies the
paper's `W_t^{b'}` with `E.total_active`; this record deliberately does not
replace a source-specific link by target-only LMD support. -/
structure PaperA32LinkSupportAtCore
    {E : Execution Root} (V : PaperA32StateView cfg E)
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
      a.data.source = source ∧
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
def PaperA32SupportThroughoutEpochCore
    {E : Execution Root} (V : PaperA32StateView cfg E)
    (b : Root) (e : Epoch) : Prop :=
  ∀ w ∈ E.honest, ∀ m : ℕ,
    E.WithinHorizon cfg m →
    compute_epoch_at_slot cfg (E.slot_at cfg m) = e + 1 →
    b ∈ (E.store cfg ext w m).block_roots ∧
      get_block_epoch cfg (E.store cfg ext w m) b ≤ e ∧
      ∀ b' ∈ (E.store cfg ext w m).block_roots,
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root b') (get_node_for_root (V.C b e).root) = true →
        Nonempty (PaperA32LinkSupportAtCore cfg ext V w m b'
          (V.VSAt cfg (E.store cfg ext w m) b e) (V.C b e))

/-- Paper Assumption 3.2, separated from state-transition coherence.

This is the paper's quantifier shape: if `b` is canonical and the exact fixed
`vs(b,e)`-to-`C(b,e)` support condition holds in every honest view throughout
epoch `e+1`, then by `st(e+2)` each honest view contains a pre-boundary
descendant carrying `C(b,e)` in AU.  Target-only support or a free
`A32IncludedAtTip` consequence is intentionally insufficient. -/
structure PaperA32InclusionCore
    {E : Execution Root} (V : PaperA32StateView cfg E) : Prop where
  included : ∀ {b : Root} {bb : BeaconBlock Root} {e : Epoch},
    V.BlockAt b bb →
    compute_epoch_at_slot cfg bb.slot ≤ e →
    E.CanonicalThroughoutEpoch cfg ext b (e + 1) →
    PaperA32SupportThroughoutEpochCore cfg ext V b e →
    ∀ w ∈ E.honest, ∀ m : ℕ,
      E.WithinHorizon cfg m →
      compute_start_slot_at_epoch cfg (e + 2) ≤ E.slot_at cfg m →
      ∃ b' ∈ (E.store cfg ext w m).block_roots,
        b ∈ (E.store cfg ext w m).block_roots ∧
        is_ancestor (E.store cfg ext w m)
          (get_node_for_root b') (get_node_for_root b) = true ∧
        get_block_epoch cfg (E.store cfg ext w m) b' < e + 2 ∧
        V.AU cfg b' (V.C b e)

namespace ChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- Migration-only alias for the generic paper voting-source selector. -/
abbrev VSAt (S : ChainFFGState cfg E anchor) (store : Store Root)
    (b : Root) (e : Epoch) : Checkpoint Root :=
  if get_block_epoch cfg store b = e then S.GJ b else S.GU b

end ChainFFGState

namespace AcceptedChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- Accepted-state paper voting-source selector. -/
abbrev VSAt (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (b : Root) (e : Epoch) : Checkpoint Root :=
  if get_block_epoch cfg store b = e then S.GJ b else S.GU b

/-- Accepted-state specialization of exact link support. -/
abbrev PaperA32LinkSupportAt
    (S : AcceptedChainFFGState cfg ext E anchor)
    (w : ValidatorIndex) (m : ℕ) (b' : Root)
    (source target : Checkpoint Root) : Type :=
  PaperA32LinkSupportAtCore cfg ext (S.paperA32View cfg ext)
    w m b' source target

/-- Accepted-state specialization of support throughout the next epoch. -/
abbrev PaperA32SupportThroughoutEpoch
    (S : AcceptedChainFFGState cfg ext E anchor)
    (b : Root) (e : Epoch) : Prop :=
  PaperA32SupportThroughoutEpochCore cfg ext (S.paperA32View cfg ext) b e

/-- Accepted-state specialization of paper Assumption 3.2. -/
abbrev PaperA32Inclusion
    (S : AcceptedChainFFGState cfg ext E anchor) : Prop :=
  PaperA32InclusionCore cfg ext (S.paperA32View cfg ext)

end AcceptedChainFFGState

/-! ## Scheduled-root specializations -/


/-- Support antecedent for the scheduled-root state. -/
abbrev PaperA32SupportThroughoutEpoch
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : ChainFFGState cfg E anchor) (b : Root) (e : Epoch) : Prop :=
  PaperA32SupportThroughoutEpochCore cfg ext (S.paperA32View cfg) b e

/-- Paper inclusion assumption for the scheduled-root state. -/
abbrev PaperA32Inclusion
    {E : Execution Root} {anchor : Checkpoint Root}
    (S : ChainFFGState cfg E anchor) : Prop :=
  PaperA32InclusionCore cfg ext (S.paperA32View cfg)

end FastConfirmation.Spec

end
