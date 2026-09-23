module
public import FastConfirmationStatements.Premises.FFGCertificates
public import FastConfirmationModel.Execution.ScheduledPrefixes

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

/-- Evidence for one attestation assigned to a carrier block.

The projected `BeaconBlock` has no ordinary FFG attestation body. The supplied
inclusion relation assigns the attestation to a carrier; this evidence does
not check body membership. It identifies a carrier in the execution, a block
origin for the wire attestation, a same-registry state with a true validity
answer, committee membership, and the required chain relations. The
validation state need not be a reachable or prepared handler state. -/
structure IncludedAttestationEvidence
    (validity : BeaconState Root → Attestation Root → Bool)
    (carrier : Root) (a : Attestation Root) where
  carrier_message : BeaconBlock Root
  carrier_at : E.BlockAt carrier carrier_message
  received_from_block : ∃ (w : ValidatorIndex) (n : ℕ),
    Event.attestation a true ∈ E.schedule w n
  /-- A state with the execution registry and a true validity answer.
      It need not be reached by the execution or prepared by a handler. -/
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

/-- A supplied inclusion relation for ordinary FFG attestations.
The projected `BeaconBlock` has no ordinary FFG attestation body. The evidence
requires a carrier and a received vote, but does not check body membership or
the origin of the validation state. -/
structure IncludedAttestationRelation
    (validity : BeaconState Root → Attestation Root → Bool) where
  /-- Supplied assignment of an attestation to a carrier block. -/
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

/-- A supplied positive inclusion relation with accepted carrier evidence.
The projected block has no ordinary FFG attestation body, so the evidence does
not check whether the carrier contains the vote. The validation state needs
only the execution registry and a true validity answer. It need not be a
reachable or prepared handler state. -/
structure AcceptedIncludedAttestationRelation
    (validity : BeaconState Root → Attestation Root → Bool) where
  /-- Supplied carrier-vote assignment. Evidence ties the vote to an accepted
      carrier and a block-origin receipt, but not to carrier body membership. -/
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

end IncludedSupermajorityLink

namespace IncludedCertifiedJustified

end IncludedCertifiedJustified

namespace IncludedCertifiedFinalized

end IncludedCertifiedFinalized

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

namespace ChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}


end ChainFFGState

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

/-- The exact-prefix bundle with causal-store checkpoint reflection.
Its accepted inclusion relation is supplied with causal carrier evidence.
The projected block has no ordinary FFG attestations, so this bundle does not
check votes against carrier block bodies. Its validating state needs only the
execution registry and a true validity answer, not a reachable or prepared
handler state. Safety claims hold for every relation that meets these fields;
they do not alone certify votes in real block bodies. The bundle does not
cover delayed queues or arbitrary global action traces. -/
structure ExactPrefixAcceptedFFGSemantics (E : Execution Root) where
  anchor : Checkpoint Root
  state : AcceptedChainFFGState cfg ext E anchor
  coherence : AcceptedFFGTransitionCoherence cfg ext state

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

end ChainFFGState

namespace AcceptedChainFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

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


end FastConfirmation.Spec

end
