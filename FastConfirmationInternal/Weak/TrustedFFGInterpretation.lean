module
public import FastConfirmationInternal.Weak.TrustedCarrierEvidence
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions

/-! Accepted FFG interpretations with an explicit validation-store domain.
The original FFG records remain available through lossless honest-store adapters. -/

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

structure TrustedCausalCarrierFFGState (E : Execution Root)
    (anchor : Checkpoint Root) (trusted : Store Root → Prop) where
  attestationValidity : BeaconState Root → Attestation Root → Bool
  includedAttestations :
    Execution.TrustedCarrierAttestationRelation cfg ext E
      attestationValidity trusted
  /-- Body evidence for the paper's slashing set. Certificate normalization
  can restrict `includedAttestations` while this relation retains the body. -/
  paperIncludedAttestations : Execution.IncludedAttestationRelation cfg E
      attestationValidity := includedAttestations.relation
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
    formed r c → IncludedVoteCheckpointCertificate cfg ext E
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

namespace TrustedCausalCarrierFFGState

variable {E : Execution Root} {anchor : Checkpoint Root}

/-- The paper A3.2 view uses body evidence before certificate normalization.
Its formed entries and selectors are those of the same semantic state. -/
def paperA32Inputs {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) :
    PaperA32StateView cfg E where
  BlockAt := E.AcceptedBlockAt cfg ext
  attestationValidity := S.attestationValidity
  includedAttestations := S.paperIncludedAttestations
  formed := S.formed
  C := S.C
  GJ := S.GJ
  GU := S.GU
  checkpoint_epoch := S.checkpoint_epoch

abbrev PaperA32SupportThroughoutEpoch {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (b : Root) (e : Epoch) : Prop :=
  PaperA32SupportThroughoutEpochCore cfg ext (S.paperA32Inputs cfg ext) b e

abbrev PaperA32Inclusion {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) : Prop :=
  PaperA32InclusionCore cfg ext (S.paperA32Inputs cfg ext)

abbrev ExactLinkValidity {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) : Prop :=
  ExactIncludedLinkValidity cfg E S.includedAttestations.Included anchor
    S.C (E.AcceptedRoot cfg ext)

/-- Exact links on a stated carrier domain for the trusted-store state. -/
abbrev GuardedExactLinkValidity {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (Domain : Root → Prop) : Prop :=
  ExactIncludedLinkValidity cfg E S.includedAttestations.Included anchor
    S.C (E.AcceptedRoot cfg ext) Domain

/-- The fold uses contributing links at accepted certificate carriers. -/
abbrev AcceptedExactLinkValidity {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) : Prop :=
  S.GuardedExactLinkValidity cfg ext (E.AcceptedRoot cfg ext)


/-- Voting-source selector for the accepted trusted state. -/
abbrev VSAt {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (store : Store Root) (b : Root) (e : Epoch) : Checkpoint Root :=
  if get_block_epoch cfg store b = e then S.GJ b else S.GU b

/-- Exact paper link support on the trusted state's inclusion relation. -/
abbrev PaperA32LinkSupportAt {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (w : ValidatorIndex) (m : ℕ) (b' : Root)
    (source target : Checkpoint Root) : Type :=
  PaperA32LinkSupportAtCore cfg ext (S.paperA32Inputs cfg ext)
    w m b' source target

def AU {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (tip : Root) (c : Checkpoint Root) : Prop :=
  ∃ carrier, E.RootDescends tip carrier ∧ S.formed carrier c

end TrustedCausalCarrierFFGState

/-- Accepted-only selector coherence.  Its transition equations quantify
only over actual successful `on_block` calls at exact causal prefixes. -/
structure TrustedFFGSelectorsMatchBeaconStates
    {E : Execution Root} {anchor : Checkpoint Root}
    {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) : Prop where
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
structure TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates
    {E : Execution Root} {anchor : Checkpoint Root}
    {trusted : Store Root → Prop}
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) : Prop
    extends TrustedFFGSelectorsMatchBeaconStates cfg ext S where
  checkpoint_of_known : ∀ {store : Store Root},
    E.CausalStore cfg ext store → ∀ r ∈ store.block_roots, ∀ e,
      S.C r e = get_checkpoint_for_block cfg store r e
  au_checkpoint_of_known : ∀ {store : Store Root},
    E.CausalStore cfg ext store → ∀ r ∈ store.block_roots, ∀ c,
      S.AU cfg ext r c →
      c = get_checkpoint_for_block cfg store r c.epoch

/-- The exact-prefix bundle with causal-store checkpoint reflection.
Its accepted inclusion relation checks carrier body membership and validates
on a target block state prepared along the handler path from an honest,
in-horizon store. The prepared state need not be keyed. The bundle does not
cover delayed queues or arbitrary global action traces. -/
structure TrustedCausalPrefixFFGInterpretation (E : Execution Root)
    (trusted : Store Root → Prop) where
  anchor : Checkpoint Root
  state : TrustedCausalCarrierFFGState cfg ext E anchor trusted
  coherence : TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext state


/-- Realized finalization delay for an arbitrary trusted validation domain. -/
def Execution.TrustedRealizedFinalizationDelay {E : Execution Root}
    {trusted : Store Root → Prop}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted) : Prop :=
  ∀ t : E.AcceptedBlockTransition cfg ext,
    let finalized :=
      (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
    finalized = B.anchor ∨
      finalized.epoch + 2 ≤
        compute_epoch_at_slot cfg t.signedBlock.message.slot

variable {cfg ext}
variable {E : Execution Root} {anchor : Checkpoint Root}

def CausalCarrierFFGState.toTrusted (S : CausalCarrierFFGState cfg ext E anchor) :
    TrustedCausalCarrierFFGState cfg ext E anchor (E.HonestCausalStore cfg ext) where
  includedAttestations := {
    Included := S.includedAttestations.Included
    evidence := fun h => (S.includedAttestations.evidence h).toTrusted }
  attestationValidity := S.attestationValidity
  formed := S.formed
  C := S.C
  GJ := S.GJ
  GU := S.GU
  GF := S.GF
  GUF := S.GUF
  checkpoint_epoch := S.checkpoint_epoch
  formed_carrier_accepted := S.formed_carrier_accepted
  formed_evidence := S.formed_evidence
  gj_mem := S.gj_mem
  gu_mem := S.gu_mem
  gf_mem := S.gf_mem
  guf_mem := S.guf_mem
  gj_anchor_or_before := S.gj_anchor_or_before
  gj_max := S.gj_max
  gu_max := S.gu_max
  au_epoch_le_block := S.au_epoch_le_block
  gf_evidence := S.gf_evidence
  guf_evidence := S.guf_evidence
  gf_epoch_le_gj := S.gf_epoch_le_gj
  guf_epoch_le_gu := S.guf_epoch_le_gu
  gf_epoch_le_guf := S.gf_epoch_le_guf

def TrustedCausalCarrierFFGState.toHonest (S : TrustedCausalCarrierFFGState cfg ext E anchor (E.HonestCausalStore cfg ext)) :
    CausalCarrierFFGState cfg ext E anchor where
  includedAttestations := {
    Included := S.includedAttestations.Included
    evidence := fun h => (S.includedAttestations.evidence h).toHonest }
  attestationValidity := S.attestationValidity
  formed := S.formed
  C := S.C
  GJ := S.GJ
  GU := S.GU
  GF := S.GF
  GUF := S.GUF
  checkpoint_epoch := S.checkpoint_epoch
  formed_carrier_accepted := S.formed_carrier_accepted
  formed_evidence := S.formed_evidence
  gj_mem := S.gj_mem
  gu_mem := S.gu_mem
  gf_mem := S.gf_mem
  guf_mem := S.guf_mem
  gj_anchor_or_before := S.gj_anchor_or_before
  gj_max := S.gj_max
  gu_max := S.gu_max
  au_epoch_le_block := S.au_epoch_le_block
  gf_evidence := S.gf_evidence
  guf_evidence := S.guf_evidence
  gf_epoch_le_gj := S.gf_epoch_le_gj
  guf_epoch_le_gu := S.guf_epoch_le_gu
  gf_epoch_le_guf := S.gf_epoch_le_guf

def FFGSelectorsAndCheckpointReadsMatchBeaconStates.toTrusted {S : CausalCarrierFFGState cfg ext E anchor} (h : FFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext S) :
    TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext S.toTrusted where
  attestation_validity := h.attestation_validity
  genesis_gj := h.genesis_gj
  genesis_gf := h.genesis_gf
  genesis_gu := h.genesis_gu
  genesis_guf := h.genesis_guf
  genesis_unrealized_justification := h.genesis_unrealized_justification
  transition_gj := h.transition_gj
  transition_gf := h.transition_gf
  transition_gu := h.transition_gu
  transition_guf := h.transition_guf
  checkpoint_of_known := h.checkpoint_of_known
  au_checkpoint_of_known := h.au_checkpoint_of_known

def TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates.toHonest {S : TrustedCausalCarrierFFGState cfg ext E anchor (E.HonestCausalStore cfg ext)} (h : TrustedFFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext S) :
    FFGSelectorsAndCheckpointReadsMatchBeaconStates cfg ext S.toHonest where
  attestation_validity := h.attestation_validity
  genesis_gj := h.genesis_gj
  genesis_gf := h.genesis_gf
  genesis_gu := h.genesis_gu
  genesis_guf := h.genesis_guf
  genesis_unrealized_justification := h.genesis_unrealized_justification
  transition_gj := h.transition_gj
  transition_gf := h.transition_gf
  transition_gu := h.transition_gu
  transition_guf := h.transition_guf
  checkpoint_of_known := h.checkpoint_of_known
  au_checkpoint_of_known := h.au_checkpoint_of_known

/-- Every old honest-store interpretation has the trusted form. -/
def CausalPrefixFFGInterpretation.toTrusted
    (B : CausalPrefixFFGInterpretation cfg ext E) :
    TrustedCausalPrefixFFGInterpretation cfg ext E (E.HonestCausalStore cfg ext) where
  anchor := B.anchor
  state := B.state.toTrusted
  coherence := B.coherence.toTrusted

/-- The trusted honest-store specialization recovers the original record. -/
def TrustedCausalPrefixFFGInterpretation.toHonest
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.HonestCausalStore cfg ext)) :
    CausalPrefixFFGInterpretation cfg ext E where
  anchor := B.anchor
  state := B.state.toHonest
  coherence := B.coherence.toHonest

/-- The original delay premise is the honest trusted instance. -/
theorem CausalPrefixFFGInterpretation.realizedDelay_toTrusted
    (B : CausalPrefixFFGInterpretation cfg ext E) :
    E.TrustedRealizedFinalizationDelay cfg ext B.toTrusted ↔
      E.RealizedFinalizationDelay cfg ext B := Iff.rfl

/-- The original honest-store record is recovered without change. -/
theorem CausalPrefixFFGInterpretation.toHonest_toTrusted
    (B : CausalPrefixFFGInterpretation cfg ext E) :
    B.toTrusted.toHonest = B := by
  cases B
  rfl

/-- A trusted record with the original paper relation also round-trips. -/
theorem TrustedCausalPrefixFFGInterpretation.toTrusted_toHonest
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E
      (E.HonestCausalStore cfg ext))
    (hpaper : B.state.paperIncludedAttestations = B.state.includedAttestations.relation) :
    B.toHonest.toTrusted = B := by
  rcases B with ⟨anchor, state, coherence⟩
  cases state
  dsimp at hpaper
  subst hpaper
  rfl

end FastConfirmation.Spec
end
