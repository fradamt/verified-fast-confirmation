module
public import Mathlib.Tactic
public import FastConfirmationProofs.FFG.State.ProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.FFG.State.ScheduledFFGStateTrajectory
public import FastConfirmationProofs.Gloas.Payload.Preservation
public import FastConfirmationProofs.Safety.BlockAgreement

public import FastConfirmationStatements.Premises.FFG
public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Spec / Proof / FFGSourceCoherence

Relates stored signed blocks and transition history to FFG source certificates.

This module contains `storedSignedBlock`, `BlockStateTransitionHistory`, `on_block_inserted_message` and related declarations.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : BeaconFunctionInterface Root}

/-! ## The missing phase0 semantic contract -/

/-! ## The erased block-state transition history -/

/-- Reconstruct the projected signed block stored at `r`.  Signatures and
block bodies are already absorbed by the reduced model, so `root` and
`message` are all the data its opaque `state_transition` receives. -/
def storedSignedBlock (store : Store Root) (r : Root) : SignedBeaconBlock Root :=
  { root := r, message := store.blocks r }

/-- The narrow replayability fact erased by the reduced fork-choice store.

For every honest reachable view inside the verified horizon, a known
non-genesis block's stored post-state is exactly the result of replaying that
stored block from its stored parent state.  `BlockProvenance` already proves
that its root/message came from a scheduled block, so this contract does not
repeat message provenance or assume any checkpoint/source equality.

This is logically separate from `Phase0SourceCoherence`: replayability says
*which transition produced a stored state*; phase0 source coherence says
*what a same-epoch transition does to one field*.  The handler proves the
equation at insertion time, but the current reduced store retains neither the
insertion time nor a historical parent-state snapshot.  Existing
`BlockProvenance` tracks only block messages, and `FFGStoreProjection` tracks
only the resulting FFG values, so neither can recover this equation at an
arbitrary later view without an additional trajectory proof. -/
structure BlockStateTransitionHistory (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) : Prop where
  replay : ∀ w ∈ E.honest, ∀ n : ℕ,
    E.WithinHorizon cfg n →
    ∀ child ∈ (E.store cfg ext w n).block_roots,
      child ∉ E.genesis_store.block_roots →
      let store := E.store cfg ext w n
      let parent := (store.blocks child).parent_root
      parent ∈ store.block_roots ∧
        ext.state_transition (store.block_states parent)
          (storedSignedBlock store child) = some (store.block_states child)

/-! ## Direct handler extraction -/


/-- A fresh successful block handler installs the accepted signed block's exact
message at its root. -/
theorem on_block_inserted_message
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hfresh : sb.root ∉ store.block_roots)
    (hh : on_block cfg ext store sb = some store') :
    store'.blocks sb.root = sb.message := by
  simp only [on_block, if_neg hfresh] at hh
  split_ifs at hh <;> try cases hh
  cases hst : ext.state_transition
      (store.block_states sb.message.parent_root) sb with
  | none => rw [hst] at hh; cases hh
  | some post =>
    rw [hst] at hh
    let added : Store Root :=
      { store with
        block_roots := store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          sb.root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote := Function.update store.payload_data_availability_vote
          sb.root (some (List.replicate cfg.ptc_size none)) }
    change (match notify_ptc_messages cfg ext added post sb.message.payload_attestations with
      | none => none
      | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
          (FastConfirmation.Spec.update_checkpoints
            (FastConfirmation.Spec.update_proposer_boost_root cfg
              (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
              (get_head cfg store).root sb.root)
            post.current_justified_checkpoint post.finalized_checkpoint) sb.root)) =
        some store' at hh
    cases hn : notify_ptc_messages cfg ext added post sb.message.payload_attestations with
    | none => rw [hn] at hh; cases hh
    | some notified =>
      rw [hn] at hh
      cases hh
      have hf := notify_ptc_messages_frame cfg ext hn
      let timed := record_block_timeliness cfg notified sb.root
      let boosted := update_proposer_boost_root cfg timed
        (get_head cfg store).root sb.root
      let realized := update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
      have htail : SameBlocks added
          (compute_pulled_up_tip cfg ext realized sb.root) :=
        hf.sameBlocks.trans
          ((record_block_timeliness_sameBlocks cfg notified sb.root).trans
            ((update_proposer_boost_root_sameBlocks cfg timed
              (get_head cfg store).root sb.root).trans
              ((update_checkpoints_sameBlocks boosted
                post.current_justified_checkpoint post.finalized_checkpoint).trans
                (compute_pulled_up_tip_sameBlocks cfg ext realized sb.root))))
      rw [← htail.2.1]
      exact Function.update_self sb.root sb.message store.blocks


/-! ## Projected same-epoch block edges and segments -/

variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}



/-- One executable state-transition edge, viewed through the exact FFG store
projection.  All fields except `same_epoch` are direct data/equalities from
the handler/state model.  In particular, this structure does *not* contain a
checkpoint-equality field.

Different edges in a segment may be witnessed in different stores.  This is
useful for a historical handler trace while retaining one global block-local
projection `S`. -/
def ProjectedSameEpochTransition
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (S : ChainFFGState cfg E anchor)
    (parent child : Root) : Prop :=
  ∃ store : Store Root,
    FFGStoreProjection cfg ext S store ∧
    ∃ signed_block : SignedBeaconBlock Root,
      signed_block.root = child ∧
      signed_block.message.parent_root = parent ∧
      parent ∈ store.block_roots ∧
      (∃ w n, Event.block signed_block ∈ E.schedule w n) ∧
      ∃ post : BeaconState Root,
        ext.state_transition (store.block_states parent) signed_block = some post ∧
        compute_epoch_at_slot cfg (store.block_states parent).slot =
          compute_epoch_at_slot cfg signed_block.message.slot

namespace ProjectedSameEpochTransition




end ProjectedSameEpochTransition


/-- Reflexive/transitive closure of explicit projected same-epoch transition
edges.  This is the narrow block-state ancestry object needed for source
coherence; it contains no safety, canonicality, or A3.2 premise. -/
inductive ProjectedSameEpochSegment
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (S : ChainFFGState cfg E anchor) :
    Root → Root → Prop
  | refl (r : Root) : ProjectedSameEpochSegment cfg ext E S r r
  | tail {first middle last : Root} :
      ProjectedSameEpochSegment cfg ext E S first middle →
      ProjectedSameEpochTransition cfg ext E S middle last →
      ProjectedSameEpochSegment cfg ext E S first last

namespace ProjectedSameEpochSegment



end ProjectedSameEpochSegment

/-! ## Reachable-store same-epoch ancestry -/

/-- A concrete parent chain in one reachable store whose nontrivial edges are
known, non-genesis, and remain in one epoch.  Unlike
`ProjectedSameEpochSegment`, this relation contains only ordinary store
ancestry/epoch facts; transition witnesses are supplied later by
`BlockStateTransitionHistory`. -/
inductive KnownSameEpochAncestrySegment
    (cfg : Config) (genesisRoots : List Root) (store : Store Root) :
    Root → Root → Prop
  | refl (r : Root) (known : r ∈ store.block_roots) :
      KnownSameEpochAncestrySegment cfg genesisRoots store r r
  | tail {first parent child : Root} :
      KnownSameEpochAncestrySegment cfg genesisRoots store first parent →
      child ∈ store.block_roots →
      child ∉ genesisRoots →
      (store.blocks child).parent_root = parent →
      compute_epoch_at_slot cfg (store.blocks parent).slot =
        compute_epoch_at_slot cfg (store.blocks child).slot →
      KnownSameEpochAncestrySegment cfg genesisRoots store first child

namespace KnownSameEpochAncestrySegment

/-- The endpoint of a concrete known ancestry segment is known. -/
theorem last_known
    {genesisRoots : List Root} {store : Store Root} {first last : Root}
    (h : KnownSameEpochAncestrySegment cfg genesisRoots store first last) :
    last ∈ store.block_roots := by
  cases h with
  | refl known => exact known
  | tail _ known _ _ _ => exact known

end KnownSameEpochAncestrySegment


/-! ## Honest-attestation source readback -/

/-- If the head block state and vote slot are in one epoch, the validator
spec's optional `process_slots` call preserves the head state's realized
justified checkpoint. -/
theorem honest_attestation_data_source_eq_head_state
    (hphase : Phase0SourceCoherence cfg ext)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex)
    (hsame : compute_epoch_at_slot cfg
        (store.block_states (get_head cfg store).root).slot =
      compute_epoch_at_slot cfg slot) :
    (honest_attestation_data cfg ext store slot index).source =
      (store.block_states (get_head cfg store).root).current_justified_checkpoint := by
  simp only [honest_attestation_data]
  split_ifs with hlt
  · exact hphase.process_slots_current_justified _ _ hlt hsame
  · rfl






/-! ## Accepted exact-prefix source coherence -/

/-- Named data for one accepted same-epoch source edge.  The edge owns the
actual scheduled-prefix transition, exact parent and child accepted block
witnesses, and a named formed carrier for the child's `GJ`. -/
structure AcceptedProjectedSameEpochTransitionCarrier
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (S : AcceptedBlockFFGState cfg ext E anchor)
    (parent child : Root) where
  transition : E.SuccessfulScheduledBlockImport cfg ext
  parent_eq : transition.signedBlock.message.parent_root = parent
  child_eq : transition.signedBlock.root = child
  parent_known :
    parent ∈ (transition.atPrefix.store cfg ext).block_roots
  parent_block_at : E.BlockKnownInScheduledPrefix cfg ext parent
    ((transition.atPrefix.store cfg ext).blocks parent)
  child_block_at : E.BlockKnownInScheduledPrefix cfg ext child
    transition.signedBlock.message
  post : BeaconState Root
  state_transition :
    ext.state_transition
        ((transition.atPrefix.store cfg ext).block_states parent)
        transition.signedBlock =
      some post
  post_state : transition.postStore.block_states child = post
  same_epoch :
    compute_epoch_at_slot cfg
        ((transition.atPrefix.store cfg ext).block_states parent).slot =
      compute_epoch_at_slot cfg transition.signedBlock.message.slot
  child_gj_carrier : AcceptedSelectorAUCarrier S transition.postStore
    (S.realized_justified child)

/-- Proposition-level ownership of the full named accepted edge carrier. -/
def AcceptedProjectedSameEpochTransition
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (S : AcceptedBlockFFGState cfg ext E anchor)
    (parent child : Root) : Prop :=
  Nonempty
    (AcceptedProjectedSameEpochTransitionCarrier cfg ext E S parent child)

namespace AcceptedProjectedSameEpochTransition

/-- The sole producer for an accepted source edge: an actual successful block
transition at the exact next scheduled-prefix position.  Replay history is
not an input and cannot establish this edge. -/
theorem of_transition
    {S : AcceptedBlockFFGState cfg ext E anchor}
    (t : E.SuccessfulScheduledBlockImport cfg ext)
    (hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots)
    (hparent : t.signedBlock.message.parent_root ∈
      (t.atPrefix.store cfg ext).block_roots)
    (hsame : compute_epoch_at_slot cfg
        ((t.atPrefix.store cfg ext).block_states
          t.signedBlock.message.parent_root).slot =
      compute_epoch_at_slot cfg t.signedBlock.message.slot) :
    AcceptedProjectedSameEpochTransition cfg ext E S
      t.signedBlock.message.parent_root t.signedBlock.root := by
  obtain ⟨post, htransition, hpost⟩ :=
    Execution.SuccessfulScheduledBlockImport.on_block_inserted_state_fresh
      cfg ext hfresh t.accepted
  have hparentAt : E.BlockKnownInScheduledPrefix cfg ext
      t.signedBlock.message.parent_root
      ((t.atPrefix.store cfg ext).blocks
        t.signedBlock.message.parent_root) :=
    E.acceptedBlockAt_of_causal_known cfg ext
      (.scheduledPrefix t.atPrefix) hparent
  have hchildAt : E.BlockKnownInScheduledPrefix cfg ext t.signedBlock.root
      t.signedBlock.message :=
    ⟨t.postStore, t.post_causal, t.root_known,
      on_block_inserted_message hfresh t.accepted⟩
  have htip : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) t.postStore t.signedBlock.root :=
    ⟨t.root_known, t.signedBlock.message, hchildAt⟩
  obtain ⟨carrier, hdesc, hformed⟩ :=
    S.realized_justified_mem t.signedBlock.root t.root_accepted
  let hgjCarrier : AcceptedSelectorAUCarrier S t.postStore
      (S.realized_justified t.signedBlock.root) :=
    { tip := t.signedBlock.root
      carrier := carrier
      tip_carrier := htip
      au := ⟨carrier, hdesc, hformed⟩
      tip_descends_carrier := hdesc
      carrier_accepted := S.formed_carrier_accepted hformed
      formed_evidence := S.formed_evidence hformed }
  exact ⟨
    { transition := t
      parent_eq := rfl
      child_eq := rfl
      parent_known := hparent
      parent_block_at := hparentAt
      child_block_at := hchildAt
      post := post
      state_transition := htransition
      post_state := hpost
      same_epoch := hsame
      child_gj_carrier := hgjCarrier }⟩

/-- One actual accepted same-epoch transition preserves the block-local
justified selector.  The parent projection is taken at the transition's exact
pre-prefix, and the child selector equation is the accepted-transition law. -/
theorem gj_eq_parent
    {S : AcceptedBlockFFGState cfg ext E anchor}
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGStateReadAgreement cfg ext S)
    {parent child : Root}
    (h : AcceptedProjectedSameEpochTransition cfg ext E S parent child) :
    S.realized_justified child = S.realized_justified parent := by
  obtain ⟨edge⟩ := h
  have hprojection : AcceptedFFGStoreProjection S
      (edge.transition.atPrefix.store cfg ext) :=
    edge.transition.atPrefix.acceptedFFGStoreProjection hcoh
  calc
    S.realized_justified child =
        (edge.transition.postStore.block_states child
          ).current_justified_checkpoint := by
      exact (congrArg S.realized_justified edge.child_eq).symm |>.trans
        ((hcoh.transition_gj edge.transition).symm.trans
          (congrArg (fun r =>
            (edge.transition.postStore.block_states r
              ).current_justified_checkpoint) edge.child_eq))
    _ = edge.post.current_justified_checkpoint := by
      rw [edge.post_state]
    _ = ((edge.transition.atPrefix.store cfg ext).block_states parent
          ).current_justified_checkpoint :=
      hphase.state_transition_current_justified _ _ _
        edge.state_transition edge.same_epoch
    _ = S.realized_justified parent :=
      hprojection.block_state_gj parent edge.parent_known

end AcceptedProjectedSameEpochTransition

/-- Reflexive/transitive closure of accepted edges.  Even a reflexive segment
retains an exact accepted block witness; every nontrivial edge owns an actual
`SuccessfulScheduledBlockImport` through its carrier evidence. -/
inductive AcceptedProjectedSameEpochSegment
    (cfg : Config) (ext : BeaconFunctionInterface Root)
    (E : Execution Root) (S : AcceptedBlockFFGState cfg ext E anchor) :
    Root → Root → Prop
  | refl (r : Root) (b : BeaconBlock Root)
      (block_at : E.BlockKnownInScheduledPrefix cfg ext r b) :
      AcceptedProjectedSameEpochSegment cfg ext E S r r
  | tail {first middle last : Root} :
      AcceptedProjectedSameEpochSegment cfg ext E S first middle →
      AcceptedProjectedSameEpochTransition cfg ext E S middle last →
      AcceptedProjectedSameEpochSegment cfg ext E S first last

namespace AcceptedProjectedSameEpochSegment

theorem gj_eq_first
    {S : AcceptedBlockFFGState cfg ext E anchor}
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGStateReadAgreement cfg ext S)
    {first last : Root}
    (h : AcceptedProjectedSameEpochSegment cfg ext E S first last) :
    S.realized_justified last = S.realized_justified first := by
  induction h with
  | refl => rfl
  | tail hprefix hedge ih =>
      exact (hedge.gj_eq_parent hphase hcoh).trans ih


end AcceptedProjectedSameEpochSegment

/-- Named accepted/global readback carrier for one honest attestation source.
It retains the exact accepted head block and the formed carrier witnessing AU
for the selected block-local `GJ`. -/
structure AcceptedHonestSourceCarrier
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex) where
  global_projection : AcceptedFFGGlobalStoreProjection S store
  head_block : BeaconBlock Root
  head_block_at : E.BlockKnownInScheduledPrefix cfg ext (get_head cfg store).root
    head_block
  head_block_eq : head_block = store.blocks (get_head cfg store).root
  head_gj_carrier : AcceptedSelectorAUCarrier S store
    (S.realized_justified (get_head cfg store).root)
  source_eq : (honest_attestation_data cfg ext store slot index).source =
    S.realized_justified (get_head cfg store).root

def AcceptedHonestSourceEvidence
    (S : AcceptedBlockFFGState cfg ext E anchor)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex) : Prop :=
  Nonempty (AcceptedHonestSourceCarrier S store slot index)

namespace AcceptedHonestSourceEvidence

theorem source_eq
    {S : AcceptedBlockFFGState cfg ext E anchor}
    {store : Store Root} {slot : Slot} {index : CommitteeIndex}
    (h : AcceptedHonestSourceEvidence S store slot index) :
    (honest_attestation_data cfg ext store slot index).source =
      S.realized_justified (get_head cfg store).root := by
  obtain ⟨carrier⟩ := h
  exact carrier.source_eq

end AcceptedHonestSourceEvidence

namespace ScheduledFFGInterpretation

/-- Small causal/global source consumer for the production accepted bundle.
The semantic state is selected before the store; local projection, global
origins, the exact accepted head block, AU, and formed evidence are retained. -/
theorem causalStoreHonestSourceEvidence
    {E : Execution Root}
    (B : ScheduledFFGInterpretation cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    {slot : Slot} {index : CommitteeIndex}
    (hhead : (get_head cfg store).root ∈ store.block_roots)
    (hsame : compute_epoch_at_slot cfg
        (store.block_states (get_head cfg store).root).slot =
      compute_epoch_at_slot cfg slot) :
    AcceptedHonestSourceEvidence B.state store slot index := by
  let hglobal : AcceptedFFGGlobalStoreProjection B.state store :=
    B.causalStoreGlobalProjection hgen hanchor hstore
  let htip : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) store (get_head cfg store).root :=
    Execution.AcceptedCarrierIn.of_causal_known hstore hhead
  obtain ⟨carrier, hdesc, hformed⟩ :=
    B.state.realized_justified_mem (get_head cfg store).root htip.acceptedRoot
  let hgjCarrier : AcceptedSelectorAUCarrier B.state store
      (B.state.realized_justified (get_head cfg store).root) :=
    { tip := (get_head cfg store).root
      carrier := carrier
      tip_carrier := htip
      au := ⟨carrier, hdesc, hformed⟩
      tip_descends_carrier := hdesc
      carrier_accepted := B.state.formed_carrier_accepted hformed
      formed_evidence := B.state.formed_evidence hformed }
  have hsource :
      (honest_attestation_data cfg ext store slot index).source =
        B.state.realized_justified (get_head cfg store).root := by
    rw [honest_attestation_data_source_eq_head_state hphase store slot index
      hsame]
    exact hglobal.blockLocal.block_state_gj _ hhead
  exact ⟨
    { global_projection := hglobal
      head_block := store.blocks (get_head cfg store).root
      head_block_at := E.acceptedBlockAt_of_causal_known cfg ext hstore hhead
      head_block_eq := rfl
      head_gj_carrier := hgjCarrier
      source_eq := hsource }⟩




end ScheduledFFGInterpretation

/-! ## Contract non-vacuity -/

namespace SourceCoherenceNonVacuity
























end SourceCoherenceNonVacuity

end FastConfirmation.Spec

end
