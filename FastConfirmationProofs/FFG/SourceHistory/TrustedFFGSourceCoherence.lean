module
public import FastConfirmationProofs.FFG.SourceHistory.FFGSourceCoherence
public import FastConfirmationProofs.FFG.State.TrustedProcessedFFGGlobalCheckpointTrajectory
public import FastConfirmationProofs.ModelFacts.TrustedFFGState

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}
variable {E : Execution Root} {anchor : Checkpoint Root}
variable {trusted : Store Root → Prop}

structure TrustedTrustedAcceptedProjectedSameEpochTransitionCarrier
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (parent child : Root) where
  transition : E.AcceptedBlockTransition cfg ext
  parent_eq : transition.signedBlock.message.parent_root = parent
  child_eq : transition.signedBlock.root = child
  parent_known :
    parent ∈ (transition.atPrefix.store cfg ext).block_roots
  parent_block_at : E.AcceptedBlockAt cfg ext parent
    ((transition.atPrefix.store cfg ext).blocks parent)
  child_block_at : E.AcceptedBlockAt cfg ext child
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
  child_gj_carrier : TrustedAcceptedSelectorAUCarrier S transition.postStore
    (S.GJ child)

/-- Proposition-level ownership of the full named accepted edge carrier. -/
def TrustedAcceptedProjectedSameEpochTransition
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (parent child : Root) : Prop :=
  Nonempty
    (TrustedTrustedAcceptedProjectedSameEpochTransitionCarrier cfg ext E S parent child)

namespace TrustedAcceptedProjectedSameEpochTransition

/-- The sole producer for an accepted source edge: an actual successful block
transition at the exact next scheduled-prefix position.  Replay history is
not an input and cannot establish this edge. -/
theorem of_transition
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (t : E.AcceptedBlockTransition cfg ext)
    (hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots)
    (hparent : t.signedBlock.message.parent_root ∈
      (t.atPrefix.store cfg ext).block_roots)
    (hsame : compute_epoch_at_slot cfg
        ((t.atPrefix.store cfg ext).block_states
          t.signedBlock.message.parent_root).slot =
      compute_epoch_at_slot cfg t.signedBlock.message.slot) :
    TrustedAcceptedProjectedSameEpochTransition cfg ext E S
      t.signedBlock.message.parent_root t.signedBlock.root := by
  obtain ⟨post, htransition, hpost⟩ :=
    Execution.AcceptedBlockTransition.on_block_inserted_state_fresh
      cfg ext hfresh t.accepted
  have hparentAt : E.AcceptedBlockAt cfg ext
      t.signedBlock.message.parent_root
      ((t.atPrefix.store cfg ext).blocks
        t.signedBlock.message.parent_root) :=
    E.acceptedBlockAt_of_causal_known cfg ext
      (.scheduledPrefix t.atPrefix) hparent
  have hchildAt : E.AcceptedBlockAt cfg ext t.signedBlock.root
      t.signedBlock.message :=
    ⟨t.postStore, t.post_causal, t.root_known,
      on_block_inserted_message hfresh t.accepted⟩
  have htip : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) t.postStore t.signedBlock.root :=
    ⟨t.root_known, t.signedBlock.message, hchildAt⟩
  obtain ⟨carrier, hdesc, hformed⟩ :=
    S.gj_mem t.signedBlock.root t.root_accepted
  let hgjCarrier : TrustedAcceptedSelectorAUCarrier S t.postStore
      (S.GJ t.signedBlock.root) :=
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
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    {parent child : Root}
    (h : TrustedAcceptedProjectedSameEpochTransition cfg ext E S parent child) :
    S.GJ child = S.GJ parent := by
  obtain ⟨edge⟩ := h
  have hprojection : TrustedAcceptedFFGStoreProjection S
      (edge.transition.atPrefix.store cfg ext) :=
    edge.transition.atPrefix.trustedAcceptedFFGStoreProjection hcoh
  calc
    S.GJ child =
        (edge.transition.postStore.block_states child
          ).current_justified_checkpoint := by
      exact (congrArg S.GJ edge.child_eq).symm |>.trans
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
    _ = S.GJ parent :=
      hprojection.block_state_gj parent edge.parent_known

end TrustedAcceptedProjectedSameEpochTransition

/-- Reflexive/transitive closure of accepted edges.  Even a reflexive segment
retains an exact accepted block witness; every nontrivial edge owns an actual
`AcceptedBlockTransition` through its carrier evidence. -/
inductive TrustedAcceptedProjectedSameEpochSegment
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted) :
    Root → Root → Prop
  | refl (r : Root) (b : BeaconBlock Root)
      (block_at : E.AcceptedBlockAt cfg ext r b) :
      TrustedAcceptedProjectedSameEpochSegment cfg ext E S r r
  | tail {first middle last : Root} :
      TrustedAcceptedProjectedSameEpochSegment cfg ext E S first middle →
      TrustedAcceptedProjectedSameEpochTransition cfg ext E S middle last →
      TrustedAcceptedProjectedSameEpochSegment cfg ext E S first last

namespace TrustedAcceptedProjectedSameEpochSegment

theorem gj_eq_first
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : TrustedFFGSelectorsMatchBeaconStates cfg ext S)
    {first last : Root}
    (h : TrustedAcceptedProjectedSameEpochSegment cfg ext E S first last) :
    S.GJ last = S.GJ first := by
  induction h with
  | refl => rfl
  | tail hprefix hedge ih =>
      exact (hedge.gj_eq_parent hphase hcoh).trans ih


end TrustedAcceptedProjectedSameEpochSegment

/-- Named accepted/global readback carrier for one honest attestation source.
It retains the exact accepted head block and the formed carrier witnessing AU
for the selected block-local `GJ`. -/
structure TrustedAcceptedHonestSourceCarrier
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex) where
  global_projection : TrustedAcceptedFFGGlobalStoreProjection S store
  head_block : BeaconBlock Root
  head_block_at : E.AcceptedBlockAt cfg ext (get_head cfg store).root
    head_block
  head_block_eq : head_block = store.blocks (get_head cfg store).root
  head_gj_carrier : TrustedAcceptedSelectorAUCarrier S store
    (S.GJ (get_head cfg store).root)
  source_eq : (honest_attestation_data cfg ext store slot index).source =
    S.GJ (get_head cfg store).root

def TrustedAcceptedHonestSourceEvidence
    (S : TrustedCausalCarrierFFGState cfg ext E anchor trusted)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex) : Prop :=
  Nonempty (TrustedAcceptedHonestSourceCarrier S store slot index)

namespace TrustedAcceptedHonestSourceEvidence

theorem source_eq
    {S : TrustedCausalCarrierFFGState cfg ext E anchor trusted}
    {store : Store Root} {slot : Slot} {index : CommitteeIndex}
    (h : TrustedAcceptedHonestSourceEvidence S store slot index) :
    (honest_attestation_data cfg ext store slot index).source =
      S.GJ (get_head cfg store).root := by
  obtain ⟨carrier⟩ := h
  exact carrier.source_eq

end TrustedAcceptedHonestSourceEvidence

namespace TrustedCausalPrefixFFGInterpretation

/-- Small causal/global source consumer for the production accepted bundle.
The semantic state is selected before the store; local projection, global
origins, the exact accepted head block, AU, and formed evidence are retained. -/
theorem causalStoreHonestSourceEvidence
    {E : Execution Root}
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hphase : Phase0SourceCoherence cfg ext)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {slot : Slot} {index : CommitteeIndex}
    (hhead : (get_head cfg store).root ∈ store.block_roots)
    (hsame : compute_epoch_at_slot cfg
        (store.block_states (get_head cfg store).root).slot =
      compute_epoch_at_slot cfg slot) :
    TrustedAcceptedHonestSourceEvidence B.state store slot index := by
  let hglobal : TrustedAcceptedFFGGlobalStoreProjection B.state store :=
    B.causalStoreGlobalProjection hgen hanchor hstore
  let htip : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) store (get_head cfg store).root :=
    Execution.AcceptedCarrierIn.of_causal_known hstore hhead
  obtain ⟨carrier, hdesc, hformed⟩ :=
    B.state.gj_mem (get_head cfg store).root htip.acceptedRoot
  let hgjCarrier : TrustedAcceptedSelectorAUCarrier B.state store
      (B.state.GJ (get_head cfg store).root) :=
    { tip := (get_head cfg store).root
      carrier := carrier
      tip_carrier := htip
      au := ⟨carrier, hdesc, hformed⟩
      tip_descends_carrier := hdesc
      carrier_accepted := B.state.formed_carrier_accepted hformed
      formed_evidence := B.state.formed_evidence hformed }
  have hsource :
      (honest_attestation_data cfg ext store slot index).source =
        B.state.GJ (get_head cfg store).root := by
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




end TrustedCausalPrefixFFGInterpretation

end FastConfirmation.Spec
end
