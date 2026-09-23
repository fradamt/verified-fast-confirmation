module
public import Mathlib.Tactic
public import FastConfirmation.Spec.Proof.AcceptedFFGGlobalCheckpointTrajectory
public import FastConfirmation.Spec.Proof.FFGStateTrajectory
public import FastConfirmation.Spec.Proof.Preservation
public import FastConfirmation.Spec.Proof.BlockAgreement
public import FastConfirmation.Spec.Proof.ModelFacts

public import FastConfirmation.Spec.Statements.Premises.FFG
@[expose] public section

/-!
# Spec / Proof / FFGSourceCoherence

The reduced model makes phase0's `process_slots` and `state_transition`
opaque.  Their existing coherence record constrains slots, registries, and
checkpoint *epochs*, but it does not say when
`current_justified_checkpoint` may change.  This file isolates the narrow
phase0 law needed to rule out an arbitrary source split inside one epoch.

There are two deliberately separate narrow contracts.  `Phase0SourceCoherence`
says that neither empty-slot processing nor a block transition changes the
realized justified checkpoint unless an epoch boundary is crossed.  This is a
fact about phase0's state transition.  `BlockStateTransitionHistory` restores
the exact parent-state transition equation erased from an arbitrary later
reduced store view.  The handler proves it at insertion time, but the existing
trajectory library has no block-state replay/immutability invariant carrying
that equation through later root deliveries.

Everything else below is executable bookkeeping conditional on those two
non-overlapping facts:

* `on_block_transition_witness` extracts the actual opaque transition invoked
  by a successful transcribed handler;
* `WellFormedStoreCore` supplies the already-proved equality between a known
  block's slot and its stored state's slot;
* `FFGStoreProjection`/`FFGTransitionCoherence` identify reachable block-state
  checkpoints with `GJ`;
* existing `BlockProvenance` supplies scheduled root/message provenance, so
  the history contract does not assume it again;
* `ProjectedSameEpochTransition` and its transitive closure retain explicit
  transition witnesses, so the source-coherence conclusion does not assume
  the desired checkpoint equality in disguise.

The final honest-attestation lemmas also account for the validator spec's
conditional `process_slots` call.  They show that heads joined by such a
same-epoch transition segment produce equal FFG sources, provided each head
state and its vote slot lie in one epoch.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root}

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
structure BlockStateTransitionHistory (cfg : Config) (ext : Externals Root)
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

/-- A fresh successful `on_block` call necessarily reached a successful
invocation of the opaque `state_transition` on the parent block state. -/
theorem on_block_transition_witness
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hfresh : sb.root ∉ store.block_roots)
    (hh : on_block cfg ext store sb = some store') :
    ∃ post : BeaconState Root,
      ext.state_transition (store.block_states sb.message.parent_root) sb =
        some post := by
  simp only [on_block, if_neg hfresh] at hh
  split_ifs at hh <;> try cases hh
  cases hst : ext.state_transition
      (store.block_states sb.message.parent_root) sb with
  | none => rw [hst] at hh; cases hh
  | some post => exact ⟨post, rfl⟩

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

/-- At the state-function boundary, a same-epoch successful handler transition
preserves the realized justified checkpoint.  The transition witness comes
from the handler; only the equality itself comes from
`Phase0SourceCoherence`. -/
theorem on_block_transition_current_justified
    (hphase : Phase0SourceCoherence cfg ext)
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hfresh : sb.root ∉ store.block_roots)
    (hsame : compute_epoch_at_slot cfg
        (store.block_states sb.message.parent_root).slot =
      compute_epoch_at_slot cfg sb.message.slot)
    (hh : on_block cfg ext store sb = some store') :
    ∃ post : BeaconState Root,
      ext.state_transition (store.block_states sb.message.parent_root) sb =
          some post ∧
        post.current_justified_checkpoint =
          (store.block_states sb.message.parent_root).current_justified_checkpoint := by
  obtain ⟨post, htransition⟩ := on_block_transition_witness (cfg := cfg)
    (ext := ext) hfresh hh
  exact ⟨post, htransition,
    hphase.state_transition_current_justified _ _ _ htransition hsame⟩

/-! ## Projected same-epoch block edges and segments -/

variable {E : Execution Root} {anchor : Checkpoint Root}
variable {S : ChainFFGState cfg E anchor}

/-- Message provenance identifies the reconstructed stored block as an actual
scheduled block whenever its root is known and non-genesis.  This is already
derivable from the handlers; it is not part of
`BlockStateTransitionHistory`. -/
theorem Execution.storedSignedBlock_scheduled
    (E : Execution Root) (w : ValidatorIndex) (n : ℕ)
    {child : Root}
    (hchild : child ∈ (E.store cfg ext w n).block_roots)
    (hnongenesis : child ∉ E.genesis_store.block_roots) :
    IsScheduledBlock E
      (storedSignedBlock (E.store cfg ext w n) child) := by
  rcases E.blockProvenance cfg ext w n child hchild with hgen | hscheduled
  · exact False.elim (hnongenesis hgen.1)
  · rcases hscheduled with ⟨sb, hschedule, hroot, hmessage⟩
    have heq : sb = storedSignedBlock (E.store cfg ext w n) child := by
      cases sb with
      | mk message root =>
          simp only at hroot hmessage ⊢
          subst root
          simp only [storedSignedBlock]
          rw [hmessage]
    rwa [← heq]

/-- Full accepted-block history statement recovered at a reachable view: a
known non-genesis root has a scheduled signed-block witness with the stored
root/message, a known stored parent, and the exact parent-state-to-child-state
transition equation.  Scheduled-message provenance is derived; only replay
of the erased state equation comes from `BlockStateTransitionHistory`. -/
theorem Execution.known_non_genesis_block_transition_witness
    (hhistory : BlockStateTransitionHistory cfg ext E)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n) {child : Root}
    (hchild : child ∈ (E.store cfg ext w n).block_roots)
    (hnongenesis : child ∉ E.genesis_store.block_roots) :
    ∃ sb : SignedBeaconBlock Root,
      IsScheduledBlock E sb ∧
      sb.root = child ∧
      sb.message = (E.store cfg ext w n).blocks child ∧
      ((E.store cfg ext w n).blocks child).parent_root ∈
        (E.store cfg ext w n).block_roots ∧
      ext.state_transition
          ((E.store cfg ext w n).block_states
            ((E.store cfg ext w n).blocks child).parent_root) sb =
        some ((E.store cfg ext w n).block_states child) := by
  have hreplay := hhistory.replay w hw n hH child hchild hnongenesis
  refine ⟨storedSignedBlock (E.store cfg ext w n) child,
    E.storedSignedBlock_scheduled (cfg := cfg) (ext := ext)
      w n hchild hnongenesis,
    rfl, rfl, ?_⟩
  exact hreplay

/-- One executable state-transition edge, viewed through the exact FFG store
projection.  All fields except `same_epoch` are direct data/equalities from
the handler/state model.  In particular, this structure does *not* contain a
checkpoint-equality field.

Different edges in a segment may be witnessed in different stores.  This is
useful for a historical handler trace while retaining one global block-local
projection `S`. -/
def ProjectedSameEpochTransition
    (cfg : Config) (ext : Externals Root)
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

/-- Recover an explicit projected edge at an arbitrary later reachable view
from the narrow replay-history contract.  Scheduled-message provenance and
the FFG store projection remain derived trajectory theorems. -/
theorem of_history
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    {child : Root}
    (hchild : child ∈ (E.store cfg ext w n).block_roots)
    (hnongenesis : child ∉ E.genesis_store.block_roots)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    (hsame : compute_epoch_at_slot cfg
        ((E.store cfg ext w n).blocks
          ((E.store cfg ext w n).blocks child).parent_root).slot =
      compute_epoch_at_slot cfg
        ((E.store cfg ext w n).blocks child).slot) :
    ProjectedSameEpochTransition cfg ext E S
      ((E.store cfg ext w n).blocks child).parent_root child := by
  let store := E.store cfg ext w n
  let parent := (store.blocks child).parent_root
  have hreplay := hhistory.replay w hw n hH child hchild hnongenesis
  change parent ∈ store.block_roots ∧
    ext.state_transition (store.block_states parent)
      (storedSignedBlock store child) = some (store.block_states child) at hreplay
  have hscheduled : ∃ w' n',
      Event.block (storedSignedBlock store child) ∈ E.schedule w' n' := by
    exact E.storedSignedBlock_scheduled (cfg := cfg) (ext := ext)
      w n hchild hnongenesis
  refine ⟨store, E.ffgStoreProjection hcoh w n,
    storedSignedBlock store child, rfl, rfl, hreplay.1, hscheduled,
    store.block_states child, hreplay.2, ?_⟩
  rw [hcore.2 parent hreplay.1]
  exact hsame

/-- Construct a projected edge directly from a successful handler call.
`WellFormedStoreCore` turns the executable block-epoch equality into the
state-epoch equality consumed by the phase0 contract.  No checkpoint equality
is assumed. -/
theorem of_on_block
    {store store' : Store Root} {sb : SignedBeaconBlock Root}
    (hprojection : FFGStoreProjection cfg ext S store)
    (hcore : WellFormedStoreCore store)
    (hscheduled : ∃ w n, Event.block sb ∈ E.schedule w n)
    (hfresh : sb.root ∉ store.block_roots)
    (hparent : sb.message.parent_root ∈ store.block_roots)
    (hsame : compute_epoch_at_slot cfg
        (store.blocks sb.message.parent_root).slot =
      compute_epoch_at_slot cfg sb.message.slot)
    (hh : on_block cfg ext store sb = some store') :
    ProjectedSameEpochTransition cfg ext E S
      sb.message.parent_root sb.root := by
  obtain ⟨post, htransition⟩ := on_block_transition_witness (cfg := cfg)
    (ext := ext) hfresh hh
  refine ⟨store, hprojection, sb, rfl, rfl, hparent, hscheduled,
    post, htransition, ?_⟩
  rw [hcore.2 sb.message.parent_root hparent]
  exact hsame

/-- The new phase0 contract turns one explicit same-epoch transition into the
corresponding `GJ` source equality.  Projection and transition coherence are
used only for their exact state-function equations. -/
theorem gj_eq_parent
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {parent child : Root}
    (h : ProjectedSameEpochTransition cfg ext E S parent child) :
    S.GJ child = S.GJ parent := by
  rcases h with
    ⟨store, hprojection, signed_block, hchild, hparent, hparentKnown,
      hscheduled, post, htransition, hsame⟩
  calc
    S.GJ child = post.current_justified_checkpoint := by
      rw [← hchild]
      exact (hcoh.transition_gj _ _ _ hscheduled htransition).symm
    _ = (store.block_states parent).current_justified_checkpoint :=
      hphase.state_transition_current_justified _ _ _ htransition hsame
    _ = S.GJ parent :=
      hprojection.block_state_gj parent hparentKnown

end ProjectedSameEpochTransition

/-- Every known non-genesis same-epoch parent edge in a reachable honest view
preserves `GJ`.  The result combines the replay-history contract with the
separate phase0 same-epoch law; neither contract contains this conclusion. -/
theorem Execution.known_same_epoch_parent_gj_eq
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    {child : Root}
    (hchild : child ∈ (E.store cfg ext w n).block_roots)
    (hnongenesis : child ∉ E.genesis_store.block_roots)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    (hsame : compute_epoch_at_slot cfg
        ((E.store cfg ext w n).blocks
          ((E.store cfg ext w n).blocks child).parent_root).slot =
      compute_epoch_at_slot cfg
        ((E.store cfg ext w n).blocks child).slot) :
    S.GJ child =
      S.GJ ((E.store cfg ext w n).blocks child).parent_root := by
  have hedge : ProjectedSameEpochTransition cfg ext E S
      ((E.store cfg ext w n).blocks child).parent_root child :=
    ProjectedSameEpochTransition.of_history (S := S) hhistory hcoh hw hH hchild
      hnongenesis hcore hsame
  exact hedge.gj_eq_parent hphase hcoh

/-- Reflexive/transitive closure of explicit projected same-epoch transition
edges.  This is the narrow block-state ancestry object needed for source
coherence; it contains no safety, canonicality, or A3.2 premise. -/
inductive ProjectedSameEpochSegment
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (S : ChainFFGState cfg E anchor) :
    Root → Root → Prop
  | refl (r : Root) : ProjectedSameEpochSegment cfg ext E S r r
  | tail {first middle last : Root} :
      ProjectedSameEpochSegment cfg ext E S first middle →
      ProjectedSameEpochTransition cfg ext E S middle last →
      ProjectedSameEpochSegment cfg ext E S first last

namespace ProjectedSameEpochSegment

/-- `GJ` is constant along any explicitly witnessed same-epoch transition
segment. -/
theorem gj_eq_first
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {first last : Root}
    (h : ProjectedSameEpochSegment cfg ext E S first last) :
    S.GJ last = S.GJ first := by
  induction h with
  | refl => rfl
  | tail hsegment hedge ih =>
      exact (hedge.gj_eq_parent hphase hcoh).trans ih

/-- Two branches reached from one explicitly witnessed same-epoch transition
ancestor have the same realized justified source. -/
theorem gj_eq_of_common_first
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {common left right : Root}
    (hleft : ProjectedSameEpochSegment cfg ext E S common left)
    (hright : ProjectedSameEpochSegment cfg ext E S common right) :
    S.GJ left = S.GJ right :=
  (hleft.gj_eq_first hphase hcoh).trans
    (hright.gj_eq_first hphase hcoh).symm

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

/-- `GJ` is constant along every concrete known same-epoch ancestry segment
in a reachable honest view.  This is the trajectory-facing closure of the
single-edge theorem above. -/
theorem Execution.gj_eq_of_known_same_epoch_ancestry
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    {first last : Root}
    (hsegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots (E.store cfg ext w n) first last) :
    S.GJ last = S.GJ first := by
  induction hsegment with
  | refl => rfl
  | @tail parent child hprefix hchild hnongenesis hparent hsame ih =>
      have hsame' : compute_epoch_at_slot cfg
          ((E.store cfg ext w n).blocks
            ((E.store cfg ext w n).blocks child).parent_root).slot =
        compute_epoch_at_slot cfg
          ((E.store cfg ext w n).blocks child).slot := by
        rw [hparent]
        exact hsame
      have hedge := E.known_same_epoch_parent_gj_eq hhistory hphase hcoh
        hw hH hchild hnongenesis hcore hsame'
      rw [hparent] at hedge
      exact hedge.trans ih

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

/-- Read the honest attestation's source as the exact block-local `GJ` value
of its head.  Head knownness and the FFG projection are executable/reachable
store facts; only preservation through `process_slots` uses the new contract. -/
theorem honest_attestation_data_source_eq_gj
    (hphase : Phase0SourceCoherence cfg ext)
    {store : Store Root} {slot : Slot} {index : CommitteeIndex}
    (hprojection : FFGStoreProjection cfg ext S store)
    (hhead : (get_head cfg store).root ∈ store.block_roots)
    (hsame : compute_epoch_at_slot cfg
        (store.block_states (get_head cfg store).root).slot =
      compute_epoch_at_slot cfg slot) :
    (honest_attestation_data cfg ext store slot index).source =
      S.GJ (get_head cfg store).root := by
  rw [honest_attestation_data_source_eq_head_state hphase store slot index hsame]
  exact hprojection.block_state_gj _ hhead

/-- Common-boundary-to-head source theorem for an actual reachable view.  If
the fork-choice head is connected to `common` by known same-epoch parent
edges, an honest vote whose slot remains in the head state's epoch uses
exactly `GJ(common)` as its source. -/
theorem Execution.honest_attestation_source_eq_common_ancestor
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w : ValidatorIndex} (hw : w ∈ E.honest) {n : ℕ}
    (hH : E.WithinHorizon cfg n)
    (hcore : WellFormedStoreCore (E.store cfg ext w n))
    {common : Root} {slot : Slot} {index : CommitteeIndex}
    (hsegment : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots (E.store cfg ext w n)
      common (get_head cfg (E.store cfg ext w n)).root)
    (hvoteEpoch : compute_epoch_at_slot cfg
        ((E.store cfg ext w n).block_states
          (get_head cfg (E.store cfg ext w n)).root).slot =
      compute_epoch_at_slot cfg slot) :
    (honest_attestation_data cfg ext (E.store cfg ext w n) slot index).source =
      S.GJ common := by
  calc
    (honest_attestation_data cfg ext (E.store cfg ext w n) slot index).source =
        S.GJ (get_head cfg (E.store cfg ext w n)).root :=
      honest_attestation_data_source_eq_gj hphase
        (E.ffgStoreProjection hcoh w n) hsegment.last_known hvoteEpoch
    _ = S.GJ common :=
      E.gj_eq_of_known_same_epoch_ancestry hhistory hphase hcoh hw hH hcore hsegment

/-- Two reachable honest views voting from heads on same-epoch branches above
one common root use the same FFG source.  This is the executable-store form
needed before aggregating their target votes into a source-specific link. -/
theorem Execution.honest_attestation_sources_eq_of_known_common_ancestor
    (hhistory : BlockStateTransitionHistory cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {w₁ w₂ : ValidatorIndex} (hw₁ : w₁ ∈ E.honest)
    (hw₂ : w₂ ∈ E.honest) {n₁ n₂ : ℕ}
    (hH₁ : E.WithinHorizon cfg n₁) (hH₂ : E.WithinHorizon cfg n₂)
    (hcore₁ : WellFormedStoreCore (E.store cfg ext w₁ n₁))
    (hcore₂ : WellFormedStoreCore (E.store cfg ext w₂ n₂))
    {common : Root} {slot₁ slot₂ : Slot}
    {index₁ index₂ : CommitteeIndex}
    (hsegment₁ : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots (E.store cfg ext w₁ n₁)
      common (get_head cfg (E.store cfg ext w₁ n₁)).root)
    (hsegment₂ : KnownSameEpochAncestrySegment cfg
      E.genesis_store.block_roots (E.store cfg ext w₂ n₂)
      common (get_head cfg (E.store cfg ext w₂ n₂)).root)
    (hvoteEpoch₁ : compute_epoch_at_slot cfg
        ((E.store cfg ext w₁ n₁).block_states
          (get_head cfg (E.store cfg ext w₁ n₁)).root).slot =
      compute_epoch_at_slot cfg slot₁)
    (hvoteEpoch₂ : compute_epoch_at_slot cfg
        ((E.store cfg ext w₂ n₂).block_states
          (get_head cfg (E.store cfg ext w₂ n₂)).root).slot =
      compute_epoch_at_slot cfg slot₂) :
    (honest_attestation_data cfg ext (E.store cfg ext w₁ n₁)
        slot₁ index₁).source =
      (honest_attestation_data cfg ext (E.store cfg ext w₂ n₂)
        slot₂ index₂).source := by
  exact (E.honest_attestation_source_eq_common_ancestor hhistory hphase hcoh
    hw₁ hH₁ hcore₁ hsegment₁ hvoteEpoch₁).trans
      (E.honest_attestation_source_eq_common_ancestor hhistory hphase hcoh
        hw₂ hH₂ hcore₂ hsegment₂ hvoteEpoch₂).symm

/-- Two honest attestation constructions whose heads are joined by an
explicit same-epoch transition segment have the same source.  The vote slots
may differ, but each must remain in the epoch of its own head state. -/
theorem honest_attestation_sources_eq_of_segment
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {store₁ store₂ : Store Root}
    {slot₁ slot₂ : Slot} {index₁ index₂ : CommitteeIndex}
    (hprojection₁ : FFGStoreProjection cfg ext S store₁)
    (hprojection₂ : FFGStoreProjection cfg ext S store₂)
    (hhead₁ : (get_head cfg store₁).root ∈ store₁.block_roots)
    (hhead₂ : (get_head cfg store₂).root ∈ store₂.block_roots)
    (hsame₁ : compute_epoch_at_slot cfg
        (store₁.block_states (get_head cfg store₁).root).slot =
      compute_epoch_at_slot cfg slot₁)
    (hsame₂ : compute_epoch_at_slot cfg
        (store₂.block_states (get_head cfg store₂).root).slot =
      compute_epoch_at_slot cfg slot₂)
    (hsegment : ProjectedSameEpochSegment cfg ext E S
      (get_head cfg store₁).root (get_head cfg store₂).root) :
    (honest_attestation_data cfg ext store₁ slot₁ index₁).source =
      (honest_attestation_data cfg ext store₂ slot₂ index₂).source := by
  rw [honest_attestation_data_source_eq_gj hphase hprojection₁ hhead₁ hsame₁,
    honest_attestation_data_source_eq_gj hphase hprojection₂ hhead₂ hsame₂]
  exact (hsegment.gj_eq_first hphase hcoh).symm

/-- Branching form of source coherence: honest attestation constructions on
two heads have equal sources when both heads descend, through explicitly
witnessed same-epoch state transitions, from one common block-state source.
This is the form relevant to two views that share an epoch target but may have
different descendant heads. -/
theorem honest_attestation_sources_eq_of_common_segment
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : FFGTransitionCoherence cfg ext S)
    {store₁ store₂ : Store Root}
    {slot₁ slot₂ : Slot} {index₁ index₂ : CommitteeIndex}
    {common : Root}
    (hprojection₁ : FFGStoreProjection cfg ext S store₁)
    (hprojection₂ : FFGStoreProjection cfg ext S store₂)
    (hhead₁ : (get_head cfg store₁).root ∈ store₁.block_roots)
    (hhead₂ : (get_head cfg store₂).root ∈ store₂.block_roots)
    (hsame₁ : compute_epoch_at_slot cfg
        (store₁.block_states (get_head cfg store₁).root).slot =
      compute_epoch_at_slot cfg slot₁)
    (hsame₂ : compute_epoch_at_slot cfg
        (store₂.block_states (get_head cfg store₂).root).slot =
      compute_epoch_at_slot cfg slot₂)
    (hsegment₁ : ProjectedSameEpochSegment cfg ext E S
      common (get_head cfg store₁).root)
    (hsegment₂ : ProjectedSameEpochSegment cfg ext E S
      common (get_head cfg store₂).root) :
    (honest_attestation_data cfg ext store₁ slot₁ index₁).source =
      (honest_attestation_data cfg ext store₂ slot₂ index₂).source := by
  rw [honest_attestation_data_source_eq_gj hphase hprojection₁ hhead₁ hsame₁,
    honest_attestation_data_source_eq_gj hphase hprojection₂ hhead₂ hsame₂]
  exact hsegment₁.gj_eq_of_common_first hphase hcoh hsegment₂

/-! ## Accepted exact-prefix source coherence -/

/-- Named data for one accepted same-epoch source edge.  The edge owns the
actual scheduled-prefix transition, exact parent and child accepted block
witnesses, and a named formed carrier for the child's `GJ`. -/
structure AcceptedProjectedSameEpochTransitionCarrier
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (S : AcceptedChainFFGState cfg ext E anchor)
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
  child_gj_carrier : AcceptedSelectorAUCarrier S transition.postStore
    (S.GJ child)

/-- Proposition-level ownership of the full named accepted edge carrier. -/
def AcceptedProjectedSameEpochTransition
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (S : AcceptedChainFFGState cfg ext E anchor)
    (parent child : Root) : Prop :=
  Nonempty
    (AcceptedProjectedSameEpochTransitionCarrier cfg ext E S parent child)

namespace AcceptedProjectedSameEpochTransition

/-- The sole producer for an accepted source edge: an actual successful block
transition at the exact next scheduled-prefix position.  Replay history is
not an input and cannot establish this edge. -/
theorem of_transition
    {S : AcceptedChainFFGState cfg ext E anchor}
    (t : E.AcceptedBlockTransition cfg ext)
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
  let hgjCarrier : AcceptedSelectorAUCarrier S t.postStore
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
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    {parent child : Root}
    (h : AcceptedProjectedSameEpochTransition cfg ext E S parent child) :
    S.GJ child = S.GJ parent := by
  obtain ⟨edge⟩ := h
  have hprojection : AcceptedFFGStoreProjection S
      (edge.transition.atPrefix.store cfg ext) :=
    edge.transition.atPrefix.acceptedFFGStoreProjection hcoh
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

end AcceptedProjectedSameEpochTransition

/-- Reflexive/transitive closure of accepted edges.  Even a reflexive segment
retains an exact accepted block witness; every nontrivial edge owns an actual
`AcceptedBlockTransition` through its carrier evidence. -/
inductive AcceptedProjectedSameEpochSegment
    (cfg : Config) (ext : Externals Root)
    (E : Execution Root) (S : AcceptedChainFFGState cfg ext E anchor) :
    Root → Root → Prop
  | refl (r : Root) (b : BeaconBlock Root)
      (block_at : E.AcceptedBlockAt cfg ext r b) :
      AcceptedProjectedSameEpochSegment cfg ext E S r r
  | tail {first middle last : Root} :
      AcceptedProjectedSameEpochSegment cfg ext E S first middle →
      AcceptedProjectedSameEpochTransition cfg ext E S middle last →
      AcceptedProjectedSameEpochSegment cfg ext E S first last

namespace AcceptedProjectedSameEpochSegment

theorem gj_eq_first
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    {first last : Root}
    (h : AcceptedProjectedSameEpochSegment cfg ext E S first last) :
    S.GJ last = S.GJ first := by
  induction h with
  | refl => rfl
  | tail hprefix hedge ih =>
      exact (hedge.gj_eq_parent hphase hcoh).trans ih

theorem gj_eq_of_common_first
    {S : AcceptedChainFFGState cfg ext E anchor}
    (hphase : Phase0SourceCoherence cfg ext)
    (hcoh : AcceptedFFGSelectorCoherence cfg ext S)
    {common left right : Root}
    (hleft : AcceptedProjectedSameEpochSegment cfg ext E S common left)
    (hright : AcceptedProjectedSameEpochSegment cfg ext E S common right) :
    S.GJ left = S.GJ right :=
  (hleft.gj_eq_first hphase hcoh).trans
    (hright.gj_eq_first hphase hcoh).symm

end AcceptedProjectedSameEpochSegment

/-- Named accepted/global readback carrier for one honest attestation source.
It retains the exact accepted head block and the formed carrier witnessing AU
for the selected block-local `GJ`. -/
structure AcceptedHonestSourceCarrier
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex) where
  global_projection : AcceptedFFGGlobalStoreProjection S store
  head_block : BeaconBlock Root
  head_block_at : E.AcceptedBlockAt cfg ext (get_head cfg store).root
    head_block
  head_block_eq : head_block = store.blocks (get_head cfg store).root
  head_gj_carrier : AcceptedSelectorAUCarrier S store
    (S.GJ (get_head cfg store).root)
  source_eq : (honest_attestation_data cfg ext store slot index).source =
    S.GJ (get_head cfg store).root

def AcceptedHonestSourceEvidence
    (S : AcceptedChainFFGState cfg ext E anchor)
    (store : Store Root) (slot : Slot) (index : CommitteeIndex) : Prop :=
  Nonempty (AcceptedHonestSourceCarrier S store slot index)

namespace AcceptedHonestSourceEvidence

theorem source_eq
    {S : AcceptedChainFFGState cfg ext E anchor}
    {store : Store Root} {slot : Slot} {index : CommitteeIndex}
    (h : AcceptedHonestSourceEvidence S store slot index) :
    (honest_attestation_data cfg ext store slot index).source =
      S.GJ (get_head cfg store).root := by
  obtain ⟨carrier⟩ := h
  exact carrier.source_eq

end AcceptedHonestSourceEvidence

namespace ExactPrefixAcceptedFFGSemantics

/-- Small causal/global source consumer for the production accepted bundle.
The semantic state is selected before the store; local projection, global
origins, the exact accepted head block, AU, and formed evidence are retained. -/
theorem causalStoreHonestSourceEvidence
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
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
    AcceptedHonestSourceEvidence B.state store slot index := by
  let hglobal : AcceptedFFGGlobalStoreProjection B.state store :=
    B.causalStoreGlobalProjection hgen hanchor hstore
  let htip : E.AcceptedCarrierIn
      (cfg := cfg) (ext := ext) store (get_head cfg store).root :=
    Execution.AcceptedCarrierIn.of_causal_known hstore hhead
  obtain ⟨carrier, hdesc, hformed⟩ :=
    B.state.gj_mem (get_head cfg store).root htip.acceptedRoot
  let hgjCarrier : AcceptedSelectorAUCarrier B.state store
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

/-- Exact scheduled-prefix specialization of the causal/global source
consumer. -/
theorem scheduledEventPrefixHonestSourceEvidence
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (p : E.ScheduledEventPrefix)
    {slot : Slot} {index : CommitteeIndex}
    (hhead : (get_head cfg (p.store cfg ext)).root ∈
      (p.store cfg ext).block_roots)
    (hsame : compute_epoch_at_slot cfg
        ((p.store cfg ext).block_states
          (get_head cfg (p.store cfg ext)).root).slot =
      compute_epoch_at_slot cfg slot) :
    AcceptedHonestSourceEvidence B.state (p.store cfg ext) slot index :=
  B.causalStoreHonestSourceEvidence hphase hgen hanchor
    (.scheduledPrefix p) hhead hsame

/-- Two causal stores whose heads are joined only by actual accepted
same-epoch transitions produce the same honest FFG source. -/
theorem honestAttestationSources_eq_of_segment
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store₁ store₂ : Store Root}
    (hstore₁ : E.CausalStore cfg ext store₁)
    (hstore₂ : E.CausalStore cfg ext store₂)
    {slot₁ slot₂ : Slot} {index₁ index₂ : CommitteeIndex}
    (hhead₁ : (get_head cfg store₁).root ∈ store₁.block_roots)
    (hhead₂ : (get_head cfg store₂).root ∈ store₂.block_roots)
    (hsame₁ : compute_epoch_at_slot cfg
        (store₁.block_states (get_head cfg store₁).root).slot =
      compute_epoch_at_slot cfg slot₁)
    (hsame₂ : compute_epoch_at_slot cfg
        (store₂.block_states (get_head cfg store₂).root).slot =
      compute_epoch_at_slot cfg slot₂)
    (hsegment : AcceptedProjectedSameEpochSegment cfg ext E B.state
      (get_head cfg store₁).root (get_head cfg store₂).root) :
    (honest_attestation_data cfg ext store₁ slot₁ index₁).source =
      (honest_attestation_data cfg ext store₂ slot₂ index₂).source := by
  have hsource₁ := B.causalStoreHonestSourceEvidence hphase hgen hanchor
    hstore₁ (slot := slot₁) (index := index₁) hhead₁ hsame₁
  have hsource₂ := B.causalStoreHonestSourceEvidence hphase hgen hanchor
    hstore₂ (slot := slot₂) (index := index₂) hhead₂ hsame₂
  exact hsource₁.source_eq.trans
    ((hsegment.gj_eq_first hphase
      B.coherence.toAcceptedFFGSelectorCoherence).symm.trans
        hsource₂.source_eq.symm)

/-- Branching causal-store consumer used by fixed-source support arguments:
both heads may lie on different branches, but every edge on both paths from
the common root is backed by an actual accepted scheduled-prefix transition. -/
theorem honestAttestationSources_eq_of_common_segment
    {E : Execution Root}
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hphase : Phase0SourceCoherence cfg ext)
    (hgen : ∃ (ast : BeaconState Root) (ablk : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg ast ablk ∧
      ast.slot = ablk.message.slot)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    {store₁ store₂ : Store Root}
    (hstore₁ : E.CausalStore cfg ext store₁)
    (hstore₂ : E.CausalStore cfg ext store₂)
    {slot₁ slot₂ : Slot} {index₁ index₂ : CommitteeIndex}
    {common : Root}
    (hhead₁ : (get_head cfg store₁).root ∈ store₁.block_roots)
    (hhead₂ : (get_head cfg store₂).root ∈ store₂.block_roots)
    (hsame₁ : compute_epoch_at_slot cfg
        (store₁.block_states (get_head cfg store₁).root).slot =
      compute_epoch_at_slot cfg slot₁)
    (hsame₂ : compute_epoch_at_slot cfg
        (store₂.block_states (get_head cfg store₂).root).slot =
      compute_epoch_at_slot cfg slot₂)
    (hsegment₁ : AcceptedProjectedSameEpochSegment cfg ext E B.state
      common (get_head cfg store₁).root)
    (hsegment₂ : AcceptedProjectedSameEpochSegment cfg ext E B.state
      common (get_head cfg store₂).root) :
    (honest_attestation_data cfg ext store₁ slot₁ index₁).source =
      (honest_attestation_data cfg ext store₂ slot₂ index₂).source := by
  have hsource₁ := B.causalStoreHonestSourceEvidence hphase hgen hanchor
    hstore₁ (slot := slot₁) (index := index₁) hhead₁ hsame₁
  have hsource₂ := B.causalStoreHonestSourceEvidence hphase hgen hanchor
    hstore₂ (slot := slot₂) (index := index₂) hhead₂ hsame₂
  exact hsource₁.source_eq.trans
    ((hsegment₁.gj_eq_of_common_first hphase
      B.coherence.toAcceptedFFGSelectorCoherence hsegment₂).trans
        hsource₂.source_eq.symm)

end ExactPrefixAcceptedFFGSemantics

/-! ## Contract non-vacuity -/

namespace SourceCoherenceNonVacuity

/-- A finite root domain with distinct dangling-parent, anchor, and child
roots. -/
abbrev WitnessRoot := Fin 3

private def junkRoot : WitnessRoot := 0
private def anchorRoot : WitnessRoot := 1
private def childRoot : WitnessRoot := 2

private def witnessConfig : Config where
  slots_per_epoch := 2
  slots_per_epoch_pos := by decide
  slot_duration_ms := 1000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 40
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 100
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 3333
  min_seed_lookahead := 1

private def anchorCheckpoint : Checkpoint WitnessRoot :=
  { epoch := 0, root := anchorRoot }

private def witnessValidator : Validator :=
  { effective_balance := 100
    slashed := false
    activation_epoch := 0
    exit_epoch := 1 }

private def stateAt (slot : Slot) : BeaconState WitnessRoot :=
  { genesis_time := 0
    slot := slot
    validators := [witnessValidator]
    current_justified_checkpoint := anchorCheckpoint
    finalized_checkpoint := anchorCheckpoint }

private def anchorState : BeaconState WitnessRoot := stateAt 0

private def anchorBlock : SignedBeaconBlock WitnessRoot :=
  { root := anchorRoot
    message := { slot := 0, parent_root := junkRoot } }

private def childBlock : SignedBeaconBlock WitnessRoot :=
  { root := childRoot
    message := { slot := 1, parent_root := anchorRoot } }

private def vote0 : Attestation WitnessRoot :=
  { attesting_indices := [0]
    data :=
      { slot := 0
        index := 0
        beacon_block_root := anchorRoot
        source := anchorCheckpoint
        target := anchorCheckpoint } }

/-- The concrete opaque functions are intentionally simple but non-vacuous:
the child transition succeeds and preserves the entire pre-state except for
its slot. -/
private def witnessExternals : Externals WitnessRoot where
  get_beacon_committee := fun _ _ _ => [0]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := fun st slot => { st with slot := slot }
  state_transition := fun st block =>
    if block = childBlock ∧ st.slot < block.message.slot then
      some { st with slot := block.message.slot }
    else none
  process_justification_and_finalization := id
  is_valid_indexed_attestation := fun _ _ => false

private def witnessSchedule (w : ValidatorIndex) (n : ℕ) :
    List (Event WitnessRoot) :=
  if w = 0 ∧ n = 1 then [Event.block childBlock] else []

private def witnessVote (v : ValidatorIndex) (slot : Slot) :
    Option (ℕ × Attestation WitnessRoot) :=
  if v = 0 ∧ slot = 0 then some (0, vote0) else none

/-- One positive-balance honest validator, one recorded vote, and one
handler-accepted non-genesis block. -/
private def witnessExecution : Execution WitnessRoot where
  verification_horizon := 1
  genesis_store := get_forkchoice_store witnessConfig anchorState anchorBlock
  schedule := witnessSchedule
  honest := {0}
  committee := fun _ => {0}
  vote := witnessVote

private theorem witness_slot_at (n : ℕ) :
    witnessExecution.slot_at witnessConfig n = n := by
  norm_num [Execution.slot_at, Execution.time_at, witnessExecution,
    witnessConfig, anchorState, stateAt, anchorBlock,
    get_forkchoice_store, GENESIS_SLOT]

private theorem witness_time_lt_two {n : ℕ}
    (hn : witnessExecution.WithinHorizon witnessConfig n) : n < 2 := by
  have hepoch := hn.2.2
  rw [witness_slot_at] at hepoch
  change n / 2 < 1 at hepoch
  rwa [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)] at hepoch

private theorem witness_phase0_source_coherence :
    Phase0SourceCoherence witnessConfig witnessExternals := by
  constructor
  · intro st target _hlt _hsame
    rfl
  · intro pre sb post htransition _hsame
    simp only [witnessExternals] at htransition
    split at htransition
    · simp only [Option.some.injEq] at htransition
      subst post
      rfl
    · contradiction

private theorem witness_store_one_roots :
    (witnessExecution.store witnessConfig witnessExternals 0 1).block_roots =
      [anchorRoot, childRoot] := by
  set_option maxRecDepth 20000 in decide

private theorem witness_store_one_child_block :
    (witnessExecution.store witnessConfig witnessExternals 0 1).blocks childRoot =
      childBlock.message := by
  rfl

private theorem witness_store_one_anchor_state :
    (witnessExecution.store witnessConfig witnessExternals 0 1).block_states anchorRoot =
      anchorState := by
  rfl

private theorem witness_store_one_child_state :
    (witnessExecution.store witnessConfig witnessExternals 0 1).block_states childRoot =
      stateAt 1 := by
  rfl

private theorem witness_block_state_transition_history :
    BlockStateTransitionHistory witnessConfig witnessExternals witnessExecution := by
  constructor
  intro w hw n hH child hchild hnongenesis
  have hw0 : w = 0 := by
    simpa [witnessExecution] using hw
  subst w
  have hnlt : n < 2 := witness_time_lt_two hH
  interval_cases n
  · exact False.elim (hnongenesis hchild)
  · rw [witness_store_one_roots] at hchild
    have hcases : child = anchorRoot ∨ child = childRoot := by
      simpa using hchild
    rcases hcases with hanchor | hchild
    · subst child
      exact False.elim (hnongenesis (by decide))
    · subst child
      dsimp only
      rw [witness_store_one_child_block]
      change anchorRoot ∈
          (witnessExecution.store witnessConfig witnessExternals 0 1).block_roots ∧
        witnessExternals.state_transition
            ((witnessExecution.store witnessConfig witnessExternals 0 1).block_states
              anchorRoot) childBlock =
          some ((witnessExecution.store witnessConfig witnessExternals 0 1).block_states
            childRoot)
      constructor
      · rw [witness_store_one_roots]
        simp
      · rw [witness_store_one_anchor_state, witness_store_one_child_state]
        rfl

/-- The two new contracts are jointly satisfiable in a finite,
handler-driven, economically nonzero execution.  The witness includes an
accepted non-genesis child and a recorded vote, so replay history is exercised
rather than discharged by an empty block domain. -/
theorem source_coherence_contracts_nonvacuous :
    ∃ (cfg : Config) (ext : Externals WitnessRoot)
      (E : Execution WitnessRoot),
      Phase0SourceCoherence cfg ext ∧
      BlockStateTransitionHistory cfg ext E ∧
      E.honest.Nonempty ∧
      0 < E.total_active cfg ∧
      (∃ v s, E.vote v s ≠ none) ∧
      ∃ w n r,
        w ∈ E.honest ∧ E.WithinHorizon cfg n ∧
        r ∈ (E.store cfg ext w n).block_roots ∧
        r ∉ E.genesis_store.block_roots := by
  refine ⟨witnessConfig, witnessExternals, witnessExecution,
    witness_phase0_source_coherence, witness_block_state_transition_history,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨0, by decide⟩
  · decide
  · exact ⟨0, 0, by decide⟩
  · refine ⟨0, 1, childRoot, by decide, ?_, ?_, ?_⟩
    · norm_num [Execution.WithinHorizon, Execution.time_at, witnessExecution,
        witnessConfig, anchorState, stateAt, anchorBlock,
        get_forkchoice_store, Execution.slot_at, compute_epoch_at_slot,
        UINT64_MAX, GENESIS_SLOT]
    · set_option maxRecDepth 20000 in decide
    · decide

end SourceCoherenceNonVacuity

end FastConfirmation.Spec

end
