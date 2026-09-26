module
public import Mathlib.Tactic
public import FastConfirmationProofs.Checkpoints.ResetCheckpointClassification
public import FastConfirmationProofs.Execution.Calls.ScheduledPrefixGeometry

public import FastConfirmationStatements.Premises.ScheduledExecutionConditions
public import FastConfirmationProofs.ModelFacts
@[expose] public section

/-!
# Accepted realized-finalization timing

The executable reset/history argument needs a non-anchor finalized reset to
be older than the previous epoch.  In subtraction-free form, for a causal
store at epoch `e` it needs

`store.finalized_checkpoint.epoch + 2 ≤ e`.

The accepted certificate model currently proves only strict oldness.  A
finalizing link out of epoch `f` targets epoch `f + 1`, and that target may be
included in a carrier in the same epoch.  Thus the existing evidence permits
`f + 1 = e`.  The real beacon-state transition does not realize that
finalization until the following epoch boundary, but this processing delay is
not one of the current `BeaconExternalsPremises` or accepted-selector laws.

Concretely, pinned Phase0 calls `process_epoch` while `state.slot` is still the
last slot of the old epoch, before incrementing the slot into the new epoch.
Even the newest finalization rule therefore produces `f + 1 ≤ oldEpoch`; a
post-state observed in the new epoch has `f + 2 ≤ newEpoch`.  The transcription
collapses all of that into opaque `state_transition`.  Its coherence record
retains only pre-slot strictness, the final post slot, registry preservation,
and `checkpoint.epoch ≤ blockEpoch`; it does not retain the old-epoch instant
at which `process_epoch` ran.  The separately opaque pulled-up PJF primitive
also has no finalized-age field.

The file records both the narrow base-consensus law and two counterpatterns:

* the abstract state-transition constraints admit a non-anchor finalized
  checkpoint from exactly the previous epoch; and
* all currently retained certificate/selector epoch inequalities are
  arithmetically compatible with the same one-epoch lag.

No safety, head, filter, confirmation, or selected-result fact belongs in the
missing law.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)

namespace Execution

variable (E : Execution Root)

/-! ## The unrealized side is already derivable -/

/-- A successful exact block prefix embeds in the completed store of that
same scheduled second.  This lets certificate evidence attached to the
newly accepted root use the ordinary-store semantic-ancestry reflection
lemmas, without postulating a second pulled-up-finalization delay law. -/
private theorem SuccessfulScheduledBlockImport.root_known_at_second_end
    (t : E.SuccessfulScheduledBlockImport cfg ext) :
    t.signedBlock.root ∈
      (E.store cfg ext t.atPrefix.node
        (t.atPrefix.previousSecond + 1)).block_roots := by
  let p := t.successorPrefix
  let events := E.schedule p.node (p.previousSecond + 1)
  let ticked := on_tick cfg (E.store cfg ext p.node p.previousSecond)
    (E.time_at (p.previousSecond + 1))
  have hrootPrefix : t.signedBlock.root ∈
      (p.store cfg ext).block_roots := by
    change t.signedBlock.root ∈
      (t.successorPrefix.store cfg ext).block_roots
    rw [t.successorPrefix_store]
    exact t.root_known
  have hprefix : p.store cfg ext =
      (events.take p.processedCount).foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked := by
    rfl
  have hle : StoreLE (p.store cfg ext)
      (events.foldl
        (fun store event => (apply_event cfg ext store event).getD store)
        ticked) := by
    have hfull : events.foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ticked =
        (events.drop p.processedCount).foldl
          (fun store event => (apply_event cfg ext store event).getD store)
          ((events.take p.processedCount).foldl
            (fun store event => (apply_event cfg ext store event).getD store)
            ticked) := by
      rw [← List.foldl_append, List.take_append_drop]
    rw [hfull, ← hprefix]
    exact foldl_storeLE cfg ext _ _
  rw [Execution.store]
  change t.signedBlock.root ∈
    (events.foldl
      (fun store event => (apply_event cfg ext store event).getD store)
      ticked).block_roots
  exact hle.1 hrootPrefix

/-- The included finalizing link already forces pulled-up finality (`GUF`) to
be no newer than the epoch immediately before its accepted carrier block.

The proof keeps the exact accepted carrier: one signer attests in epoch
`GUF.epoch + 1`, that attestation is included strictly before a semantic
ancestor of the accepted tip, and ordinary-store reflection turns the
semantic ancestry into the executable slot order. -/
theorem acceptedPulledUpFinalized_succ_le_blockEpoch
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (t : E.SuccessfulScheduledBlockImport cfg ext) :
    let pulledFinalized :=
      (ext.process_justification_and_finalization
        (t.postStore.block_states t.signedBlock.root)).finalized_checkpoint
    pulledFinalized = B.anchor ∨
      pulledFinalized.epoch + 1 ≤
        compute_epoch_at_slot cfg t.signedBlock.message.slot := by
  have hguf := B.coherence.transition_guf t
  rw [hguf]
  rcases B.state.unrealized_finalized_evidence t.signedBlock.root t.root_accepted with
    hanchor | hcertificate
  · exact Or.inl hanchor
  · right
    obtain ⟨F⟩ := hcertificate
    have hsigners : F.finalizing_link.signers.Nonempty := by
      by_contra hnone
      have hempty : F.finalizing_link.signers = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnone
      have hzero : 2 * E.total_active cfg ≤ 0 := by
        simpa only [hempty, Execution.weight, Finset.sum_empty,
          Nat.mul_zero] using F.finalizing_link.supermajority
      exact (Nat.not_lt_of_ge hzero)
        (Nat.mul_pos (by omega) (E.total_active_pos cfg))
    obtain ⟨i, hi⟩ := hsigners
    obtain ⟨a, ⟨containing, htipContaining, hincluded⟩,
        _hiAttests, _haSource, haTarget⟩ :=
      F.finalizing_link.signer_attestation i hi
    have hevidence := B.state.includedAttestations.evidence hincluded
    obtain ⟨ast, ablk, hgenEq, hslot, hparent⟩ := hT.genesis_structure
    have htipKnown : t.signedBlock.root ∈
        (E.store cfg ext t.atPrefix.node
          (t.atPrefix.previousSecond + 1)).block_roots :=
      t.root_known_at_second_end cfg ext
    have hcontainingRoot : E.ExecutionRoot containing :=
      ⟨hevidence.carrier_message, hevidence.carrier_at⟩
    have hreflection :=
      E.store_known_ancestor_of_rootDescends_for_storeReflection
        cfg ext hT.wellFormed hT.externals_coherence
        hgenEq hslot hparent htipKnown hcontainingRoot htipContaining
    have hcontainingKnown := hreflection.1
    have hancestor := hreflection.2
    let store := E.store cfg ext t.atPrefix.node
      (t.atPrefix.previousSecond + 1)
    have hparentSlots : ParentSlotLt store :=
      E.store_parentSlotLt cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩
        hT.wellFormed.anchor_parent_unscheduled
        t.atPrefix.node (t.atPrefix.previousSecond + 1)
    have hwalkK : ∀ target ∈ store.block_roots,
        ∀ r ∈ store.block_roots,
          WalkKnown store (store.blocks target).slot r :=
      E.store_walkKnownK cfg ext hT.wellFormed hT.externals_coherence
        ⟨ast, ablk, hgenEq, hslot, hparent⟩
        t.atPrefix.node (t.atPrefix.previousSecond + 1)
    have hslotLe : (store.blocks containing).slot ≤
        (store.blocks t.signedBlock.root).slot :=
      ancestor_slot_le hparentSlots
        (hwalkK containing hcontainingKnown
          t.signedBlock.root htipKnown) hancestor
    have hstoreCausal : E.ScheduledPrefixStore cfg ext store :=
      E.store_causal cfg ext t.atPrefix.node
        (t.atPrefix.previousSecond + 1)
    have hcontainingBlock : store.blocks containing =
        hevidence.carrier_message :=
      (Execution.ScheduledPrefixStore.acceptedBlockAt_iff_eq cfg ext E
        hT.wellFormed hstoreCausal hcontainingKnown).mp
          hevidence.carrier_accepted
    have htipAt : E.BlockKnownInScheduledPrefix cfg ext t.signedBlock.root
        t.signedBlock.message := by
      refine ⟨t.postStore, t.post_causal, t.root_known, ?_⟩
      by_cases hfresh : t.signedBlock.root ∉
          (t.atPrefix.store cfg ext).block_roots
      · exact t.inserted_message_fresh hfresh
      · have hknown : t.signedBlock.root ∈
            (t.atPrefix.store cfg ext).block_roots :=
          Classical.byContradiction hfresh
        have hpreStore : E.ScheduledPrefixStore cfg ext
            (t.atPrefix.store cfg ext) := .scheduledPrefix t.atPrefix
        have hprov := hpreStore.blockProvenance
          cfg ext E t.signedBlock.root hknown
        have hpreAt : E.BlockAt t.signedBlock.root
            ((t.atPrefix.store cfg ext).blocks t.signedBlock.root) := by
          rcases hprov with hgen | ⟨b, hsched, hroot, hmessage⟩
          · exact Or.inl ⟨hgen.1, hgen.2⟩
          · rcases hsched with ⟨w, n, hb⟩
            exact Or.inr ⟨w, n, b, hb, hroot, hmessage.symm⟩
        obtain ⟨hlt, hevent⟩ :=
          List.getElem?_eq_some_iff.mp t.event_at
        have hmemAt := List.getElem_mem hlt
        rw [hevent] at hmemAt
        have hsignedAt : E.BlockAt t.signedBlock.root
            t.signedBlock.message :=
          Or.inr ⟨t.atPrefix.node, t.atPrefix.previousSecond + 1,
            t.signedBlock, hmemAt, rfl, rfl⟩
        have hmessage := E.blockAt_unique
          hT.wellFormed hpreAt hsignedAt
        have hpost : t.postStore = t.atPrefix.store cfg ext := by
          exact (Option.some.inj (by
            simpa only [on_block, if_pos hknown] using t.accepted)).symm
        rw [hpost]
        exact hmessage
    have htipBlock : store.blocks t.signedBlock.root =
        t.signedBlock.message :=
      (Execution.ScheduledPrefixStore.acceptedBlockAt_iff_eq cfg ext E
        hT.wellFormed hstoreCausal htipKnown).mp htipAt
    have hattestationBeforeTip : a.data.slot <
        t.signedBlock.message.slot := by
      calc
        a.data.slot < hevidence.carrier_message.slot :=
          hevidence.slot_before_carrier
        _ = (store.blocks containing).slot :=
          (congrArg BeaconBlock.slot hcontainingBlock).symm
        _ ≤ (store.blocks t.signedBlock.root).slot := hslotLe
        _ = t.signedBlock.message.slot :=
          congrArg BeaconBlock.slot htipBlock
    have hchildEpoch : (B.state.unrealized_finalized t.signedBlock.root).epoch + 1 =
        compute_epoch_at_slot cfg a.data.slot := by
      calc
        (B.state.unrealized_finalized t.signedBlock.root).epoch + 1 = F.child.epoch :=
          F.child_epoch.symm
        _ = a.data.target.epoch :=
          congrArg Checkpoint.epoch haTarget.symm
        _ = compute_epoch_at_slot cfg a.data.slot := hevidence.target_epoch
    rw [hchildEpoch]
    exact ce_mono cfg (Nat.le_of_lt hattestationBeforeTip)

/-! ## The paired store invariant -/

/-- The realized/unrealized pair which the concrete fork-choice handlers
maintain.  Unrealized finality may be only one epoch old; at the next epoch
boundary it is copied into the realized field and thereby becomes two epochs
old. -/
structure AcceptedFinalizationLagAt (anchor : Checkpoint Root)
    (store : Store Root) : Prop where
  realized : store.finalized_checkpoint = anchor ∨
    store.finalized_checkpoint.epoch + 2 ≤
      get_current_store_epoch cfg store
  unrealized : store.unrealized_finalized_checkpoint = anchor ∨
    store.unrealized_finalized_checkpoint.epoch + 1 ≤
      get_current_store_epoch cfg store

namespace AcceptedFinalizationLagAt

private theorem oneEpochLag_becomes_two_of_strict
    {a b c : ℕ} (hab : a + 1 ≤ b) (hbc : b < c) : a + 2 ≤ c := by
  omega

/-- Transport when only the current epoch (rather than the underlying clock
fields) is already known equal. -/
theorem of_current_eq {anchor : Checkpoint Root} {store store' : Store Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store)
    (hfinalized : store'.finalized_checkpoint = store.finalized_checkpoint)
    (hunrealized : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    AcceptedFinalizationLagAt cfg anchor store' := by
  constructor
  · rw [hfinalized, hcurrent]
    exact h.realized
  · rw [hunrealized, hcurrent]
    exact h.unrealized

/-- Transport across a helper which preserves the clock and both finalized
fields. -/
theorem of_eq {anchor : Checkpoint Root} {store store' : Store Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (htime : store'.time = store.time)
    (hgenesis : store'.genesis_time = store.genesis_time)
    (hfinalized : store'.finalized_checkpoint = store.finalized_checkpoint)
    (hunrealized : store'.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint) :
    AcceptedFinalizationLagAt cfg anchor store' := by
  have hcurrent : get_current_store_epoch cfg store' =
      get_current_store_epoch cfg store := by
    simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg htime hgenesis)
  exact AcceptedFinalizationLagAt.of_current_eq
    (cfg := cfg) h hcurrent hfinalized hunrealized

theorem update_checkpoints (store : Store Root)
    (jc fc : Checkpoint Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hfc : fc = anchor ∨
      fc.epoch + 2 ≤ get_current_store_epoch cfg store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_checkpoints store jc fc) := by
  simp only [FastConfirmation.Spec.update_checkpoints]
  split_ifs
  all_goals
    constructor
    · first | exact hfc | exact h.realized
    · exact h.unrealized

theorem update_unrealized_checkpoints (store : Store Root)
    (ujc ufc : Checkpoint Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hufc : ufc = anchor ∨
      ufc.epoch + 1 ≤ get_current_store_epoch cfg store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_unrealized_checkpoints store ujc ufc) := by
  simp only [FastConfirmation.Spec.update_unrealized_checkpoints]
  split_ifs
  all_goals
    constructor
    · exact h.realized
    · first | exact hufc | exact h.unrealized

theorem record_block_timeliness (store : Store Root) (r : Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.record_block_timeliness cfg store r) :=
  AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

theorem update_proposer_boost_root (store : Store Root) (head r : Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_proposer_boost_root cfg store head r) := by
  simp only [FastConfirmation.Spec.update_proposer_boost_root]
  split_ifs <;>
    exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

theorem store_target_checkpoint_state (store : Store Root)
    (target : Checkpoint Root) {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.store_target_checkpoint_state cfg ext store target) := by
  simp only [FastConfirmation.Spec.store_target_checkpoint_state]
  split_ifs <;>
    exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

theorem update_latest_messages (store : Store Root)
    (indices : List ValidatorIndex) (a : Attestation Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.update_latest_messages store indices a) := by
  simp only [FastConfirmation.Spec.update_latest_messages]
  induction indices.filter (fun i => decide (i ∉ store.equivocating_indices))
      generalizing store with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      apply ih
      split_ifs <;>
        exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

theorem on_attestation {store store' : Store Root}
    {a : Attestation Root} {is_from_block : Bool}
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hh : FastConfirmation.Spec.on_attestation cfg ext store a is_from_block =
      some store') :
    AcceptedFinalizationLagAt cfg anchor store' := by
  simp only [FastConfirmation.Spec.on_attestation] at hh
  split_ifs at hh
  cases hh
  exact AcceptedFinalizationLagAt.update_latest_messages
    (cfg := cfg) _ _ _
    (AcceptedFinalizationLagAt.store_target_checkpoint_state
      (cfg := cfg) (ext := ext) _ _ h)

theorem on_attester_slashing {store store' : Store Root}
    {sl : AttesterSlashing Root} {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hh : FastConfirmation.Spec.on_attester_slashing ext store sl = some store') :
    AcceptedFinalizationLagAt cfg anchor store' := by
  simp only [FastConfirmation.Spec.on_attester_slashing] at hh
  split_ifs at hh
  cases hh
  exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl

/-- Pull-up preservation from the already-derived one-epoch GUF timing. -/
theorem compute_pulled_up_tip (store : Store Root) (r : Root)
    {anchor : Checkpoint Root}
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (huf : let ufc := (ext.process_justification_and_finalization
        (store.block_states r)).finalized_checkpoint
      ufc = anchor ∨ ufc.epoch + 1 ≤ get_block_epoch cfg store r)
    (hblock : get_block_epoch cfg store r ≤
      get_current_store_epoch cfg store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.compute_pulled_up_tip cfg ext store r) := by
  let state := ext.process_justification_and_finalization
    (store.block_states r)
  set ufc : Checkpoint Root := state.finalized_checkpoint with hufcEq
  have huf' : ufc = anchor ∨
      ufc.epoch + 1 ≤
        get_block_epoch cfg store r := by
    rw [hufcEq]
    simpa only [state] using huf
  let recorded : Store Root :=
    { store with
      unrealized_justifications := Function.update
        store.unrealized_justifications r
          state.current_justified_checkpoint }
  let pulled := FastConfirmation.Spec.update_unrealized_checkpoints recorded
    state.current_justified_checkpoint state.finalized_checkpoint
  have hrecorded : AcceptedFinalizationLagAt cfg anchor recorded :=
    AcceptedFinalizationLagAt.of_eq (cfg := cfg) h rfl rfl rfl rfl
  have hufCurrent : state.finalized_checkpoint = anchor ∨
      state.finalized_checkpoint.epoch + 1 ≤
        get_current_store_epoch cfg recorded := by
    rcases huf' with hanchor | hlag
    · exact Or.inl (hufcEq.symm.trans hanchor)
    · rw [← hufcEq]
      exact Or.inr (hlag.trans hblock)
  have hpulled : AcceptedFinalizationLagAt cfg anchor pulled :=
    AcceptedFinalizationLagAt.update_unrealized_checkpoints
      (cfg := cfg) recorded state.current_justified_checkpoint
        state.finalized_checkpoint hrecorded hufCurrent
  have hpulledBlocks : pulled.blocks = store.blocks := by
    exact (FastConfirmation.Spec.update_unrealized_checkpoints_sameBlocks
      recorded state.current_justified_checkpoint
        state.finalized_checkpoint).2.1.symm.trans rfl
  have hpulledCurrent : get_current_store_epoch cfg pulled =
      get_current_store_epoch cfg store := by
    simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg)
      (get_current_slot_congr cfg
        (FastConfirmation.Spec.update_unrealized_checkpoints_time recorded
          state.current_justified_checkpoint state.finalized_checkpoint)
        (FastConfirmation.Spec.update_unrealized_checkpoints_genesis_time recorded
          state.current_justified_checkpoint state.finalized_checkpoint))
  change AcceptedFinalizationLagAt cfg anchor
    (if compute_epoch_at_slot cfg (pulled.blocks r).slot <
        get_current_store_epoch cfg pulled then
      FastConfirmation.Spec.update_checkpoints pulled
        state.current_justified_checkpoint state.finalized_checkpoint
    else pulled)
  split_ifs with hold
  · apply AcceptedFinalizationLagAt.update_checkpoints (cfg := cfg)
    · exact hpulled
    · rcases huf' with hanchor | hlag
      · exact Or.inl (hufcEq.symm.trans hanchor)
      · right
        have hold' : get_block_epoch cfg store r <
            get_current_store_epoch cfg store := by
          simpa only [get_block_epoch, hpulledBlocks, hpulledCurrent] using hold
        have htwo := oneEpochLag_becomes_two_of_strict
          (a := ufc.epoch)
          (b := get_block_epoch cfg store r)
          (c := get_current_store_epoch cfg store) hlag hold'
        have hepoch : ufc.epoch = state.finalized_checkpoint.epoch :=
          congrArg Checkpoint.epoch hufcEq
        rw [hpulledCurrent, ← hepoch]
        exact htwo
  · exact hpulled

end AcceptedFinalizationLagAt

/-- Successful `on_block` exposes the handler's not-in-the-future gate. -/
private theorem SuccessfulScheduledBlockImport.blockEpoch_le_current
    (t : E.SuccessfulScheduledBlockImport cfg ext)
    (hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots) :
    compute_epoch_at_slot cfg t.signedBlock.message.slot ≤
      get_current_store_epoch cfg (t.atPrefix.store cfg ext) := by
  have hh := t.accepted
  simp only [FastConfirmation.Spec.on_block, if_neg hfresh] at hh
  split_ifs at hh <;> try cases hh
  apply ce_mono cfg
  simp_all

/-- Handler-local block preservation once the realized and pulled-up timing
facts have been supplied for this concrete transition output. -/
private theorem AcceptedFinalizationLagAt.on_block_of_delays
    {anchor : Checkpoint Root} {store store' : Store Root}
    {sb : SignedBeaconBlock Root} {post : BeaconState Root}
    (hst : ext.state_transition (store.block_states sb.message.parent_root) sb =
      some post)
    (hgf : post.finalized_checkpoint = anchor ∨
      post.finalized_checkpoint.epoch + 2 ≤
        compute_epoch_at_slot cfg sb.message.slot)
    (hguf :
      (ext.process_justification_and_finalization post).finalized_checkpoint =
          anchor ∨
        (ext.process_justification_and_finalization post
          ).finalized_checkpoint.epoch + 1 ≤
          compute_epoch_at_slot cfg sb.message.slot)
    (hblock : compute_epoch_at_slot cfg sb.message.slot ≤
      get_current_store_epoch cfg store)
    (h : AcceptedFinalizationLagAt cfg anchor store)
    (hh : FastConfirmation.Spec.on_block cfg ext store sb = some store') :
    AcceptedFinalizationLagAt cfg anchor store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · simp only [FastConfirmation.Spec.on_block, if_pos hknown] at hh
    cases hh
    exact h
  · simp only [FastConfirmation.Spec.on_block, if_neg hknown] at hh
    split_ifs at hh <;> try cases hh
    rw [hst] at hh
    let inserted : Store Root :=
      { store with
        block_roots := store.block_roots ++ [sb.root]
        blocks := Function.update store.blocks sb.root sb.message
        block_states := Function.update store.block_states sb.root post
        payload_timeliness_vote := Function.update store.payload_timeliness_vote
          sb.root (some (List.replicate cfg.ptc_size none))
        payload_data_availability_vote := Function.update store.payload_data_availability_vote
          sb.root (some (List.replicate cfg.ptc_size none)) }
    change (match notify_ptc_messages cfg ext inserted post sb.message.payload_attestations with
      | none => none
      | some notified => some (FastConfirmation.Spec.compute_pulled_up_tip cfg ext
          (FastConfirmation.Spec.update_checkpoints
            (FastConfirmation.Spec.update_proposer_boost_root cfg
              (FastConfirmation.Spec.record_block_timeliness cfg notified sb.root)
              (get_head cfg store).root sb.root)
            post.current_justified_checkpoint post.finalized_checkpoint) sb.root)) =
      some store' at hh
    cases hn : notify_ptc_messages cfg ext inserted post sb.message.payload_attestations with
    | none => rw [hn] at hh; cases hh
    | some notified =>
      rw [hn] at hh
      cases hh
      have hf : PayloadFrame inserted notified := notify_ptc_messages_frame cfg ext hn
      let added := notified
      let staged := FastConfirmation.Spec.record_block_timeliness cfg added
        sb.root
      let boosted := FastConfirmation.Spec.update_proposer_boost_root cfg staged
        (get_head cfg store).root sb.root
      let realized := FastConfirmation.Spec.update_checkpoints boosted
        post.current_justified_checkpoint post.finalized_checkpoint
      suffices hresult : AcceptedFinalizationLagAt cfg anchor
          (FastConfirmation.Spec.compute_pulled_up_tip cfg ext realized
            sb.root) by
        exact hresult
      have hadded : AcceptedFinalizationLagAt cfg anchor added :=
        AcceptedFinalizationLagAt.of_eq (cfg := cfg) h hf.time hf.genesis_time
          hf.finalized_checkpoint hf.unrealized_finalized_checkpoint
      have hstaged : AcceptedFinalizationLagAt cfg anchor staged :=
        AcceptedFinalizationLagAt.record_block_timeliness (cfg := cfg) added
          sb.root hadded
      have hboosted : AcceptedFinalizationLagAt cfg anchor boosted :=
        AcceptedFinalizationLagAt.update_proposer_boost_root (cfg := cfg) staged
          (get_head cfg store).root sb.root hstaged
      have hgfCurrent : post.finalized_checkpoint = anchor ∨
          post.finalized_checkpoint.epoch + 2 ≤
            get_current_store_epoch cfg boosted := by
        rcases hgf with hanchor | hlag
        · exact Or.inl hanchor
        · right
          have hcurrent : get_current_store_epoch cfg boosted =
              get_current_store_epoch cfg store := by
            simp only [boosted, staged, added, hf.time, hf.genesis_time, inserted,
              FastConfirmation.Spec.update_proposer_boost_root,
              FastConfirmation.Spec.record_block_timeliness,
              get_current_store_epoch, get_current_slot, get_slots_since_genesis]
            split_ifs <;> simp only [hf.time, hf.genesis_time, inserted]
          rw [hcurrent]
          exact hlag.trans hblock
      have hrealized : AcceptedFinalizationLagAt cfg anchor realized :=
        AcceptedFinalizationLagAt.update_checkpoints (cfg := cfg) boosted
          post.current_justified_checkpoint post.finalized_checkpoint
          hboosted hgfCurrent
      have hrealizedBlock : get_block_epoch cfg realized sb.root =
          compute_epoch_at_slot cfg sb.message.slot := by
        simp only [get_block_epoch, realized, boosted, staged, added, hf.blocks, inserted,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> simp only [hf.blocks, inserted, Function.update_self]
      have hrealizedState : realized.block_states sb.root = post := by
        simp only [realized, boosted, staged, added, hf.block_states, inserted,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness]
        split_ifs <;> simp only [hf.block_states, inserted, Function.update_self]
      have hrealizedCurrent : get_current_store_epoch cfg realized =
          get_current_store_epoch cfg store := by
        simp only [realized, boosted, staged, added, hf.time, hf.genesis_time, inserted,
          FastConfirmation.Spec.update_checkpoints,
          FastConfirmation.Spec.update_proposer_boost_root,
          FastConfirmation.Spec.record_block_timeliness,
          get_current_store_epoch, get_current_slot, get_slots_since_genesis]
        split_ifs <;> simp only [hf.time, hf.genesis_time, inserted]
      apply AcceptedFinalizationLagAt.compute_pulled_up_tip
        (cfg := cfg) (ext := ext) realized
        sb.root hrealized
      · rw [hrealizedState, hrealizedBlock]
        exact hguf
      · rw [hrealizedBlock, hrealizedCurrent]
        exact hblock

/-- One accepted block preserves the paired lag invariant. -/
theorem AcceptedFinalizationLagAt.acceptedBlockTransition
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (t : E.SuccessfulScheduledBlockImport cfg ext)
    (h : AcceptedFinalizationLagAt cfg B.anchor
      (t.atPrefix.store cfg ext)) :
    AcceptedFinalizationLagAt cfg B.anchor t.postStore := by
  by_cases hfresh : t.signedBlock.root ∉
      (t.atPrefix.store cfg ext).block_roots
  · obtain ⟨post, hst, hinserted⟩ :=
      Execution.SuccessfulScheduledBlockImport.on_block_inserted_state_fresh
        cfg ext hfresh t.accepted
    apply AcceptedFinalizationLagAt.on_block_of_delays
      (cfg := cfg) (ext := ext) hst
    · simpa only [hinserted] using hDelay t
    · simpa only [hinserted] using
        E.acceptedPulledUpFinalized_succ_le_blockEpoch cfg ext B hT t
    · exact SuccessfulScheduledBlockImport.blockEpoch_le_current
        cfg ext E t hfresh
    · exact h
    · exact t.accepted
  · have hknown : t.signedBlock.root ∈
        (t.atPrefix.store cfg ext).block_roots :=
      Classical.byContradiction hfresh
    have hsame : t.postStore = t.atPrefix.store cfg ext := by
      exact (Option.some.inj (by
        simpa only [on_block, if_pos hknown] using t.accepted)).symm
    rw [hsame]
    exact h

/-! ## One-second tick preservation -/

/-- A slot whose successor is an epoch boundary advances the epoch. -/
private theorem epoch_lt_of_slots_since_succ_eq_zero (s : Slot)
    (hzero : compute_slots_since_epoch_start cfg (s + 1) = 0) :
    compute_epoch_at_slot cfg s < compute_epoch_at_slot cfg (s + 1) := by
  by_contra hnot
  have hmono : compute_epoch_at_slot cfg s ≤
      compute_epoch_at_slot cfg (s + 1) :=
    ce_mono cfg (Nat.le_succ s)
  have heq : compute_epoch_at_slot cfg (s + 1) =
      compute_epoch_at_slot cfg s :=
    Nat.le_antisymm (Nat.le_of_not_gt hnot) hmono
  have hboundaryLe : s + 1 ≤
      compute_start_slot_at_epoch cfg
        (compute_epoch_at_slot cfg (s + 1)) :=
    Nat.sub_eq_zero_iff_le.mp hzero
  rw [heq] at hboundaryLe
  have hfloor := Nat.div_mul_le_self s cfg.slots_per_epoch
  have himpossible : s + 1 ≤ s := by
    exact hboundaryLe.trans (by
      simpa only [compute_start_slot_at_epoch, compute_epoch_at_slot] using hfloor)
  exact (Nat.not_succ_le_self s) himpossible

/-- If the final clock write remains in the same slot, `on_tick_per_slot`
does not pull up checkpoints. -/
theorem AcceptedFinalizationLagAt.after_on_tick_per_slot_same
    {anchor : Checkpoint Root} (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store)
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  simp only [FastConfirmation.Spec.on_tick_per_slot]
  rw [hcurrent]
  simp only [gt_iff_lt, lt_self_iff_false, ↓reduceIte, false_and]
  apply AcceptedFinalizationLagAt.of_current_eq (cfg := cfg) h
  · simp only [get_current_store_epoch]
    exact congrArg (compute_epoch_at_slot cfg) hcurrent
  · rfl
  · rfl

/-- Crossing one slot preserves the pair.  At an epoch boundary the old
unrealized finalized checkpoint is offered to the realized maximum; its
one-epoch lag becomes a two-epoch lag because the epoch strictly advanced. -/
theorem AcceptedFinalizationLagAt.after_on_tick_per_slot_next
    {anchor : Checkpoint Root} (store : Store Root) (time : ℕ)
    (hcurrent : get_current_slot cfg { store with time := time } =
      get_current_slot cfg store + 1)
    (h : AcceptedFinalizationLagAt cfg anchor store) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.on_tick_per_slot cfg store time) := by
  let timed : Store Root := { store with time := time }
  let reset : Store Root :=
    if get_current_slot cfg timed > get_current_slot cfg store then
      { timed with proposer_boost_root := (default : Root) }
    else timed
  have hresetSlot : get_current_slot cfg reset = get_current_slot cfg timed := by
    simp only [reset]
    split_ifs <;> rfl
  have hresetFinalized : reset.finalized_checkpoint =
      store.finalized_checkpoint := by
    simp only [reset, timed]
    split_ifs <;> rfl
  have hresetUnrealized : reset.unrealized_finalized_checkpoint =
      store.unrealized_finalized_checkpoint := by
    simp only [reset, timed]
    split_ifs <;> rfl
  have hcurrentLe : get_current_store_epoch cfg store ≤
      get_current_store_epoch cfg reset := by
    apply ce_mono cfg
    rw [hresetSlot, hcurrent]
    exact Nat.le_succ _
  have hbase : AcceptedFinalizationLagAt cfg anchor reset := by
    constructor
    · rw [hresetFinalized]
      rcases h.realized with hanchor | hlag
      · exact Or.inl hanchor
      · exact Or.inr (hlag.trans hcurrentLe)
    · rw [hresetUnrealized]
      rcases h.unrealized with hanchor | hlag
      · exact Or.inl hanchor
      · exact Or.inr (hlag.trans hcurrentLe)
  change AcceptedFinalizationLagAt cfg anchor
    (if get_current_slot cfg timed > get_current_slot cfg store ∧
        compute_slots_since_epoch_start cfg (get_current_slot cfg timed) = 0 then
      FastConfirmation.Spec.update_checkpoints reset
        reset.unrealized_justified_checkpoint
        reset.unrealized_finalized_checkpoint
    else reset)
  split_ifs with hpull
  · apply AcceptedFinalizationLagAt.update_checkpoints (cfg := cfg)
    · exact hbase
    · have hzero : compute_slots_since_epoch_start cfg
          (get_current_slot cfg store + 1) = 0 := by
        rw [← hcurrent]
        exact hpull.2
      have hepochStrict : get_current_store_epoch cfg store <
          get_current_store_epoch cfg reset := by
        have htimedSlot : get_current_slot cfg timed =
            get_current_slot cfg store + 1 := by
          simpa only [timed] using hcurrent
        simp only [get_current_store_epoch]
        rw [hresetSlot, htimedSlot]
        exact epoch_lt_of_slots_since_succ_eq_zero
          (cfg := cfg) (get_current_slot cfg store) hzero
      rw [hresetUnrealized]
      rcases h.unrealized with hanchor | hlag
      · exact Or.inl hanchor
      · exact Or.inr
          (oneEpochLag_becomes_two_of_strict hlag hepochStrict)
  · exact hbase

/-- The execution clock advances by at most one slot per relative second. -/
private theorem finalizationLag_slot_at_succ_le
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (n : ℕ) :
    E.slot_at cfg (n + 1) ≤ E.slot_at cfg n + 1 := by
  have hdivKeep := hdiv
  obtain ⟨secondsPerSlot, hduration⟩ := hdivKeep
  have hsecondsPos : 0 < secondsPerSlot := by
    have hdurationPos := cfg.slot_duration_ms_pos
    rw [hduration] at hdurationPos
    omega
  have hdenPos : 0 < cfg.slot_duration_ms / 1000 := by
    rw [hduration, Nat.mul_div_cancel_left secondsPerSlot
      (by omega : (0 : ℕ) < 1000)]
    exact hsecondsPos
  rw [E.slot_at_eq cfg hdiv, E.slot_at_eq cfg hdiv]
  have hnum : E.genesis_store.time + (n + 1) -
        E.genesis_store.genesis_time =
      (E.genesis_store.time + n - E.genesis_store.genesis_time) + 1 := by
    omega
  rw [hnum]
  let a := E.genesis_store.time + n - E.genesis_store.genesis_time
  calc
    (a + 1) / (cfg.slot_duration_ms / 1000) ≤
        (a + cfg.slot_duration_ms / 1000) /
          (cfg.slot_duration_ms / 1000) :=
      Nat.div_le_div_right (by omega)
    _ = a / (cfg.slot_duration_ms / 1000) + 1 :=
      Nat.add_div_right a hdenPos

/-- The exact execution tick preserves the paired invariant. -/
private theorem finalizationLag_after_execution_tick
    {anchor : Checkpoint Root}
    (hdiv : 1000 ∣ cfg.slot_duration_ms)
    (hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time)
    (w : ValidatorIndex) (n : ℕ)
    (h : AcceptedFinalizationLagAt cfg anchor (E.store cfg ext w n)) :
    AcceptedFinalizationLagAt cfg anchor
      (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
        (E.time_at (n + 1))) := by
  let store := E.store cfg ext w n
  let s := E.slot_at cfg n
  let next := E.slot_at cfg (n + 1)
  have hs : get_current_slot cfg store = s := by
    simpa only [store, s] using E.store_current_slot cfg ext w n
  have hsnext : s ≤ next := E.slot_at_mono cfg (Nat.le_succ n)
  have hnextLe : next ≤ s + 1 :=
    E.finalizationLag_slot_at_succ_le cfg hdiv hgenTime n
  have htickSlot :
      (E.time_at (n + 1) - store.genesis_time) * 1000 /
          cfg.slot_duration_ms = next := by
    simp only [store, next, Execution.slot_at, GENESIS_SLOT, Nat.zero_add,
      E.store_genesis_time cfg ext w n]
  have htargetCurrent : get_current_slot cfg
      { store with time := E.time_at (n + 1) } = next := by
    simp only [get_current_slot, get_slots_since_genesis, GENESIS_SLOT,
      Nat.zero_add]
    exact htickSlot
  have hcases : next = s ∨ next = s + 1 := by
    by_cases heq : next = s
    · exact Or.inl heq
    · right
      exact Nat.le_antisymm hnextLe
        (Nat.succ_le_of_lt (lt_of_le_of_ne hsnext (Ne.symm heq)))
  simp only [FastConfirmation.Spec.on_tick]
  rw [htickSlot]
  rcases hcases with hsame | hnext
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1) store =
        store := by
      apply FFGGlobalCheckpointLedger.on_tick_aux_eq_of_not_lt
      rw [hsame, ← hs]
      exact Nat.lt_irrefl _
    rw [haux]
    apply AcceptedFinalizationLagAt.after_on_tick_per_slot_same
      (cfg := cfg) store (E.time_at (n + 1))
    · rw [htargetCurrent, hsame, ← hs]
    · exact h
  · have haux : FastConfirmation.Spec.on_tick_aux cfg next (next + 1) store =
        FastConfirmation.Spec.on_tick_per_slot cfg store
          (store.genesis_time + (s + 1) * cfg.slot_duration_ms / 1000) := by
      rw [hnext]
      exact FFGGlobalCheckpointLedger.on_tick_aux_one_slot store s hs hdiv
    rw [haux]
    let boundaryTime := store.genesis_time +
      (s + 1) * cfg.slot_duration_ms / 1000
    let stepped := FastConfirmation.Spec.on_tick_per_slot cfg store boundaryTime
    have hboundaryCurrent : get_current_slot cfg
        { store with time := boundaryTime } =
          get_current_slot cfg store + 1 := by
      simpa only [boundaryTime, hs] using
        FFGGlobalCheckpointLedger.current_slot_at_next_boundary
          (cfg := cfg) hdiv store
    have hstepped : AcceptedFinalizationLagAt cfg anchor stepped :=
      AcceptedFinalizationLagAt.after_on_tick_per_slot_next
        (cfg := cfg) store boundaryTime hboundaryCurrent h
    have hsteppedCurrent : get_current_slot cfg stepped = next := by
      rw [FFGGlobalCheckpointLedger.on_tick_per_slot_current_slot,
        hboundaryCurrent, hs, ← hnext]
    have hfinalCurrent : get_current_slot cfg
        { stepped with time := E.time_at (n + 1) } =
          get_current_slot cfg stepped := by
      calc
        get_current_slot cfg { stepped with time := E.time_at (n + 1) } =
            get_current_slot cfg { store with time := E.time_at (n + 1) } := by
          have hg : stepped.genesis_time = store.genesis_time :=
            (FastConfirmation.Spec.on_tick_per_slot_storeLE
              cfg store boundaryTime).2.1.symm
          exact get_current_slot_congr cfg
            (s := { stepped with time := E.time_at (n + 1) })
            (t := { store with time := E.time_at (n + 1) }) rfl hg
        _ = next := htargetCurrent
        _ = get_current_slot cfg stepped := hsteppedCurrent.symm
    exact AcceptedFinalizationLagAt.after_on_tick_per_slot_same
      (cfg := cfg) stepped (E.time_at (n + 1)) hfinalCurrent hstepped

/-- Store-level invariant generated by the realized-transition delay,
eager-finalization certificate timing, and the concrete tick/late-block
handlers.  This is the exact consumer boundary for the candidate-history
recurrence; it is displayed separately so the eventual handler induction is
not confused with the primitive base-consensus law above. -/
def CausalRealizedFinalizationLag
    (B : ScheduledFFGInterpretation cfg ext E) : Prop :=
  ∀ {store : Store Root}, E.ScheduledPrefixStore cfg ext store →
    store.finalized_checkpoint = B.anchor ∨
      store.finalized_checkpoint.epoch + 2 ≤
        get_current_store_epoch cfg store

/-! ## Exact-prefix generation of the causal invariant -/

private theorem genesisAcceptedFinalizationLagAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint) :
    AcceptedFinalizationLagAt cfg B.anchor E.genesis_store := by
  obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
  rw [hgenEq] at hanchor ⊢
  constructor <;> apply Or.inl <;>
    simpa only [get_forkchoice_store] using hanchor.symm

private theorem acceptedFinalizationLagAt_take
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (w : ValidatorIndex) (n : ℕ)
    (hbase : AcceptedFinalizationLagAt cfg B.anchor
      (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) :
    ∀ k : ℕ,
      k ≤ (E.schedule w (n + 1)).length →
      AcceptedFinalizationLagAt cfg B.anchor
        (((E.schedule w (n + 1)).take k).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (on_tick cfg (E.store cfg ext w n) (E.time_at (n + 1)))) := by
  intro k hk
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
      have hklt : k < (E.schedule w (n + 1)).length := by omega
      have hkle : k ≤ (E.schedule w (n + 1)).length := Nat.le_of_lt hklt
      let p : E.ScheduledEventPrefix :=
        { node := w
          previousSecond := n
          processedCount := k
          count_le := hkle }
      have hp : AcceptedFinalizationLagAt cfg B.anchor (p.store cfg ext) :=
        ih hkle
      let nextEvent : Event Root :=
        (E.schedule w (n + 1)).get ⟨k, hklt⟩
      have hsucc :
          (p.successor hklt).store cfg ext =
            (apply_event cfg ext (p.store cfg ext) nextEvent).getD
              (p.store cfg ext) := by
        simpa [nextEvent] using
          p.successor_store (cfg := cfg) (ext := ext) hklt
      change AcceptedFinalizationLagAt cfg B.anchor
        ((p.successor hklt).store cfg ext)
      rw [hsucc]
      cases heq : apply_event cfg ext (p.store cfg ext) nextEvent with
      | none => simpa using hp
      | some store' =>
        simp only [Option.getD_some]
        cases hevent : nextEvent with
        | block sb =>
            let t : E.SuccessfulScheduledBlockImport cfg ext :=
              { atPrefix := p
                signedBlock := sb
                event_at := by
                  have hget :
                      (E.schedule w (n + 1))[k]? = some nextEvent := by
                    simp [nextEvent, List.getElem?_eq_getElem hklt]
                  rw [hget, hevent]
                postStore := store'
                accepted := by
                  simpa [apply_event, hevent] using heq }
            exact AcceptedFinalizationLagAt.acceptedBlockTransition
              (cfg := cfg) (ext := ext) (E := E) B hT hDelay t hp
        | attestation a fromBlock =>
            exact AcceptedFinalizationLagAt.on_attestation
              (cfg := cfg) (ext := ext) hp
              (by simpa [apply_event, hevent] using heq)
        | attester_slashing sl =>
            exact AcceptedFinalizationLagAt.on_attester_slashing
              (cfg := cfg) (ext := ext) hp
              (by simpa [apply_event, hevent] using heq)
        | execution_payload_envelope envelope observation =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_execution_payload_envelope_frame ext (by simpa [apply_event, hevent] using heq)
            exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) hp hf.time hf.genesis_time
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint
        | payload_attestation_message message isFromBlock =>
            have hf : PayloadFrame (p.store cfg ext) store' :=
              on_payload_attestation_message_frame cfg ext (by simpa [apply_event, hevent] using heq)
            exact AcceptedFinalizationLagAt.of_eq (cfg := cfg) hp hf.time hf.genesis_time
              hf.finalized_checkpoint hf.unrealized_finalized_checkpoint

/-- The paired finalization-lag invariant at every ordinary execution
boundary. -/
theorem acceptedFinalizationLagAt
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B)
    (w : ValidatorIndex) (n : ℕ) :
    AcceptedFinalizationLagAt cfg B.anchor (E.store cfg ext w n) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  induction n with
  | zero =>
      exact E.genesisAcceptedFinalizationLagAt cfg ext B hT hanchor
  | succ n ih =>
      change AcceptedFinalizationLagAt cfg B.anchor
        ((E.schedule w (n + 1)).foldl
          (fun st event => (apply_event cfg ext st event).getD st)
          (FastConfirmation.Spec.on_tick cfg (E.store cfg ext w n)
            (E.time_at (n + 1))))
      simpa only [List.take_length] using
        E.acceptedFinalizationLagAt_take cfg ext B hT hDelay w n
          (E.finalizationLag_after_execution_tick cfg ext
            hT.whole_seconds hgenTime w n ih)
          (E.schedule w (n + 1)).length le_rfl

/-- The same invariant at an arbitrary exact in-second scheduled prefix. -/
theorem ScheduledEventPrefix.acceptedFinalizationLagAt
    (p : E.ScheduledEventPrefix)
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B) :
    AcceptedFinalizationLagAt cfg B.anchor (p.store cfg ext) := by
  have hgenTime : E.genesis_store.genesis_time ≤ E.genesis_store.time := by
    obtain ⟨ast, ablk, hgenEq, _hslot, _hparent⟩ := hT.genesis_structure
    rw [hgenEq]
    simp only [get_forkchoice_store]
    omega
  apply E.acceptedFinalizationLagAt_take cfg ext B hT hDelay
    p.node p.previousSecond
  · exact E.finalizationLag_after_execution_tick cfg ext
      hT.whole_seconds hgenTime p.node p.previousSecond
      (E.acceptedFinalizationLagAt cfg ext B hT hanchor
        hDelay p.node p.previousSecond)
  · exact p.count_le

/-- Paired lag at every exact causal store. -/
theorem ScheduledPrefixStore.acceptedFinalizationLagAt
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B) :
    AcceptedFinalizationLagAt cfg B.anchor store := by
  cases hstore with
  | genesis =>
      exact E.genesisAcceptedFinalizationLagAt cfg ext B hT hanchor
  | scheduledPrefix p =>
      exact p.acceptedFinalizationLagAt
        (cfg := cfg) (ext := ext) (E := E) B hT hanchor hDelay

/-- Main producer: exact accepted block delay generates the realized
two-epoch lag at every causal store.  The GUF half is derived from accepted
certificate inclusion; no second finalization timing premise is exposed. -/
theorem causalRealizedFinalizationLag_of_acceptedDelay
    (B : ScheduledFFGInterpretation cfg ext E)
    (hT : E.ScheduledExecutionPremises cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hDelay : E.ImportedBlockFinalizationLag cfg ext B) :
    E.CausalRealizedFinalizationLag cfg ext B := by
  intro store hstore
  exact (hstore.acceptedFinalizationLagAt
    (cfg := cfg) (ext := ext) (E := E) B hT hanchor hDelay).realized

/-- The store-level lag gives the exact checkpoint-age statement without
truncated subtraction. -/
theorem finalizedCheckpoint_twoEpochLag_of_causalLag
    {B : ScheduledFFGInterpretation cfg ext E}
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    (hne : store.finalized_checkpoint ≠ B.anchor) :
    store.finalized_checkpoint.epoch + 2 ≤
      get_current_store_epoch cfg store := by
  rcases hLag hstore with hanchor | hlag
  · exact False.elim (hne hanchor)
  · exact hlag

/-- Together with existing reset realization, the same law makes the
finalized reset root fail the final selector's recency guard.  This is the
precise fact needed to eliminate the finalized-reset arm in the paper-L22
candidate-history step. -/
theorem finalizedResetRoot_stale_of_causalLag
    {B : ScheduledFFGInterpretation cfg ext E}
    (hLag : E.CausalRealizedFinalizationLag cfg ext B)
    {store : Store Root} (hstore : E.ScheduledPrefixStore cfg ext store)
    (hrealized : E.ResetCheckpointRealizedAt cfg B.anchor store
      store.finalized_checkpoint)
    (hne : store.finalized_checkpoint ≠ B.anchor) :
    get_block_epoch cfg store store.finalized_checkpoint.root + 1 <
      get_current_store_epoch cfg store := by
  have hscaled :
      get_block_epoch cfg store store.finalized_checkpoint.root *
          cfg.slots_per_epoch ≤
        store.finalized_checkpoint.epoch * cfg.slots_per_epoch := by
    simpa only [compute_start_slot_at_epoch] using
      (start_slot_at_block_epoch_le cfg store
        store.finalized_checkpoint.root).trans
          hrealized.root_slot_le_boundary
  have hrootLe :
      get_block_epoch cfg store store.finalized_checkpoint.root ≤
        store.finalized_checkpoint.epoch :=
    Nat.le_of_mul_le_mul_right hscaled cfg.slots_per_epoch_pos
  have hfieldLag := E.finalizedCheckpoint_twoEpochLag_of_causalLag
    cfg ext hLag hstore hne
  have hcombined :
      get_block_epoch cfg store store.finalized_checkpoint.root + 2 ≤
        get_current_store_epoch cfg store :=
    (Nat.add_le_add_right hrootLe 2).trans hfieldLag
  apply Nat.lt_of_succ_le
  rw [show Nat.succ
      (get_block_epoch cfg store store.finalized_checkpoint.root + 1) =
        get_block_epoch cfg store store.finalized_checkpoint.root + 2 by
      omega]
  exact hcombined

end Execution

/-! ## Concrete abstraction counterpatterns -/

namespace AcceptedFinalizationLagCounterpattern

abbrev CounterRoot := Bool

def anchor : Checkpoint CounterRoot :=
  { epoch := 0, root := false }






end AcceptedFinalizationLagCounterpattern


end FastConfirmation.Spec

end
