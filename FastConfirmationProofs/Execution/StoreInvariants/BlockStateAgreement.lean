module
public import FastConfirmationProofs.Handlers.BlockTransitionProvenance
public import FastConfirmationProofs.ModelFacts

@[expose] public section

/-! # Block-state agreement

An accepted block's state is the result of the deterministic `state_transition`
on its parent's state. The trusted genesis states and every previously known
state persist through the execution. These facts give state agreement for a
root known in two causal stores of one well-formed execution. -/

namespace FastConfirmation.Spec

open Execution

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- A store extension preserves the state of every old known block. -/
private def BlockStateLE (old new : Store Root) : Prop :=
  ∀ r ∈ old.block_roots,
    r ∈ new.block_roots ∧ new.block_states r = old.block_states r

private theorem BlockStateLE.refl (s : Store Root) : BlockStateLE s s :=
  fun _ hr => ⟨hr, rfl⟩

private theorem BlockStateLE.trans {a b c : Store Root}
    (hab : BlockStateLE a b) (hbc : BlockStateLE b c) : BlockStateLE a c := by
  intro r hr
  obtain ⟨hrb, heqB⟩ := hab r hr
  obtain ⟨hrc, heqC⟩ := hbc r hrb
  exact ⟨hrc, heqC.trans heqB⟩

private theorem BlockStateLE.of_sameBlocks {a b : Store Root}
    (h : SameBlocks a b) : BlockStateLE a b := by
  intro r hr
  exact ⟨h.1 ▸ hr, congrFun h.2.2.symm r⟩

private theorem on_block_blockStateLE {store store' : Store Root}
    {sb : SignedBeaconBlock Root}
    (h : on_block cfg ext store sb = some store') : BlockStateLE store store' := by
  intro r hr
  have hroot := (on_block_storeLE cfg ext h).1 hr
  by_cases hsame : r = sb.root
  · subst r
    have hknown : sb.root ∈ store.block_roots := hr
    simp [on_block, hknown] at h
    cases h
    exact ⟨hr, rfl⟩
  · exact ⟨hroot, on_block_other_root_block_states h hsame⟩

private theorem apply_event_blockStateLE (store : Store Root) (event : Event Root) :
    BlockStateLE store ((apply_event cfg ext store event).getD store) := by
  cases h : apply_event cfg ext store event with
  | none => exact BlockStateLE.refl store
  | some next =>
      cases event with
      | block sb => exact on_block_blockStateLE cfg ext h
      | attestation a fromBlock =>
          exact BlockStateLE.of_sameBlocks (on_attestation_sameBlocks cfg ext h)
      | attester_slashing slashing =>
          exact BlockStateLE.of_sameBlocks (on_attester_slashing_sameBlocks ext h)
      | execution_payload_envelope signed observation =>
          exact BlockStateLE.of_sameBlocks
            (on_execution_payload_envelope_frame ext h).sameBlocks
      | payload_attestation_message message fromBlock =>
          exact BlockStateLE.of_sameBlocks
            (on_payload_attestation_message_frame cfg ext h).sameBlocks

private theorem foldl_blockStateLE (events : List (Event Root)) (store : Store Root) :
    BlockStateLE store
      (events.foldl (fun s event => (apply_event cfg ext s event).getD s) store) := by
  induction events generalizing store with
  | nil => exact BlockStateLE.refl store
  | cons event rest ih =>
      exact (apply_event_blockStateLE cfg ext store event).trans (ih _)

private theorem Execution.store_blockStateLE_succ (E : Execution Root)
    (v : ValidatorIndex) (n : ℕ) :
    BlockStateLE (E.store cfg ext v n) (E.store cfg ext v (n + 1)) := by
  change BlockStateLE (E.store cfg ext v n)
    ((E.schedule v (n + 1)).foldl
      (fun s event => (apply_event cfg ext s event).getD s)
      (on_tick cfg (E.store cfg ext v n) (E.time_at (n + 1))))
  exact (BlockStateLE.of_sameBlocks
    (on_tick_sameBlocks cfg (E.store cfg ext v n) (E.time_at (n + 1)))).trans
    (foldl_blockStateLE cfg ext _ _)

private theorem Execution.store_blockStateLE (E : Execution Root)
    (v : ValidatorIndex) {n m : ℕ} (hnm : n ≤ m) :
    BlockStateLE (E.store cfg ext v n) (E.store cfg ext v m) := by
  induction m, hnm using Nat.le_induction with
  | base => exact BlockStateLE.refl _
  | succ m _ ih => exact ih.trans (E.store_blockStateLE_succ cfg ext v m)

private theorem Execution.causal_genesis_state (E : Execution Root)
    {store : Store Root} (hstore : E.CausalStore cfg ext store)
    {r : Root} (hr : r ∈ E.genesis_store.block_roots) :
    store.block_states r = E.genesis_store.block_states r := by
  cases hstore with
  | genesis => rfl
  | scheduledPrefix p =>
      unfold Execution.ScheduledEventPrefix.store
      have hzero := E.store_blockStateLE cfg ext p.node
        (Nat.zero_le p.previousSecond)
      have htick := BlockStateLE.of_sameBlocks
        (on_tick_sameBlocks cfg
          (E.store cfg ext p.node p.previousSecond)
          (E.time_at (p.previousSecond + 1)))
      have hfold := foldl_blockStateLE cfg ext
        ((E.schedule p.node (p.previousSecond + 1)).take p.processedCount)
        (on_tick cfg (E.store cfg ext p.node p.previousSecond)
          (E.time_at (p.previousSecond + 1)))
      exact ((hzero.trans htick).trans hfold r hr).2

private theorem Execution.CausalStore.blockProvenance_for_states
    {E : Execution Root} {store : Store Root}
    (hstore : E.CausalStore cfg ext store) : BlockProvenance E store := by
  cases hstore with
  | genesis => exact E.blockProvenance cfg ext 0 0
  | scheduledPrefix p =>
      unfold Execution.ScheduledEventPrefix.store
      exact blockProvenance_foldl cfg ext _ _
        (fun b hb => ⟨p.node, p.previousSecond + 1,
          List.mem_of_mem_take hb⟩)
        (on_tick_blockProvenance cfg _ _
          (E.blockProvenance cfg ext p.node p.previousSecond))

/-- A last-writer carrier exposes the transition output recorded at its root. -/
private theorem Execution.AcceptedBlockLastWriterCarrier.transition_output
    {E : Execution Root} {store : Store Root} {r : Root}
    (writer : AcceptedBlockLastWriterCarrier cfg ext E store r) :
    ∃ post : BeaconState Root,
      ext.state_transition
        ((writer.transition.atPrefix.store cfg ext).block_states
          writer.transition.signedBlock.message.parent_root)
        writer.transition.signedBlock = some post ∧
      store.block_states r = post := by
  obtain ⟨post, htransition, hpost⟩ :=
    Execution.AcceptedBlockTransition.on_block_inserted_state_fresh
      cfg ext writer.fresh writer.transition.accepted
  refine ⟨post, htransition, ?_⟩
  calc
    store.block_states r = writer.transition.postStore.block_states r :=
      writer.block_state_eq.symm
    _ = writer.transition.postStore.block_states writer.transition.signedBlock.root := by
      rw [writer.root_eq]
    _ = post := hpost

private theorem Execution.AcceptedBlockLastWriterCarrier.parent_known
    {E : Execution Root} {store : Store Root} {r : Root}
    (writer : AcceptedBlockLastWriterCarrier cfg ext E store r) :
    writer.transition.signedBlock.message.parent_root ∈
      (writer.transition.atPrefix.store cfg ext).block_roots := by
  by_contra hnot
  have hnone : on_block cfg ext (writer.transition.atPrefix.store cfg ext)
      writer.transition.signedBlock = none := by
    simp [on_block, writer.fresh, hnot]
  have haccepted := writer.transition.accepted
  rw [hnone] at haccepted
  cases haccepted

/-- Equal roots have equal block states in two causal stores. The induction
uses the parent's earlier slot; each accepted child state is a deterministic
`state_transition` result on that parent and the root-committed block. -/
theorem Execution.causal_block_states_agree (E : Execution Root)
    (hwf : WellFormedExecution E) (hec : BeaconExternalsPremises cfg ext E)
    {s t : Store Root} (hs : E.CausalStore cfg ext s)
    (ht : E.CausalStore cfg ext t) {r : Root}
    (hrs : r ∈ s.block_roots) (hrt : r ∈ t.block_roots) :
    s.block_states r = t.block_states r := by
  suffices h : ∀ k : ℕ, ∀ (s t : Store Root),
      E.CausalStore cfg ext s → E.CausalStore cfg ext t →
      ∀ r, r ∈ s.block_roots → r ∈ t.block_roots →
      (s.block_states r).slot ≤ k →
      s.block_states r = t.block_states r from
    h (s.block_states r).slot s t hs ht r hrs hrt le_rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro s t hs ht r hrs hrt hslot
      by_cases hgen : r ∈ E.genesis_store.block_roots
      · exact (E.causal_genesis_state cfg ext hs hgen).trans
          (E.causal_genesis_state cfg ext ht hgen).symm
      · obtain ⟨writerS⟩ :=
          hs.acceptedBlockLastWriterProvenance r hrs hgen
        obtain ⟨writerT⟩ :=
          ht.acceptedBlockLastWriterProvenance r hrt hgen
        obtain ⟨postS, htransS, hstateS⟩ :=
          writerS.transition_output cfg ext
        obtain ⟨postT, htransT, hstateT⟩ :=
          writerT.transition_output cfg ext
        have hmessage : writerS.transition.signedBlock.message =
            writerT.transition.signedBlock.message := by
          calc
            writerS.transition.signedBlock.message = s.blocks r := writerS.message_eq
            _ = t.blocks r := hwf.blocks_agree
              (hs.blockProvenance_for_states cfg ext)
              (ht.blockProvenance_for_states cfg ext) hrs hrt
            _ = writerT.transition.signedBlock.message := writerT.message_eq.symm
        have hroot : writerS.transition.signedBlock.root =
            writerT.transition.signedBlock.root :=
          writerS.root_eq.trans writerT.root_eq.symm
        have hblock : writerS.transition.signedBlock =
            writerT.transition.signedBlock := by
          cases hsbS : writerS.transition.signedBlock with
          | mk msg root =>
              cases hsbT : writerT.transition.signedBlock with
              | mk msg' root' =>
                  simp only [hsbS, hsbT] at hmessage hroot ⊢
                  cases hmessage
                  cases hroot
                  rfl
        have hparentRoot : writerS.transition.signedBlock.message.parent_root =
            writerT.transition.signedBlock.message.parent_root :=
          congrArg (fun b => b.message.parent_root) hblock
        have hparentS := writerS.parent_known cfg ext
        have hparentT := writerT.parent_known cfg ext
        rw [← hparentRoot] at hparentT
        have hpreSlot :
            ((writerS.transition.atPrefix.store cfg ext).block_states
              writerS.transition.signedBlock.message.parent_root).slot <
            writerS.transition.signedBlock.message.slot :=
          hec.state_transition_pre_slot_lt _ _ _ htransS
        have hpostSlot : postS.slot = writerS.transition.signedBlock.message.slot :=
          hec.state_transition_slot _ _ _ htransS
        have hparentLt :
            ((writerS.transition.atPrefix.store cfg ext).block_states
              writerS.transition.signedBlock.message.parent_root).slot < k := by
          have hprePost :
              ((writerS.transition.atPrefix.store cfg ext).block_states
                writerS.transition.signedBlock.message.parent_root).slot < postS.slot := by
            rwa [hpostSlot]
          have hpostBound : postS.slot ≤ k := by
            rw [← hstateS]
            exact hslot
          exact lt_of_lt_of_le hprePost hpostBound
        have hparentStates := ih _ hparentLt
          (writerS.transition.atPrefix.store cfg ext)
          (writerT.transition.atPrefix.store cfg ext)
          (.scheduledPrefix writerS.transition.atPrefix)
          (.scheduledPrefix writerT.transition.atPrefix)
          writerS.transition.signedBlock.message.parent_root
          hparentS hparentT le_rfl
        have hpostEq : postS = postT := by
          rw [hparentStates, hblock] at htransS
          exact Option.some.inj (htransS.symm.trans htransT)
        exact hstateS.trans (hpostEq.trans hstateT.symm)

end FastConfirmation.Spec

end
