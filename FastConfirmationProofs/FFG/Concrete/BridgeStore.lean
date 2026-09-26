module
public import FastConfirmationProofs.FFG.Concrete.BridgeLaws
public import FastConfirmationProofs.FFG.SourceHistory.FFGSourceCoherence
public import FastConfirmationProofs.Handlers.BlockTransitionProvenance

@[expose] public section

/-! Proves the store bridge for executions run with `ConcreteBridge.ext` from
the setup genesis. Every block known in a node store holds the projection of
its committed concrete state. That state is reachable from genesis and within
the fixed scope. Its header root is the block root, and its slot is the block
slot. A non-genesis block opens to a wire block with a matching message, and
its state is the concrete `state_transition` of its parent's committed state.
Handler reads of a known block state are therefore the concrete reads. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-- The store invariant of the bridge. -/
structure BridgedStore (store : Store Root) : Prop where
  genesis_known : B.setup.genesisRoot ∈ store.block_roots
  genesis_parent_ne : (store.blocks B.setup.genesisRoot).parent_root ≠ B.setup.genesisRoot
  genesis_parent_unopened : B.blocks.open_ (store.blocks B.setup.genesisRoot).parent_root = none
  known : ∀ r ∈ store.block_roots, ∃ cs, B.stateOf r = some cs ∧
    store.block_states r = B.project cs ∧ B.Admits cs ∧
    cs.latest_block_header.root = r ∧ cs.slot = (store.blocks r).slot ∧
    (r ≠ B.setup.genesisRoot → ∃ wire, B.blocks.open_ r = some (wire, B.states.root cs) ∧
      wire.root = r ∧ B.MessageMatches (store.blocks r) wire ∧
      (store.blocks r).parent_root ∈ store.block_roots ∧
      ∃ cp, B.stateOf (store.blocks r).parent_root = some cp ∧
        state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle cp wire =
          .ok cs)

omit [Inhabited Root] in
theorem BridgedStore.of_sameBlocks {B : ConcreteBridge Root} {s t : Store Root}
    (h : SameBlocks s t) (hs : B.BridgedStore s) : B.BridgedStore t := by
  obtain ⟨hroots, hblocks, hstates⟩ := h
  refine ⟨hroots ▸ hs.genesis_known, hblocks ▸ hs.genesis_parent_ne,
    hblocks ▸ hs.genesis_parent_unopened, ?_⟩
  rw [← hroots, ← hblocks, ← hstates]
  exact hs.known

omit [Inhabited Root] in
theorem stateOf_genesis : B.stateOf B.setup.genesisRoot = some B.setup.genesis := by
  simp [stateOf]

omit [Inhabited Root] in
theorem stateOf_of_open {r : Root} (hr : r ≠ B.setup.genesisRoot) {wire : FFGWireBlock Root}
    {cs : FFGBeaconState Root} (h : B.blocks.open_ r = some (wire, B.states.root cs)) :
    B.stateOf r = some cs := by
  simp [stateOf, hr, h, B.states.open_root]

omit [Inhabited Root] in
theorem admits_genesis : B.Admits B.setup.genesis := by
  refine ⟨⟨[], [], .genesis⟩, ?_⟩
  change compute_epoch_at_slot B.setup.cfg 0 ≤ B.setup.scope.last_epoch
  simp [compute_epoch_at_slot]

omit [Inhabited Root] in
/-- The header root of a reachable in-scope state is the root of its last
block, and a successful transition installs the block root. -/
theorem header_root_of_transition (hB : B.Admissible) {cp cs : FFGBeaconState Root}
    {wire : FFGWireBlock Root} (hcp : B.Admits cp)
    (h : state_transition B.setup.cfg B.setup.preset B.setup.schedule B.setup.oracle cp wire =
      .ok cs)
    (hH : compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch) :
    B.Admits cs ∧ cs.latest_block_header.root = wire.root := by
  obtain ⟨⟨blocks, votes, hreach⟩, -⟩ := hcp
  have hreach' := Reachable.block wire hreach h
  refine ⟨⟨⟨_, _, hreach'⟩, hH⟩, ?_⟩
  rw [(provenanceInvariant_of_reachable hB.setup hreach' hH).header_root, tipRoot_append]

/-- A successful fresh block handler keeps the invariant. -/
theorem BridgedStore.on_block {B : ConcreteBridge Root} (hB : B.Admissible)
    {store store' : Store Root} {sb : SignedBeaconBlock Root} (hs : B.BridgedStore store)
    (hh : on_block B.setup.cfg B.ext store sb = some store') : B.BridgedStore store' := by
  by_cases hknown : sb.root ∈ store.block_roots
  · obtain rfl : store' = store := by
      simpa [FastConfirmation.Spec.on_block, hknown] using hh.symm
    exact hs
  have hparent : sb.message.parent_root ∈ store.block_roots := by
    by_contra hnot
    simp [FastConfirmation.Spec.on_block, hknown, hnot] at hh
  have hle := on_block_storeLE B.setup.cfg B.ext hh
  obtain ⟨post, hpost, hstate⟩ :=
    Execution.SuccessfulScheduledBlockImport.on_block_inserted_state_fresh B.setup.cfg B.ext
      hknown hh
  have hmsg := on_block_inserted_message hknown hh
  have hne : sb.root ≠ B.setup.genesisRoot := fun h => hknown (h ▸ hs.genesis_known)
  have hgb : store'.blocks B.setup.genesisRoot = store.blocks B.setup.genesisRoot :=
    on_block_other_root_blocks hh (Ne.symm hne)
  refine ⟨hle.1 hs.genesis_known, hgb ▸ hs.genesis_parent_ne,
    hgb ▸ hs.genesis_parent_unopened, ?_⟩
  intro r hr
  by_cases hrs : r = sb.root
  · subst hrs
    obtain ⟨cs0, wire, stateRoot, cpost, hd, ho, hwroot, hm, hst, hsr, hH, rfl⟩ :=
      B.transition_eq_some hpost
    obtain ⟨cp, hcp, hpstate, hcpadm, -⟩ := hs.known _ hparent
    rw [hpstate, B.decode_project hcpadm] at hd
    cases hd
    obtain ⟨hadm, hhead⟩ := B.header_root_of_transition hB hcpadm hst hH
    subst hsr
    refine ⟨cpost, B.stateOf_of_open hne ho, hstate, hadm, hhead.trans hwroot, ?_, ?_⟩
    · rw [hmsg, hm.1]; exact (state_transition_slot hst).1
    · intro _
      refine ⟨wire, ho, hwroot, hmsg ▸ hm, hmsg ▸ hle.1 hparent, _, ?_, hst⟩
      rw [hmsg]; exact hcp
  · have hrold := on_block_other_root_known hh hrs hr
    obtain ⟨cs, hcs, hstate', hadm, hhead, hslot, hrest⟩ := hs.known r hrold
    have hb := on_block_other_root_blocks hh hrs
    refine ⟨cs, hcs, (on_block_other_root_block_states hh hrs).trans hstate', hadm, hhead,
      hb ▸ hslot, ?_⟩
    intro hng
    obtain ⟨wire, ho, hw, hm, hp, cp, hcp, hst⟩ := hrest hng
    exact ⟨wire, ho, hw, hb ▸ hm, hb ▸ hle.1 hp, cp, hb ▸ hcp, hst⟩

theorem BridgedStore.step {B : ConcreteBridge Root} (hB : B.Admissible)
    (store : Store Root) (event : Event Root) (hs : B.BridgedStore store) :
    B.BridgedStore ((FastConfirmation.Spec.apply_event B.setup.cfg B.ext store event).getD
      store) := by
  cases he : FastConfirmation.Spec.apply_event B.setup.cfg B.ext store event with
  | none => exact hs
  | some next =>
    cases event with
    | block sb => exact hs.on_block hB he
    | attestation a fromBlock =>
      exact hs.of_sameBlocks (on_attestation_sameBlocks B.setup.cfg B.ext he)
    | attester_slashing slashing =>
      exact hs.of_sameBlocks (on_attester_slashing_sameBlocks B.ext he)
    | execution_payload_envelope signed observation =>
      exact hs.of_sameBlocks (on_execution_payload_envelope_sameBlocks B.ext he)
    | payload_attestation_message message fromBlock =>
      exact hs.of_sameBlocks (on_payload_attestation_message_sameBlocks B.setup.cfg B.ext he)

theorem BridgedStore.fold {B : ConcreteBridge Root} (hB : B.Admissible)
    (events : List (Event Root)) (store : Store Root) (hs : B.BridgedStore store) :
    B.BridgedStore (events.foldl
      (fun s event => (FastConfirmation.Spec.apply_event B.setup.cfg B.ext s event).getD s)
        store) := by
  induction events generalizing store with
  | nil => exact hs
  | cons event events ih => exact ih _ (hs.step hB store event)

theorem bridgedStore_genesis {E : Execution Root}
    (hg : B.ConcreteGenesis E) : B.BridgedStore E.genesis_store := by
  obtain ⟨anchor, hroot, hslot, hpne, hpopen, hstore⟩ := hg
  rw [hstore]
  have hgb : (get_forkchoice_store B.setup.cfg (B.project B.setup.genesis) anchor).blocks
      B.setup.genesisRoot = anchor.message := by
    simp [get_forkchoice_store, hroot]
  refine ⟨by simp [get_forkchoice_store, hroot], by rw [hgb]; exact hpne,
    by rw [hgb]; exact hpopen, ?_⟩
  intro r hr
  simp only [get_forkchoice_store, List.mem_singleton] at hr
  subst hr
  refine ⟨B.setup.genesis, hroot ▸ B.stateOf_genesis, by simp [get_forkchoice_store],
    B.admits_genesis, ?_, ?_, fun h => absurd hroot h⟩
  · rw [hroot]; rfl
  · simp [get_forkchoice_store, hslot]; rfl

/-- **Store bridge.** Every node store of an execution run with the concrete
bridge from the setup genesis satisfies `BridgedStore`. -/
theorem bridgedStore_store (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (v : ValidatorIndex) (n : ℕ) :
    B.BridgedStore (E.store B.setup.cfg B.ext v n) := by
  induction n with
  | zero => exact B.bridgedStore_genesis hg
  | succ n ih =>
    exact BridgedStore.fold hB _ _
      (ih.of_sameBlocks (on_tick_sameBlocks B.setup.cfg _ _))

/-- **Store bridge at exact prefixes.** -/
theorem bridgedStore_prefix (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) {store : Store Root}
    (h : E.ScheduledPrefixStore B.setup.cfg B.ext store) : B.BridgedStore store := by
  cases h with
  | genesis => exact B.bridgedStore_genesis hg
  | scheduledPrefix p =>
    unfold Execution.ScheduledEventPrefix.store
    exact BridgedStore.fold hB _ _
      ((B.bridgedStore_store hB hg p.node p.previousSecond).of_sameBlocks
        (on_tick_sameBlocks B.setup.cfg _ _))

/-! ### Handler reads of known block states -/

omit [Inhabited Root] in
/-- The reads of a known block state are the concrete reads: its checkpoints,
eager PJF, and slot processing to an in-scope target. -/
theorem known_reads (hB : B.Admissible) {store : Store Root} (hs : B.BridgedStore store)
    {r : Root} (hr : r ∈ store.block_roots) :
    ∃ cs blocks votes, B.stateOf r = some cs ∧ store.block_states r = B.project cs ∧
      Reachable B.setup blocks votes cs ∧
      compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch ∧
      (∃ Y, process_justification_and_finalization B.setup.cfg B.setup.preset cs = .ok Y ∧
        B.ext.process_justification_and_finalization (store.block_states r) = B.project Y) ∧
      ∀ target, cs.slot < target →
        compute_epoch_at_slot B.setup.cfg target ≤ B.setup.scope.last_epoch →
        ∃ next, process_slots B.setup.cfg B.setup.preset cs target = .ok next ∧
          B.ext.process_slots (store.block_states r) target = B.project next := by
  obtain ⟨cs, hcs, hstate, hadm, -⟩ := hs.known r hr
  obtain ⟨⟨blocks, votes, hreach⟩, hH⟩ := hadm
  have hd : B.decode (store.block_states r) = some cs := by
    rw [hstate]; exact B.decode_project ⟨⟨blocks, votes, hreach⟩, hH⟩
  refine ⟨cs, blocks, votes, hcs, hstate, hreach, hH, ?_, ?_⟩
  · obtain ⟨Y, hY, hp, -⟩ := B.pjf_decoded hB hd hreach
    exact ⟨Y, hY, hp⟩
  · intro target hlt hin
    obtain ⟨next, hnext, hs', -⟩ := B.slots_decoded hB hd hreach hlt hin
    exact ⟨next, hnext, hs'⟩

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
