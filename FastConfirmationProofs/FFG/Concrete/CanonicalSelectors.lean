module
public import FastConfirmationProofs.FFG.Concrete.BridgeStore
public import FastConfirmationProofs.ForkChoice.Ancestry.AncestryRoots
public import FastConfirmationProofs.Checkpoints.ExecutionRootReflection
public import FastConfirmationStatements.Premises.CheckpointLinks
public import FastConfirmationStatements.Premises.ScheduledExecutionConditions

@[expose] public section

/-! Defines the canonical checkpoint selectors of an execution run with the
concrete bridge, and proves their block-local laws. `GJ` and `GF` read the
committed concrete state of a block root; `GU` and `GUF` read one eager PJF
copy of it; `checkpointAt` walks the committed parent chain. A raw
genesis-epoch checkpoint reads as the genesis anchor (`norm0`). The file
proves the nine read agreements, the imported finalization lag, the
checkpoint reflection in every exact prefix store, the checkpoint projection
laws, and the selector orderings of `AcceptedBlockFFGState`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type} [LinearOrder Root] [Inhabited Root]

namespace ConcreteBridge

variable (B : ConcreteBridge Root)

/-! ### Selectors -/

/-- The genesis anchor: `Checkpoint(GENESIS_EPOCH, genesis_root)`. -/
def anchorCheckpoint : Checkpoint Root := ⟨GENESIS_EPOCH, B.setup.genesisRoot⟩

/-- A genesis-epoch checkpoint reads as the anchor; other checkpoints read as
themselves. -/
def norm0 (c : Checkpoint Root) : Checkpoint Root :=
  if c.epoch = GENESIS_EPOCH then B.anchorCheckpoint else c

/-- One eager PJF copy of the committed state of a root. -/
noncomputable def eagerOf (r : Root) : Option (FFGBeaconState Root) :=
  match B.stateOf r with
  | some cs =>
    match process_justification_and_finalization B.setup.cfg B.setup.preset cs with
    | .ok Y => some Y
    | .error _ => none
  | none => none

/-- Realized justification `GJ`. -/
noncomputable def GJ (r : Root) : Checkpoint Root :=
  match B.stateOf r with
  | some cs => B.norm0 cs.current_justified_checkpoint
  | none => B.anchorCheckpoint

/-- Realized finalization `GF`. -/
noncomputable def GF (r : Root) : Checkpoint Root :=
  match B.stateOf r with
  | some cs => B.norm0 cs.finalized_checkpoint
  | none => B.anchorCheckpoint

/-- Unrealized justification `GU`. -/
noncomputable def GU (r : Root) : Checkpoint Root :=
  match B.eagerOf r with
  | some Y => B.norm0 Y.current_justified_checkpoint
  | none => B.anchorCheckpoint

/-- Unrealized finalization `GUF`. -/
noncomputable def GUF (r : Root) : Checkpoint Root :=
  match B.eagerOf r with
  | some Y => B.norm0 Y.finalized_checkpoint
  | none => B.anchorCheckpoint

/-- The committed parent walk down to the last block at or before `slot`. The
genesis root stops the walk. -/
def ancestorWalk (slot : Slot) : ℕ → Root → Root
  | 0, r => r
  | fuel + 1, r =>
    if r = B.setup.genesisRoot then r
    else match B.blocks.open_ r with
      | some (wire, _) => if slot < wire.slot then ancestorWalk slot fuel wire.parent_root else r
      | none => r

/-- The slot of the committed state of a root. -/
def slotOfRoot (r : Root) : Slot :=
  match B.stateOf r with
  | some cs => cs.slot
  | none => 0

/-- The checkpoint selector `C(r, e)`: epoch `e` and the committed ancestor of
`r` at or before the start slot of `e`. -/
def checkpointAt (r : Root) (e : Epoch) : Checkpoint Root :=
  ⟨e, B.ancestorWalk (compute_start_slot_at_epoch B.setup.cfg e) (B.slotOfRoot r + 1) r⟩

/-! ### Selector reads -/

omit [LinearOrder Root] [Inhabited Root] in
theorem norm0_epoch (c : Checkpoint Root) : (B.norm0 c).epoch = c.epoch := by
  unfold norm0
  split_ifs with h
  · exact h.symm
  · rfl

omit [LinearOrder Root] [Inhabited Root] in
theorem readsAs_norm0 (c : Checkpoint Root) : CheckpointReadsAs c (B.norm0 c) := by
  unfold norm0
  split_ifs with h
  · exact Or.inr ⟨h, rfl⟩
  · exact Or.inl rfl

omit [Inhabited Root] in
theorem GJ_of (r : Root) {cs : FFGBeaconState Root} (h : B.stateOf r = some cs) :
    B.GJ r = B.norm0 cs.current_justified_checkpoint := by
  simp [GJ, h]

omit [Inhabited Root] in
theorem GF_of (r : Root) {cs : FFGBeaconState Root} (h : B.stateOf r = some cs) :
    B.GF r = B.norm0 cs.finalized_checkpoint := by
  simp [GF, h]

omit [Inhabited Root] in
theorem eagerOf_of (r : Root) {cs Y : FFGBeaconState Root} (h : B.stateOf r = some cs)
    (hY : process_justification_and_finalization B.setup.cfg B.setup.preset cs = .ok Y) :
    B.eagerOf r = some Y := by
  simp [eagerOf, h, hY]

omit [Inhabited Root] in
theorem GU_of (r : Root) {Y : FFGBeaconState Root} (h : B.eagerOf r = some Y) :
    B.GU r = B.norm0 Y.current_justified_checkpoint := by
  simp [GU, h]

omit [Inhabited Root] in
theorem GUF_of (r : Root) {Y : FFGBeaconState Root} (h : B.eagerOf r = some Y) :
    B.GUF r = B.norm0 Y.finalized_checkpoint := by
  simp [GUF, h]

omit [Inhabited Root] in
/-- The four raw reads of a known block state of a bridged store read as the
canonical selectors. -/
theorem known_selector_reads (hB : B.Admissible) {store : Store Root}
    (hs : B.BridgedStore store) {r : Root} (hr : r ∈ store.block_roots) :
    CheckpointReadsAs (store.block_states r).current_justified_checkpoint (B.GJ r) ∧
    CheckpointReadsAs (store.block_states r).finalized_checkpoint (B.GF r) ∧
    CheckpointReadsAs (B.ext.process_justification_and_finalization
      (store.block_states r)).current_justified_checkpoint (B.GU r) ∧
    CheckpointReadsAs (B.ext.process_justification_and_finalization
      (store.block_states r)).finalized_checkpoint (B.GUF r) := by
  obtain ⟨cs, blocks, votes, hcs, hstate, hreach, hH, ⟨Y, hY, hpjf⟩, -⟩ :=
    B.known_reads hB hs hr
  have he := B.eagerOf_of r hcs hY
  rw [hpjf, hstate, B.GJ_of r hcs, B.GF_of r hcs, B.GU_of r he, B.GUF_of r he]
  exact ⟨B.readsAs_norm0 _, B.readsAs_norm0 _, B.readsAs_norm0 _, B.readsAs_norm0 _⟩

/-- An accepted root has a bridged prefix store that knows it. -/
theorem accepted_bridged (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {r : Root} (h : E.RootKnownInScheduledPrefix B.setup.cfg B.ext r) :
    ∃ store, E.ScheduledPrefixStore B.setup.cfg B.ext store ∧ B.BridgedStore store ∧
      r ∈ store.block_roots := by
  obtain ⟨store, hstore, hr⟩ := h
  exact ⟨store, hstore, B.bridgedStore_prefix hB hg hstore, hr⟩

/-- An accepted root has an admitted committed state, with a successful eager
copy. -/
theorem accepted_state (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {r : Root} (h : E.RootKnownInScheduledPrefix B.setup.cfg B.ext r) :
    ∃ cs blocks votes Y, B.stateOf r = some cs ∧ Reachable B.setup blocks votes cs ∧
      compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch ∧
      process_justification_and_finalization B.setup.cfg B.setup.preset cs = .ok Y ∧
      B.eagerOf r = some Y ∧ B.GJ r = B.norm0 cs.current_justified_checkpoint ∧
      B.GF r = B.norm0 cs.finalized_checkpoint ∧
      B.GU r = B.norm0 Y.current_justified_checkpoint ∧
      B.GUF r = B.norm0 Y.finalized_checkpoint := by
  obtain ⟨store, -, hs, hr⟩ := B.accepted_bridged hB hg h
  obtain ⟨cs, blocks, votes, hcs, -, hreach, hH, ⟨Y, hY, -⟩, -⟩ := B.known_reads hB hs hr
  have he := B.eagerOf_of r hcs hY
  exact ⟨cs, blocks, votes, Y, hcs, hreach, hH, hY, he, B.GJ_of r hcs, B.GF_of r hcs,
    B.GU_of r he, B.GUF_of r he⟩

/-- The block of an exact accepted carrier has the slot of the committed state. -/
theorem blockKnown_slot (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {r : Root} {b : BeaconBlock Root} (h : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b)
    {cs : FFGBeaconState Root} (hcs : B.stateOf r = some cs) : cs.slot = b.slot := by
  obtain ⟨store, hstore, hr, hb⟩ := h
  obtain ⟨cs', hcs', -, -, -, hslot, -⟩ := (B.bridgedStore_prefix hB hg hstore).known r hr
  rw [hcs] at hcs'
  cases hcs'
  rw [hslot, hb]

/-! ### The nine read agreements -/

theorem genesis_reads (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E) :
    ∀ r ∈ E.genesis_store.block_roots,
      CheckpointReadsAs (E.genesis_store.block_states r).current_justified_checkpoint (B.GJ r) ∧
      CheckpointReadsAs (E.genesis_store.block_states r).finalized_checkpoint (B.GF r) ∧
      CheckpointReadsAs (B.ext.process_justification_and_finalization
        (E.genesis_store.block_states r)).current_justified_checkpoint (B.GU r) ∧
      CheckpointReadsAs (B.ext.process_justification_and_finalization
        (E.genesis_store.block_states r)).finalized_checkpoint (B.GUF r) :=
  fun _ hr => B.known_selector_reads hB (B.bridgedStore_genesis hg) hr

theorem genesis_unrealized_justification_reads {E : Execution Root}
    (hg : B.ConcreteGenesis E) :
    ∀ r ∈ E.genesis_store.block_roots,
      CheckpointReadsAs (E.genesis_store.unrealized_justifications r) (B.GU r) := by
  intro r hr
  obtain ⟨anchor, hroot, hslot, -, -, hstore⟩ := hg
  rw [hstore] at hr ⊢
  simp only [get_forkchoice_store, List.mem_singleton] at hr
  subst hr
  have hY : process_justification_and_finalization B.setup.cfg B.setup.preset B.setup.genesis =
      .ok B.setup.genesis := by
    unfold process_justification_and_finalization
    rw [if_pos (by change compute_epoch_at_slot B.setup.cfg 0 ≤ 1; simp [compute_epoch_at_slot])]
    rfl
  have he := B.eagerOf_of anchor.root (hroot ▸ B.stateOf_genesis) hY
  rw [B.GU_of _ he]
  simp only [get_forkchoice_store, Function.update_self]
  refine Or.inr ⟨?_, ?_⟩
  · change compute_epoch_at_slot B.setup.cfg 0 = GENESIS_EPOCH
    simp [compute_epoch_at_slot, GENESIS_EPOCH]
  · rw [B.norm0_epoch]; rfl

theorem transition_reads (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    (t : E.SuccessfulScheduledBlockImport B.setup.cfg B.ext) :
    CheckpointReadsAs (t.postStore.block_states t.signedBlock.root).current_justified_checkpoint
      (B.GJ t.signedBlock.root) ∧
    CheckpointReadsAs (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
      (B.GF t.signedBlock.root) ∧
    CheckpointReadsAs (B.ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)).current_justified_checkpoint
      (B.GU t.signedBlock.root) ∧
    CheckpointReadsAs (B.ext.process_justification_and_finalization
      (t.postStore.block_states t.signedBlock.root)).finalized_checkpoint
      (B.GUF t.signedBlock.root) :=
  B.known_selector_reads hB
    (B.bridgedStore_prefix hB hg
      (Execution.SuccessfulScheduledBlockImport.post_causal B.setup.cfg B.ext t))
    (Execution.SuccessfulScheduledBlockImport.root_known B.setup.cfg B.ext t)

/-! ### Imported finalization lag -/

/-- The stored message of an imported root is the imported message. -/
theorem import_message (hwf : WellFormedExecution E)
    (t : E.SuccessfulScheduledBlockImport B.setup.cfg B.ext) :
    t.postStore.blocks t.signedBlock.root = t.signedBlock.message := by
  have hpost := Execution.SuccessfulScheduledBlockImport.post_causal B.setup.cfg B.ext t
  have hr := Execution.SuccessfulScheduledBlockImport.root_known B.setup.cfg B.ext t
  have hat : E.BlockAt t.signedBlock.root (t.postStore.blocks t.signedBlock.root) := by
    rcases Execution.ScheduledPrefixStore.blockProvenance B.setup.cfg B.ext E hpost _ hr with
      hgen | hsched
    · exact Or.inl ⟨hgen.1, hgen.2⟩
    · obtain ⟨sb, ⟨u, k, hscheduled⟩, hroot, hmessage⟩ := hsched
      exact Or.inr ⟨u, k, sb, hscheduled, hroot, hmessage.symm⟩
  have hev : E.BlockAt t.signedBlock.root t.signedBlock.message :=
    Or.inr ⟨t.atPrefix.node, t.atPrefix.previousSecond + 1, t.signedBlock,
      List.mem_of_getElem? t.event_at, rfl, rfl⟩
  exact E.blockAt_unique hwf hat hev

/-- **Imported finalization lag.** The finalized checkpoint of an imported
block state reads as the genesis anchor, or it is at least two epochs before
the block epoch. -/
theorem imported_finalization_lag (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E)
    (t : E.SuccessfulScheduledBlockImport B.setup.cfg B.ext) :
    CheckpointReadsAs (t.postStore.block_states t.signedBlock.root).finalized_checkpoint
        B.anchorCheckpoint ∨
      (t.postStore.block_states t.signedBlock.root).finalized_checkpoint.epoch + 2 ≤
        compute_epoch_at_slot B.setup.cfg t.signedBlock.message.slot := by
  have hs := B.bridgedStore_prefix hB hg
    (Execution.SuccessfulScheduledBlockImport.post_causal B.setup.cfg B.ext t)
  have hr := Execution.SuccessfulScheduledBlockImport.root_known B.setup.cfg B.ext t
  obtain ⟨cs, -, hstate, ⟨⟨blocks, votes, hreach⟩, hH⟩, -, hslot, -⟩ := hs.known _ hr
  rw [hstate, project_finalized, ← B.import_message hwf t, ← hslot]
  rcases finalized_lag hB.setup hreach hH with h | h
  · left; rw [h]; exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inr h

/-- The canonical lag premise of `NextSlotSafetyPremises` for any
interpretation whose anchor is the genesis anchor. -/
theorem importedBlockFinalizationLag (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) (hwf : WellFormedExecution E)
    (I : ScheduledFFGInterpretation B.setup.cfg B.ext E) (hI : I.anchor = B.anchorCheckpoint) :
    E.ImportedBlockFinalizationLag B.setup.cfg B.ext I := by
  intro t
  rw [hI]
  exact B.imported_finalization_lag hB hg hwf t

/-- The genesis store justified checkpoint is the genesis anchor. -/
theorem genesis_justified (hg : B.ConcreteGenesis E) :
    E.genesis_store.justified_checkpoint = B.anchorCheckpoint := by
  obtain ⟨anchor, hroot, -, -, -, hstore⟩ := hg
  rw [hstore]
  simp only [get_forkchoice_store, anchorCheckpoint, hroot]
  congr 1
  change compute_epoch_at_slot B.setup.cfg 0 = GENESIS_EPOCH
  simp [compute_epoch_at_slot, GENESIS_EPOCH]

/-! ### The committed parent walk -/

omit [Inhabited Root] in
/-- Parent slots decrease in a bridged store. -/
theorem BridgedStore.parentSlotLt {B : ConcreteBridge Root} {store : Store Root}
    (hs : B.BridgedStore store) :
    ∀ r ∈ store.block_roots, (store.blocks r).parent_root ∈ store.block_roots →
      (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot := by
  intro r hr hp
  by_cases hg : r = B.setup.genesisRoot
  · subst hg
    exfalso
    have hne := hs.genesis_parent_ne
    obtain ⟨cs, -, -, -, -, -, hrest⟩ := hs.known _ hp
    obtain ⟨wire, ho, -⟩ := hrest hne
    rw [hs.genesis_parent_unopened] at ho
    cases ho
  · obtain ⟨cs, hcs, -, -, -, hslot, hrest⟩ := hs.known r hr
    obtain ⟨wire, -, -, hm, -, cp, hcp, hst⟩ := hrest hg
    obtain ⟨cp', hcp', -, -, -, hpslot, -⟩ := hs.known _ hp
    rw [hcp] at hcp'
    cases hcp'
    rw [← hpslot, ← hslot, (state_transition_slot hst).1]
    exact (state_transition_slot hst).2

omit [Inhabited Root] in
theorem stateOf_genesis_slot : B.slotOfRoot B.setup.genesisRoot = 0 := by
  simp [slotOfRoot, B.stateOf_genesis]; rfl

omit [Inhabited Root] in
/-- The genesis block of a bridged store has slot zero. -/
theorem BridgedStore.genesis_slot {B : ConcreteBridge Root} {store : Store Root}
    (hs : B.BridgedStore store) : (store.blocks B.setup.genesisRoot).slot = 0 := by
  obtain ⟨cs, hcs, -, -, -, hslot, -⟩ := hs.known _ hs.genesis_known
  rw [B.stateOf_genesis] at hcs
  cases hcs
  exact hslot.symm

omit [Inhabited Root] in
/-- Every known root has a known ancestor walk. -/
theorem BridgedStore.walkKnown {B : ConcreteBridge Root} {store : Store Root}
    (hs : B.BridgedStore store) (y : Slot) :
    ∀ n, ∀ r ∈ store.block_roots, (store.blocks r).slot ≤ n → WalkKnown store y r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r hr hn
    by_cases hle : (store.blocks r).slot ≤ y
    · exact .stop hr hle
    · have hg : r ≠ B.setup.genesisRoot := by
        intro h; subst h; rw [hs.genesis_slot] at hle; exact hle (Nat.zero_le _)
      obtain ⟨cs, -, -, -, -, -, hrest⟩ := hs.known r hr
      obtain ⟨-, -, -, -, hp, -⟩ := hrest hg
      have hlt := hs.parentSlotLt r hr hp
      exact .step hr (Nat.lt_of_not_le hle) (ih _ (Nat.lt_of_lt_of_le hlt hn) _ hp le_rfl)

omit [Inhabited Root] in
/-- The committed parent walk is the store ancestor walk on known roots. -/
theorem ancestorWalk_eq {store : Store Root} (hs : B.BridgedStore store) (y : Slot) :
    ∀ fuel (r : Root) (status : PayloadStatus), r ∈ store.block_roots →
      (get_ancestor_aux store y fuel (ForkChoiceNode.mk r status)).root =
        B.ancestorWalk y fuel r := by
  intro fuel
  induction fuel with
  | zero => intro r status _; rfl
  | succ fuel ih =>
    intro r status hr
    simp only [get_ancestor_aux, ancestorWalk]
    by_cases hg : r = B.setup.genesisRoot
    · subst hg
      rw [if_pos rfl, hs.genesis_slot, if_neg (Nat.not_lt_zero _)]
    · rw [if_neg hg]
      obtain ⟨cs, -, -, -, -, -, hrest⟩ := hs.known r hr
      obtain ⟨wire, ho, -, hm, hp, -⟩ := hrest hg
      rw [ho]
      dsimp only
      rw [hm.1, hm.2.1]
      split_ifs with hlt
      · exact ih _ _ (hm.2.1 ▸ hp)
      · rfl

omit [Inhabited Root] in
theorem slotOfRoot_eq {store : Store Root} (hs : B.BridgedStore store) {r : Root}
    (hr : r ∈ store.block_roots) : B.slotOfRoot r = (store.blocks r).slot := by
  obtain ⟨cs, hcs, -, -, -, hslot, -⟩ := hs.known r hr
  simp [slotOfRoot, hcs, hslot]

omit [Inhabited Root] in
/-- **Checkpoint reflection.** The checkpoint selector equals
`get_checkpoint_for_block` in every bridged store that knows the root. -/
theorem checkpointAt_eq {store : Store Root} (hs : B.BridgedStore store) {r : Root}
    (hr : r ∈ store.block_roots) (e : Epoch) :
    B.checkpointAt r e = get_checkpoint_for_block B.setup.cfg store r e := by
  unfold checkpointAt get_checkpoint_for_block get_checkpoint_block get_ancestor
  rw [B.ancestorWalk_eq hs _ _ r .pending hr, B.slotOfRoot_eq hs hr]

theorem checkpoint_of_known (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {store : Store Root} (hstore : E.ScheduledPrefixStore B.setup.cfg B.ext store) :
    ∀ r ∈ store.block_roots, ∀ e,
      B.checkpointAt r e = get_checkpoint_for_block B.setup.cfg store r e :=
  fun _ hr e => B.checkpointAt_eq (B.bridgedStore_prefix hB hg hstore) hr e

/-- **Checkpoint projection laws** on the accepted domain. -/
theorem checkpoint_projection_laws (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) :
    EpochCheckpointProjectionLaws B.anchorCheckpoint
      (E.RootKnownInScheduledPrefix B.setup.cfg B.ext) B.checkpointAt where
  checkpoint_root_accepted := by
    intro r e hr _
    obtain ⟨store, hstore, hs, hrk⟩ := B.accepted_bridged hB hg hr
    refine ⟨store, hstore, ?_⟩
    rw [B.checkpointAt_eq hs hrk]
    exact (get_ancestor_spec hs.parentSlotLt
      (hs.walkKnown _ _ r hrk le_rfl)).1
  checkpoint_comp := by
    intro r s t hr _ hst
    obtain ⟨store, hstore, hs, hrk⟩ := B.accepted_bridged hB hg hr
    have hw := hs.walkKnown (compute_start_slot_at_epoch B.setup.cfg s) _ r hrk le_rfl
    have hmid : (B.checkpointAt r t).root ∈ store.block_roots := by
      rw [B.checkpointAt_eq hs hrk]
      exact (get_ancestor_spec hs.parentSlotLt (hs.walkKnown _ _ r hrk le_rfl)).1
    rw [B.checkpointAt_eq hs hmid, B.checkpointAt_eq hs hrk, B.checkpointAt_eq hs hrk]
    simp only [get_checkpoint_for_block, get_checkpoint_block]
    congr 1
    exact get_ancestor_comp_root hs.parentSlotLt
      (Nat.mul_le_mul_right _ hst) hw

/-! ### Selector orderings and timing at one block -/

omit [Inhabited Root] in
/-- One PJF pass does not lower a current justified checkpoint that is before
the pass epoch. -/
theorem cjFormula_epoch_ge {S : FFGSetup Root} {blocks : List (FFGWireBlock Root)}
    {votes : List (IncludedVote Root)} {E : Epoch} {c : Checkpoint Root} (hc : c.epoch ≤ E - 1) :
    c.epoch ≤ (cjFormula S blocks votes E c).epoch := by
  unfold cjFormula
  split_ifs
  · exact le_rfl
  · change c.epoch ≤ E; beacon_omega
  · exact hc
  · exact le_rfl

/-- The eager copy of an accepted root follows `cjFormula`. -/
theorem accepted_eager (hB : B.Admissible) {E : Execution Root} (hg : B.ConcreteGenesis E)
    {r : Root} (h : E.RootKnownInScheduledPrefix B.setup.cfg B.ext r) :
    ∃ cs blocks votes Y, B.stateOf r = some cs ∧ Reachable B.setup blocks votes cs ∧
      compute_epoch_at_slot B.setup.cfg cs.slot ≤ B.setup.scope.last_epoch ∧
      process_justification_and_finalization B.setup.cfg B.setup.preset cs = .ok Y ∧
      Y.current_justified_checkpoint = cjFormula B.setup blocks votes
        (compute_epoch_at_slot B.setup.cfg cs.slot) cs.current_justified_checkpoint ∧
      B.GJ r = B.norm0 cs.current_justified_checkpoint ∧
      B.GF r = B.norm0 cs.finalized_checkpoint ∧
      B.GU r = B.norm0 Y.current_justified_checkpoint ∧
      B.GUF r = B.norm0 Y.finalized_checkpoint := by
  obtain ⟨cs, blocks, votes, Y, hcs, hreach, hH, hY, -, hgj, hgf, hgu, hguf⟩ :=
    B.accepted_state hB hg h
  obtain ⟨Y', hY', hcj⟩ := eager_pjf hB.setup hB.numeric
    (provenanceInvariant_of_reachable hB.setup hreach hH) (lengthsOK_of_reachable hreach) hH
  rw [hY] at hY'
  cases hY'
  exact ⟨cs, blocks, votes, Y, hcs, hreach, hH, hY, hcj, hgj, hgf, hgu, hguf⟩

/-- `realized_justified_anchor_or_before`. -/
theorem realized_justified_anchor_or_before (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) {r : Root} {b : BeaconBlock Root}
    (h : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b) :
    B.GJ r = B.anchorCheckpoint ∨
      (B.GJ r).epoch < compute_epoch_at_slot B.setup.cfg b.slot := by
  obtain ⟨cs, blocks, votes, -, hcs, hreach, hH, -, -, hgj, -⟩ :=
    B.accepted_state hB hg (Execution.BlockKnownInScheduledPrefix.acceptedRoot
      B.setup.cfg B.ext E h)
  have hslot := B.blockKnown_slot hB hg h hcs
  have hle := (provenanceInvariant_of_reachable hB.setup hreach hH).current_epoch_le
  rw [hgj, ← hslot]
  unfold norm0
  split_ifs with h0
  · exact Or.inl rfl
  · right
    simp only [GENESIS_EPOCH] at h0
    beacon_omega

/-- `realized_justified_epoch_le_unrealized`. -/
theorem realized_justified_epoch_le_unrealized (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) {r : Root}
    (h : E.RootKnownInScheduledPrefix B.setup.cfg B.ext r) :
    (B.GJ r).epoch ≤ (B.GU r).epoch := by
  obtain ⟨cs, blocks, votes, Y, -, hreach, hH, -, hcj, hgj, -, hgu, -⟩ :=
    B.accepted_eager hB hg h
  rw [hgj, hgu, B.norm0_epoch, B.norm0_epoch, hcj]
  exact cjFormula_epoch_ge (provenanceInvariant_of_reachable hB.setup hreach hH).current_epoch_le

/-- `unrealized_justified_early`: at epochs up to `GENESIS_EPOCH + 1`, PJF
returns early and `GU = GJ`. -/
theorem unrealized_justified_early (hB : B.Admissible) {E : Execution Root}
    (hg : B.ConcreteGenesis E) {r : Root} {b : BeaconBlock Root}
    (h : E.BlockKnownInScheduledPrefix B.setup.cfg B.ext r b)
    (he : compute_epoch_at_slot B.setup.cfg b.slot ≤ GENESIS_EPOCH + 1) :
    B.GU r = B.GJ r := by
  obtain ⟨cs, blocks, votes, Y, hcs, -, -, hY, -, hgj, -, hgu, -⟩ :=
    B.accepted_state hB hg (Execution.BlockKnownInScheduledPrefix.acceptedRoot
      B.setup.cfg B.ext E h)
  have hslot := B.blockKnown_slot hB hg h hcs
  unfold process_justification_and_finalization at hY
  rw [if_pos (by rw [hslot]; simpa [GENESIS_EPOCH] using he)] at hY
  cases hY
  rw [hgu, hgj]

/-- `realized_finalized_epoch_le_realized_justified`. -/
theorem realized_finalized_epoch_le_realized_justified (hB : B.Admissible)
    {E : Execution Root} (hg : B.ConcreteGenesis E) {r : Root}
    (h : E.RootKnownInScheduledPrefix B.setup.cfg B.ext r) :
    (B.GF r).epoch ≤ (B.GJ r).epoch := by
  obtain ⟨cs, blocks, votes, Y, -, hreach, hH, -, -, hgj, hgf, -⟩ := B.accepted_state hB hg h
  rw [hgj, hgf, B.norm0_epoch, B.norm0_epoch]
  obtain ⟨h1, h2⟩ := checkpoint_epochs_ordered hB.setup hreach hH
  exact h1.trans h2

/-- `unrealized_finalized_epoch_le_unrealized_justified`. -/
theorem unrealized_finalized_epoch_le_unrealized_justified (hB : B.Admissible)
    {E : Execution Root} (hg : B.ConcreteGenesis E) {r : Root}
    (h : E.RootKnownInScheduledPrefix B.setup.cfg B.ext r) :
    (B.GUF r).epoch ≤ (B.GU r).epoch := by
  obtain ⟨cs, blocks, votes, Y, -, hreach, hH, hY, -, -, -, hgu, hguf⟩ :=
    B.accepted_state hB hg h
  rw [hgu, hguf, B.norm0_epoch, B.norm0_epoch]
  obtain ⟨h1, h2⟩ := eager_checkpoint_epochs_ordered hB.setup hreach hH hY
  exact h1.trans h2

/-- `unrealized_finalized_epoch_le_realized_justified`: every finalization
assignment of PJF selects an old justified checkpoint. -/
theorem unrealized_finalized_epoch_le_realized_justified (hB : B.Admissible)
    {E : Execution Root} (hg : B.ConcreteGenesis E) {r : Root}
    (h : E.RootKnownInScheduledPrefix B.setup.cfg B.ext r) :
    (B.GUF r).epoch ≤ (B.GJ r).epoch := by
  obtain ⟨cs, blocks, votes, Y, -, hreach, hH, hY, -, hgj, -, -, hguf⟩ :=
    B.accepted_state hB hg h
  rw [hgj, hguf, B.norm0_epoch, B.norm0_epoch]
  obtain ⟨h1, h2⟩ := checkpoint_epochs_ordered hB.setup hreach hH
  obtain ⟨bits, pj, j, f, rfl, hout⟩ := process_justification_and_finalization_outcome hY
  change f.epoch ≤ _
  rcases hout with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl | rfl | rfl⟩
  · exact h1.trans h2
  · exact h1.trans h2
  · exact h2
  · exact le_rfl

end ConcreteBridge

end FastConfirmation.Spec.ConcreteFFG

end
