module
public import FastConfirmationModel.Spec.BeaconChain.ConcreteTransition

@[expose] public section

/-! Defines concrete FFG body-vote provenance, reachable traces, and
justification certificates over `ConcreteFFG.state_transition`. The
certificate vocabulary uses only included body votes and the fixed registry. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

/-- The fixed inputs of one concrete FFG run from Python genesis. -/
structure FFGSetup (Root : Type) where
  cfg : Config
  preset : FFGPreset
  scope : FixedFFGScope
  schedule : FixedCommitteeSchedule
  oracle : BlockValidityOracle Root
  zeroRoot : Root
  genesisRoot : Root
  genesisTime : ℕ

variable {Root : Type}

/-- The Python genesis state of the setup. -/
def FFGSetup.genesis (S : FFGSetup Root) : FFGBeaconState Root :=
  FFGBeaconState.genesis S.zeroRoot S.genesisRoot S.genesisTime S.scope S.preset

/-- The raw zero-root genesis checkpoint stub. -/
def FFGSetup.stub (S : FFGSetup Root) : Checkpoint Root :=
  ⟨0, S.zeroRoot⟩

/-- Conditions under which the fixed registry weighs every in-horizon epoch
the same, and the block-root ring covers the two epochs that PJF reads. -/
structure FFGSetup.Admissible (S : FFGSetup Root) : Prop where
  ring_covers_two_epochs :
    2 * S.cfg.slots_per_epoch ≤ S.preset.slots_per_historical_root
  scope_from_genesis : S.scope.first_epoch = 0
  balance_floor : 2 * S.cfg.effective_balance_increment ≤ S.scope.activeBalance

/-- Weight of a signer set in the fixed registry. -/
def _root_.FastConfirmation.Spec.FixedFFGScope.weight (scope : FixedFFGScope)
    (signers : Finset ValidatorIndex) : Gwei :=
  ∑ i ∈ signers, (scope.validators.getD i default).effective_balance

/-- One successful `process_attestation` call of an accepted block body. The
record keeps the carrier block, the wire vote, the exact state on which the
call ran, and the saved parent slot. -/
structure IncludedVote (Root : Type) where
  block : FFGWireBlock Root
  vote : FFGWireAttestation Root
  pre : FFGBeaconState Root
  parentSlot : Slot

/-- The participation flags that `process_attestation` computed for the vote. -/
def IncludedVote.flags [BEq Root] (S : FFGSetup Root) (r : IncludedVote Root) :
    Checked (List ℕ) :=
  get_attestation_participation_flag_indices S.cfg S.preset r.pre r.vote.data
    (r.pre.slot - r.vote.data.slot) r.parentSlot

/-- The validators that the wire vote names in the fixed schedule. -/
def IncludedVote.attesters (S : FFGSetup Root) (r : IncludedVote Root) :
    Finset ValidatorIndex :=
  get_attesting_indices S.schedule r.vote

/-- The successful ordered attestation calls of one block body. -/
def attestationVotes [BEq Root] (S : FFGSetup Root) (block : FFGWireBlock Root)
    (parentSlot : Slot) : FFGBeaconState Root → List (FFGWireAttestation Root) →
    List (IncludedVote Root)
  | _, [] => []
  | state, vote :: votes =>
    match process_attestation S.cfg S.preset S.schedule state vote parentSlot with
    | .ok next => ⟨block, vote, state, parentSlot⟩ :: attestationVotes S block parentSlot next votes
    | .error _ => []

/-- The body votes that `state_transition state block` processes, each with
its pre-state. The order is the body order. -/
def blockVotes [BEq Root] (S : FFGSetup Root) (state : FFGBeaconState Root)
    (block : FFGWireBlock Root) : List (IncludedVote Root) :=
  match process_slots S.cfg S.preset state block.slot with
  | .error _ => []
  | .ok atSlot =>
    match process_parent_execution_payload S.preset atSlot block >>=
        fun state => process_block_header state block with
    | .error _ => []
    | .ok headed =>
      attestationVotes S block atSlot.latest_block_header.slot
        (process_execution_payload_bid headed block) block.attestations

/-- A concrete run from genesis. It records the accepted blocks in order and
every successful body attestation call. Slot processing without a block is
also a step, as in fork-choice checkpoint-state computation. -/
inductive Reachable [BEq Root] (S : FFGSetup Root) :
    List (FFGWireBlock Root) → List (IncludedVote Root) → FFGBeaconState Root → Prop
  | genesis : Reachable S [] [] S.genesis
  | slots {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
      {state next : FFGBeaconState Root} {target : Slot} :
      Reachable S blocks votes state →
      process_slots S.cfg S.preset state target = .ok next →
      Reachable S blocks votes next
  | block {blocks : List (FFGWireBlock Root)} {votes : List (IncludedVote Root)}
      {state next : FFGBeaconState Root} (block : FFGWireBlock Root) :
      Reachable S blocks votes state →
      state_transition S.cfg S.preset S.schedule S.oracle state block = .ok next →
      Reachable S (blocks ++ [block]) (votes ++ blockVotes S state block) next

/-- `TIMELY_TARGET_FLAG_INDEX`. Python: `specs/altair/beacon-chain.md:131-133`. -/
abbrev timelyTargetFlagIndex : ℕ := 1

/-- The canonical certificate inclusion relation: an included body vote whose
`process_attestation` call computed the timely-target flag. -/
def TargetIncluded [BEq Root] (S : FFGSetup Root) (votes : List (IncludedVote Root))
    (r : IncludedVote Root) : Prop :=
  r ∈ votes ∧ ∃ flags, r.flags S = .ok flags ∧ timelyTargetFlagIndex ∈ flags

/-- A supermajority link from `source` to `target`. The signers are distinct
active and unslashed registry validators. Each signer has a target-included
body vote with exactly this source and target. Their fixed weight is at least
two thirds of the fixed total active balance. -/
structure SupermajorityLink [BEq Root] (S : FFGSetup Root)
    (votes : List (IncludedVote Root)) (source target : Checkpoint Root) : Type where
  signers : Finset ValidatorIndex
  source_before_target : source.epoch < target.epoch
  signer_vote : ∀ i ∈ signers, ∃ r, TargetIncluded S votes r ∧ i ∈ r.attesters S ∧
    r.vote.data.source = source ∧ r.vote.data.target = target
  signer_active : ∀ i ∈ signers, i < S.scope.validators.length ∧
    is_active_validator (S.scope.validators.getD i default) target.epoch = true
  signer_unslashed : ∀ i ∈ signers, (S.scope.validators.getD i default).slashed = false
  supermajority : 2 * S.scope.activeBalance ≤ 3 * S.scope.weight signers

/-- Justification from the genesis stub by supermajority links of included
body votes. -/
inductive Justified [BEq Root] (S : FFGSetup Root) (votes : List (IncludedVote Root)) :
    Checkpoint Root → Prop
  | anchor : Justified S votes S.stub
  | link {source target : Checkpoint Root} :
      Justified S votes source → SupermajorityLink S votes source target →
      Justified S votes target

/-- The root of the latest accepted block at or before `slot`, or the genesis
block root. -/
def chainRootAt (genesisRoot : Root) (blocks : List (FFGWireBlock Root)) (slot : Slot) : Root :=
  (((blocks.filter fun block => decide (block.slot ≤ slot)).getLast?).map
    FFGWireBlock.root).getD genesisRoot

/-- Each block names the previous block, or the genesis block, as its parent. -/
def ParentLinked : Root → List (FFGWireBlock Root) → Prop
  | _, [] => True
  | parent, block :: blocks => block.parent_root = parent ∧ ParentLinked block.root blocks

/-- Root of the last accepted block, or the genesis block root. -/
def tipRoot (genesisRoot : Root) (blocks : List (FFGWireBlock Root)) : Root :=
  (blocks.getLast?.map FFGWireBlock.root).getD genesisRoot

/-- Slot of the last accepted block, or the genesis slot. -/
def tipSlot (blocks : List (FFGWireBlock Root)) : Slot :=
  (blocks.getLast?.map FFGWireBlock.slot).getD 0

/-- The provenance invariant of a reachable concrete state `state` with
accepted blocks `blocks` and included body votes `votes`. It states the
history facts (I1), the flag provenance facts (I2), and the justification
facts (I3). -/
structure ProvenanceInvariant [BEq Root] (S : FFGSetup Root)
    (blocks : List (FFGWireBlock Root)) (votes : List (IncludedVote Root))
    (state : FFGBeaconState Root) : Prop where
  validators_eq : state.validators = S.scope.validators
  blocks_ordered : blocks.Pairwise fun a b => a.slot < b.slot
  parent_linked : ParentLinked S.genesisRoot blocks
  header_root : state.latest_block_header.root = tipRoot S.genesisRoot blocks
  header_slot : state.latest_block_header.slot = tipSlot blocks
  blocks_le_header : ∀ b ∈ blocks, b.slot ≤ state.latest_block_header.slot
  header_le_slot : state.latest_block_header.slot ≤ state.slot
  ring : ∀ y, y < state.slot → state.slot ≤ y + S.preset.slots_per_historical_root →
    state.block_roots[y % S.preset.slots_per_historical_root]? =
      some (chainRootAt S.genesisRoot blocks y)
  target_epoch_le : ∀ r ∈ votes,
    r.vote.data.target.epoch ≤ compute_epoch_at_slot S.cfg state.slot
  current_flags : ∀ i, has_flag (state.current_epoch_participation.getD i 0) 1 = true ↔
    ∃ r, TargetIncluded S votes r ∧ i ∈ r.attesters S ∧
      r.vote.data.target.epoch = compute_epoch_at_slot S.cfg state.slot
  previous_flags : ∀ i, has_flag (state.previous_epoch_participation.getD i 0) 1 = true ↔
    ∃ r, TargetIncluded S votes r ∧ i ∈ r.attesters S ∧
      r.vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg state.slot
  current_sources : ∀ r, TargetIncluded S votes r →
    r.vote.data.target.epoch = compute_epoch_at_slot S.cfg state.slot →
    r.vote.data.source = state.current_justified_checkpoint
  previous_sources : ∀ r, TargetIncluded S votes r →
    r.vote.data.target.epoch + 1 = compute_epoch_at_slot S.cfg state.slot →
    r.vote.data.source = state.previous_justified_checkpoint
  target_on_chain : ∀ r, TargetIncluded S votes r →
    compute_start_slot_at_epoch S.cfg r.vote.data.target.epoch < state.slot ∧
    r.vote.data.target.root = chainRootAt S.genesisRoot blocks
      (compute_start_slot_at_epoch S.cfg r.vote.data.target.epoch)
  source_justified : ∀ r ∈ votes, Justified S votes r.vote.data.source
  early_sources : compute_epoch_at_slot S.cfg state.slot ≤ 2 →
    state.previous_justified_checkpoint = state.current_justified_checkpoint
  current_epoch_le : state.current_justified_checkpoint.epoch ≤
    compute_epoch_at_slot S.cfg state.slot - 1
  previous_epoch_le : state.previous_justified_checkpoint.epoch ≤
    compute_epoch_at_slot S.cfg state.slot - 2
  current_justified : Justified S votes state.current_justified_checkpoint
  previous_justified : Justified S votes state.previous_justified_checkpoint
  finalized_justified : Justified S votes state.finalized_checkpoint

/-- The block oracle authenticates every body vote of an accepted block. This
is a contract on the opaque oracle; it supplies no FFG state. -/
def OracleAuthenticatesBodies (S : FFGSetup Root)
    (Authentic : FFGWireBlock Root → FFGWireAttestation Root → Prop) : Prop :=
  ∀ pre block post, S.oracle.accepts pre block post = true →
    ∀ vote ∈ block.attestations, Authentic block vote

end FastConfirmation.Spec.ConcreteFFG

end
