module
public import FastConfirmationModel.Spec.BeaconChain.ConcreteRun

@[expose] public section

/-! Defines the provenance invariant of reachable concrete FFG runs and the
oracle body-authentication contract. The run vocabulary is in
`FastConfirmationModel.Spec.BeaconChain.ConcreteRun`. -/

namespace FastConfirmation.Spec.ConcreteFFG
open FastConfirmation.Spec

variable {Root : Type}

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
