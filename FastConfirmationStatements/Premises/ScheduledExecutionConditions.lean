module
public import FastConfirmationModel
public import FastConfirmationModel.Execution.ScheduledPrefixes
public import FastConfirmationStatements.Premises.Economics
public import FastConfirmationStatements.Premises.FFGState

@[expose] public section

/-! Defines well-formed scheduled blocks: wire block roots are injective labels. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
/-- Execution-level well-formedness: wire block roots are injective labels.
Equal labels identify equal block messages across scheduled block events and
the genesis store. This record does not assert a `hash_tree_root` equation. -/
structure WellFormedExecution (E : Execution Root) : Prop where
  blocks_root_injective : ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n →
    ∀ w' n' (b' : SignedBeaconBlock Root), Event.block b' ∈ E.schedule w' n' →
      b.root = b'.root → b.message = b'.message
  genesis_blocks_agree : ∀ w n (b : SignedBeaconBlock Root),
    Event.block b ∈ E.schedule w n → b.root ∈ E.genesis_store.block_roots →
      b.message = E.genesis_store.blocks b.root
  /-- No scheduled block reuses the unresolved parent root of a genesis-store
      block. In the concrete protocol, a block root commits to its block, so a
      block at that root is the anchor's lower-slot parent and is rejected by
      `on_block`'s finalized-slot gate. This projection treats roots as data and
      omits the pre-anchor block, so the coherence fact is explicit. -/
  anchor_parent_unscheduled : ∀ r ∈ E.genesis_store.block_roots,
    ∀ w n (b : SignedBeaconBlock Root), Event.block b ∈ E.schedule w n →
      b.root ≠ (E.genesis_store.blocks r).parent_root

end FastConfirmation.Spec

end
