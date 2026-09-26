module
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-!
Defines included FFG link certificates and execution block ancestry.
These objects form the boundary between the transcribed fork-choice
state and Casper FFG.  They contain concrete scheduled attestation evidence;
accountable-safety consequences are proved from these objects in
`FastConfirmationProofs/FFG/Certificates/FFGCertificates.lean`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

/-- The FFG reading of a raw checkpoint. Real genesis states carry the stub
`Checkpoint(GENESIS_EPOCH, ZERO_HASH)`, and honest attestations made before
the first justification name it as their source (`phase0/validator.md`,
`get_attestation_data`). `get_forkchoice_store` instead records
`Checkpoint(GENESIS_EPOCH, anchor_root)` (`phase0/fork-choice.md:217-244`).
The FFG interpretation identifies all `GENESIS_EPOCH` checkpoints. Every other
raw checkpoint reads only as itself. This wider genesis-epoch identification is safe for slashability because slashability compares checkpoint epochs, while raw roots remain unchanged in handlers. Executable handlers and wire attestations
keep the raw value; only the semantic reads use this relation. -/
def CheckpointReadsAs {Root : Type*} (raw c : Checkpoint Root) : Prop :=
  raw = c ∨ (raw.epoch = GENESIS_EPOCH ∧ c.epoch = GENESIS_EPOCH)

namespace Execution

variable (E : Execution Root)

/-- A parent edge in the concrete execution's block universe.  Edges come
either from a block in the trusted initial store or from a scheduled wire
block; `WellFormedExecution` makes the latter roots genuine commitments. -/
def ParentEdge (child parent : Root) : Prop :=
  (∃ r ∈ E.genesis_store.block_roots,
      child = r ∧ parent = (E.genesis_store.blocks r).parent_root) ∨
  (∃ (w : ValidatorIndex) (n : ℕ) (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w n ∧
      child = b.root ∧ parent = b.message.parent_root)

/-- Reflexive-transitive descent in the execution's concrete parent graph. -/
inductive RootDescends : Root → Root → Prop
  | refl (r : Root) : RootDescends r r
  | step {child parent ancestor : Root} :
      E.ParentEdge child parent →
      RootDescends parent ancestor →
      RootDescends child ancestor

end Execution

end FastConfirmation.Spec

end
