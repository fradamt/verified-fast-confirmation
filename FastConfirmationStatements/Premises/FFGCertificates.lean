module
public import FastConfirmationModel.Execution.Stake

@[expose] public section

/-!
# Spec / Model / FFGCertificates

Semantic certificate objects at the boundary between the transcribed fork-choice
state and Casper FFG.  They contain concrete scheduled attestation evidence;
accountable-safety consequences are proved from these objects and the ordinary
cryptographic/economic assumptions in `Proof/FFGCertificates.lean`.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)

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
