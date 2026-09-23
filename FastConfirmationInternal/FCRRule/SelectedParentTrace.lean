module
public import FastConfirmationModel.Spec.ForkChoice

@[expose] public section

/-! Defines a direct parent edge trace with known roots at each step. -/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- A list of direct parent transitions from `start` to `result`.  Knownness is
stored at every node so completeness uses only ordinary well-formed tree
geometry. -/
inductive SelectedParentTrace (store : Store Root) :
    Root → Root → List (Root × Root) → Prop where
  | nil {r : Root} (hr : r ∈ store.block_roots) :
      SelectedParentTrace store r r []
  | cons {start next result : Root} {rest : List (Root × Root)}
      (hstart : start ∈ store.block_roots)
      (hnext : next ∈ store.block_roots)
      (hparent : (store.blocks next).parent_root = start)
      (tail : SelectedParentTrace store next result rest) :
      SelectedParentTrace store start result ((start, next) :: rest)

end FastConfirmation.Spec

end
