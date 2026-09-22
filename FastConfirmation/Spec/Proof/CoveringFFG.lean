module
public import FastConfirmation.Spec.Proof.MicroSteps

@[expose] public section

/-!
# Spec / Proof / Covering FFG interface

The concrete covering package consumed by the anchoring bridge.  It lives in its
own small module so the selected-result closing path does not depend on the
legacy arbitrary-confirmed-root existence proof.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Execution

variable (E : Execution Root)

/-- A covering justified checkpoint and compatible head witness for `b` at
endpoint `(w, m)`. -/
def CoveringFFG (b : Root) (w : ValidatorIndex) (m : ℕ) : Prop :=
  ∃ (jcb : Checkpoint Root) (head : Root),
    JustifiedIn (E.store cfg ext w m) jcb ∧
    jcb.root ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root b) (get_node_for_root jcb.root) = true ∧
    head ∈ (E.store cfg ext w m).block_roots ∧
    is_ancestor (E.store cfg ext w m)
      (get_node_for_root head) (get_node_for_root b) = true ∧
    get_checkpoint_block cfg (E.store cfg ext w m) head
        (E.store cfg ext w m).justified_checkpoint.epoch =
      (E.store cfg ext w m).justified_checkpoint.root ∧
    ((E.store cfg ext w m).blocks b).slot ≤
      compute_start_slot_at_epoch cfg (E.store cfg ext w m).justified_checkpoint.epoch

end Execution

end FastConfirmation.Spec

end
