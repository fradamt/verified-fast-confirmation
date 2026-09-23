module
public import FastConfirmationModel.Execution.Run

@[expose] public section

/-!
# Elementary checkpoint geometry

This module contains structural facts about checkpoint values which do not
depend on the selected FCR pipeline or on any safety conclusion.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

omit [LinearOrder Root] [Inhabited Root] in
/-- Checkpoints are determined by their epoch and root fields. -/
theorem checkpoint_eq_of_epoch_root_eq
    {a b : Checkpoint Root}
    (hepoch : a.epoch = b.epoch) (hroot : a.root = b.root) : a = b := by
  cases a
  cases b
  simp_all

end FastConfirmation.Spec

end
