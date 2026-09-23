module
public import FastConfirmation.Spec.Model.FFGCertificates

@[expose] public section

/-!
# FFGCertificates model facts

Proofs about Model/FFGCertificates. Read the corresponding Model file first.
-/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config)
namespace Execution
variable (E : Execution Root)
theorem RootDescends.trans {a b c : Root}
    (hab : E.RootDescends a b) (hbc : E.RootDescends b c) :
    E.RootDescends a c := by
  induction hab with
  | refl => exact hbc
  | step hedge _ ih => exact .step hedge (ih hbc)

end Execution
end FastConfirmation.Spec

end
