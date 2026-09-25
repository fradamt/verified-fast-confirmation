module
public import FastConfirmationStatements.Traces

@[expose] public section

/-! Defines the previous-loop edges retained by the selected FCR wrapper trace. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- A previous-loop edge retained by the complete wrapper trace. -/
def PreviousEpochSelectedEdge (fcrStore : FastConfirmationStore Root)
    (latestConfirmedRoot a c : Root) : Prop :=
  (a, c) ∈ (findLatestSelectedTrace cfg ext fcrStore latestConfirmedRoot).2.1

end FastConfirmation.Spec

end
