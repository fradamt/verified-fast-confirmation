module
public import FastConfirmation.Spec.Model.Config
public import FastConfirmation.Spec.Model.Types
public import FastConfirmation.Spec.Model.ForkChoice
public import FastConfirmation.Spec.Model.FCRStore
public import FastConfirmation.Spec.Model.LMDHelpers
public import FastConfirmation.Spec.Model.FFGHelpers
public import FastConfirmation.Spec.Model.Confirmation
public import FastConfirmation.Spec.Model.Handlers
public import FastConfirmation.Spec.Model.Validator
public import FastConfirmation.Spec.Model.Execution
public import FastConfirmation.Spec.Model.AcceptedExecution
public import FastConfirmation.Spec.Model.Assumptions
public import FastConfirmation.Spec.Model.FFGCertificates
public import FastConfirmation.Spec.Model.FFGStateSemantics

/-!
# Spec / Model — facade

The complete executable model of the Fast Confirmation Rule consensus spec
(`consensus-specs/specs/phase0/fast-confirmation.md` @ public commit
`30aa65f`) together
with its dynamics: the fork-choice environment and handlers
(`fork-choice.md`), honest validator behavior (`validator.md`), and the
execution/synchrony model. Definitions only — the faithfulness review surface
is the per-function mapping in `docs/spec-annotation.md`.
-/
