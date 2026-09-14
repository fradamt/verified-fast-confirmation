import FastConfirmation.Spec.Model.Config
import FastConfirmation.Spec.Model.Types
import FastConfirmation.Spec.Model.ForkChoice
import FastConfirmation.Spec.Model.FCRStore
import FastConfirmation.Spec.Model.LMDHelpers
import FastConfirmation.Spec.Model.FFGHelpers
import FastConfirmation.Spec.Model.Confirmation
import FastConfirmation.Spec.Model.Handlers
import FastConfirmation.Spec.Model.Validator
import FastConfirmation.Spec.Model.Execution
import FastConfirmation.Spec.Model.AcceptedExecution
import FastConfirmation.Spec.Model.Assumptions
import FastConfirmation.Spec.Model.FFGCertificates
import FastConfirmation.Spec.Model.FFGStateSemantics
import FastConfirmation.Spec.Model.WeakSynchrony

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
