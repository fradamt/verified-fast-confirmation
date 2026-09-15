import FastConfirmation.Spec.Model
import FastConfirmation.Spec.ProvenTheorems
import FastConfirmation.Spec.Proof.AcceptedStrictPrefixExtraQueryCounterexample
import FastConfirmation.Spec.Proof.AcceptedPinnedEconomicsStrictPrefixExtraQueryCounterexample
import FastConfirmation.Spec.Proof.WeakOneShotSafety
import FastConfirmation.Spec.Proof.WeakFinalizedInput
import FastConfirmation.Spec.Proof.WeakFreshSupport

/-!
# Spec — facade

The consensus-spec model of the Fast Confirmation Rule: executable rule and
fork-choice functions, scheduled multi-node executions, explicit assumptions,
and the primary accepted-execution theorem
`acceptedSpec_safety_next_slot : AcceptedSpec_Safety_next_slot`. Its premise
surface is `AcceptedActualFCRNextSlotSafetyAssumptions`; finalized and observed
reset safety are derived rather than assumed.

This development is mechanically independent of the abstract paper model in
`FastConfirmation/Paper/`: it imports none of those modules, and no formal
refinement theorem between the two models is claimed.

The facade also exports strict-prefix counterexamples delimiting the theorem.
A source-permitted pre-update query can return a root which is not on another
honest endpoint's head at that exact global action position, even under the
proved structural, honest-behavior, synchrony, and Byzantine-bound packages.
The second finite regression uses the pinned proposer-boost and confirmation-
Byzantine-threshold values `40`/`25`; it deliberately remains a small
four-slot preset rather than claiming to instantiate every field of
`mainnet_config`. These counterexamples do not touch the accepted mandatory
boundary-call proof path: the primary stored-output theorem starts at the next
slot, after the modeled synchrony deadline.
-/
