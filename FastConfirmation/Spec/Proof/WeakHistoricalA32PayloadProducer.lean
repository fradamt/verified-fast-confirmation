import FastConfirmation.Spec.Proof.WeakHistoricalA32Induction
import FastConfirmation.Spec.Proof.WeakSelectedJustifiedOrientation

/-!
# Spec / Proof / WeakHistoricalA32PayloadProducer

The one-line seam between the observer-side A3.2 write-back induction
(`WeakHistoricalA32Induction.lean`) and the weak-edge producer interface
`Weak.HistoricalA32PayloadProducerAt`
(`WeakSelectedJustifiedOrientation.lean`).

**Why this is its own module.**  The producer interface lives downstream of
the pre-query SIR layer, while everything with mathematical content here lives
upstream of it: the whole payload construction is
`Weak.observerCall_currentTargetHistoricalA32Payload`, proved in the induction
module, which imports nothing from the SIR side.  Splitting the seam off keeps
the induction independent of that layer; this file is a pure re-spelling and
contains no proof.

**Why the re-spelling is needed at all.**
`Execution.AcceptedHistoricalA32PayloadProducerAt` states its no-crossing side
condition over the *strong* `CurrentTargetAcceptedEdge`, hence over
`findLatestSelectedTrace`.  Rule delta 1 gives the observer a different
selector (`Weak.findLatestSelectedTrace`), so that side condition is a
different proposition with no bridge in the required direction.  Both
producers below have the very same proof — the antecedent is never read,
because the retained lineage invariant is strictly stronger than it — so the
two spellings cost one `fun` each.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-- The observer-side twin of
`Execution.completedPrefix_acceptedHistoricalA32PayloadProducerAt`: the weak
write-back induction instantiates the retained A3.2 payload producer on the
exact weak strict-selector result, in the weak-edge spelling the weak
call-site classifier consumes.

This is the bridge the rest of the weak wave was blocked on: its only missing
input was the observer-side instance of the historical write-back induction,
which `Weak.observerCall_currentLineage` now supplies. -/
noncomputable def observerCall_historicalA32PayloadProducerAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    {obs : ValidatorIndex}
    (hC : Weak.ObserverHistoricalA32CallAssumptions cfg ext E obs)
    (hfit : EpochEndsFitUint64 cfg)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hcoh : E.ObserverCoherence cfg ext obs)
    {n : Nat} (hcall : E.IsFCRCallAt cfg ext obs n)
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    Weak.HistoricalA32PayloadProducerAt cfg ext E B
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
  fun hcurrent _hnoCrossing =>
    Weak.observerCall_currentTargetHistoricalA32Payload cfg ext B hT hC hfit
      hanchor hboundary hcoh hcall hHn1 hinput hselector hcurrent

end Weak

end FastConfirmation.Spec
