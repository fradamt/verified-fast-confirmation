module
public import FastConfirmation.Spec.Proof.WeakHistoricalA32Induction
public import FastConfirmation.Spec.Proof.WeakSelectedJustifiedOrientation

@[expose] public section

/-!
# Spec / Proof / WeakHistoricalA32PayloadProducer

The one-line seam between the observer-side A3.2 write-back induction
(`WeakHistoricalA32Induction.lean`) and the weak-edge producer interface
`Weak.HistoricalCurrentTargetCertificateProducerAt`
(`WeakSelectedJustifiedOrientation.lean`).

**Why this is its own module.**  The producer interface lives downstream of
the pre-query SIR layer, while everything with mathematical content here lives
upstream of it: the whole payload construction is
`Weak.observerCall_currentTargetHistoricalCertificate`, proved in the
induction module, which imports nothing from the SIR side.  Splitting the seam off keeps
the induction independent of that layer; this file is a pure re-spelling and
contains no proof.

**Why the re-spelling is needed at all.**
`Execution.HistoricalCurrentTargetCertificateProducerAt` states its
no-crossing side condition over the *strong* `CurrentTargetAcceptedEdge`, hence
over `findLatestSelectedTrace`.  Rule delta 1 gives the observer a different
selector (`Weak.findLatestSelectedTrace`), so that side condition is a
different proposition with no bridge in the required direction; the weak
spelling `Weak.HistoricalCurrentTargetCertificateProducerAt` is the one the
weak call-site classifier consumes.

Since `docs/weak-final-wave.md` W4/W5 the interface is the *certificate*, not
the retained payload: the `currentHistorical` arm of the classifier read only
`hpayload.certified.some`, and taking that directly is what lets the lazy
route supply the arm through the no-crossing branch, which creates no payload
at the consuming call at all.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

variable (cfg : Config) (ext : Externals Root)

namespace Weak

variable {E : Execution Root}

/-- The observer-side twin of
`Execution.completedPrefix_acceptedHistoricalCertificateProducerAt`, in the
weak-edge spelling the weak call-site classifier consumes.

Pure re-spelling of `Weak.observerCall_currentTargetHistoricalCertificate`;
both routes (eager and lazy) flow through it unchanged, the only difference
being which `certElim` is supplied. -/
theorem observerCall_historicalCertificateProducerAt
    (B : ExactPrefixAcceptedFFGSemantics cfg ext E)
    (hT : E.ScheduledPrefixTrajectoryAssumptions cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.ObserverLineageRouteAt cfg ext E B obs Cert Supp)
    {n : Nat}
    (certElim : ∀ {c : Checkpoint Root}, Cert n c →
      Nonempty (CertifiedJustified cfg E B.anchor c))
    (hHn1 : E.WithinHorizon cfg (n + 1))
    (hinput : (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved ∈
      (E.weakFcrStep cfg ext obs n).store.block_roots)
    (hselector : Weak.StrictSelectorAdvanceAt cfg ext
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n)) :
    Weak.HistoricalCurrentTargetCertificateProducerAt cfg ext E B.anchor
      (E.weakFcrStep cfg ext obs n)
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).afterObserved
      (E.weakGetLatestConfirmedTraceAt cfg ext obs n).result :=
  fun hcurrent hnoCrossing =>
    Weak.observerCall_currentTargetHistoricalCertificate cfg ext B hT hphase
      hanchor hboundary hcoh hroute certElim hHn1 hinput hselector hcurrent
      hnoCrossing

end Weak

end FastConfirmation.Spec

end
