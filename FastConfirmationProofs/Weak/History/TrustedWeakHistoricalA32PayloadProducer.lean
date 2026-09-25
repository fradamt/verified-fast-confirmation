module
public import FastConfirmationProofs.Weak.History.WeakHistoricalA32PayloadProducer
public import FastConfirmationProofs.Weak.History.TrustedWeakHistoricalA32Induction

@[expose] public section
namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Weak
variable {E : Execution Root} {trusted : Store Root → Prop}

theorem trusted_observerCall_historicalCertificateProducerAt
    (B : TrustedCausalPrefixFFGInterpretation cfg ext E trusted)
    (hT : E.ScheduledPrefixPremises cfg ext)
    (hphase : Phase0SourceCoherence cfg ext)
    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    {obs : ValidatorIndex} (hcoh : E.ObserverCoherence cfg ext obs)
    {Cert : ℕ → Checkpoint Root → Prop} {Supp : ℕ → Root → Epoch → Prop}
    (hroute : Weak.TrustedObserverLineageRouteAt cfg ext E B obs Cert Supp)
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
    Weak.trusted_observerCall_currentTargetHistoricalCertificate cfg ext B hT hphase
      hanchor hboundary hcoh hroute certElim hHn1 hinput hselector hcurrent
      hnoCrossing

end Weak
end FastConfirmation.Spec
end
