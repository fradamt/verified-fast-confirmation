module
public import FastConfirmationProofs.Weak.Safety.WeakObservedRestartDynamicSafety
public import FastConfirmationProofs.Weak.Safety.WeakTrajectorySafety

@[expose] public section

/-!
# Spec / Proof / WeakObservedResetSeedSafety

Stage 6 of the **weak full-rule** effort (`docs/weak-full-rule.md`): the
assembly of stages 2–5 into `Weak.ObservedResetSeedSafety` itself, and the
corollary form of the headline fold with that obligation discharged.

`WeakTrajectorySafety.lean` closes five of the six cells of the weak full-rule
induction and pins the sixth — the observed-reset branch's `hbase` — as the
named `Prop` `Weak.ObservedResetSeedSafety`.  Every ingredient of that `Prop`
now exists:

* the banking invariant at the *query* store, from
  `Weak.weakFcrStep_certifiedBankedJustification`, so neither arm assumes a
  certificate the trajectory cannot produce;
* the **anchor arm** (`Weak.ObservedResetCandidateInputAt.safeFrom_of_anchorArm`,
  stage 3), which closes outright at the trusted anchor and never reaches the
  epoch split;
* the **adoption law** (`Weak.ObservedResetCandidateInputAt.
  guardedObservedAdoption`, stage 2), which orders the banked checkpoint's
  epoch below every in-horizon honest endpoint's realized justified epoch at
  the call's own boundary second;
* the **same-epoch arm** (`…head_of_sameEpoch`, stage 4) and the
  **later-epoch arm** (`…head_of_laterEpoch`, stage 5).

The composition is the strong proof's own skeleton with the querying node's
honesty binder gone: run `Execution.safeFrom_of_headStep_at`, transport the
adoption bound forward with `Execution.store_justified_epoch_mono`, and split
it with `Nat.eq_or_lt_of_le`.  No index or temporal adjustment is needed — the
adoption law is already stated at `n + 1`, which is exactly the second
`safeFrom_of_headStep_at` quantifies from.

## Premise surface

`Weak.observedResetSeedSafety_of_acceptedDynamics` takes only floor data: the
selected-margin assumptions `hA`, the accepted FFG semantic bundle `B` and its
anchor alignment (`hanchor`, `hboundary`),
and the observer's own committee agreement
(`Execution.ObserverCoherence.committees_agree`).  That is the whole signature:
the scheduled-prefix trajectory assumptions it runs on are *derived* from `hA`
inside the proof
(`Execution.ScheduledPrefixPremises.of_selectedMarginAssumptions`),
never taken as a premise.  Every one of those inputs is already a premise of
`Execution.weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold`, so the
discharged fold below has *strictly smaller* premise surface than the
conditional one: the obligation disappears and nothing is added.  In particular
there is still no honesty binder at `obs` — the observer is arbitrary and may
be honest.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

namespace Weak

/-! ## Stage 6 — the obligation, discharged -/

/-- **Observed-reset seed safety at a possibly-Byzantine observer.**

At a genuine weak FCR call whose candidate input came from the epoch-start
restart branch, the restarted-from root is an ancestor of every in-horizon
honest node's fork-choice head from the call's own second onward.

This is the weak twin of
`Execution.ObservedResetCandidateInputAt.safeFrom_of_acceptedDynamics`
(`AcceptedObservedRestartDynamicSafety.lean`) with the querying node's honesty
binder dropped, and it is the theorem that removes the single open obligation
of the weak full-rule fold.  The three places the strong proof reads that
node's honesty — the two sender-side `NextSlotSynchronyPremises.block_relay` uses
and the observed-reset *realization* record behind them — are replaced,
respectively, by broadcast-certificate dissemination
(`Weak.bankedSupplier_known_at_all_honest_endpoints_at_observer`,
`Weak.bankedRoot_known_at_all_honest_endpoints_at_observer`), rule delta 5's
own `banked_known` (`Weak.weakFcrStep_observed_known`), and the accepted `AU`
geometry of the query head's unrealized justification
(`Weak.ObservedResetCandidateInputAt.bankedAU` and its two corollaries).

The body is the strong proof's skeleton: split the banking invariant, close the
anchor arm outright, and otherwise run the slot-indexed strong induction
`Execution.safeFrom_of_headStep_at` and split the endpoint's realized justified
epoch against the banked one. -/
theorem observedResetSeedSafety_of_acceptedDynamics
    {E : Execution Root} (hA : SelectedMarginAssumptions cfg ext E)
    (hgen : ∃ (anchorState : BeaconState Root) (anchorBlock : SignedBeaconBlock Root),
      E.genesis_store = get_forkchoice_store cfg anchorState anchorBlock ∧
      anchorState.slot = anchorBlock.message.slot ∧
      ext.AnchorCommitsToState anchorBlock.message anchorState ∧
      anchorBlock.message.parent_root ≠ anchorBlock.root)
    (B : CausalPrefixFFGInterpretation cfg ext E)

    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : Execution.TrustedAnchorBoundaryAligned (cfg := cfg) (E := E)
      (anchor := B.anchor))
    {obs : ValidatorIndex}
    (hcomm : ∀ k : ℕ, E.WithinHorizon cfg k → ∀ s : Slot, E.SlotWithinHorizon cfg s →
      get_slot_committee cfg ext (E.store cfg ext obs k) s = E.committee s) :
    Weak.ObservedResetSeedSafety cfg ext E obs := by
  have hT : E.ScheduledPrefixPremises cfg ext :=
    Execution.ScheduledPrefixPremises.of_selectedMarginAssumptions
      cfg ext E hA hgen
  intro n hHn1 hcall trace hinput
  rcases Weak.weakFcrStep_certifiedBankedJustification cfg ext hA B hT hanchor
    hboundary hHn1 hcall with hgenesisArm | hcertified
  · exact Weak.ObservedResetCandidateInputAt.safeFrom_of_anchorArm cfg ext B hT
      hanchor hboundary hinput hgenesisArm
  · obtain ⟨hcert⟩ := hcertified
    have hadoption :=
      Weak.ObservedResetCandidateInputAt.guardedObservedAdoption cfg ext hA B hT
        hanchor hboundary hA.synchrony  hcomm hinput hcert
    rw [hinput.input_eq]
    apply E.safeFrom_of_headStep_at cfg ext
    intro w hw m hnm hHm hIH
    have hcJ : (E.weakFcrStep cfg ext obs n
          ).current_epoch_observed_justified_checkpoint.epoch ≤
        (E.store cfg ext w m).justified_checkpoint.epoch :=
      (hadoption w hw hHn1).trans (E.store_justified_epoch_mono cfg ext w hnm)
    rcases Nat.eq_or_lt_of_le hcJ with heq | hlt
    · exact Weak.ObservedResetCandidateInputAt.head_of_sameEpoch cfg ext hA B hT
        hanchor hboundary hA.synchrony  hcomm hinput (Or.inr ⟨hcert⟩) hw hnm
        hHm heq
    · exact Weak.ObservedResetCandidateInputAt.head_of_laterEpoch cfg ext hA B hT
        hanchor hboundary hA.synchrony  hcomm hHn1 hcall hinput
        (Or.inr ⟨hcert⟩) hw hnm hHm hIH hlt

end Weak

namespace Execution

variable (E : Execution Root)

/-! ## The weak full-rule fold with a derived reset seed -/

/-- **The weak full-rule safety theorem with a derived reset seed.**

Every root the observer's weak FCR trajectory holds, at every in-horizon
second, is an ancestor of every in-horizon honest node's fork-choice head from
the following slot onward — at an observer that is granted nothing (no honesty,
no guaranteed delivery), and whose every use of synchrony is licensed by a
broadcast certificate.

The honest head-root knownness needed by certificate dissemination follows
from `SelectedMarginDomain.justified_root_known`. No strong `E.fcr` cache
interface is required by this theorem.

`Execution.weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold` with its
last premise discharged by `Weak.observedResetSeedSafety_of_acceptedDynamics`.
Since `docs/weak-final-wave.md` W6 the call contract carries no observer-side
normative proviso, because the historical A3.2 crossing payload is manufactured
lazily at the consuming call from the fold's own strictly earlier output.  The
proviso machinery has since been deleted outright.

The premise list is exactly the conditional fold's minus
`hOR : Weak.ObservedResetSeedSafety`; the obligation's own inputs (`hW.base`,
`B`, `hanchor`, `hboundary`, and the observer's committee agreement
`hW.committees_agree`) were already carried.  The strong fold's
observer-honesty binder `hv : v ∈ E.honest` does not appear.

That list is, in full: `B` (accepted FFG semantics), `hanchor`,
`hboundary`, `hDelay`, `hpaper`, `P`, `V`, `hW`
(`WeakObserverPremises` = the selected-margin floor plus committee readback
at the observer's own store), `hCbase`
(`WeakCompletedFCRCallSupplement`: the two phase-0
coherence contracts, the balance floor, and vote-delivery lookahead) and `hfit` — **ten** premises.
Five surface duplications are gone: `hT` is *derived* from `hW.base`
(`Execution.ScheduledPrefixPremises.of_selectedMarginAssumptions`),
`hwalkDomain : PostAnchorHonestVoteTargetWalkDomain` is *derived* from
`hW.base`/`hanchor`/`hboundary`
(`Execution.postAnchorHonestVoteTargetWalkDomain_of_selectedMarginAssumptions`),
`hanchorExact : B.anchor = B.state.C B.anchor.root B.anchor.epoch` is *derived*
from `B`/`hT`/`hanchor`/`hboundary`
(`Execution.acceptedAnchorExact_of_trajectory` — causal checkpoint reflection at
the trusted anchor, so it restates `hboundary` through the checkpoint walk and
is not an independent premise; `docs/plumbing-spec-citations.md` P-10),
the standalone `hphase0`/`hboundaryPhase` are read off `hCbase`, and the
`synchrony`/`static_validators`/`byzantine_bound` fields of the full 7-field
call contract are read off `hW.base` when it is rebuilt internally.

Observer-wise the premise surface is exactly `hW : WeakObserverPremises` —
committee readback at the observer's own store, nothing else; `obs` is
arbitrary and may be honest.  `ObserverCoherence.justified_root_known` is
*derived* from `B`/`hT`/`hanchor`/`hboundary` inside the fold
(`WeakObserverPremises.toMarginAssumptions`), never assumed. -/
theorem weak_confirmed_root_safe_from_next_slot
    (B : CausalPrefixFFGInterpretation cfg ext E)

    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (hCbase : E.WeakCompletedFCRCallSupplement cfg ext)
    (hfit : EpochEndsFitUint64 cfg) :
    ∀ n : ℕ, E.WithinHorizon cfg n →
      E.WeakConfirmedSafeFromFollowingSlot cfg ext obs n :=
  E.weakConfirmed_safeFromFollowingSlot_of_weakFullRuleFold cfg ext B
    hanchor hboundary hDelay hpaper P V hW
    hCbase hfit
    (Weak.observedResetSeedSafety_of_acceptedDynamics cfg ext hW.base hW.genesis B
      hanchor hboundary hW.committees_agree)

/-- Endpoint form of the weak full-rule theorem, matching the
paper's timing: the observer's weak confirmed root at second `n` is canonical
at every in-horizon honest endpoint in a strictly later slot.  Weak twin of
`Execution.confirmed_head_of_acceptedActualFCRFold_nextSlot`, with no honesty
binder at `obs` and no residual reset-seed obligation. Honest head-root
knownness follows from the selected-margin domain. -/
theorem weak_confirmed_root_on_honest_heads_from_next_slot
    (B : CausalPrefixFFGInterpretation cfg ext E)

    (hanchor : B.anchor = E.genesis_store.justified_checkpoint)
    (hboundary : TrustedAnchorBoundaryAligned (cfg := cfg)
      (E := E) (anchor := B.anchor))
    (hDelay : E.RealizedFinalizationDelay cfg ext B)
    (hpaper : B.state.PaperA32Inclusion cfg ext)
    (P : EpochCheckpointClosure B.anchor
      (E.AcceptedRoot cfg ext) B.state.C)
    (V : B.state.ExactLinkValidity)
    {obs : ValidatorIndex}
    (hW : E.WeakObserverPremises cfg ext obs)
    (hCbase : E.WeakCompletedFCRCallSupplement cfg ext)
    (hfit : EpochEndsFitUint64 cfg)
    {n : ℕ} {w : ValidatorIndex} (hw : w ∈ E.honest) {m : ℕ}
    (hnm : n ≤ m)
    (hnext : E.slot_at cfg n + 1 ≤ E.slot_at cfg m)
    (hHm : E.WithinHorizon cfg m) :
    is_ancestor (E.store cfg ext w m)
      (get_head cfg (E.store cfg ext w m))
      (get_node_for_root (E.weakConfirmed cfg ext obs n)) = true :=
  E.weakConfirmed_head_of_weakFullRuleFold_nextSlot cfg ext B  hanchor
    hboundary hDelay hpaper P V hW
    hCbase hfit
    (Weak.observedResetSeedSafety_of_acceptedDynamics cfg ext hW.base hW.genesis B
      hanchor hboundary hW.committees_agree)
    hw hnm hnext hHm

end Execution

end FastConfirmation.Spec

end
