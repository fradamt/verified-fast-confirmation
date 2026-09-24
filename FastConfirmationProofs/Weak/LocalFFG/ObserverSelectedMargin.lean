module
public import FastConfirmationProofs.Weak.LocalFFG.ObserverHeadPaths

/-! The actual-run selected-margin premises follow from restricted inputs.
The only changed receiver is handled by the observer's local FFG certificate.
-/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {cfg : Config} {ext : Externals Root} {E : Execution Root}
variable {obs : ValidatorIndex}

private theorem unchanged_exclusion {v w : ValidatorIndex}
    (hv : v ≠ obs) (hw : w ≠ obs) (n m : ℕ) (r : Root) :
    PermanentBlockExclusion cfg ext (E.withoutObserver obs) v n r w m ↔
      PermanentBlockExclusion cfg ext E v n r w m := by
  unfold PermanentBlockExclusion
  simp only [withoutObserver_store cfg ext E obs v hv,
    withoutObserver_store cfg ext E obs w hw]
  rfl

private theorem unchanged_path {v w : ValidatorIndex}
    (hv : v ≠ obs) (hw : w ≠ obs) {n m : ℕ} {slot : Slot} {r : Root}
    (h : VotePathAdmissible cfg ext (E.withoutObserver obs) v n w m slot r) :
    VotePathAdmissible cfg ext E v n w m slot r := by
  induction h with
  | stop hr hn hl =>
    exact .stop (by simpa only [withoutObserver_store cfg ext E obs v hv] using hr)
      ((unchanged_exclusion hv hw n m _).not.mp hn)
      (by simpa only [withoutObserver_store cfg ext E obs v hv] using hl)
  | step hr hn hg _ ih =>
    rw [withoutObserver_store cfg ext E obs v hv] at ih
    exact .step (by simpa only [withoutObserver_store cfg ext E obs v hv] using hr)
      ((unchanged_exclusion hv hw n m _).not.mp hn)
      (by simpa only [withoutObserver_store cfg ext E obs v hv] using hg) ih

/-- Full all-receiver G4 is restored. The source is honest; the receiver
may be the actual non-honest observer. This is admissibility, not delivery. -/
theorem nonhonest_headPaths
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) :
    HonestHeadPathAdmissibility cfg ext E := by
  obtain ⟨B⟩ := localInputs.ffg
  intro v hv n hn w slot hb hwalk
  by_cases hw : w = obs
  · subst w
    exact B.honest_head_path hobs core localInputs hv hn hb hwalk
  · have hvne : v ≠ obs := by intro he; subst v; exact hobs hv
    have hvR : v ∈ (E.withoutObserver obs).honest :=
      (withoutObserver_honest hobs).symm ▸ hv
    have hwalkR : WalkKnown ((E.withoutObserver obs).store cfg ext v n) slot
        (get_head cfg ((E.withoutObserver obs).store cfg ext v n)).root := by
      simpa only [withoutObserver_store cfg ext E obs v hvne n] using hwalk
    have hp := core.base.domain.honest_head_paths v hvR n hn w slot hb hwalkR
    have hactual := unchanged_path hvne hw hp
    rw [withoutObserver_store cfg ext E obs v hvne n] at hactual
    exact hactual

/-- The old selected-margin record is a derived result for the actual run.
Its type and every existing consumer stay unchanged. -/
def nonhonest_selectedMargin
    (hobs : obs ∉ E.honest) (core : E.WeakObserverRestrictedCore cfg ext obs)
    (localInputs : E.ObserverLocalInputs cfg ext obs) :
    SelectedMarginAssumptions cfg ext E where
  genesis := core.base.genesis
  wellFormed := localInputs.wellFormed cfg ext core.base.wellFormed
  whole_seconds := core.base.whole_seconds
  honest_behavior := nonhonest_honestBehavior hobs core localInputs
  synchrony := nonhonest_synchrony hobs core
  externals_coherence := nonhonest_externals hobs core
  static_validators := nonhonest_staticValidators core
  byzantine_bound := nonhonest_byzantineBound hobs core
  domain := {
    honest_head_paths := nonhonest_headPaths hobs core localInputs
    justified_root_known := by
      intro w hw n hn
      have hne : w ≠ obs := by intro he; subst w; exact hobs hw
      have hwR : w ∈ (E.withoutObserver obs).honest :=
        (withoutObserver_honest hobs).symm ▸ hw
      simpa only [withoutObserver_store cfg ext E obs w hne n] using
        core.base.domain.justified_root_known w hwR n hn
    justified_checkpoint_cached := by
      intro w hw n hn
      have hne : w ≠ obs := by intro he; subst w; exact hobs hw
      have hwR : w ∈ (E.withoutObserver obs).honest :=
        (withoutObserver_honest hobs).symm ▸ hw
      simpa only [withoutObserver_store cfg ext E obs w hne n] using
        core.base.domain.justified_checkpoint_cached w hwR n hn }

/-- The old observer premise record follows from the restricted core and
the listed local input contracts. The FFG interpretation is separate. -/
def nonhonest_weakObserverPremises
    (hobs : obs ∉ E.honest) (premises : E.WeakObserverRestrictedPremises cfg ext obs) :
    E.WeakObserverPremises cfg ext obs where
  base := nonhonest_selectedMargin hobs premises.core premises.local_inputs
  genesis := premises.core.genesis
  validity := premises.local_inputs.validity
  committees_agree := premises.local_inputs.committees_agree

end Execution
end FastConfirmation.Spec
end
