module
public import FastConfirmationStatements.Weak.RestrictedObserver

/-! Observer schedule independence for the restricted weak premise design. -/

@[expose] public section
namespace FastConfirmation.Spec
namespace Execution
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable {E E' : Execution Root} {obs : ValidatorIndex}

omit [LinearOrder Root] [Inhabited Root] in
/-- The erased view has no dependence on the actual observer schedule. -/
theorem SameOutsideObserver.withoutObserver_eq
    (h : SameOutsideObserver E E' obs) :
    E.withoutObserver obs = E'.withoutObserver obs := by
  rcases E with ⟨horizon, genesis, schedule, honest, committee, vote⟩
  rcases E' with ⟨horizon', genesis', schedule', honest', committee', vote'⟩
  rcases h with ⟨hh, hg, ho, hc, hv, hs⟩
  dsimp at hh hg ho hc hv hs
  cases hh
  cases hg
  cases ho
  cases hc
  cases hv
  unfold withoutObserver
  congr 1
  funext v n
  by_cases hvo : v = obs
  · simp [hvo]
  · simp only [if_neg hvo]
    exact congrFun (hs v hvo) n

variable (cfg : Config) (ext : Externals Root)

/-- A non-honest observer does not change the honest set in the restricted view. -/
theorem withoutObserver_honest (hobs : obs ∉ E.honest) :
    (E.withoutObserver obs).honest = E.honest := by
  apply Finset.ext
  intro v
  simp only [withoutObserver, Finset.mem_erase]
  constructor
  · exact And.right
  · intro hv
    exact ⟨by intro heq; subst v; exact hobs hv, hv⟩

/-- The shared premise record transfers without any observer input hypothesis. -/
def WeakObserverRestrictedCore.transport
    (h : SameOutsideObserver E E' obs)
    (c : E.WeakObserverRestrictedCore cfg ext obs) :
    E'.WeakObserverRestrictedCore cfg ext obs := by
  change WeakRestrictedNetworkPremises cfg ext (E'.withoutObserver obs)
  rw [← h.withoutObserver_eq]
  exact c

/-- Exact premise independence oracle. The replacement execution keeps the
signed votes and every other node's schedule. Its listed local input fields
are supplied from its own run. No observer delivery hypothesis is needed. -/
def WeakObserverRestrictedPremises.observer_independent
    (h : SameOutsideObserver E E' obs)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs)
    (local' : E'.ObserverLocalInputs cfg ext obs) :
    E'.WeakObserverRestrictedPremises cfg ext obs where
  core := premises.core.transport cfg ext h
  local_inputs := local'

/-- The non-honest observer and the restricted premises remain independent of
changes to its input schedule. No timed receipt at the observer is assumed. -/
theorem weakObserverRestrictedPremises_observer_independent
    (hobs : obs ∉ E.honest)
    (h : SameOutsideObserver E E' obs)
    (premises : E.WeakObserverRestrictedPremises cfg ext obs)
    (local' : E'.ObserverLocalInputs cfg ext obs) :
    obs ∉ E'.honest ∧ Nonempty (E'.WeakObserverRestrictedPremises cfg ext obs) :=
  ⟨h.honest ▸ hobs, ⟨premises.observer_independent cfg ext h local'⟩⟩

/-- Erasure preserves every other node's actual store, at every second. -/
theorem withoutObserver_store (E : Execution Root) (obs w : ValidatorIndex)
    (hw : w ≠ obs) (n : ℕ) :
    (E.withoutObserver obs).store cfg ext w n = E.store cfg ext w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [store, withoutObserver, if_neg hw, time_at] at ih ⊢
    rw [ih]

/-- Erasure preserves the weak cache at every other node. This theorem does
not compare the strong cache with the weak cache. -/
theorem withoutObserver_weakFcr (E : Execution Root) (obs w : ValidatorIndex)
    (hw : w ≠ obs) (n : ℕ) :
    (E.withoutObserver obs).weakFcr cfg ext w n = E.weakFcr cfg ext w n := by
  induction n with
  | zero => simp only [weakFcr, withoutObserver_store cfg ext E obs w hw]
  | succ n ih =>
    simp only [weakFcr, withoutObserver_store cfg ext E obs w hw, ih]

/-- The local block clauses recover execution well-formedness on the actual
run. They need no observer delivery or source-relay premise. -/
theorem ObserverLocalInputs.wellFormed
    (core : WellFormedExecution (E.withoutObserver obs))
    (localInputs : E.ObserverLocalInputs cfg ext obs) : WellFormedExecution E := by
  have event_other : ∀ w, w ≠ obs → ∀ n (b : SignedBeaconBlock Root),
      Event.block b ∈ E.schedule w n →
      Event.block b ∈ (E.withoutObserver obs).schedule w n := by
    intro w hw n b hb
    simpa only [withoutObserver, if_neg hw] using hb
  constructor
  · intro w n b hb w' n' b' hb' heq
    by_cases hw : w = obs
    · subst w
      exact localInputs.block_labels n b hb w' n' b' hb' heq
    · by_cases hw' : w' = obs
      · subst w'
        exact (localInputs.block_labels n' b' hb' w n b hb heq.symm).symm
      · exact core.blocks_root_injective w n b (event_other w hw n b hb)
          w' n' b' (event_other w' hw' n' b' hb') heq
  · intro w n b hb hgen
    by_cases hw : w = obs
    · subst w
      exact localInputs.genesis_blocks n b hb hgen
    · exact core.genesis_blocks_agree w n b (event_other w hw n b hb) hgen
  · intro r hr w n b hb
    by_cases hw : w = obs
    · subst w
      exact localInputs.anchor_parent r hr n b hb
    · exact core.anchor_parent_unscheduled r hr w n b (event_other w hw n b hb)

end Execution
end FastConfirmation.Spec
end
