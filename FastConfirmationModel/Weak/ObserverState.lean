module
public import FastConfirmationModel.Execution.ScheduledPrefixes

@[expose] public section

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)
namespace Execution

/-- Stores produced by the observer's own validated handler run. -/
inductive ObserverCausalStore (E : Execution Root) (obs : ValidatorIndex) :
    Store Root → Prop
  | genesis : ObserverCausalStore E obs E.genesis_store
  | scheduledPrefix (p : ScheduledEventPrefix E) : p.node = obs →
      ObserverCausalStore E obs (p.store cfg ext)

/-- Keyed states of the observer's handler run. -/
def ObserverValidationState (E : Execution Root) (obs : ValidatorIndex)
    (state : BeaconState Root) : Prop :=
  ∃ store, ObserverCausalStore cfg ext E obs store ∧
    ((∃ root ∈ store.block_roots, store.block_states root = state) ∨
      ∃ checkpoint ∈ store.checkpoint_state_keys,
        store.checkpoint_states checkpoint = state)

end Execution
end FastConfirmation.Spec

end
