module
public import FastConfirmationModel.Execution.ScheduledPrefixes

@[expose] public section

/-! Defines anchor-registry balances and committee-union weights for scheduled executions. Python: `specs/phase0/beacon-chain.md`, `BeaconState` and balance helpers. -/

namespace FastConfirmation.Spec
variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : BeaconFunctionInterface Root)
namespace Execution
variable (E : Execution Root)
/-- The trusted anchor state (of the genesis store's justified checkpoint —
how `get_forkchoice_store` seeds every state map). -/
def anchor_state : BeaconState Root :=
  E.genesis_store.block_states E.genesis_store.justified_checkpoint.root

/-- Ground-truth validator registry: the anchor state's. -/
def registry : List Validator :=
  (E.anchor_state).validators

/-- Ground-truth effective balance of validator `i`. -/
def weight_of (i : ValidatorIndex) : Gwei :=
  ((E.registry).getD i default).effective_balance

/-- Ground-truth total weight of a validator set. -/
def weight (s : Finset ValidatorIndex) : Gwei :=
  ∑ i ∈ s, E.weight_of i

/-- Ground-truth total active balance (the anchor state's). -/
def total_active : Gwei :=
  get_total_active_balance cfg E.anchor_state

/-- The (ground-truth) union of committees over the inclusive slot span
`[a, b]` — the object `get_block_support_between_slots` and
`compute_adversarial_weight` reason about. -/
def span_committee (a b : Slot) : Finset ValidatorIndex :=
  (Finset.Icc a b).biUnion E.committee

end Execution
end FastConfirmation.Spec

end
