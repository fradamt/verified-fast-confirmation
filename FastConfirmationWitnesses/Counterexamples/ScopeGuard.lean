module
public import FastConfirmationWitnesses.NonVacuity.GenesisStubRun

@[expose] public section

/-!
Regression for the fixed-scope guard of the concrete transition. Before the
guard, a child block with one proposer slashing, one attester slashing, and one
voluntary exit was accepted under a preset that admits these operations, and
the post-state kept the genesis registry. Python would mark a validator
slashed or set an exit epoch. The transition now rejects the block with
`Error.scope`, and it still accepts the same child without these operations.
-/

namespace FastConfirmation.Spec
namespace ScopeGuardRegression

open ConcreteFFG GenesisStubBridgeRun

/-- The witness preset with the Python bounds on slashings and exits. -/
def operationPreset : FFGPreset :=
  { witnessPreset with
    max_attester_slashings := 1
    max_voluntary_exits := 16
    max_proposer_slashings := 16 }

/-- The genesis child with one of each registry-changing operation. -/
def registryChangingChild : FFGWireBlock WitnessRoot :=
  { childWire with
    attester_slashing_count := 1
    voluntary_exit_count := 1
    proposer_slashing_count := 1 }

/-- The same child with a non-empty parent execution request list. -/
def parentRequestChild : FFGWireBlock WitnessRoot :=
  { childWire with parent_requests_empty := false }

theorem registry_changing_block_out_of_scope :
    state_transition witnessConfig operationPreset committeeSchedule witnessOracle
      witnessSetup.genesis registryChangingChild = .error .scope := by
  decide +kernel

theorem parent_request_block_out_of_scope :
    state_transition witnessConfig operationPreset committeeSchedule witnessOracle
      witnessSetup.genesis parentRequestChild = .error .scope := by
  decide +kernel

theorem in_scope_child_accepted :
    (state_transition witnessConfig operationPreset committeeSchedule witnessOracle
      witnessSetup.genesis childWire).isOk = true := by
  decide +kernel

end ScopeGuardRegression
end FastConfirmation.Spec

end
