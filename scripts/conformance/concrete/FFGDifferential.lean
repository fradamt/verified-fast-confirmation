import Lean.Data.Json
import FastConfirmationModel.Spec.BeaconChain.ConcreteTransition

/-! Checked evaluation of concrete FFG fixtures. The Python runner supplies
the same JSON input to pinned pyspec and to this Lean program. -/

namespace FastConfirmation.ConcreteDifferential
open FastConfirmation.Spec FastConfirmation.Spec.ConcreteFFG Lean

abbrev J := Json

def field (j : J) (name : String) : Except String J := j.getObjVal? name
def nat (j : J) : Except String Nat := j.getNat?
def boolean (j : J) : Except String Bool := j.getBool?
def list (f : J → Except String α) (j : J) : Except String (List α) := do
  return ← (← j.getArr?).toList.mapM f

def natField (j : J) (name : String) : Except String Nat := do
  nat (← field j name)

def parseCheckpoint (j : J) : Except String (Checkpoint Nat) := do
  let a ← j.getArr?
  if a.size != 2 then throw "checkpoint length"
  return ⟨← nat a[0]!, ← nat a[1]!⟩

def parseValidator (j : J) : Except String Validator := do
  return {
    effective_balance := ← natField j "effective_balance"
    slashed := ← boolean (← field j "slashed")
    activation_epoch := ← natField j "activation_epoch"
    exit_epoch := ← natField j "exit_epoch"
  }

def parseState (j : J) : Except String (FFGBeaconState Nat) := do
  return {
    genesis_time := 0
    slot := ← natField j "slot"
    validators := ← list parseValidator (← field j "validators")
    justification_bits := ← list boolean (← field j "bits")
    previous_justified_checkpoint := ← parseCheckpoint (← field j "previous_justified")
    current_justified_checkpoint := ← parseCheckpoint (← field j "current_justified")
    finalized_checkpoint := ← parseCheckpoint (← field j "finalized")
    previous_epoch_participation := ← list nat (← field j "previous_participation")
    current_epoch_participation := ← list nat (← field j "current_participation")
    block_roots := ← list nat (← field j "block_roots")
    latest_block_header := ⟨← natField j "header_slot", 0, 0,
      ← natField j "header_root"⟩
    execution_payload_availability := ← list boolean (← field j "availability")
    latest_block_hash := ← natField j "latest_block_hash"
    latest_bid_block_hash := ← natField j "latest_bid_block_hash"
  }

def cfg : Config := {
  slots_per_epoch := 8
  slots_per_epoch_pos := by decide
  slot_duration_ms := 12000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 40
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 1000000000
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 2500
  min_seed_lookahead := 1
}

def preset : FFGPreset := {
  slots_per_historical_root := 64
  max_committees_per_slot := 4
  max_validators_per_committee := 2048
  max_attestations := 8
  max_proposer_slashings := 16
  max_attester_slashings := 1
  max_voluntary_exits := 16
  max_bls_to_execution_changes := 16
  max_payload_attestations := 4
  min_attestation_inclusion_delay := 1
  ring_pos := by decide
  min_delay_pos := by decide
}

def checkpointJson (cp : Checkpoint Nat) : J :=
  toJson #[cp.epoch, cp.root]

def stateJson (state : FFGBeaconState Nat) : J := Json.mkObj [
  ("slot", toJson state.slot),
  ("header_slot", toJson state.latest_block_header.slot),
  ("header_root", toJson state.latest_block_header.root),
  ("bits", toJson state.justification_bits),
  ("previous_justified", checkpointJson state.previous_justified_checkpoint),
  ("current_justified", checkpointJson state.current_justified_checkpoint),
  ("finalized", checkpointJson state.finalized_checkpoint),
  ("previous_participation", toJson state.previous_epoch_participation),
  ("current_participation", toJson state.current_epoch_participation),
  ("block_roots", toJson state.block_roots),
  ("availability", toJson state.execution_payload_availability),
  ("latest_block_hash", toJson state.latest_block_hash),
  ("latest_bid_block_hash", toJson state.latest_bid_block_hash)
]

def parseAttestationData (j : J) : Except String (AttestationData Nat) := do
  return {
    slot := ← natField j "slot"
    index := ← natField j "index"
    beacon_block_root := ← natField j "beacon_block_root"
    source := ← parseCheckpoint (← field j "source")
    target := ← parseCheckpoint (← field j "target")
  }

def parseVote (j : J) : Except String (FFGWireAttestation Nat) := do
  return {
    aggregation_bits := ← list boolean (← field j "aggregation_bits")
    committee_bits := ← list boolean (← field j "committee_bits")
    data := ← parseAttestationData (← field j "data")
    signature := 0
  }

def parseBlock (j : J) : Except String (FFGWireBlock Nat) := do
  return {
    slot := ← natField j "slot"
    parent_root := ← natField j "parent_root"
    proposer_index := ← natField j "proposer_index"
    root := ← natField j "root"
    parent_block_hash := ← natField j "parent_block_hash"
    block_hash := ← natField j "block_hash"
    parent_requests_empty := ← boolean (← field j "parent_requests_empty")
    parent_requests_match := ← boolean (← field j "parent_requests_match")
    deposit_count := ← natField j "deposit_count"
    attestations := ← list parseVote (← field j "attestations")
  }

def errorClass : Error → String
  | .state => "state" | .slot => "slot" | .root => "root"
  | .header => "header" | .parentPayload => "parentPayload"
  | .operations => "operations"
  | .committee => "committee" | .bitfield => "bitfield"
  | .target => "target" | .inclusion => "inclusion"
  | .payloadIndex => "payloadIndex" | .source => "source"
  | .indexed => "indexed" | .oracle => "oracle"

def runCase (j : J) : Except String J := do
  let state ← parseState (← field j "state")
  let action ← (← field j "action").getStr?
  let result ← if action == "pjf" then
    pure ((process_justification_and_finalization cfg preset state).map stateJson)
  else if action == "root" then
    let querySlot ← natField j "query_slot"
    pure ((get_block_root_at_slot preset state querySlot).map
      fun root => Json.mkObj [("root", toJson root)])
  else if action == "attestation" then
    let vote ← parseVote (← field j "vote")
    let schedule : FixedCommitteeSchedule := {
      committees := [(vote.data.slot, 0, [0, 1]),
        (vote.data.slot, 1, [2, 3])]
      counts := [(vote.data.target.epoch, 2)]
    }
    let parentSlot ← natField j "parent_slot"
    pure ((process_attestation cfg preset schedule state vote parentSlot).map stateJson)
  else if action == "attestations" then
    let votes ← list parseVote (← field j "votes")
    let schedule : FixedCommitteeSchedule := {
      committees := votes.flatMap fun vote =>
        [(vote.data.slot, 0, [0, 1]), (vote.data.slot, 1, [2, 3])]
      counts := votes.map fun vote => (vote.data.target.epoch, 2)
    }
    let parentSlot ← natField j "parent_slot"
    pure ((votes.foldlM (init := state) fun current vote =>
      process_attestation cfg preset schedule current vote parentSlot).map stateJson)
  else if action == "slots" then
    let target ← natField j "target_slot"
    pure ((process_slots cfg preset state target).map stateJson)
  else if action == "transition" then
    let block ← parseBlock (← field j "block")
    let schedule : FixedCommitteeSchedule := {
      committees := block.attestations.flatMap fun vote =>
        [(vote.data.slot, 0, [0, 1]), (vote.data.slot, 1, [2, 3])]
      counts := block.attestations.map fun vote => (vote.data.target.epoch, 2)
    }
    let accepts ← boolean (← field j "oracle_accept")
    let oracle : BlockValidityOracle Nat := ⟨fun _ _ _ => accepts⟩
    pure ((state_transition cfg preset schedule oracle state block).map stateJson)
  else
    throw s!"unknown action {action}"
  return match result with
  | .ok value => Json.mkObj [("ok", toJson true), ("value", value)]
  | .error e => Json.mkObj [("ok", toJson false), ("error", toJson (errorClass e))]

def main (args : List String) : IO Unit := do
  let path := args.headD ""
  let content ← IO.FS.readFile path
  let parsed := Json.parse content
  match parsed with
  | .error e => throw (IO.userError e)
  | .ok j =>
    match j.getArr? with
    | .error e => throw (IO.userError e)
    | .ok cases =>
      for case in cases do
        match runCase case with
        | .error e => throw (IO.userError e)
        | .ok output => IO.println output.compress

end FastConfirmation.ConcreteDifferential

unsafe def main (args : List String) : IO Unit :=
  FastConfirmation.ConcreteDifferential.main args
