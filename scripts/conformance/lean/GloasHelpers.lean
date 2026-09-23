import Lean.Data.Json
import FastConfirmationModel.Execution.Run

/-! Direct helper comparisons for the four-block projected source fixture.
These stores are not claimed to be accepted executions. -/

namespace FastConfirmation.GloasHelpers

open FastConfirmation.Spec Lean

structure Inputs where
  verified : Bool
  timelyYes : Nat
  timelyNo : Nat
  availableYes : Nat
  availableNo : Nat
  boostRoot : Nat
  boostParentFull : Bool
  siblingAttestationTimely : Bool
  siblingPtcTimely : Bool

def parseInputs (j : Json) : Except String Inputs := do
  let result : Inputs := {
    verified := ← (← j.getObjVal? "verified").getBool?
    timelyYes := ← (← j.getObjVal? "timely_yes").getNat?
    timelyNo := ← (← j.getObjVal? "timely_no").getNat?
    availableYes := ← (← j.getObjVal? "available_yes").getNat?
    availableNo := ← (← j.getObjVal? "available_no").getNat?
    boostRoot := ← (← j.getObjVal? "boost_root").getNat?
    boostParentFull := ← (← j.getObjVal? "boost_parent_full").getBool?
    siblingAttestationTimely := ← (← j.getObjVal? "sibling_attestation_timely").getBool?
    siblingPtcTimely := ← (← j.getObjVal? "sibling_ptc_timely").getBool?
  }
  if result.timelyYes + result.timelyNo > 512 ∨
      result.availableYes + result.availableNo > 512 then
    throw "vote counts exceed PTC size"
  if result.boostRoot != 0 && result.boostRoot != 4 then
    throw "fixture boost root must be 0 or 4"
  return result

def checkpoint : Checkpoint Nat := ⟨0, 1⟩

def state (slot : Nat) : BeaconState Nat := {
  genesis_time := 0
  slot := slot
  validators := List.replicate 100 {
    effective_balance := 32000000000
    slashed := false
    activation_epoch := 0
    exit_epoch := 2 ^ 64 - 1
  }
  current_justified_checkpoint := checkpoint
  finalized_checkpoint := checkpoint
  beacon_committee_reads := [(slot, 0, List.range 100)]
  committee_count_reads := [(0, 1)]
}

def block (inputs : Inputs) : Nat → BeaconBlock Nat
  | 1 => { slot := 0, parent_root := 0, proposer_index := 0,
           block_hash := 101, parent_block_hash := 0 }
  | 2 => { slot := 1, parent_root := 1, proposer_index := 7,
           block_hash := 102, parent_block_hash := 101 }
  | 3 => { slot := 1, parent_root := 1, proposer_index := 7,
           block_hash := 103, parent_block_hash := 101 }
  | 4 => { slot := 2, parent_root := 2, proposer_index := 8,
           block_hash := 104, parent_block_hash := if inputs.boostParentFull then 102 else 101 }
  | _ => default

def votes (yes no : Nat) : List (Option Bool) :=
  List.replicate yes (some true) ++ List.replicate no (some false) ++
    List.replicate (512 - yes - no) none

def store (inputs : Inputs) : Store Nat := {
  time := 24
  genesis_time := 0
  justified_checkpoint := checkpoint
  finalized_checkpoint := checkpoint
  unrealized_justified_checkpoint := checkpoint
  unrealized_finalized_checkpoint := checkpoint
  proposer_boost_root := inputs.boostRoot
  equivocating_indices := ∅
  block_roots := [1, 2, 3, 4]
  blocks := block inputs
  block_states := fun root => state (block inputs root).slot
  block_timeliness := fun root => some (if root = 3 then
    (inputs.siblingAttestationTimely, inputs.siblingPtcTimely) else (true, true))
  checkpoint_state_keys := {checkpoint}
  checkpoint_states := fun _ => state 0
  latest_messages := fun _ => none
  unrealized_justifications := fun _ => checkpoint
  payloads := fun root =>
    if root ∈ [1, 2, 3, 4] ∧ (root ≠ 2 ∨ inputs.verified = true) then
      some {
        beacon_block_root := root
        parent_beacon_block_root := (block inputs root).parent_root
        identity := root + 1000
      }
    else none
  payload_timeliness_vote := fun root => some (if root = 2 then
    votes inputs.timelyYes inputs.timelyNo else List.replicate 512 (some true))
  payload_data_availability_vote := fun root => some (if root = 2 then
    votes inputs.availableYes inputs.availableNo else List.replicate 512 (some true))
}

def observations (s : Store Nat) : List (String × Json) :=
  let cfg := mainnet_config
  [ ("payload_verified", toJson (is_payload_verified s 2)),
    ("timely_yes", toJson (payload_timeliness cfg s 2 true)),
    ("timely_no", toJson (payload_timeliness cfg s 2 false)),
    ("available_yes", toJson (payload_data_availability cfg s 2 true)),
    ("available_no", toJson (payload_data_availability cfg s 2 false)),
    ("extend", toJson (should_extend_payload cfg s 2)),
    ("head_weak", toJson (is_head_weak cfg s 2)),
    ("apply_boost", toJson (should_apply_proposer_boost cfg s)),
    ("sibling_head_late", toJson (is_head_late s 3)) ] ++
    ([ ("empty", PayloadStatus.empty), ("full", .full), ("pending", .pending) ].flatMap
      fun (label, status) =>
        let node := ForkChoiceNode.mk 2 status
        [ ("previous_" ++ label, toJson (is_previous_slot_payload_decision cfg s node)),
          ("tiebreak_" ++ label, toJson (get_payload_status_tiebreaker cfg s node)),
          ("weight_" ++ label, toJson (get_weight cfg s node)) ])

def checkFixture (j : Json) : Except String (String × List String × Nat) := do
  let name ← (← j.getObjVal? "name").getStr?
  let inputs ← parseInputs (← j.getObjVal? "input")
  let expected ← j.getObjVal? "expected"
  let actual := observations (store inputs)
  let failures ← actual.filterMapM fun (key, value) => do
    let source ← expected.getObjVal? key
    pure (if source.compress = value.compress then none else
      some s!"MISMATCH {name} {key} lean={value.compress} source={source.compress}")
  return (name, failures, actual.length)

def run (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  let parsed : Except String (Array Json) := do
    let j ← Json.parse text
    if (← (← j.getObjVal? "format").getStr?) != "gloas-helper-observations-v1" then
      throw "unexpected helper observation format"
    if (← (← j.getObjVal? "pin").getStr?) != "6b9bd532cca16555e2f3282d757622ebff29743e" then
      throw "unexpected consensus source pin"
    (← j.getObjVal? "fixtures").getArr?
  match parsed with
  | .error error =>
      IO.eprintln s!"ERROR {error}"
      return 1
  | .ok fixtures =>
      if fixtures.isEmpty then
        IO.eprintln "ERROR no helper fixtures"
        return 1
      let mut count := 0
      let mut mismatches := 0
      for fixture in fixtures do
        match checkFixture fixture with
        | .error error =>
            IO.eprintln s!"ERROR {error}"
            return 1
        | .ok (name, failures, observations) =>
            count := count + observations
            mismatches := mismatches + failures.length
            if failures.isEmpty then IO.println s!"OK {name}"
            for failure in failures do IO.println failure
      IO.println s!"SUMMARY helpers={fixtures.size} observations={count} mismatch={mismatches}"
      return if mismatches = 0 then 0 else 1

end FastConfirmation.GloasHelpers

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => FastConfirmation.GloasHelpers.run path
  | _ => do
      IO.eprintln "usage: lake env lean --run scripts/conformance/lean/GloasHelpers.lean observations.json"
      return 2
