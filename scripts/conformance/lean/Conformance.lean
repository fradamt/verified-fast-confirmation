import Lean.Data.Json
import FastConfirmation.Spec.Model.Execution

namespace FastConfirmation.Conformance

open FastConfirmation.Spec

abbrev J := Lean.Json

def field (j : J) (name : String) : Except String J :=
  match j.getObjVal? name with
  | .ok value => .ok value
  | .error e => .error s!"field {name}: {e}"

def stringValue (j : J) : Except String String :=
  match j.getStr? with
  | .ok value => .ok value
  | .error e => .error e

def natValue (j : J) : Except String Nat :=
  match j with
  | .num number =>
      if number.exponent = 0 ∧ number.mantissa ≥ 0 then
        .ok number.mantissa.natAbs
      else
        .error "expected a non-negative integer JSON number"
  | .str value =>
      match value.toNat? with
      | some n => .ok n
      | none => .error s!"expected a decimal integer string, got {value}"
  | _ => .error "expected an integer number or decimal string"

def boolValue (j : J) : Except String Bool :=
  match j.getBool? with
  | .ok value => .ok value
  | .error e => .error e

def arrayValue (j : J) : Except String (Array J) :=
  match j.getArr? with
  | .ok value => .ok value
  | .error e => .error e

def natField (j : J) (name : String) : Except String Nat := do
  natValue (← field j name)

def stringField (j : J) (name : String) : Except String String := do
  stringValue (← field j name)

def boolField (j : J) (name : String) : Except String Bool := do
  boolValue (← field j name)

def arrayField (j : J) (name : String) : Except String (Array J) := do
  arrayValue (← field j name)

def arrayMap (f : J → Except String α) (a : Array J) : Except String (Array α) :=
  (a.toList.mapM f).map List.toArray

def hexDigitValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def rootValue (j : J) : Except String Nat := do
  let text ← stringValue j
  if text.length ≠ 66 ∨ !text.startsWith "0x" then
    throw "root must be 0x followed by exactly 64 lowercase hexadecimal digits"
  let digits := (text.drop 2).toString.toList
  digits.foldlM (fun acc c =>
    match hexDigitValue c with
    | some d => pure (acc * 16 + d)
    | none => throw "root contains a non-lowercase-hexadecimal digit") 0

def rootField (j : J) (name : String) : Except String Nat := do
  rootValue (← field j name)

def rootText (root : Nat) : String :=
  let digit (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n)
    else Char.ofNat ('a'.toNat + n - 10)
  let rec go (remaining value : Nat) : List Char → List Char
    | acc =>
        if remaining = 0 then acc
        else go (remaining - 1) (value / 16) (digit (value % 16) :: acc)
  "0x" ++ String.ofList (go 64 root [])

def parseCheckpoint (j : J) : Except String (Checkpoint Nat) := do
  return { epoch := ← natField j "epoch", root := ← rootField j "root" }

def parseValidator (j : J) : Except String Validator := do
  return {
    effective_balance := ← natField j "effective_balance"
    slashed := ← boolField j "slashed"
    activation_epoch := ← natField j "activation_epoch"
    exit_epoch := ← natField j "exit_epoch"
  }

def parseCommitteeRead (j : J) : Except String (Slot × CommitteeIndex × List ValidatorIndex) := do
  let result ← arrayMap natValue (← arrayField j "result")
  return (← natField j "slot", ← natField j "index", result.toList)

def parseCountRead (j : J) : Except String (Epoch × Nat) := do
  return (← natField j "epoch", ← natField j "result")

def parseState (j : J) : Except String (BeaconState Nat) := do
  let validatorsJson ← arrayField j "validators"
  let validators ← arrayMap parseValidator validatorsJson
  let committeeReads ← arrayMap parseCommitteeRead (← arrayField j "beacon_committee_reads")
  let countReads ← arrayMap parseCountRead (← arrayField j "committee_count_reads")
  return {
    source_identity := some (← rootField j "id")
    genesis_time := ← natField j "genesis_time"
    slot := ← natField j "slot"
    validators := validators.toList
    beacon_committee_reads := committeeReads.toList
    committee_count_reads := countReads.toList
    current_justified_checkpoint := ← parseCheckpoint (← field j "current_justified_checkpoint")
    finalized_checkpoint := ← parseCheckpoint (← field j "finalized_checkpoint")
  }

def checkpointEq (a b : Checkpoint Nat) : Bool :=
  a.epoch == b.epoch && a.root == b.root

def validatorEq (a b : Validator) : Bool :=
  a.effective_balance == b.effective_balance &&
    a.slashed == b.slashed &&
    a.activation_epoch == b.activation_epoch && a.exit_epoch == b.exit_epoch

def listEq (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => eq a b && listEq eq as bs
  | _, _ => false

def stateEq (a b : BeaconState Nat) : Bool :=
  a.source_identity == b.source_identity &&
    a.genesis_time == b.genesis_time && a.slot == b.slot &&
    listEq validatorEq a.validators b.validators &&
    checkpointEq a.current_justified_checkpoint b.current_justified_checkpoint &&
    checkpointEq a.finalized_checkpoint b.finalized_checkpoint &&
    a.beacon_committee_reads == b.beacon_committee_reads &&
    a.committee_count_reads == b.committee_count_reads

def lookupNat (key : Nat) : List (Nat × α) → Option α
  | [] => none
  | (key', value) :: rest => if key == key' then some value else lookupNat key rest

def lookupCheckpoint (key : Checkpoint Nat) :
    List (Checkpoint Nat × BeaconState Nat) → Option (BeaconState Nat)
  | [] => none
  | (key', value) :: rest =>
      if checkpointEq key key' then some value else lookupCheckpoint key rest

def parsePayloadAttestationData (j : J) : Except String (PayloadAttestationData Nat) := do
  return {
    beacon_block_root := ← rootField j "beacon_block_root"
    slot := ← natField j "slot"
    payload_present := ← boolField j "payload_present"
    blob_data_available := ← boolField j "blob_data_available"
  }

def parsePayloadAttestation (j : J) : Except String (IndexedPayloadAttestation Nat) := do
  let indices ← arrayMap natValue (← arrayField j "attesting_indices")
  return {
    attesting_indices := indices.toList
    data := ← parsePayloadAttestationData (← field j "data")
    signature := ← rootField j "signature"
  }

def parseBlock (j : J) : Except String (Nat × BeaconBlock Nat) := do
  let attestations ← arrayMap parsePayloadAttestation (← arrayField j "payload_attestations")
  return (← rootField j "root", {
    slot := ← natField j "slot"
    parent_root := ← rootField j "parent_root"
    proposer_index := ← natField j "proposer_index"
    parent_block_hash := ← rootField j "parent_block_hash"
    block_hash := ← rootField j "block_hash"
    payload_attestations := attestations.toList
  })

def parseBlockState (j : J) : Except String (Nat × BeaconState Nat) := do
  return (← rootField j "root", ← parseState (← field j "state"))

def parseTimeliness (j : J) : Except String (Nat × (Bool × Bool)) := do
  let values ← arrayMap boolValue (← arrayField j "timely")
  match values.toList with
  | [attestation, ptc] => return (← rootField j "root", (attestation, ptc))
  | _ => throw "block timeliness requires exactly two booleans"

def parsePayload (j : J) : Except String (Nat × ExecutionPayloadEnvelope Nat) := do
  let root ← rootField j "root"
  let beaconRoot ← rootField j "beacon_block_root"
  if root != beaconRoot then throw "payload map key differs from beacon_block_root"
  return (root, {
    beacon_block_root := beaconRoot
    parent_beacon_block_root := ← rootField j "parent_beacon_block_root"
    identity := ← rootField j "identity"
  })

def parseVote (j : J) : Except String (Option Bool) :=
  match j with
  | .null => pure none
  | _ => some <$> boolValue j

def parseVotes (cfg : Config) (j : J) : Except String (Nat × List (Option Bool)) := do
  let votes ← arrayMap parseVote (← arrayField j "votes")
  if votes.size != cfg.ptc_size then throw "PTC vote list length differs from ptc_size"
  return (← rootField j "root", votes.toList)

def parseNode (j : J) : Except String (ForkChoiceNode Nat) := do
  let status ← natField j "payload_status"
  let payloadStatus ← match status with
    | 0 => pure PayloadStatus.empty
    | 1 => pure PayloadStatus.full
    | 2 => pure PayloadStatus.pending
    | _ => throw "payload_status must be 0, 1, or 2"
  return { root := ← rootField j "root", payload_status := payloadStatus }

def parseCheckpointState (j : J) : Except String (Checkpoint Nat × BeaconState Nat) := do
  return (← parseCheckpoint (← field j "checkpoint"), ← parseState (← field j "state"))

def parseLatestMessage (j : J) : Except String (Nat × LatestMessage Nat) := do
  return (← natField j "index", {
    slot := ← natField j "slot"
    root := ← rootField j "root"
    payload_present := ← boolField j "payload_present"
  })

def parseUnrealizedJustification (j : J) : Except String (Nat × Checkpoint Nat) := do
  return (← rootField j "root", ← parseCheckpoint (← field j "checkpoint"))

def parseConfig (j : J) : Except String Config := do
  let slotsPerEpoch ← natField j "slots_per_epoch"
  let slotDurationMs ← natField j "slot_duration_ms"
  let proposerScoreBoost ← natField j "proposer_score_boost"
  let threshold ← natField j "confirmation_byzantine_threshold"
  let adjustment ← natField j "committee_weight_estimation_adjustment_factor"
  let increment ← natField j "effective_balance_increment"
  let attestationDue ← natField j "attestation_due_bps"
  let minLookahead ← natField j "min_seed_lookahead"
  let ptcSize ← natField j "ptc_size"
  let payloadDue ← natField j "payload_due_bps"
  let payloadAttestationDue ← natField j "payload_attestation_due_bps"
  let reorgHeadWeight ← natField j "reorg_head_weight_threshold"
  if h : 0 < slotsPerEpoch then
    if hSlot : 0 < slotDurationMs then
      if hThreshold : threshold ≤ 25 then
        if hIncrement : 0 < increment then
          if hHundred : 100 ∣ increment then
            return {
              slots_per_epoch := slotsPerEpoch
              slots_per_epoch_pos := h
              slot_duration_ms := slotDurationMs
              slot_duration_ms_pos := hSlot
              proposer_score_boost := proposerScoreBoost
              confirmation_byzantine_threshold := threshold
              confirmation_byzantine_threshold_le := hThreshold
              committee_weight_estimation_adjustment_factor := adjustment
              effective_balance_increment := increment
              effective_balance_increment_pos := hIncrement
              hundred_dvd_effective_balance_increment := hHundred
              attestation_due_bps := attestationDue
              min_seed_lookahead := minLookahead
              ptc_size := ptcSize
              payload_due_bps := payloadDue
              payload_attestation_due_bps := payloadAttestationDue
              reorg_head_weight_threshold := reorgHeadWeight
            }
          else throw "config check failed: effective_balance_increment is not divisible by 100"
        else throw "config check failed: effective_balance_increment is not positive"
      else throw "config check failed: confirmation_byzantine_threshold is greater than 25"
    else throw "config check failed: slot_duration_ms is not positive"
  else throw "config check failed: slots_per_epoch is not positive"

structure ParsedStore where
  store : Store Nat

def parseStore (cfg : Config) (j : J) : Except String ParsedStore := do
  let blockJson ← arrayField j "blocks"
  let blockStatesJson ← arrayField j "block_states"
  let timelinessJson ← arrayField j "block_timeliness"
  let checkpointStatesJson ← arrayField j "checkpoint_states"
  let latestMessagesJson ← arrayField j "latest_messages"
  let unrealizedJson ← arrayField j "unrealized_justifications"
  let blocks ← arrayMap parseBlock blockJson
  let blockStates ← arrayMap parseBlockState blockStatesJson
  let timeliness ← arrayMap parseTimeliness timelinessJson
  let checkpointStates ← arrayMap parseCheckpointState checkpointStatesJson
  let latestMessages ← arrayMap parseLatestMessage latestMessagesJson
  let unrealized ← arrayMap parseUnrealizedJustification unrealizedJson
  let payloads ← arrayMap parsePayload (← arrayField j "payloads")
  let payloadTimeliness ← arrayMap (parseVotes cfg) (← arrayField j "payload_timeliness_vote")
  let payloadAvailability ← arrayMap (parseVotes cfg) (← arrayField j "payload_data_availability_vote")
  let finalized ← parseCheckpoint (← field j "finalized_checkpoint")
  let justified ← parseCheckpoint (← field j "justified_checkpoint")
  let unrealizedJustified ← parseCheckpoint (← field j "unrealized_justified_checkpoint")
  let unrealizedFinalized ← parseCheckpoint (← field j "unrealized_finalized_checkpoint")
  let equivocatingJson ← arrayField j "equivocating_indices"
  let equivocating ← arrayMap natValue equivocatingJson
  let blockList := blocks.toList
  let blockStateList := blockStates.toList
  let timelinessList := timeliness.toList
  let checkpointStateList := checkpointStates.toList
  let latestMessageList := latestMessages.toList
  let unrealizedList := unrealized.toList
  let store : Store Nat := {
    time := ← natField j "time"
    genesis_time := ← natField j "genesis_time"
    justified_checkpoint := justified
    finalized_checkpoint := finalized
    unrealized_justified_checkpoint := unrealizedJustified
    unrealized_finalized_checkpoint := unrealizedFinalized
    proposer_boost_root := ← rootField j "proposer_boost_root"
    equivocating_indices := equivocating.toList.toFinset
    block_roots := blockList.map Prod.fst
    blocks := fun root => (lookupNat root blockList).getD default
    block_states := fun root => (lookupNat root blockStateList).getD default
    block_timeliness := fun root => lookupNat root timelinessList
    payloads := fun root => lookupNat root payloads.toList
    payload_timeliness_vote := fun root => lookupNat root payloadTimeliness.toList
    payload_data_availability_vote := fun root => lookupNat root payloadAvailability.toList
    checkpoint_state_keys := checkpointStateList.map Prod.fst |>.toFinset
    checkpoint_states := fun checkpoint =>
      (lookupCheckpoint checkpoint checkpointStateList).getD default
    latest_messages := fun index => lookupNat index latestMessageList
    unrealized_justifications := fun root =>
      (lookupNat root unrealizedList).getD default
  }
  return { store }

structure CommitteeAnswer where
  state : BeaconState Nat
  slot : Nat
  index : Nat
  result : List Nat

structure CountAnswer where
  state : BeaconState Nat
  epoch : Nat
  result : Nat

structure ProcessSlotsAnswer where
  state : BeaconState Nat
  slot : Nat
  result : BeaconState Nat

structure ProcessFinalAnswer where
  state : BeaconState Nat
  result : BeaconState Nat

structure Answers where
  committees : List CommitteeAnswer
  counts : List CountAnswer
  slots : List ProcessSlotsAnswer
  finals : List ProcessFinalAnswer

def parseCommitteeAnswer (j : J) : Except String CommitteeAnswer := do
  let resultJson ← arrayField j "result"
  let result ← arrayMap natValue resultJson
  return {
    state := ← parseState (← field j "state")
    slot := ← natField j "slot"
    index := ← natField j "index"
    result := result.toList
  }

def parseCountAnswer (j : J) : Except String CountAnswer := do
  return {
    state := ← parseState (← field j "state")
    epoch := ← natField j "epoch"
    result := ← natField j "result"
  }

def parseProcessSlotsAnswer (j : J) : Except String ProcessSlotsAnswer := do
  return {
    state := ← parseState (← field j "state")
    slot := ← natField j "slot"
    result := ← parseState (← field j "result")
  }

def parseProcessFinalAnswer (j : J) : Except String ProcessFinalAnswer := do
  return {
    state := ← parseState (← field j "state")
    result := ← parseState (← field j "result")
  }

def parseAnswers (j : J) : Except String Answers := do
  let committees ← arrayMap parseCommitteeAnswer (← arrayField j "get_beacon_committee")
  let counts ← arrayMap parseCountAnswer (← arrayField j "get_committee_count_per_slot")
  let slots ← arrayMap parseProcessSlotsAnswer (← arrayField j "process_slots")
  let finals ← arrayMap parseProcessFinalAnswer
    (← arrayField j "process_justification_and_finalization")
  return {
    committees := committees.toList
    counts := counts.toList
    slots := slots.toList
    finals := finals.toList
  }

def parseFcr (store : Store Nat) (j : J) : Except String (FastConfirmationStore Nat) := do
  return {
    store := store
    confirmed_root := ← rootField j "confirmed_root"
    previous_epoch_observed_justified_checkpoint :=
      ← parseCheckpoint (← field j "previous_epoch_observed_justified_checkpoint")
    current_epoch_observed_justified_checkpoint :=
      ← parseCheckpoint (← field j "current_epoch_observed_justified_checkpoint")
    previous_epoch_greatest_unrealized_checkpoint :=
      ← parseCheckpoint (← field j "previous_epoch_greatest_unrealized_checkpoint")
    previous_slot_head := ← rootField j "previous_slot_head"
    current_slot_head := ← rootField j "current_slot_head"
  }

structure Record where
  testId : String
  callIndex : Nat
  cfg : Config
  before : FastConfirmationStore Nat
  after : FastConfirmationStore Nat
  answers : Answers
  headBefore : ForkChoiceNode Nat
  safeExecutionBlockHashAfter : Option Nat

def parseRecord (j : J) : Except String Record := do
  let schema ← natField j "schema"
  if schema == 1 then
    throw "schema v1 describes a phase0 store; schema v2 is required"
  if schema != 2 then throw "unsupported schema; expected v2"
  if (← stringField j "fork") != "gloas" then throw "schema v2 requires Gloas"
  let cfg ← parseConfig (← field j "config")
  let parsedStore ← parseStore cfg (← field j "store")
  let safeExecutionBlockHashAfter ← match j.getObjVal? "safe_execution_block_hash_after" with
    | .ok value => some <$> rootValue value
    | .error _ => pure none
  return {
    testId := ← stringField j "test_id"
    callIndex := ← natField j "call_index"
    cfg := cfg
    safeExecutionBlockHashAfter := safeExecutionBlockHashAfter
    headBefore := ← parseNode (← field j "head_before")
    before := ← parseFcr parsedStore.store (← field j "fcr_before")
    after := ← parseFcr parsedStore.store (← field j "fcr_after")
    answers := ← parseAnswers (← field j "externals")
  }

def findCommittee (answers : List CommitteeAnswer) (state : BeaconState Nat)
    (slot index : Nat) : Option (List Nat) :=
  match answers with
  | [] => none
  | answer :: rest =>
      if stateEq answer.state state && answer.slot == slot && answer.index == index then
        some answer.result
      else findCommittee rest state slot index

def findCount (answers : List CountAnswer) (state : BeaconState Nat)
    (epoch : Nat) : Option Nat :=
  match answers with
  | [] => none
  | answer :: rest =>
      if stateEq answer.state state && answer.epoch == epoch then some answer.result
      else findCount rest state epoch

def findSlots (answers : List ProcessSlotsAnswer) (state : BeaconState Nat)
    (slot : Nat) : Option (BeaconState Nat) :=
  match answers with
  | [] => none
  | answer :: rest =>
      if stateEq answer.state state && answer.slot == slot then some answer.result
      else findSlots rest state slot

def findFinal (answers : List ProcessFinalAnswer) (state : BeaconState Nat) :
    Option (BeaconState Nat) :=
  match answers with
  | [] => none
  | answer :: rest =>
      if stateEq answer.state state then some answer.result
      else findFinal rest state

/-- Return the fallback through the IO call so recording a miss is required
for evaluation of the external result. An unused pure Unit binding could
otherwise be removed by the compiler. -/
unsafe def missingValue (misses : IO.Ref (List String)) (message : String)
    (fallback : α) : α :=
  match unsafeIO (do
    misses.modify (fun old => message :: old)
    pure fallback) with
  | .ok value => value
  | .error _ => fallback

unsafe def makeExternals (answers : Answers) (misses : IO.Ref (List String)) :
    Externals Nat := {
  get_beacon_committee := fun state slot index =>
    match findCommittee answers.committees state slot index with
    | some result => result
    | none =>
        missingValue misses s!"get_beacon_committee slot={slot} index={index}" []
  get_committee_count_per_slot := fun state epoch =>
    match findCount answers.counts state epoch with
    | some result => result
    | none =>
        missingValue misses s!"get_committee_count_per_slot epoch={epoch}" 0
  process_slots := fun state slot =>
    match findSlots answers.slots state slot with
    | some result => result
    | none =>
        missingValue misses s!"process_slots slot={slot}" state
  state_transition := fun _ _ => none
  process_justification_and_finalization := fun state =>
    match findFinal answers.finals state with
    | some result => result
    | none =>
        missingValue misses "process_justification_and_finalization" state
  is_valid_indexed_attestation := fun _ _ => false
}

def checkpointText (checkpoint : Checkpoint Nat) : String :=
  s!"({checkpoint.epoch},{rootText checkpoint.root})"

def fieldResult (name : String) (leanValue pythonValue : String) : String :=
  s!"MISMATCH {name} lean={leanValue} python={pythonValue}"

def compareFcr (leanValue pythonValue : FastConfirmationStore Nat) :
    Option (String × String × String) :=
  if leanValue.confirmed_root != pythonValue.confirmed_root then
    some ("confirmed_root", rootText leanValue.confirmed_root,
      rootText pythonValue.confirmed_root)
  else if !checkpointEq leanValue.previous_epoch_observed_justified_checkpoint
      pythonValue.previous_epoch_observed_justified_checkpoint then
    some ("previous_epoch_observed_justified_checkpoint",
      checkpointText leanValue.previous_epoch_observed_justified_checkpoint,
      checkpointText pythonValue.previous_epoch_observed_justified_checkpoint)
  else if !checkpointEq leanValue.current_epoch_observed_justified_checkpoint
      pythonValue.current_epoch_observed_justified_checkpoint then
    some ("current_epoch_observed_justified_checkpoint",
      checkpointText leanValue.current_epoch_observed_justified_checkpoint,
      checkpointText pythonValue.current_epoch_observed_justified_checkpoint)
  else if !checkpointEq leanValue.previous_epoch_greatest_unrealized_checkpoint
      pythonValue.previous_epoch_greatest_unrealized_checkpoint then
    some ("previous_epoch_greatest_unrealized_checkpoint",
      checkpointText leanValue.previous_epoch_greatest_unrealized_checkpoint,
      checkpointText pythonValue.previous_epoch_greatest_unrealized_checkpoint)
  else if leanValue.previous_slot_head != pythonValue.previous_slot_head then
    some ("previous_slot_head", rootText leanValue.previous_slot_head,
      rootText pythonValue.previous_slot_head)
  else if leanValue.current_slot_head != pythonValue.current_slot_head then
    some ("current_slot_head", rootText leanValue.current_slot_head,
      rootText pythonValue.current_slot_head)
  else none

def nodeText (node : ForkChoiceNode Nat) : String :=
  s!"({rootText node.root},{node.payload_status.toNat})"

/-- Check the complete state-read domain that Gloas proposer boost can use.
The exporter fills this domain even when its first head call skips it. -/
def missingHeadRead (cfg : Config) (store : Store Nat) : Option String := do
  if store.proposer_boost_root == 0 then none else do
    let block := store.blocks store.proposer_boost_root
    let parent := store.blocks block.parent_root
    if parent.slot + 1 < block.slot then none else do
      let state := store.block_states block.parent_root
      let epoch := compute_epoch_at_slot cfg parent.slot
      match state.committee_count_reads.find? (fun entry => entry.1 == epoch) with
      | none => some s!"get_committee_count_per_slot head epoch={epoch}"
      | some (_, count) =>
          let missing := (List.range count).find? (fun index =>
            !(state.beacon_committee_reads.any (fun entry =>
              entry.1 == parent.slot && entry.2.1 == index)))
          match missing with
          | none => none
          | some index => some s!"get_beacon_committee head slot={parent.slot} index={index}"

unsafe def evaluate (record : Record) : IO (Option String) := do
  if let some missing := missingHeadRead record.cfg record.before.store then
    return some s!"MISSING_EXTERNAL {missing}"
  let misses ← IO.mkRef []
  let ext := makeExternals record.answers misses
  let head := get_head record.cfg record.before.store
  let leanValue := on_fast_confirmation record.cfg ext record.before
  -- Store the comparison through IO before reading the miss log. This
  -- forces the pure external callers before the effectful log inspection.
  let comparisonRef ← IO.mkRef (compareFcr leanValue record.after)
  let missList ← misses.get
  let comparison ← comparisonRef.get
  match missList with
  | miss :: _ => return some s!"MISSING_EXTERNAL {miss}"
  | [] =>
      if head != record.headBefore then
        return some (fieldResult "head_before" (nodeText head) (nodeText record.headBefore))
      match comparison with
      | some (name, leanText, pythonText) =>
          return some (fieldResult name leanText pythonText)
      | none =>
          match record.safeExecutionBlockHashAfter with
          | none => return none
          | some expected =>
              let actual := get_safe_execution_block_hash leanValue
              if actual == expected then return none
              return some (fieldResult "safe_execution_block_hash_after"
                (rootText actual) (rootText expected))

unsafe def processLine (line : String) : IO (Bool × Bool) := do
  match Lean.Json.parse line with
  | .error e =>
      IO.eprintln s!"ERROR JSON: {e}"
      return (false, false)
  | .ok json =>
      match parseRecord json with
      | .error e =>
          IO.eprintln s!"ERROR record: {e}"
          return (false, false)
      | .ok record =>
          match ← evaluate record with
          | none =>
              IO.println s!"OK {record.testId} {record.callIndex}"
              return (true, false)
          | some message =>
              IO.println s!"{message} {record.testId} {record.callIndex}"
              return (false, message.startsWith "MISSING_EXTERNAL")

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let input ← IO.FS.Handle.mk path .read
      let mut records := 0
      let mut ok := 0
      let mut mismatch := 0
      let mut missing := 0
      repeat
        let line ← input.getLine
        if line.isEmpty then break
        if line.trimAscii != "" then
          let (recordOk, recordMissing) ← processLine line
          if recordOk then
            records := records + 1
            ok := ok + 1
          else if recordMissing then
            records := records + 1
            missing := missing + 1
          else
            records := records + 1
            mismatch := mismatch + 1
      IO.println s!"SUMMARY records={records} ok={ok} mismatch={mismatch} missing_external={missing}"
      if records == 0 then IO.eprintln "ERROR empty trace: at least one Gloas record is required"
      return if records > 0 ∧ mismatch = 0 ∧ missing = 0 then 0 else 1
  | _ =>
      IO.eprintln "usage: lake env lean --run scripts/conformance/lean/Conformance.lean <trace.jsonl>"
      return 2

end FastConfirmation.Conformance

unsafe def main (args : List String) : IO UInt32 :=
  FastConfirmation.Conformance.main args
