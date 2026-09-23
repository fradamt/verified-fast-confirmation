import Lean.Data.Json
import FastConfirmationModel
import FastConfirmationModel.Weak.WeakSynchrony
import FastConfirmationModel.Weak.StrongReference


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

def parseState (j : J) : Except String (BeaconState Nat) := do
  let validatorsJson ← arrayField j "validators"
  let validators ← arrayMap parseValidator validatorsJson
  return {
    genesis_time := ← natField j "genesis_time"
    slot := ← natField j "slot"
    validators := validators.toList
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
  a.genesis_time == b.genesis_time && a.slot == b.slot &&
    listEq validatorEq a.validators b.validators &&
    checkpointEq a.current_justified_checkpoint b.current_justified_checkpoint &&
    checkpointEq a.finalized_checkpoint b.finalized_checkpoint

def lookupNat (key : Nat) : List (Nat × α) → Option α
  | [] => none
  | (key', value) :: rest => if key == key' then some value else lookupNat key rest

def lookupCheckpoint (key : Checkpoint Nat) :
    List (Checkpoint Nat × BeaconState Nat) → Option (BeaconState Nat)
  | [] => none
  | (key', value) :: rest =>
      if checkpointEq key key' then some value else lookupCheckpoint key rest

def parseBlock (j : J) : Except String (Nat × BeaconBlock Nat) := do
  return (← rootField j "root", {
    slot := ← natField j "slot"
    parent_root := ← rootField j "parent_root"
  })

def parseBlockState (j : J) : Except String (Nat × BeaconState Nat) := do
  return (← rootField j "root", ← parseState (← field j "state"))

def parseTimeliness (j : J) : Except String (Nat × (Bool × Bool)) := do
  let value ← field j "timely"
  let pair ← match value with
    | .bool timely => pure (timely, timely)
    | .arr values =>
      if values.size == 2 then
        pure (← boolValue values[0]!, ← boolValue values[1]!)
      else throw "timely pair must have two entries"
    | _ => throw "timely must be a bool or pair"
  return (← rootField j "root", pair)

def parseCheckpointState (j : J) : Except String (Checkpoint Nat × BeaconState Nat) := do
  return (← parseCheckpoint (← field j "checkpoint"), ← parseState (← field j "state"))

def parseLatestMessage (cfg : Config) (j : J) : Except String (Nat × LatestMessage Nat) := do
  let slot ← match j.getObjVal? "slot" with
    | .ok slot => natValue slot
    | .error _ => do
      let epoch ← natField j "epoch"
      -- Phase 0 traces record only an epoch. Place the legacy vote at its
      -- final slot so its implicit payload is resolved in the Gloas model.
      pure ((epoch + 1) * cfg.slots_per_epoch - 1)
  let payloadPresent ← match j.getObjVal? "payload_present" with
    | .ok present => boolValue present
    | .error _ => pure false
  return (← natField j "index", {
    slot := slot
    root := ← rootField j "root"
    payload_present := payloadPresent
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
  let latestMessages ← arrayMap (parseLatestMessage cfg) latestMessagesJson
  let unrealized ← arrayMap parseUnrealizedJustification unrealizedJson
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

/-- Keep the first occurrence of each complete JSON answer. This runs before
state parsing, which is costly when a trace repeats the same 64-validator
state hundreds of times. Answers with different results remain in order, so
first-match lookup is unchanged even for conflicting duplicate queries. -/
def uniqueJsonAnswers (answers : Array J) : Array J := Id.run do
  let mut seen : Std.HashSet J := {}
  let mut unique := #[]
  for answer in answers do
    if !seen.contains answer then
      seen := seen.insert answer
      unique := unique.push answer
  return unique

def parseContainmentAnswers (j : J) : Except String Answers := do
  let committees ← arrayMap parseCommitteeAnswer
    (uniqueJsonAnswers (← arrayField j "get_beacon_committee"))
  let counts ← arrayMap parseCountAnswer
    (uniqueJsonAnswers (← arrayField j "get_committee_count_per_slot"))
  let slots ← arrayMap parseProcessSlotsAnswer
    (uniqueJsonAnswers (← arrayField j "process_slots"))
  let finals ← arrayMap parseProcessFinalAnswer
    (uniqueJsonAnswers (← arrayField j "process_justification_and_finalization"))
  return {
    committees := committees.toList
    counts := counts.toList
    slots := slots.toList
    finals := finals.toList
  }

def parseFcr (store : Store Nat) (j : J) (schema : Nat) :
    Except String (FastConfirmationStore Nat) := do
  let currentGreatest ←
    if schema == 2 then do
      parseCheckpoint (← field j "current_epoch_greatest_unrealized_checkpoint")
    else pure store.finalized_checkpoint

  return {
    store := store
    confirmed_root := ← rootField j "confirmed_root"
    previous_epoch_observed_justified_checkpoint :=
      ← parseCheckpoint (← field j "previous_epoch_observed_justified_checkpoint")
    current_epoch_observed_justified_checkpoint :=
      ← parseCheckpoint (← field j "current_epoch_observed_justified_checkpoint")
    previous_epoch_greatest_unrealized_checkpoint :=
      ← parseCheckpoint (← field j "previous_epoch_greatest_unrealized_checkpoint")
    current_epoch_greatest_unrealized_checkpoint := currentGreatest

    previous_slot_head := ← rootField j "previous_slot_head"
    current_slot_head := ← rootField j "current_slot_head"
  }

structure Record where
  schema : Nat

  testId : String
  callIndex : Nat
  cfg : Config
  before : FastConfirmationStore Nat
  after : FastConfirmationStore Nat
  answers : Answers

def parseRecord (j : J) : Except String Record := do
  let schema ← natField j "schema"
  if schema != 1 && schema != 2 then throw s!"unsupported schema {schema}"
  let cfg ← parseConfig (← field j "config")
  let parsedStore ← parseStore cfg (← field j "store")
  return {
    schema := schema
    testId := ← stringField j "test_id"
    callIndex := ← natField j "call_index"
    cfg := cfg
    before := ← parseFcr parsedStore.store (← field j "fcr_before") schema
    after := ← parseFcr parsedStore.store (← field j "fcr_after") schema
    answers := ← parseAnswers (← field j "externals")
  }

/-- Only containment removes repeated external JSON answers; all store and FCR
inputs use the same parsers. -/
def parseContainmentRecord (j : J) : Except String Record := do
  let schema ← natField j "schema"
  if schema != 1 && schema != 2 then throw s!"unsupported schema {schema}"
  let cfg ← parseConfig (← field j "config")
  let parsedStore ← parseStore cfg (← field j "store")
  return {
    schema := schema
    testId := ← stringField j "test_id"
    callIndex := ← natField j "call_index"
    cfg := cfg
    before := ← parseFcr parsedStore.store (← field j "fcr_before") schema
    after := ← parseFcr parsedStore.store (← field j "fcr_after") schema
    answers := ← parseContainmentAnswers (← field j "externals")
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

unsafe def noteMiss (misses : IO.Ref (List String)) (message : String) : Unit :=
  match unsafeIO (misses.modify (fun old => message :: old)) with
  | .ok _ => ()
  | .error _ => ()

unsafe def makeExternals (answers : Answers) (misses : IO.Ref (List String)) :
    Externals Nat := {
  get_beacon_committee := fun state slot index =>
    match findCommittee answers.committees state slot index with
    | some result => result
    | none =>
        let _ := noteMiss misses s!"get_beacon_committee slot={slot} index={index}"
        []
  get_committee_count_per_slot := fun state epoch =>
    match findCount answers.counts state epoch with
    | some result => result
    | none =>
        let _ := noteMiss misses s!"get_committee_count_per_slot epoch={epoch}"
        0
  process_slots := fun state slot =>
    match findSlots answers.slots state slot with
    | some result => result
    | none =>
        let _ := noteMiss misses s!"process_slots slot={slot}"
        state
  state_transition := fun _ _ => none
  process_justification_and_finalization := fun state =>
    match findFinal answers.finals state with
    | some result => result
    | none =>
        let _ := noteMiss misses "process_justification_and_finalization"
        state
  is_valid_indexed_attestation := fun _ _ => false
}

/-- Scalar guards precede full state equality in containment lookups. The
answer order and exact equality predicate are identical to the normal runner. -/
def findContainmentCommittee (answers : List CommitteeAnswer) (state : BeaconState Nat)
    (slot index : Nat) : Option (List Nat) :=
  match answers with
  | [] => none
  | answer :: rest =>
      if answer.slot == slot && answer.index == index && stateEq answer.state state then
        some answer.result
      else findContainmentCommittee rest state slot index

def findContainmentCount (answers : List CountAnswer) (state : BeaconState Nat)
    (epoch : Nat) : Option Nat :=
  match answers with
  | [] => none
  | answer :: rest =>
      if answer.epoch == epoch && stateEq answer.state state then some answer.result
      else findContainmentCount rest state epoch

def findContainmentSlots (answers : List ProcessSlotsAnswer) (state : BeaconState Nat)
    (slot : Nat) : Option (BeaconState Nat) :=
  match answers with
  | [] => none
  | answer :: rest =>
      if answer.slot == slot && stateEq answer.state state then some answer.result
      else findContainmentSlots rest state slot

/-- Return the fallback through the IO result. A Unit-only notification can
be erased by the compiler because both result branches have the same value. -/
unsafe def missingContainmentAnswer (misses : IO.Ref (List String))
    (message : String) (fallback : α) : α :=
  match unsafeIO (do
    misses.modify (fun old => message :: old)
    pure fallback) with
  | .ok value => value
  | .error _ => fallback

unsafe def makeContainmentExternals (answers : Answers) (misses : IO.Ref (List String)) :
    Externals Nat := {
  makeExternals answers misses with
  get_beacon_committee := fun state slot index =>
    match findContainmentCommittee answers.committees state slot index with
    | some result => result
    | none => missingContainmentAnswer misses
        s!"get_beacon_committee slot={slot} index={index}" []
  get_committee_count_per_slot := fun state epoch =>
    match findContainmentCount answers.counts state epoch with
    | some result => result
    | none => missingContainmentAnswer misses
        s!"get_committee_count_per_slot epoch={epoch}" 0
  process_slots := fun state slot =>
    match findContainmentSlots answers.slots state slot with
    | some result => result
    | none => missingContainmentAnswer misses s!"process_slots slot={slot}" state
  process_justification_and_finalization := fun state =>
    match findFinal answers.finals state with
    | some result => result
    | none => missingContainmentAnswer misses "process_justification_and_finalization" state
}


def checkpointText (checkpoint : Checkpoint Nat) : String :=
  s!"({checkpoint.epoch},{rootText checkpoint.root})"

def fieldResult (name : String) (leanValue pythonValue : String) : String :=
  s!"MISMATCH {name} lean={leanValue} python={pythonValue}"

def compareFcr (leanValue pythonValue : FastConfirmationStore Nat)
    (compareGreatest : Bool) :

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
  else if compareGreatest && !checkpointEq leanValue.current_epoch_greatest_unrealized_checkpoint
      pythonValue.current_epoch_greatest_unrealized_checkpoint then
    some ("current_epoch_greatest_unrealized_checkpoint",
      checkpointText leanValue.current_epoch_greatest_unrealized_checkpoint,
      checkpointText pythonValue.current_epoch_greatest_unrealized_checkpoint)

  else if leanValue.previous_slot_head != pythonValue.previous_slot_head then
    some ("previous_slot_head", rootText leanValue.previous_slot_head,
      rootText pythonValue.previous_slot_head)
  else if leanValue.current_slot_head != pythonValue.current_slot_head then
    some ("current_slot_head", rootText leanValue.current_slot_head,
      rootText pythonValue.current_slot_head)
  else none

unsafe def evaluate (record : Record) : IO (Option String) := do
  let misses ← IO.mkRef []
  let ext := makeExternals record.answers misses
  let leanValue :=
    if record.schema == 2 then
      Weak.on_fast_confirmation record.cfg ext record.before
    else
      Strong.on_fast_confirmation record.cfg ext record.before

  let missList ← misses.get
  match missList with
  | miss :: _ => return some s!"MISSING_EXTERNAL {miss}"
  | [] =>
      match compareFcr leanValue record.after (record.schema == 2) with

      | none => return none
      | some (name, leanText, pythonText) =>
          return some (fieldResult name leanText pythonText)

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

/-- The order is checked in the input store. Equal roots are handled first,
so `WEAK_BELOW` and `WEAK_ABOVE` always mean strict ancestry. -/
def containmentClass (store : Store Nat) (strongRoot weakRoot : Nat) : String :=
  if strongRoot == weakRoot then "EQUAL"
  else if is_ancestor store (get_node_for_root strongRoot) (get_node_for_root weakRoot) then
    "WEAK_BELOW"
  else if is_ancestor store (get_node_for_root weakRoot) (get_node_for_root strongRoot) then
    "WEAK_ABOVE"
  else "INCOMPARABLE"

def rootWithSlot (store : Store Nat) (root : Nat) : String :=
  s!"{rootText root}@{(store.blocks root).slot}"

structure ContainmentResult where
  classification : String
  getterClassification : String
  missing : Bool

/-- Both handlers receive exactly the parsed pre-call FCR store and the same
external answer table. Getter diagnostics also compare the two getters on that
same pre-call store, without either handler's variable update. Missing answers
are reported separately: their fallback outputs are diagnostic, not evidence
about a complete external oracle. -/
unsafe def evaluateContainment (record : Record) : IO ContainmentResult := do
  let strongMisses ← IO.mkRef []
  let weakMisses ← IO.mkRef []
  let strongGetterMisses ← IO.mkRef []
  let weakGetterMisses ← IO.mkRef []
  let strongValue := Strong.on_fast_confirmation record.cfg
    (makeContainmentExternals record.answers strongMisses) record.before
  let weakValue := Weak.on_fast_confirmation record.cfg
    (makeContainmentExternals record.answers weakMisses) record.before
  let strongGetter := Strong.get_latest_confirmed record.cfg
    (makeContainmentExternals record.answers strongGetterMisses) record.before
  let weakGetter := Weak.get_latest_confirmed record.cfg
    (makeContainmentExternals record.answers weakGetterMisses) record.before
  let store := record.before.store
  let classification := containmentClass store strongValue.confirmed_root weakValue.confirmed_root
  let getterClassification := containmentClass store strongGetter weakGetter
  -- Printing forces all compared values before inspecting the miss references.
  IO.println s!"{classification} {record.testId} {record.callIndex} strong={rootWithSlot store strongValue.confirmed_root} weak={rootWithSlot store weakValue.confirmed_root} strong_bank={checkpointText strongValue.current_epoch_observed_justified_checkpoint} weak_bank={checkpointText weakValue.current_epoch_observed_justified_checkpoint} bank_equal={checkpointEq strongValue.current_epoch_observed_justified_checkpoint weakValue.current_epoch_observed_justified_checkpoint} getter={getterClassification} strong_getter={rootWithSlot store strongGetter} weak_getter={rootWithSlot store weakGetter}"
  let mut missing := false
  for (name, ref) in [("strong_handler", strongMisses), ("weak_handler", weakMisses),
      ("strong_getter", strongGetterMisses), ("weak_getter", weakGetterMisses)] do
    let misses ← ref.get
    if !misses.isEmpty then
      missing := true
      IO.println s!"MISSING_EXTERNAL {record.testId} {record.callIndex} rule={name} calls={misses.length} first={misses.head!}"
  return { classification, getterClassification, missing }

structure RunnerOptions where
  path : Option String := none
  containment : Bool := false
  tests : List String := []

def parseOptions : List String → RunnerOptions → Except String RunnerOptions
  | [], options =>
      if options.path.isSome then .ok options else .error "missing trace path"
  | "--containment" :: rest, options =>
      parseOptions rest { options with containment := true }
  | "--test" :: pattern :: rest, options =>
      parseOptions rest { options with tests := options.tests ++ [pattern] }
  | "--test" :: [], _ => .error "--test needs a substring"
  | argument :: rest, options =>
      if argument.startsWith "--" then .error s!"unknown option {argument}"
      else if options.path.isSome then .error "more than one trace path"
      else parseOptions rest { options with path := some argument }

def matchesTests (tests : List String) (value : String) : Bool :=
  tests.isEmpty || tests.any (fun pattern => value.contains pattern)

structure ClassCounts where
  equal : Nat := 0
  weakBelow : Nat := 0
  weakAbove : Nat := 0
  incomparable : Nat := 0

def ClassCounts.add (counts : ClassCounts) (classification : String) : ClassCounts :=
  if classification == "EQUAL" then { counts with equal := counts.equal + 1 }
  else if classification == "WEAK_BELOW" then { counts with weakBelow := counts.weakBelow + 1 }
  else if classification == "WEAK_ABOVE" then { counts with weakAbove := counts.weakAbove + 1 }
  else { counts with incomparable := counts.incomparable + 1 }

def ClassCounts.summary (counts : ClassCounts) (label : String) (records : Nat) : String :=
  s!"{label} records={records} equal={counts.equal} weak_below={counts.weakBelow} weak_above={counts.weakAbove} incomparable={counts.incomparable}"

/-- Stream large traces. Raw-line filtering avoids parsing records that cannot
match; the parsed test ID is then checked to prevent matches in other fields.
Repeated `--test` arguments are combined by OR. -/
unsafe def runSelected (options : RunnerOptions) : IO UInt32 := do
  let handle ← IO.FS.Handle.mk options.path.get! .read
  let mut records := 0
  let mut counts : ClassCounts := {}
  let mut getterCounts : ClassCounts := {}
  let mut missing := 0
  let mut errors := 0
  let mut ok := 0
  let mut mismatch := 0
  repeat
    let line ← handle.getLine
    if line.isEmpty then break
    if line.trimAscii != "" && matchesTests options.tests line then
      match Lean.Json.parse line >>=
          (if options.containment then parseContainmentRecord else parseRecord) with
      | .error e =>
          errors := errors + 1
          IO.eprintln s!"ERROR record: {e}"
      | .ok record =>
          if matchesTests options.tests record.testId then
            records := records + 1
            if options.containment then
              let result ← evaluateContainment record
              counts := counts.add result.classification
              getterCounts := getterCounts.add result.getterClassification
              if result.missing then missing := missing + 1
            else
              match ← evaluate record with
              | none =>
                  ok := ok + 1
                  IO.println s!"OK {record.testId} {record.callIndex}"
              | some message =>
                  IO.println s!"{message} {record.testId} {record.callIndex}"
                  if message.startsWith "MISSING_EXTERNAL" then missing := missing + 1
                  else mismatch := mismatch + 1
  if options.containment then
    IO.println (counts.summary "CONTAINMENT" records)
    IO.println (getterCounts.summary "GETTER_CONTAINMENT" records)
    IO.println s!"CONTAINMENT_COVERAGE missing_external_records={missing} errors={errors}"
    return if missing = 0 ∧ errors = 0 then 0 else 1
  else
    IO.println s!"SUMMARY records={records + errors} ok={ok} mismatch={mismatch + errors} missing_external={missing}"
    return if mismatch = 0 ∧ missing = 0 ∧ errors = 0 then 0 else 1


unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      let contents ← IO.FS.readFile path
      let mut records := 0
      let mut ok := 0
      let mut mismatch := 0
      let mut missing := 0
      for line in contents.splitOn "\n" do
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
      return if mismatch = 0 ∧ missing = 0 then 0 else 1
  | _ =>
      match parseOptions args {} with
      | .ok options => runSelected options
      | .error message =>
          IO.eprintln s!"ERROR arguments: {message}"
          IO.eprintln "usage: lake env lean --run scripts/conformance/lean/Conformance.lean [--containment] [--test <substring>]... <trace.jsonl>"
          return 2


end FastConfirmation.Conformance

unsafe def main (args : List String) : IO UInt32 :=
  FastConfirmation.Conformance.main args
