import FastConfirmationModel.Execution.Run

/-!
# Gloas handler checks

These finite checks cover handler control flow and store writes. The fixture
uses a four-position PTC and two validators. It is a synthetic configuration.
The committee read tables agree with the external committee functions. Each
PTC has exactly `cfg.ptc_size` positions, including repeated validators.

Signature identity 7 denotes an accepted signature. Observation identity 1
denotes available data. The envelope verifier binds the known block, state,
payload identity, signature, and observation. These choices define the local
external inputs for these checks. They do not test cryptography or the
execution engine. All assertions use kernel reduction through `decide`.
-/

namespace GloasHandlerChecks

open FastConfirmation.Spec

def cfg : Config :=
  { mainnet_config with
    slots_per_epoch := 8
    slots_per_epoch_pos := by decide
    slot_duration_ms := 6000
    slot_duration_ms_pos := by decide
    effective_balance_increment := 100
    effective_balance_increment_pos := by decide
    hundred_dvd_effective_balance_increment := by decide
    ptc_size := 4 }

def checkpoint : Checkpoint Nat := ⟨0, 1⟩

def validator : Validator :=
  { effective_balance := 100
    slashed := false
    activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH }

def anchorState : BeaconState Nat :=
  { genesis_time := 0
    slot := 0
    validators := [validator, validator]
    current_justified_checkpoint := checkpoint
    finalized_checkpoint := checkpoint
    source_identity := some 1
    beacon_committee_reads :=
      [(0, 0, [0, 1]), (1, 0, [0, 1]), (2, 0, [0, 1]), (3, 0, [0, 1])]
    committee_count_reads := [(0, 1)] }

def anchorBlock : SignedBeaconBlock Nat :=
  { root := 1
    message :=
      { slot := 0
        parent_root := 0
        parent_block_hash := 0
        block_hash := 10 } }

/-- B selects the anchor's EMPTY node, so it needs no anchor envelope. -/
def blockB : SignedBeaconBlock Nat :=
  { root := 2
    message :=
      { slot := 1
        parent_root := 1
        parent_block_hash := 0
        block_hash := 20 } }

def envelopeB : SignedExecutionPayloadEnvelope Nat :=
  { message :=
      { beacon_block_root := 2
        parent_beacon_block_root := 1
        identity := 20 }
    signature := 7 }

def available : EnvelopeObservation Nat := ⟨1⟩
def unavailable : EnvelopeObservation Nat := ⟨0⟩

def externals : Externals Nat :=
  { get_beacon_committee := fun state slot index => state.beacon_committees slot index
    get_committee_count_per_slot := fun state epoch => state.committee_count_per_slot epoch
    process_slots := fun state slot => { state with slot := slot }
    state_transition := fun state block =>
      some { state with slot := block.message.slot, source_identity := some block.root }
    process_justification_and_finalization := id
    is_valid_indexed_attestation := fun _ _ => true
    get_ptc := fun _ _ => [0, 1, 0, 1]
    is_valid_indexed_payload_attestation := fun state vote =>
      decide (vote.data.slot = state.slot ∧ vote.signature = 7 ∧
        vote.attesting_indices = [0])
    is_data_available := fun root observation =>
      decide (root = 2 ∧ observation.identity = 1)
    verify_execution_payload_envelope := fun state envelope observation =>
      decide (state.source_identity = some 2 ∧ state.slot = 1 ∧
        envelope = envelopeB ∧ observation.identity = 1) }

def beforeB : Store Nat :=
  on_tick cfg (get_forkchoice_store cfg anchorState anchorBlock) 6

/-- B is inserted by the real handler, including both vote-map entries. -/
def currentStore : Store Nat :=
  (on_block cfg externals beforeB blockB).getD beforeB

def laterStore : Store Nat := on_tick cfg currentStore 12

def positiveVote : PayloadAttestationMessage Nat :=
  { validator_index := 0
    data :=
      { beacon_block_root := 2
        slot := 1
        payload_present := true
        blob_data_available := false }
    signature := 7 }

def replacementVote : PayloadAttestationMessage Nat :=
  { positiveVote with
    data := { positiveVote.data with payload_present := false, blob_data_available := true } }

def badSignatureVote : PayloadAttestationMessage Nat :=
  { positiveVote with signature := 0 }

/-- C selects B's FULL node and includes B's old-slot PTC vote. -/
def blockC : SignedBeaconBlock Nat :=
  { root := 3
    message :=
      { slot := 2
        parent_root := 2
        parent_block_hash := 20
        block_hash := 30
        payload_attestations :=
          [{ attesting_indices := [0], data := positiveVote.data, signature := 7 }] } }

def votes (store : Store Nat) :
    Option (List (Option Bool)) × Option (List (Option Bool)) :=
  (store.payload_timeliness_vote 2, store.payload_data_availability_vote 2)

def positiveVotes : Option (List (Option Bool)) × Option (List (Option Bool)) :=
  (some [some true, none, some true, none],
    some [some false, none, some false, none])

def replacementVotes : Option (List (Option Bool)) × Option (List (Option Bool)) :=
  (some [some false, none, some false, none],
    some [some true, none, some true, none])

/-- The fixture reaches B through the handler and has a complete PTC domain. -/
theorem fixture_initialization :
    (on_block cfg externals beforeB blockB).map (fun store => store.block_roots) =
      some [1, 2] ∧
    get_current_slot cfg currentStore = 1 ∧
    (externals.get_ptc (currentStore.block_states 2) 1).length = cfg.ptc_size ∧
    votes currentStore =
      (some [none, none, none, none], some [none, none, none, none]) := by
  decide

/-- The same FULL-parent child succeeds after the parent's envelope arrives.
The accepted child also applies its body PTC vote through the notification fold. -/
theorem full_parent_requires_envelope :
    is_parent_node_full laterStore blockC.message = true ∧
    (on_block cfg externals laterStore blockC).isNone = true ∧
    (on_execution_payload_envelope externals laterStore envelopeB available).map
      (fun store => store.payloads 2) = some (some envelopeB.message) ∧
    ((on_execution_payload_envelope externals laterStore envelopeB available).bind
      (fun store => on_block cfg externals store blockC)).map
        (fun store => (store.block_roots, votes store)) =
      some ([1, 2, 3], positiveVotes) := by
  decide

/-- A known block and otherwise accepted envelope do not bypass missing data. -/
theorem envelope_requires_data :
    (laterStore.block_roots.contains 2) = true ∧
    externals.verify_execution_payload_envelope
      (laterStore.block_states 2) envelopeB available = true ∧
    externals.is_data_available 2 unavailable = false ∧
    (on_execution_payload_envelope externals laterStore envelopeB unavailable).isNone = true := by
  decide

/-- Both occurrences of validator 0 are written; a later vote replaces both. -/
theorem repeated_positions_and_replacement :
    (on_payload_attestation_message cfg externals currentStore positiveVote false).map votes =
      some positiveVotes ∧
    ((on_payload_attestation_message cfg externals currentStore positiveVote false).bind
      (fun store => on_payload_attestation_message cfg externals store replacementVote false)).map
        votes = some replacementVotes := by
  decide

/-- Wire votes require the current slot and an accepted signature. The block
path skips those checks. Membership and assigned-slot checks still precede it. -/
theorem block_and_wire_checks :
    (on_payload_attestation_message cfg externals laterStore positiveVote false).isNone = true ∧
    (on_payload_attestation_message cfg externals currentStore badSignatureVote false).isNone = true ∧
    (on_payload_attestation_message cfg externals laterStore badSignatureVote true).map votes =
      some positiveVotes ∧
    (on_payload_attestation_message cfg externals currentStore
      { positiveVote with validator_index := 2 } true).isNone = true := by
  decide

#print axioms fixture_initialization
#print axioms full_parent_requires_envelope
#print axioms envelope_requires_data
#print axioms repeated_positions_and_replacement
#print axioms block_and_wire_checks

#eval ("GLOAS_HANDLER_CHECKS", 5)

end GloasHandlerChecks
