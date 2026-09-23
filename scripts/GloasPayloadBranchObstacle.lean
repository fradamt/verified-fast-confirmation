import FastConfirmationModel.Execution.Run

/-!
# Gloas payload-branch obstacle

This finite store tests the former generic `descendStep_of_dom` interface.
Beacon child 2 strictly beats the other beacon child of root 1's FULL node.
Root 1's pending node nevertheless chooses EMPTY, because that branch has
more weight. Thus dominance within one resolved branch does not establish
selection of that branch from the pending parent.

The fixture has three validators, four beacon roots, and no proposer boost.
Validator 0 votes for child 2. Validators 1 and 2 vote for child 4, which
selects root 1's EMPTY node. Child 3 also selects FULL and has no votes.
All votes are later than their beacon blocks. The clock is at slot 3, so the
previous-slot zero-weight rule does not apply to root 1's payload decision.

This is a local fork-choice counterexample. It does not claim a full accepted
execution, an FCR confirmation, or a refutation of the public safety theorem.
The file imports only the executable model. It uses kernel `decide`, no
additional axiom, and no proof-layer definition.
-/

namespace GloasPayloadBranchObstacle

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
    ptc_size := 2 }

def checkpoint : Checkpoint Nat := ⟨0, 1⟩

def validator : Validator :=
  { effective_balance := 100
    slashed := false
    activation_epoch := 0
    exit_epoch := FAR_FUTURE_EPOCH }

def anchorState : BeaconState Nat :=
  { genesis_time := 0
    slot := 0
    validators := [validator, validator, validator]
    current_justified_checkpoint := checkpoint
    finalized_checkpoint := checkpoint }

def anchorBlock : SignedBeaconBlock Nat :=
  { root := 1
    message :=
      { slot := 0
        parent_root := 0
        parent_block_hash := 0
        block_hash := 10 } }

def fullChild : BeaconBlock Nat :=
  { slot := 1
    parent_root := 1
    parent_block_hash := 10
    block_hash := 20 }

def fullSibling : BeaconBlock Nat :=
  { slot := 1
    parent_root := 1
    parent_block_hash := 10
    block_hash := 30 }

def emptyChild : BeaconBlock Nat :=
  { slot := 1
    parent_root := 1
    parent_block_hash := 0
    block_hash := 40 }

def store : Store Nat :=
  let anchor := get_forkchoice_store cfg anchorState anchorBlock
  { anchor with
    time := 18
    block_roots := [1, 2, 3, 4]
    blocks := fun root =>
      match root with
      | 2 => fullChild
      | 3 => fullSibling
      | 4 => emptyChild
      | _ => anchor.blocks root
    block_states := fun root =>
      if root = 1 then anchorState
      else { anchorState with slot := 1 }
    block_timeliness := fun root =>
      if root ∈ [1, 2, 3, 4] then some (true, true) else none
    latest_messages := fun index =>
      match index with
      | 0 => some ⟨2, 2, false⟩
      | 1 => some ⟨2, 4, false⟩
      | 2 => some ⟨2, 4, false⟩
      | _ => none
    unrealized_justifications := fun _ => checkpoint
    payloads := fun root =>
      if root = 1 then some
        { beacon_block_root := 1
          parent_beacon_block_root := 0
          identity := 10 }
      else none
    payload_timeliness_vote := fun root =>
      if root ∈ [1, 2, 3, 4] then some [none, none] else none
    payload_data_availability_vote := fun root =>
      if root ∈ [1, 2, 3, 4] then some [none, none] else none }

def blocks : List Nat := get_filtered_block_tree cfg store

/-- Use the exact source key: weight, beacon root, then payload status. -/
def selectedChild (parent : ForkChoiceNode Nat) : Option (ForkChoiceNode Nat) :=
  (get_node_children store blocks parent).argmax
    (fun child => toLex (get_weight cfg store child,
      toLex (child.root, get_payload_status_tiebreaker cfg store child)))

/-- Every candidate survives the filter, and FULL is locally available. -/
theorem fixture_domain :
    blocks = [2, 3, 4, 1] ∧
    get_current_slot cfg store = 3 ∧
    is_payload_verified store 1 = true ∧
    should_apply_proposer_boost cfg store = false ∧
    get_parent_payload_status store (store.blocks 2) = .full ∧
    get_parent_payload_status store (store.blocks 3) = .full ∧
    get_parent_payload_status store (store.blocks 4) = .empty := by
  decide

/-- The FULL branch has a real competing beacon child. -/
theorem full_children :
    get_node_children store blocks (ForkChoiceNode.mk 1 .full) =
      [ForkChoiceNode.mk 2 .pending, ForkChoiceNode.mk 3 .pending] := by
  decide

theorem exact_weights :
    get_weight cfg store (ForkChoiceNode.mk 2 .pending) = 100 ∧
    get_weight cfg store (ForkChoiceNode.mk 3 .pending) = 0 ∧
    get_weight cfg store (ForkChoiceNode.mk 1 .full) = 100 ∧
    get_weight cfg store (ForkChoiceNode.mk 1 .empty) = 200 := by
  decide

/-- The old beacon-child membership and strict-dominance premises hold
within the resolved parent selected by child 2's bid. -/
theorem selected_beacon_child_dominates :
    ForkChoiceNode.mk 2 .pending ∈
      get_node_children store blocks
        (ForkChoiceNode.mk 1 (get_parent_payload_status store (store.blocks 2))) ∧
    ∀ child ∈ get_node_children store blocks
        (ForkChoiceNode.mk 1 (get_parent_payload_status store (store.blocks 2))),
      child ≠ ForkChoiceNode.mk 2 .pending →
        get_weight cfg store child < get_weight cfg store (ForkChoiceNode.mk 2 .pending) := by
  have hstatus : get_parent_payload_status store (store.blocks 2) = .full := by
    decide
  rw [hstatus, full_children]
  constructor
  · decide
  · intro child hchild hne
    have hcases : child = ForkChoiceNode.mk 2 .pending ∨
        child = ForkChoiceNode.mk 3 .pending := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hchild
    rcases hcases with heq | heq
    · exact False.elim (hne heq)
    · rw [heq]
      decide

/-- The FULL branch selects child 2, but its pending parent selects EMPTY. -/
theorem opposite_branch_selected :
    selectedChild (ForkChoiceNode.mk 1 .full) = some (ForkChoiceNode.mk 2 .pending) ∧
    selectedChild (ForkChoiceNode.mk 1 .pending) = some (ForkChoiceNode.mk 1 .empty) ∧
    selectedChild (ForkChoiceNode.mk 1 .pending) ≠
      some (ForkChoiceNode.mk 1
        (get_parent_payload_status store (store.blocks 2))) := by
  decide

/-- The complete source head walk reaches the other beacon child. -/
theorem head_uses_other_branch :
    get_head cfg store = ForkChoiceNode.mk 4 .empty ∧
    is_ancestor store (get_head cfg store) (get_node_for_root 2) = false := by
  decide

#print axioms fixture_domain
#print axioms full_children
#print axioms exact_weights
#print axioms selected_beacon_child_dominates
#print axioms opposite_branch_selected
#print axioms head_uses_other_branch

#eval ("GLOAS_PAYLOAD_BRANCH_OBSTACLE",
  get_weight cfg store (ForkChoiceNode.mk 2 .pending),
  get_weight cfg store (ForkChoiceNode.mk 3 .pending),
  get_weight cfg store (ForkChoiceNode.mk 1 .full),
  get_weight cfg store (ForkChoiceNode.mk 1 .empty),
  (get_head cfg store).root)

end GloasPayloadBranchObstacle
