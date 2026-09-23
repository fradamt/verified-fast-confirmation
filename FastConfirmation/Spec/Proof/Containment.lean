module
public import FastConfirmation.Spec.Model.StrongReference
public import FastConfirmation.Spec.Model.WeakSynchrony
public import FastConfirmation.Spec.Proof.AncestryRoots

@[expose] public section

/-!
# Weak-to-strong containment: initialization and a negative handler result

`Dominates` records the proposed trajectory relation. The strong observed
checkpoint equals the weak saved greatest checkpoint. Both copies have the
same fork-choice store, legacy snapshot, and slot-head history. The weak
confirmed root is an ancestor of the strong confirmed root.

The finite example below tests the requested unrestricted handler theorem.
It does not assert that the example has an accepted execution history.
-/

namespace FastConfirmation.Spec.Containment

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-- State relation proposed for weak-to-strong containment. `is_ancestor`
accepts the descendant first. The configuration and externals are explicit
parameters to keep the relation paired with the two rule instances. -/
structure Dominates (_cfg : Config) (_ext : Externals Root)
    (fw fs : FastConfirmationStore Root) : Prop where
  same_store : fw.store = fs.store
  confirmed_ancestor : is_ancestor fw.store (get_node_for_root fs.confirmed_root)
    (get_node_for_root fw.confirmed_root) = true
  current_snapshot : fs.current_epoch_observed_justified_checkpoint =
    fw.current_epoch_greatest_unrealized_checkpoint
  previous_snapshot : fw.previous_epoch_greatest_unrealized_checkpoint =
    fs.previous_epoch_greatest_unrealized_checkpoint
  previous_head : fw.previous_slot_head = fs.previous_slot_head
  current_head : fw.current_slot_head = fs.current_slot_head

omit [Inhabited Root] in
/-- The proposed relation holds at the shared conservative initialization. -/
theorem dominates_init (cfg : Config) (ext : Externals Root) (store : Store Root) :
    Dominates cfg ext (get_fast_confirmation_store store)
      (get_fast_confirmation_store store) where
  same_store := rfl
  confirmed_ancestor := is_ancestor_refl _ _
  current_snapshot := rfl
  previous_snapshot := rfl
  previous_head := rfl
  current_head := rfl

namespace Negative

set_option maxRecDepth 10000

/-- Minimal-preset constants, with two validators in each abstract committee. -/
def config : Config where
  slots_per_epoch := 8
  slots_per_epoch_pos := by decide
  slot_duration_ms := 6000
  slot_duration_ms_pos := by decide
  proposer_score_boost := 40
  confirmation_byzantine_threshold := 25
  confirmation_byzantine_threshold_le := by decide
  committee_weight_estimation_adjustment_factor := 5
  effective_balance_increment := 1000000000
  effective_balance_increment_pos := by decide
  hundred_dvd_effective_balance_increment := by decide
  attestation_due_bps := 3333
  min_seed_lookahead := 1

def finalized : Checkpoint Nat := ⟨0, 1⟩
def observed : Checkpoint Nat := ⟨1, 2⟩

def state (slot : Slot) : BeaconState Nat where
  genesis_time := 0
  slot := slot
  validators := [⟨64000000000, false, 0, 10⟩, ⟨32000000000, false, 0, 10⟩]
  current_justified_checkpoint := observed
  finalized_checkpoint := finalized

def externals : Externals Nat where
  get_beacon_committee := fun _ _ _ => [0, 1]
  get_committee_count_per_slot := fun _ _ => 1
  process_slots := fun st slot => { st with slot := slot }
  state_transition := fun _ _ => none
  process_justification_and_finalization := id
  is_valid_indexed_attestation := fun _ _ => true

/-- The chain is `1@0 → 2@8 → 3@9`. The certified carrier is 2.
The actual head 3 carries a different unrealized checkpoint. -/
def storeAt (slot : Slot) : Store Nat where
  time := slot * 6
  genesis_time := 0
  justified_checkpoint := finalized
  finalized_checkpoint := finalized
  unrealized_justified_checkpoint := observed
  unrealized_finalized_checkpoint := finalized
  proposer_boost_root := 0
  equivocating_indices := ∅
  block_roots := [1, 2, 3]
  blocks := fun r =>
    if r = 3 then { slot := 9, parent_root := 2 }
    else if r = 2 then { slot := 8, parent_root := 1 }
    else { slot := 0, parent_root := 0 }
  block_states := fun r => state (if r = 3 then 9 else if r = 2 then 8 else 0)
  block_timeliness := fun _ => some (true, true)
  checkpoint_state_keys := {finalized, observed}
  checkpoint_states := fun _ => state 8
  latest_messages := fun i =>
    if i = 0 then some { slot := 8, root := 2 }
    else if i = 1 then some { slot := 9, root := 3 }
    else none
  unrealized_justifications := fun r => if r = 2 then observed else finalized

def weakInput : FastConfirmationStore Nat where
  store := storeAt 16
  confirmed_root := 2
  previous_epoch_observed_justified_checkpoint := finalized
  current_epoch_observed_justified_checkpoint := observed
  previous_epoch_greatest_unrealized_checkpoint := observed
  current_epoch_greatest_unrealized_checkpoint := observed
  previous_slot_head := 3
  current_slot_head := 3

def strongInput : FastConfirmationStore Nat := { weakInput with confirmed_root := 3 }

/-- The input relation holds. The two inputs differ only in confirmed root. -/
theorem input_dominates : Dominates config externals weakInput strongInput where
  same_store := rfl
  confirmed_ancestor := by decide
  current_snapshot := rfl
  previous_snapshot := rfl
  previous_head := rfl
  current_head := rfl

/-- There is no mismatch in balance sources in this counterexample. -/
theorem balance_sources_equal :
    get_current_balance_source weakInput = get_current_balance_source strongInput ∧
    get_previous_balance_source weakInput = get_previous_balance_source strongInput := by
  exact ⟨rfl, rfl⟩

/-- The strong extra suffix fails reconfirmation; the weak checkpoint root
has no suffix to reconfirm. -/
theorem reconfirmation_split :
    Weak.is_confirmed_chain_safe config externals weakInput 2 = true ∧
    Strong.is_confirmed_chain_safe config externals strongInput 3 = false := by decide

/-- The final reset accepts weak root 2. The strong restart fails because
its observed checkpoint differs from the actual head's checkpoint. -/
theorem reset_and_restart_guards :
    get_checkpoint_for_block config weakInput.store 2 observed.epoch = observed ∧
    (get_head config weakInput.store).root = 3 ∧
    observed ≠ weakInput.store.unrealized_justifications 3 := by decide

/-- The getters reverse the proposed order. -/
theorem getter_outputs :
    Weak.get_latest_confirmed config externals weakInput = 2 ∧
    Strong.get_latest_confirmed config externals strongInput = 1 := by decide

/-- Banking does not repair this failure: the handlers also reverse the order. -/
theorem handler_outputs :
    (Weak.on_fast_confirmation config externals weakInput).confirmed_root = 2 ∧
    (Strong.on_fast_confirmation config externals strongInput).confirmed_root = 1 := by decide

/-- Kernel-checked failure of the requested one-shot containment conclusion. -/
theorem one_shot_not_contained :
    is_ancestor weakInput.store
      (get_node_for_root (Strong.get_latest_confirmed config externals strongInput))
      (get_node_for_root (Weak.get_latest_confirmed config externals weakInput)) = false := by
  decide

/-- Kernel-checked failure of the requested handler preservation conclusion. -/
theorem handler_not_dominates :
    ¬ Dominates config externals
      (Weak.on_fast_confirmation config externals weakInput)
      (Strong.on_fast_confirmation config externals strongInput) := by
  intro h
  have hfalse : is_ancestor
      (Weak.on_fast_confirmation config externals weakInput).store
      (get_node_for_root
        (Strong.on_fast_confirmation config externals strongInput).confirmed_root)
      (get_node_for_root
        (Weak.on_fast_confirmation config externals weakInput).confirmed_root) = false := by
    decide
  have hc := h.confirmed_ancestor
  rw [hfalse] at hc
  exact Bool.false_ne_true hc

/-- The universal handler preservation claim is false for the proposed relation. -/
theorem not_handler_preservation :
    ¬ ∀ fw fs : FastConfirmationStore Nat, Dominates config externals fw fs →
      Dominates config externals
        (Weak.on_fast_confirmation config externals fw)
        (Strong.on_fast_confirmation config externals fs) := by
  intro h
  exact handler_not_dominates (h weakInput strongInput input_dominates)

/-- The universal one-shot containment claim is false for the proposed relation. -/
theorem not_one_shot_containment :
    ¬ ∀ fw fs : FastConfirmationStore Nat, Dominates config externals fw fs →
      is_ancestor fw.store
        (get_node_for_root (Strong.get_latest_confirmed config externals fs))
        (get_node_for_root (Weak.get_latest_confirmed config externals fw)) = true := by
  intro h
  have hc := h weakInput strongInput input_dominates
  rw [one_shot_not_contained] at hc
  exact Bool.false_ne_true hc

end Negative
end FastConfirmation.Spec.Containment

end
