module
public import FastConfirmation.Spec.Proof.Ancestry
public import FastConfirmation.Spec.Proof.QuorumAccounting

@[expose] public section

/-!
# Payload support at one beacon root

A later-slot message selects EMPTY or FULL at its own beacon root. A message
from the block's slot supports neither resolved node. The two resolved nodes
have disjoint supporter sets.

Each node's score splits into votes whose recorded root is the node's root
and votes whose recorded root differs. This partition keeps parent-root votes
visible when a proof compares the two payload branches. It does not assert
that either branch wins, or add a vote-history assumption.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]

/-- At its own root, a message supports a resolved status exactly when its
vote slot is later than the block slot and its payload bit selects that status.
This follows from `get_supported_node` and the Gloas ancestry test. -/
theorem supported_node_own_root_resolved_iff (store : Store Root)
    (message : LatestMessage Root) (status : PayloadStatus)
    (hresolved : status ≠ .pending) :
    is_ancestor store (get_supported_node store message)
        (ForkChoiceNode.mk message.root status) = true ↔
      (store.blocks message.root).slot < message.slot ∧
        status = (if message.payload_present then .full else .empty) := by
  have hstop : get_ancestor store (get_supported_node store message)
      (store.blocks message.root).slot = get_supported_node store message :=
    get_ancestor_stop_status (by exact Nat.le_refl _)
  simp only [is_ancestor, hstop]
  cases status with
  | pending => exact (hresolved rfl).elim
  | empty =>
      by_cases hslot : (store.blocks message.root).slot < message.slot
      all_goals cases hpayload : message.payload_present
      all_goals simp [get_supported_node, hslot, hpayload]
  | full =>
      by_cases hslot : (store.blocks message.root).slot < message.slot
      all_goals cases hpayload : message.payload_present
      all_goals simp [get_supported_node, hslot, hpayload]

/-- One node cannot descend from both resolved statuses at the same root.
Both tests inspect the same ancestor result, so no known-walk premise is
needed. -/
theorem not_ancestor_both_payload_statuses (store : Store Root)
    (node : ForkChoiceNode Root) (root : Root) :
    ¬ (is_ancestor store node (ForkChoiceNode.mk root .empty) = true ∧
      is_ancestor store node (ForkChoiceNode.mk root .full) = true) := by
  rintro ⟨hempty, hfull⟩
  simp only [is_ancestor, Bool.and_eq_true, decide_eq_true_eq] at hempty hfull
  rcases hempty.2 with hempty | himpossible
  · rcases hfull.2 with hfull | himpossible
    · have hbad : PayloadStatus.empty = .full := hempty.symm.trans hfull
      cases hbad
    · cases himpossible
  · cases himpossible

variable (cfg : Config)

/-- EMPTY and FULL at one root have disjoint recorded supporter sets. -/
theorem payload_status_supporters_disjoint (store : Store Root)
    (root : Root) (state : BeaconState Root) :
    Disjoint (AttSupporters cfg store (ForkChoiceNode.mk root .empty) state).toFinset
      (AttSupporters cfg store (ForkChoiceNode.mk root .full) state).toFinset := by
  refine Finset.disjoint_left.mpr ?_
  intro i hempty hfull
  obtain ⟨message, hmessage, _, hsupportEmpty⟩ :=
    mem_AttSupporters cfg (List.mem_toFinset.mp hempty)
  obtain ⟨message', hmessage', _, hsupportFull⟩ :=
    mem_AttSupporters cfg (List.mem_toFinset.mp hfull)
  have heq : message = message' := Option.some.inj (hmessage.symm.trans hmessage')
  cases heq
  exact not_ancestor_both_payload_statuses store (get_supported_node store message) root
    ⟨hsupportEmpty, hsupportFull⟩

open Classical in
/-- Supporters whose recorded message names the node's own beacon root. -/
noncomputable def SameRootAttSupporters (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) : Finset ValidatorIndex :=
  (AttSupporters cfg store node state).toFinset.filter fun i =>
    ∃ message, store.latest_messages i = some message ∧ message.root = node.root

open Classical in
/-- The remaining supporters. Each has a recorded message at another root,
as `mem_otherRootAttSupporters` states. -/
noncomputable def OtherRootAttSupporters (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) : Finset ValidatorIndex :=
  (AttSupporters cfg store node state).toFinset.filter fun i =>
    ¬ ∃ message, store.latest_messages i = some message ∧ message.root = node.root

/-- The complement in the supporter set consists of messages at other roots;
it contains no validator without a recorded message. -/
theorem mem_otherRootAttSupporters {store : Store Root}
    {node : ForkChoiceNode Root} {state : BeaconState Root} {i : ValidatorIndex} :
    i ∈ OtherRootAttSupporters cfg store node state ↔
      i ∈ AttSupporters cfg store node state ∧
        ∃ message, store.latest_messages i = some message ∧ message.root ≠ node.root := by
  classical
  simp only [OtherRootAttSupporters, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨hi, hnot⟩
    obtain ⟨message, hmessage, _, _⟩ := mem_AttSupporters cfg hi
    exact ⟨hi, message, hmessage, fun hroot => hnot ⟨message, hmessage, hroot⟩⟩
  · rintro ⟨hi, message, hmessage, hroot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨message', hmessage', hroot'⟩
    have heq : message = message' := Option.some.inj (hmessage.symm.trans hmessage')
    exact hroot ((congrArg LatestMessage.root heq).trans hroot')

/-- The two root classes partition the complete recorded supporter set. -/
theorem sameRoot_otherRoot_supporters_union (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) :
    SameRootAttSupporters cfg store node state ∪
        OtherRootAttSupporters cfg store node state =
      (AttSupporters cfg store node state).toFinset := by
  classical
  exact Finset.filter_union_filter_not_eq
    (p := fun i => ∃ message, store.latest_messages i = some message ∧
      message.root = node.root) (AttSupporters cfg store node state).toFinset

/-- No validator occurs in both parts of the root partition. -/
theorem sameRoot_otherRoot_supporters_disjoint (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) :
    Disjoint (SameRootAttSupporters cfg store node state)
      (OtherRootAttSupporters cfg store node state) := by
  classical
  exact Finset.disjoint_filter_filter_not _ _ _

/-- A node's score is the sum of its own-root and other-root support. No
registry or execution-history premise is needed: both parts use the same
balance source as the score. -/
theorem attestation_score_sameRoot_otherRoot (store : Store Root)
    (node : ForkChoiceNode Root) (state : BeaconState Root) :
    get_attestation_score cfg store node state =
      (∑ i ∈ SameRootAttSupporters cfg store node state,
        (state.validators.getD i default).effective_balance) +
      ∑ i ∈ OtherRootAttSupporters cfg store node state,
        (state.validators.getD i default).effective_balance := by
  classical
  rw [get_attestation_score_eq_sum,
    ← List.sum_toFinset (fun i => (state.validators.getD i default).effective_balance)
      (AttSupporters_nodup cfg store node state)]
  exact (Finset.sum_filter_add_sum_filter_not
    (AttSupporters cfg store node state).toFinset
    (fun i => ∃ message, store.latest_messages i = some message ∧ message.root = node.root)
    (fun i => (state.validators.getD i default).effective_balance)).symm

end FastConfirmation.Spec

end
