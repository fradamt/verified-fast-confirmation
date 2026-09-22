module
public import FastConfirmation.Spec.Proof.AncestryRoots
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

/-- The two distinct resolved statuses at a root have disjoint ancestry
predicates, in either order. -/
theorem not_ancestor_two_resolved_statuses (store : Store Root)
    (node : ForkChoiceNode Root) (root : Root)
    (selected other : PayloadStatus)
    (hselected : selected ≠ .pending) (hother : other ≠ .pending)
    (hne : other ≠ selected) :
    ¬ (is_ancestor store node (ForkChoiceNode.mk root selected) = true ∧
      is_ancestor store node (ForkChoiceNode.mk root other) = true) := by
  cases selected with
  | pending => exact (hselected rfl).elim
  | empty =>
    cases other with
    | pending => exact (hother rfl).elim
    | empty => exact (hne rfl).elim
    | full => exact not_ancestor_both_payload_statuses store node root
  | full =>
    cases other with
    | pending => exact (hother rfl).elim
    | empty =>
      intro h
      exact not_ancestor_both_payload_statuses store node root ⟨h.2, h.1⟩
    | full => exact (hne rfl).elim

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

/-- A recorded supporter of a descendant node also supports a resolved
ancestor, when its latest-message walk is known down to that ancestor.  This
keeps the payload status in the ancestry test; replacing the ancestor by a
pending root would lose the branch distinction. -/
theorem attSupporters_subset_resolved_ancestor {store : Store Root}
    {child parent : ForkChoiceNode Root} {state : BeaconState Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hancestor : is_ancestor store child parent = true)
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      i ∈ AttSupporters cfg store child state →
        WalkKnown store (store.blocks parent.root).slot lm.root)
    (hchildWalk : WalkKnown store (store.blocks parent.root).slot child.root) :
    (AttSupporters cfg store child state).toFinset ⊆
      (AttSupporters cfg store parent state).toFinset := by
  intro i hi
  simp only [List.mem_toFinset] at hi ⊢
  have hiChild := hi
  obtain ⟨lm, hlm, hnotEquiv, hsupports⟩ := mem_AttSupporters cfg hi
  simp only [AttSupporters, List.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  rw [hlm]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hnotEquiv,
    is_ancestor_trans hwf (hwalk i lm hlm hiChild)
      hchildWalk hsupports hancestor⟩

/-- The child's pending node descends from exactly the resolved parent status
encoded by its bid.  This is the one-step Gloas ancestor equation. -/
theorem child_pending_descends_required_parent_status {store : Store Root}
    {b : Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hb : b ∈ store.block_roots)
    (hp : (store.blocks b).parent_root ∈ store.block_roots) :
    is_ancestor store (get_node_for_root b)
      (ForkChoiceNode.mk (store.blocks b).parent_root
        (get_parent_payload_status store (store.blocks b))) = true := by
  have hslot := hwf b hb hp
  have hpWalk : WalkKnown store (store.blocks (store.blocks b).parent_root).slot
      (store.blocks b).parent_root := WalkKnown.stop hp (le_refl _)
  simp only [get_node_for_root, is_ancestor, Bool.and_eq_true,
    decide_eq_true_eq]
  rw [get_ancestor_step_status hwf hb hslot hpWalk,
    get_ancestor_stop_status (le_refl _)]
  exact ⟨rfl, Or.inl rfl⟩

/-- A child supporter cannot be counted by the opposite resolved payload
branch of its parent.  The latest-message walk and parent slot order are the
same known-domain facts used by the existing sibling-support accounting. -/
theorem childSupporters_disjoint_oppositeParentStatus {store : Store Root}
    {bs : BeaconState Root} {b : Root} (other : PayloadStatus)
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hb : b ∈ store.block_roots)
    (hp : (store.blocks b).parent_root ∈ store.block_roots)
    (hother : other ≠ .pending)
    (hne : other ≠ get_parent_payload_status store (store.blocks b))
    (hwalk : ∀ i lm, store.latest_messages i = some lm →
      i ∈ AttSupporters cfg store (get_node_for_root b) bs →
        WalkKnown store (store.blocks (store.blocks b).parent_root).slot lm.root) :
    Disjoint (AttSupporters cfg store (get_node_for_root b) bs).toFinset
      (AttSupporters cfg store
        (ForkChoiceNode.mk (store.blocks b).parent_root other) bs).toFinset := by
  let selected := get_parent_payload_status store (store.blocks b)
  have hselected : selected ≠ .pending := by
    simp only [selected, get_parent_payload_status]
    split_ifs <;> decide
  have hchildWalk : WalkKnown store (store.blocks (store.blocks b).parent_root).slot b :=
    WalkKnown.step hb (hwf b hb hp) (WalkKnown.stop hp (le_refl _))
  have hsub : (AttSupporters cfg store (get_node_for_root b) bs).toFinset ⊆
      (AttSupporters cfg store
        (ForkChoiceNode.mk (store.blocks b).parent_root selected) bs).toFinset :=
    attSupporters_subset_resolved_ancestor cfg hwf
      (child_pending_descends_required_parent_status hwf hb hp)
      hwalk hchildWalk
  rw [Finset.disjoint_left]
  intro i hiChild hiOther
  obtain ⟨lm, hlm, _, hsupportsSelected⟩ :=
    mem_AttSupporters cfg (List.mem_toFinset.mp (hsub hiChild))
  obtain ⟨lm', hlm', _, hsupportsOther⟩ :=
    mem_AttSupporters cfg (List.mem_toFinset.mp hiOther)
  have heq : lm' = lm := Option.some.inj (hlm'.symm.trans hlm)
  cases heq
  exact not_ancestor_two_resolved_statuses store (get_supported_node store lm)
    (store.blocks b).parent_root selected other hselected hother hne
    ⟨hsupportsSelected, hsupportsOther⟩

/-- The parent of a child whose slot is inside the completed-vote cutoff is
older than the previous slot.  The payload tie breaker is therefore not the
branch used for that parent at this store. -/
theorem confirmed_child_parent_not_previous_slot (store : Store Root) (b : Root)
    (status : PayloadStatus)
    (hslot : (store.blocks (store.blocks b).parent_root).slot < (store.blocks b).slot)
    (hcutoff : (store.blocks b).slot ≤ get_current_slot cfg store - 1) :
    is_previous_slot_payload_decision cfg store
      (ForkChoiceNode.mk (store.blocks b).parent_root status) = false := by
  have hnat (p c now : ℕ) (hp : p < c) (hc : c ≤ now - 1) :
      p + 1 ≠ now := by omega
  have hne : (store.blocks (store.blocks b).parent_root).slot + 1 ≠
      get_current_slot cfg store := hnat _ _ _ hslot hcutoff
  simp [is_previous_slot_payload_decision, hne]

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
