module
public import FastConfirmationProofs.ForkChoice.Ancestry.AncestryRoots
public import FastConfirmationProofs.FFG.Certificates.QuorumAccounting
public import FastConfirmationProofs.Safety.BlockAgreement

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

/-- A recorded vote for a resolved payload status at `root` belongs to a
committee after `root`'s slot.  The exact latest-message slot in provenance
is needed when the message is at `root` itself; a descendant message is
confined by its later block slot. -/
theorem resolved_supporter_mem_post_root_span {E : Execution Root}
    {store : Store Root} {bs : BeaconState Root} {root : Root}
    {status : PayloadStatus} {i : ValidatorIndex}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    (hprov : LatestMessageProvenance E cfg (get_current_slot cfg store) store)
    (hresolved : status ≠ .pending)
    (hi : i ∈ AttSupporters cfg store (ForkChoiceNode.mk root status) bs)
    (hwalk : ∀ lm, store.latest_messages i = some lm →
      WalkKnown store (store.blocks root).slot lm.root) :
    i ∈ E.span_committee ((store.blocks root).slot + 1)
      (get_current_slot cfg store - 1) := by
  obtain ⟨lm, hlm, _, hsupport⟩ := mem_AttSupporters cfg hi
  obtain ⟨a, _, _, _, _, hupper, hcomm, _, hblock, hslotEq⟩ := hprov i lm hlm
  have hanc : (get_ancestor store (get_supported_node store lm)
        (store.blocks root).slot).root = root := by
    have hsupport' := hsupport
    simp only [is_ancestor, Bool.and_eq_true, decide_eq_true_eq] at hsupport'
    exact hsupport'.1
  have hrootLe : (store.blocks root).slot ≤ (store.blocks lm.root).slot := by
    have hbound := get_ancestor_slot_le_status hwf (hwalk lm hlm)
      (get_supported_node store lm).payload_status
    change (store.blocks
        (get_ancestor store (get_supported_node store lm)
          (store.blocks root).slot).root).slot ≤ (store.blocks lm.root).slot at hbound
    rw [hanc] at hbound
    exact hbound
  have hlower : (store.blocks root).slot < a.data.slot := by
    rcases hrootLe.lt_or_eq with hlt | heq
    · exact hlt.trans_le hblock
    · have hstop : get_ancestor store (get_supported_node store lm)
          (store.blocks root).slot = get_supported_node store lm :=
        get_ancestor_stop_status (by
          change (store.blocks lm.root).slot ≤ (store.blocks root).slot
          exact le_of_eq heq.symm)
      rw [hstop] at hanc
      have hsame : lm.root = root := by
        simpa only [get_supported_node] using hanc
      have hown : is_ancestor store (get_supported_node store lm)
          (ForkChoiceNode.mk lm.root status) = true := by
        simpa only [hsame] using hsupport
      have hafter := (supported_node_own_root_resolved_iff store lm status hresolved).mp hown
      rw [hslotEq] at hafter
      simpa only [hsame] using hafter.1
  refine Finset.mem_biUnion.mpr ⟨a.data.slot,
    Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hlower,
      Nat.le_sub_one_of_lt hupper⟩, hcomm⟩

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

/-- At a same-slot or later endpoint, the parent of a confirmed child is too
old for Gloas's previous-slot payload tie breaker.  The source cutoff comes
from actual confirmation; block provenance identifies the child's slot in
both stores. -/
theorem confirmed_parent_not_previous_at_later_store (ext : Externals Root)
    {E : Execution Root}
    (hwf : WellFormedExecution E)
    (v w : ValidatorIndex) (n m : ℕ) {b : Root}
    (status : PayloadStatus)
    (hbSource : b ∈ (E.store cfg ext v n).block_roots)
    (hbEndpoint : b ∈ (E.store cfg ext w m).block_roots)
    (hparentLt : ((E.store cfg ext w m).blocks
      ((E.store cfg ext w m).blocks b).parent_root).slot <
        ((E.store cfg ext w m).blocks b).slot)
    (hwfSource : ∀ r ∈ (E.store cfg ext v n).block_roots,
      ((E.store cfg ext v n).blocks r).parent_root ∈
        (E.store cfg ext v n).block_roots →
        ((E.store cfg ext v n).blocks
          ((E.store cfg ext v n).blocks r).parent_root).slot <
          ((E.store cfg ext v n).blocks r).slot)
    (hprov : LatestMessageProvenance E cfg
      (get_current_slot cfg (E.store cfg ext v n)) (E.store cfg ext v n))
    {bs : BeaconState Root}
    (hwalk : ∀ i ∈ AttSupporters cfg (E.store cfg ext v n) (get_node_for_root b) bs,
      ∀ lm, (E.store cfg ext v n).latest_messages i = some lm →
        WalkKnown (E.store cfg ext v n)
          ((E.store cfg ext v n).blocks b).slot lm.root)
    (hclock : E.slot_at cfg n ≤ E.slot_at cfg m)
    (hconf : is_one_confirmed cfg ext (E.store cfg ext v n) bs b = true) :
    is_previous_slot_payload_decision cfg (E.store cfg ext w m)
      (ForkChoiceNode.mk ((E.store cfg ext w m).blocks b).parent_root status) = false := by
  have hcutoffSource := confirmed_block_slot_le_cutoff cfg ext hwfSource
    hprov hwalk hconf
  have hblock := hwf.blocks_agree
    (E.blockProvenance cfg ext v n) (E.blockProvenance cfg ext w m)
    hbSource hbEndpoint
  have hnat (c q e : ℕ) (hc : c ≤ q - 1) (hqe : q ≤ e) : c ≤ e - 1 := by omega
  have hcutoffEndpoint : ((E.store cfg ext w m).blocks b).slot ≤
      get_current_slot cfg (E.store cfg ext w m) - 1 := by
    rw [← hblock]
    rw [E.store_current_slot cfg ext v n] at hcutoffSource
    rw [E.store_current_slot cfg ext w m]
    exact hnat _ _ _ hcutoffSource hclock
  exact confirmed_child_parent_not_previous_slot cfg (E.store cfg ext w m)
    b status hparentLt hcutoffEndpoint







end FastConfirmation.Spec

end
