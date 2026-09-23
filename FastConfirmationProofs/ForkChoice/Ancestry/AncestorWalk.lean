module
public import FastConfirmationProofs.Execution.Trajectory.ExecutionClock

@[expose] public section

/-!
# Spec / Proof / Genesis

The trusted-anchor store satisfies `WellFormedStore` — the witness for the
genesis premise of `SpecAssumptions` and the `n = 0` base of safety. The two
hypotheses are exactly the python facts the projection cannot carry: the
dropped `anchor_block.state_root == hash_tree_root(anchor_state)` assert ties
the anchor state to the block (here: their slots agree), and genuine hashing
makes the anchor's parent pointer differ from its own root.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root] (cfg : Config)

theorem wellFormedStore_get_forkchoice_store
    (anchor_state : BeaconState Root) (anchor_block : SignedBeaconBlock Root)
    (hslot : anchor_state.slot = anchor_block.message.slot)
    (hparent : anchor_block.message.parent_root ≠ anchor_block.root) :
    WellFormedStore (get_forkchoice_store cfg anchor_state anchor_block) := by
  constructor
  · -- block_roots_nodup
    simp [get_forkchoice_store]
  · -- time_ge_genesis
    simp only [get_forkchoice_store]
    exact Nat.le_add_right _ _
  · -- parent_slot_lt: vacuous — the anchor's parent is not in the store
    intro r hr hpar
    simp only [get_forkchoice_store, List.mem_singleton] at hr hpar
    subst hr
    rw [Function.update_self] at hpar
    exact absurd hpar hparent
  · -- block_state_slot_eq
    intro r hr
    simp only [get_forkchoice_store, List.mem_singleton] at hr
    subst hr
    simp [get_forkchoice_store, hslot]
  · -- justified_known
    simp [get_forkchoice_store]
  · -- finalized_known
    simp [get_forkchoice_store]
  · -- finalized_ancestor_of_justified: both are the anchor; the walk stops
    -- immediately (the anchor's slot is not greater than itself)
    simp only [get_forkchoice_store, is_ancestor, get_ancestor, get_ancestor_aux,
      Function.update_self]
    simp

end FastConfirmation.Spec

/-!
# Spec / Proof / Ancestry

Layer 0, the ancestry toolkit: fuel elimination for `get_ancestor`. The
python recursion is defined exactly on walks that stay inside the store's
known blocks; `WalkKnown` captures that domain, and on it the fuel-bounded
`get_ancestor_aux` is fuel-independent (any fuel above the walked block's
slot computes the same value), unlocking the python-shaped unfold equations
(`get_ancestor_stop`/`get_ancestor_step`) the later layers rewrite with.
-/

namespace FastConfirmation.Spec

variable {Root : Type*}

/-- The parent-walk from `r` down to `slot` stays inside the store's known
blocks — the domain on which python's `get_ancestor` recursion is defined.
Uses the store's own `parent_slot_lt` discipline implicitly: derivations are
finite by construction. -/
inductive WalkKnown (store : Store Root) (slot : Slot) : Root → Prop
  | stop {r : Root} (hr : r ∈ store.block_roots)
      (hle : (store.blocks r).slot ≤ slot) : WalkKnown store slot r
  | step {r : Root} (hr : r ∈ store.block_roots)
      (hgt : slot < (store.blocks r).slot)
      (hp : WalkKnown store slot (store.blocks r).parent_root) :
      WalkKnown store slot r

namespace WalkKnown

theorem root_mem {store : Store Root} {slot : Slot} {r : Root}
    (h : WalkKnown store slot r) : r ∈ store.block_roots := by
  cases h with
  | stop hr _ => exact hr
  | step hr _ _ => exact hr

end WalkKnown

variable [LinearOrder Root]

/-- The root of a fuel-bounded ancestor is independent of the start status.
The first parent step reads its status from the child bid. -/
theorem get_ancestor_aux_root_eq_status (store : Store Root) (slot fuel : ℕ)
    (r : Root) (status status' : PayloadStatus) :
    (get_ancestor_aux store slot fuel (ForkChoiceNode.mk r status)).root =
      (get_ancestor_aux store slot fuel (ForkChoiceNode.mk r status')).root := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [get_ancestor_aux]
    split_ifs <;> rfl

/-- Ancestor beacon roots do not depend on the starting payload status. -/
theorem get_ancestor_root_eq_status (store : Store Root) (slot : Slot)
    (r : Root) (status status' : PayloadStatus) :
    (get_ancestor store (ForkChoiceNode.mk r status) slot).root =
      (get_ancestor store (ForkChoiceNode.mk r status') slot).root := by
  exact get_ancestor_aux_root_eq_status store slot _ r status status'

/-- Equal start roots give equal ancestor roots, including outside the known
walk domain. -/
theorem get_ancestor_root_eq_of_root_eq {store : Store Root}
    {a b : ForkChoiceNode Root} (hab : a.root = b.root) (slot : Slot) :
    (get_ancestor store a slot).root = (get_ancestor store b slot).root := by
  cases a with
  | mk ar ast =>
    cases b with
    | mk br bst =>
      change ar = br at hab
      subst br
      exact get_ancestor_root_eq_status store slot ar ast bst

/-- A strict parent walk discards the start status, so equal roots give
complete equality of its result, rather than only root equality. -/
theorem get_ancestor_eq_of_root_eq_of_lt {store : Store Root}
    {a b : ForkChoiceNode Root} (hab : a.root = b.root) {slot : Slot}
    (hlt : slot < (store.blocks a.root).slot) :
    get_ancestor store a slot = get_ancestor store b slot := by
  cases a with
  | mk ar ast =>
    cases b with
    | mk br bst =>
      change ar = br at hab
      subst br
      simp only [get_ancestor, get_ancestor_aux]
      rw [if_pos hlt, if_pos hlt]

/-- Fuel independence for arbitrary starting status on the known walk domain. -/
theorem get_ancestor_aux_fuel_eq_status {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    ∀ (status : PayloadStatus) (fuel fuel' : ℕ),
      (store.blocks r).slot < fuel → (store.blocks r).slot < fuel' →
      get_ancestor_aux store slot fuel (ForkChoiceNode.mk r status) =
        get_ancestor_aux store slot fuel' (ForkChoiceNode.mk r status) := by
  induction hw with
  | stop hr hle =>
    intro status fuel fuel' hf hf'
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f =>
      cases fuel' with
      | zero => exact absurd hf' (Nat.not_lt_zero _)
      | succ f' =>
        simp only [get_ancestor_aux]
        rw [if_neg (Nat.not_lt.mpr hle), if_neg (Nat.not_lt.mpr hle)]
  | step hr hgt hp ih =>
    intro status fuel fuel' hf hf'
    cases fuel with
    | zero => exact absurd hf (Nat.not_lt_zero _)
    | succ f =>
      cases fuel' with
      | zero => exact absurd hf' (Nat.not_lt_zero _)
      | succ f' =>
        simp only [get_ancestor_aux]
        rw [if_pos hgt, if_pos hgt]
        have hparent_lt := hwf _ hr hp.root_mem
        exact ih _ f f'
          (Nat.lt_of_lt_of_le hparent_lt (Nat.lt_succ_iff.mp hf))
          (Nat.lt_of_lt_of_le hparent_lt (Nat.lt_succ_iff.mp hf'))

/-- Pending-node form of fuel independence. -/
theorem get_ancestor_aux_fuel_eq {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    ∀ fuel fuel' : ℕ, (store.blocks r).slot < fuel → (store.blocks r).slot < fuel' →
      get_ancestor_aux store slot fuel (ForkChoiceNode.mk r .pending) =
        get_ancestor_aux store slot fuel' (ForkChoiceNode.mk r .pending) :=
  get_ancestor_aux_fuel_eq_status hwf hw .pending

/-- At or below the target slot, the walk preserves the complete node. -/
theorem get_ancestor_stop_status {store : Store Root} {slot : Slot}
    {node : ForkChoiceNode Root} (hle : (store.blocks node.root).slot ≤ slot) :
    get_ancestor store node slot = node := by
  rw [get_ancestor, get_ancestor_aux, if_neg (Nat.not_lt.mpr hle)]

/-- Pending-node stop equation. -/
theorem get_ancestor_stop {store : Store Root} {slot : Slot} {r : Root}
    (hle : (store.blocks r).slot ≤ slot) :
    get_ancestor store (ForkChoiceNode.mk r .pending) slot = ForkChoiceNode.mk r .pending :=
  get_ancestor_stop_status hle

/-- Exact Gloas parent-step equation. The child bid resolves the status of
its parent; the parent is not a pending node. -/
theorem get_ancestor_step_status {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {node : ForkChoiceNode Root} (hr : node.root ∈ store.block_roots)
    (hgt : slot < (store.blocks node.root).slot)
    (hp : WalkKnown store slot (store.blocks node.root).parent_root) :
    get_ancestor store node slot =
      get_ancestor store
        (ForkChoiceNode.mk (store.blocks node.root).parent_root
          (get_parent_payload_status store (store.blocks node.root))) slot := by
  rw [get_ancestor, get_ancestor_aux, if_pos hgt]
  rw [get_ancestor]
  exact get_ancestor_aux_fuel_eq_status hwf hp _ _ _ (hwf _ hr hp.root_mem)
    (Nat.lt_succ_self _)

/-- Root form of the parent-step equation. Compared with the phase0 theorem,
only the roots are equal: Gloas resolves the parent's payload status. -/
theorem get_ancestor_step {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hr : r ∈ store.block_roots)
    (hgt : slot < (store.blocks r).slot)
    (hp : WalkKnown store slot (store.blocks r).parent_root) :
    (get_ancestor store (ForkChoiceNode.mk r .pending) slot).root =
      (get_ancestor store (ForkChoiceNode.mk (store.blocks r).parent_root .pending) slot).root := by
  rw [get_ancestor_step_status hwf hr hgt hp]
  exact get_ancestor_root_eq_status store slot _ _ .pending

/-- On the known domain, every status lands at a known root at or below the
requested slot. -/
theorem get_ancestor_spec_status {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    ∀ status : PayloadStatus,
      (get_ancestor store (ForkChoiceNode.mk r status) slot).root ∈ store.block_roots ∧
        (store.blocks (get_ancestor store (ForkChoiceNode.mk r status) slot).root).slot ≤
          slot := by
  induction hw with
  | stop hr hle =>
    intro status
    rw [get_ancestor_stop_status hle]
    exact ⟨hr, hle⟩
  | step hr hgt hp ih =>
    intro status
    rw [get_ancestor_step_status hwf hr hgt hp]
    exact ih _

/-- Pending-node postcondition on the known domain. -/
theorem get_ancestor_spec {store : Store Root}
    (hwf : ∀ r ∈ store.block_roots,
      (store.blocks r).parent_root ∈ store.block_roots →
        (store.blocks (store.blocks r).parent_root).slot < (store.blocks r).slot)
    {slot : Slot} {r : Root} (hw : WalkKnown store slot r) :
    (get_ancestor store (ForkChoiceNode.mk r .pending) slot).root ∈ store.block_roots ∧
      (store.blocks (get_ancestor store (ForkChoiceNode.mk r .pending) slot).root).slot ≤ slot :=
  get_ancestor_spec_status hwf hw .pending

/-- A pending ancestor accepts every payload status at its root. -/
@[simp] theorem is_ancestor_pending (store : Store Root)
    (node : ForkChoiceNode Root) (r : Root) :
    is_ancestor store node (ForkChoiceNode.mk r .pending) =
      decide ((get_ancestor store node (store.blocks r).slot).root = r) := by
  simp [is_ancestor]

/-- Fast Confirmation's root constructor is the pending constructor. -/
@[simp] theorem is_ancestor_get_node_for_root (store : Store Root)
    (node : ForkChoiceNode Root) (r : Root) :
    is_ancestor store node (get_node_for_root r) =
      decide ((get_ancestor store node (store.blocks r).slot).root = r) :=
  is_ancestor_pending store node r

/-- Pending-root ancestry does not depend on the descendant's status. -/
theorem is_ancestor_pending_root_eq (store : Store Root) (r a : Root)
    (status status' : PayloadStatus) :
    is_ancestor store (ForkChoiceNode.mk r status) (get_node_for_root a) =
      is_ancestor store (ForkChoiceNode.mk r status') (get_node_for_root a) := by
  simp only [is_ancestor_get_node_for_root]
  rw [get_ancestor_root_eq_status store _ r status status']

/-- Convert a status-bearing descendant to its pending root for a beacon
ancestry query. -/
theorem is_ancestor_node_root (store : Store Root) (node : ForkChoiceNode Root)
    (r : Root) :
    is_ancestor store node (get_node_for_root r) =
      is_ancestor store (get_node_for_root node.root) (get_node_for_root r) := by
  exact is_ancestor_pending_root_eq store node.root r node.payload_status .pending

/-- A vote's payload flag does not change support for a pending beacon root. -/
@[simp] theorem is_ancestor_supported_pending (store : Store Root)
    (message : LatestMessage Root) (r : Root) :
    is_ancestor store (get_supported_node store message) (ForkChoiceNode.mk r .pending) =
      is_ancestor store (ForkChoiceNode.mk message.root .pending) (ForkChoiceNode.mk r .pending) := by
  unfold get_supported_node
  exact is_ancestor_pending_root_eq store message.root r _ .pending

end FastConfirmation.Spec

end
