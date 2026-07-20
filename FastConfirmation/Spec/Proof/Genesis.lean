import FastConfirmation.Spec.Proof.Trajectory

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
