module
public import FastConfirmation.Spec.Proof.CertExtract
public import FastConfirmation.Spec.Proof.GetLatestConfirmedTrace

@[expose] public section

/-!
# Slot monotonicity of the non-finalized FCR phases

The observed restart guard requires a strictly higher block slot. The
descendant selector walks from its input toward the head and preserves that
slot order. These are local executable facts; the liveness proof must still
show that the finalized-revert guard stays false at actual calls.
-/

namespace FastConfirmation.Spec

variable {Root : Type*} [LinearOrder Root] [Inhabited Root]
variable (cfg : Config) (ext : Externals Root)

/-- The selector does not lower the slot of its input, on the known-walk
domain. -/
theorem getLatestTraceResult_slot_ge_afterObserved
    (query : FastConfirmationStore Root)
    (hwf : ∀ r ∈ query.store.block_roots,
      (query.store.blocks r).parent_root ∈ query.store.block_roots →
        (query.store.blocks (query.store.blocks r).parent_root).slot <
          (query.store.blocks r).slot)
    (hwalk : ∀ t ∈ query.store.block_roots, ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : getLatestAfterObserved cfg ext query ∈ query.store.block_roots) :
    get_block_slot query.store (getLatestAfterObserved cfg ext query) ≤
      get_block_slot query.store (getLatestTraceResult cfg ext query) := by
  let input := getLatestAfterObserved cfg ext query
  by_cases hselector : getLatestSelectorGuard cfg query input
  · have hbetween := find_latest_confirmed_descendant_between cfg ext query
      hwf hwalk hhead input (by simpa only [input] using hinput)
    have hanc := hbetween.1
    simp only [get_node_for_root, is_ancestor_pending,
      decide_eq_true_eq] at hanc
    have hslot := get_ancestor_slot_le hwf
      (hwalk input (by simpa only [input] using hinput)
        (find_latest_confirmed_descendant cfg ext query input) hbetween.2.1)
    rw [hanc] at hslot
    have hyes : get_block_epoch cfg query.store input + 1 ≥
        get_current_store_epoch cfg query.store := hselector
    simpa [getLatestTraceResult, input, hyes, get_block_slot] using hslot
  · have hno : ¬ (get_block_epoch cfg query.store input + 1 ≥
        get_current_store_epoch cfg query.store) := hselector
    simp [getLatestTraceResult, input, hno]

/-- The observed restart and descendant selector together never lower the
slot of the candidate produced by the finalized-revert phase. -/
theorem getLatestTraceResult_slot_ge_afterFinalized
    (query : FastConfirmationStore Root)
    (hwf : ∀ r ∈ query.store.block_roots,
      (query.store.blocks r).parent_root ∈ query.store.block_roots →
        (query.store.blocks (query.store.blocks r).parent_root).slot <
          (query.store.blocks r).slot)
    (hwalk : ∀ t ∈ query.store.block_roots, ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : getLatestAfterObserved cfg ext query ∈ query.store.block_roots) :
    get_block_slot query.store (getLatestAfterFinalized cfg ext query) ≤
      get_block_slot query.store (getLatestTraceResult cfg ext query) :=
  (getLatestAfterObserved_slot_ge_afterFinalized cfg ext query).trans
    (getLatestTraceResult_slot_ge_afterObserved cfg ext query hwf hwalk hhead hinput)

/-- If the finalized guard is false, the entire executable call does not
lower the cached block slot. The liveness proof must establish that guard
failure from votes and production at each actual call. -/
theorem getLatestTraceResult_slot_ge_confirmed_of_no_finalized_revert
    (query : FastConfirmationStore Root)
    (hwf : ∀ r ∈ query.store.block_roots,
      (query.store.blocks r).parent_root ∈ query.store.block_roots →
        (query.store.blocks (query.store.blocks r).parent_root).slot <
          (query.store.blocks r).slot)
    (hwalk : ∀ t ∈ query.store.block_roots, ∀ r ∈ query.store.block_roots,
      WalkKnown query.store (query.store.blocks t).slot r)
    (hhead : (get_head cfg query.store).root ∈ query.store.block_roots)
    (hinput : getLatestAfterObserved cfg ext query ∈ query.store.block_roots)
    (hguard : ¬ getLatestFinalizedRevertGuard cfg ext query) :
    get_block_slot query.store query.confirmed_root ≤
      get_block_slot query.store (getLatestTraceResult cfg ext query) := by
  have hfirst : getLatestAfterFinalized cfg ext query = query.confirmed_root := by
    unfold getLatestAfterFinalized
    split_ifs with h
    · exact False.elim (hguard h)
    · rfl
  rw [← hfirst]
  exact getLatestTraceResult_slot_ge_afterFinalized cfg ext query
    hwf hwalk hhead hinput

end FastConfirmation.Spec

end
